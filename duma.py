import argparse
import asyncio
import hashlib
import html
import json
import logging
import os
import re
import sqlite3
from dataclasses import asdict, dataclass
from datetime import date, datetime, timedelta
from functools import lru_cache
from pathlib import Path
from urllib.parse import urlsplit

import snowballstemmer
from bs4 import BeautifulSoup
from playwright.async_api import TimeoutError as BrowserTimeout, async_playwright

from bot import (
    ATTACHMENT, ATTACHMENT_LIMIT, MOSCOW, Portal, TelegramError, clean,
    extract_document, field, portal_date, same_origin, send,
)

LIST_URL = "https://sozd.duma.gov.ru/oz?b%5BClassOfTheObjectLawmakingId%5D=1&count_items=50"
BILL_PATH = re.compile(r"^/bill/(\d+-\d{1,2})/?$", re.I)
REGISTRATION = r"дата\s+(?:регистрации(?:\s+законопроекта)?|внесения(?:\s+в\s+(?:гд|государственную думу))?)|зарегистрирован"
STAGE = re.compile(
    r"^(?:\d+(?:\.\d+)+(?:\.)?\s+.{4,200}|"
    r"(?:регистрация|внесение)\s+законопроекта.{0,150}|"
    r"(?:первое|второе|третье)\s+чтение.{0,130}|"
    r"(?:рассмотрение|принятие|отклонение|направление|возвращение|снятие|подписание|опубликование)\b.{3,165})$",
    re.I,
)
WORD = re.compile(r"[a-zа-яё]+|\d+", re.I)
STEMMER = snowballstemmer.stemmer("russian")
NO_RESULTS = re.compile(r"ничего не найдено|законопроекты не найдены|найдено\s*:?\s*0\b", re.I)


@dataclass
class ListedBill:
    number: str
    url: str
    registered: str = ""


@dataclass
class Event:
    name: str
    date: str = ""
    detail: str = ""

    @property
    def key(self):
        parts = (clean(value).casefold().replace("ё", "е")
                 for value in (self.name, self.date, self.detail))
        return hashlib.sha256(json.dumps(list(parts), ensure_ascii=False).encode()).hexdigest()


@dataclass
class Bill:
    number: str
    url: str
    registered: str
    title: str
    initiators: str
    status: str
    summary: str
    events: list[Event]
    attachments: dict[str, str]


@lru_cache(maxsize=16000)
def stem(word):
    return STEMMER.stemWord(word)


def tokens(text):
    return [(match, match[0].casefold().replace("ё", "е")) for match in WORD.finditer(text)]


class Keywords:
    def __init__(self, content):
        self.rules = {}
        seen = set()
        for line in content.splitlines():
            phrase = clean(line)
            words = tokens(phrase)
            norms = tuple(word for _, word in words)
            if not norms or norms in seen:
                continue
            seen.add(norms)
            flags = tuple(len(word) > 3 and word.isalpha() and not match[0].isupper()
                          for match, word in words)
            key = stem(norms[0]) if flags[0] else norms[0]
            self.rules.setdefault((flags[0], key), []).append((norms, flags, phrase))
        if not self.rules:
            raise ValueError("Файл ключевых слов пуст")

    def find(self, text):
        text = clean(text)
        words = tokens(text)
        norms = [word for _, word in words]
        stems = [stem(word) if word.isalpha() else word for word in norms]
        for index, word in enumerate(norms):
            rules = self.rules.get((False, word), []) + self.rules.get((True, stems[index]), [])
            for expected, flags, phrase in sorted(rules, key=lambda rule: -len(rule[0])):
                end = index + len(expected)
                if end > len(words):
                    continue
                if any((stems[pos] != stem(value) if inflect else norms[pos] != value)
                       for pos, (value, inflect) in enumerate(zip(expected, flags), index)):
                    continue
                # Punctuation inside legal references is allowed. Sentence breaks are separate.
                if any(re.search(r"[.!?;]", text[words[pos][0].end():words[pos + 1][0].start()])
                       for pos in range(index, end - 1)):
                    continue
                left = max(0, words[index][0].start() - 48)
                right = min(len(text), words[end - 1][0].end() + 70)
                fragment = ("…" if left else "") + text[left:right].strip()
                if right < len(text):
                    fragment += "…"
                return f"{phrase} — «{fragment}»"
        return None


def markup_body(markup):
    soup = BeautifulSoup(markup, "html.parser")
    for node in soup.select("script, style, nav, footer, header, [hidden]"):
        node.decompose()
    return soup


def date_in(text):
    try:
        value = portal_date(text)
    except ValueError:
        return ""
    return value.isoformat() if value else ""


def listing_entries(markup, base):
    soup = markup_body(markup)
    found = {}
    for link in soup.select("a[href]"):
        url = same_origin(base, link["href"])
        match = BILL_PATH.fullmatch(urlsplit(url).path) if url else None
        if not match or match[1] in found:
            continue
        registered = ""
        row = link.find_parent(["tr", "article", "li"])
        if row:
            table = row.find_parent("table")
            if table:
                headings = table.select("thead tr:last-child th") or table.find_all("th")
                index = next((idx for idx, element in enumerate(headings)
                              if re.search(REGISTRATION, clean(element.get_text(" ")), re.I)), None)
                cells = row.find_all("td", recursive=False)
                if index is not None and index < len(cells):
                    registered = date_in(cells[index].get_text(" ", strip=True))
            if not registered:
                text = row.get_text(" ", strip=True)
                label = re.search(rf"(?:{REGISTRATION})\s*:?\s*(.{{1,40}})", text, re.I)
                if label:
                    registered = date_in(label[1])
        found[match[1]] = ListedBill(match[1], url, registered)
    if found or NO_RESULTS.search(soup.get_text(" ", strip=True)):
        return list(found.values())
    raise ValueError("На странице СОЗД нет ссылок на законопроекты или сообщения о пустой выдаче")


def timeline(lines, registered):
    events = []
    stage = ""
    chunk = []

    def collect():
        if not stage:
            return
        # Different dated actions can be recorded under the same stage heading.
        actions = []
        for line in chunk:
            date_text = re.sub(r"^дата(?:\s+события)?\s*:\s*", "", line, flags=re.I)
            value = date_in(date_text)
            if value and re.fullmatch(r"\d{2}\.\d{2}\.\d{4}|\d{4}-\d{2}-\d{2}|"
                                      r"\d{1,2}\s+[а-яё]+\s+\d{4}", date_text, re.I):
                actions.append((value, []))
            elif actions and not re.match(r"^(?:скачать|документ|материалы)\b", line, re.I):
                actions[-1][1].append(line)
        if not actions and re.search(r"регистрац|внесение", stage, re.I):
            actions.append((registered, []))
        for value, details in actions:
            detail = clean(" ".join(details))[:550]
            event = Event(stage, value, detail)
            if event not in events:
                events.append(event)

    parts = iter(lines)
    for line in parts:
        if re.fullmatch(r"\d+(?:\.\d+)+\.?", line):
            line += " " + next(parts, "")
        if STAGE.fullmatch(line):
            collect()
            stage = line
            chunk = []
        elif stage:
            chunk.append(line)
    collect()
    return sorted(events, key=lambda event: event.date)


def parse_bill(markup, item):
    soup = markup_body(markup)
    body = soup.select_one("main, [role=main]") or soup.body or soup
    lines = [clean(line) for line in body.stripped_strings if clean(line)]
    text = "\n".join(lines)
    if not re.search(rf"(?<!\d){re.escape(item.number)}(?!\d)", text):
        raise ValueError("В карточке не найден номер законопроекта")
    title = field(body, text, r"наименование(?: законопроекта)?|название законопроекта")
    if not title:
        for node in body.select("h1, h2, h3, .bill-title, .bill-name"):
            value = clean(node.get_text(" "))
            value = re.sub(rf"^(?:законопроект\s*)?№?\s*{re.escape(item.number)}\s*[.\-–:]?\s*",
                           "", value, flags=re.I)
            if len(value) > 10 and not re.match(r"^законопроект(?:\s*[№\d]|$)", value, re.I):
                title = value
                break
    if not title:
        title = next((line for line in lines if re.match(r"^О(?:б|бо)?\s+", line, re.I)), "")
    if not title:
        raise ValueError("В карточке не найдено название законопроекта")
    registered = date_in(field(body, text, REGISTRATION)) or item.registered
    if not registered:
        label = re.search(rf"(?:{REGISTRATION})\s*:?\s*(.{{1,45}})", text, re.I)
        registered = date_in(label[1]) if label else ""
    if not registered:
        for index, line in enumerate(lines):
            if re.search(r"(?:регистрация законопроекта|\(внесение\))", line, re.I):
                registered = next((value for nearby in lines[index:index + 7]
                                   if (value := date_in(nearby))), "")
                if registered:
                    break
    if not registered:
        raise ValueError("В карточке не найдена дата регистрации")
    initiators = field(body, text, r"инициатор(?:ы)?(?: законопроекта)?|"
                                  r"субъект(?:ы)? права законодательной инициативы")
    summary = field(body, text, r"краткое содержание|аннотация|содержание законопроекта|суть законопроекта")
    status = field(body, text, r"(?:текущий )?статус(?: законопроекта)?|текущая стадия|стадия рассмотрения|состояние законопроекта")
    events = timeline(lines, registered)
    if not status and not events:
        raise ValueError("В карточке не найдены статус или этапы рассмотрения")
    attachments = {}
    for link in body.select("a[href]"):
        href = link["href"]
        label = clean(link.get_text(" ", strip=True) or link.get("title", ""))
        url = same_origin(item.url, href)
        if url and (ATTACHMENT.search(f"{href} {label}") or link.has_attr("download")):
            attachments[url] = label
    primary = {url: label for url, label in attachments.items()
               if re.search(r"текст законопроекта|пояснительн\w* запис|текст проекта", label, re.I)}
    return Bill(item.number, item.url, registered, title, initiators, status, summary, events,
                primary or attachments)


def notice(bill, event=None, reason="", previous=""):
    def esc(value, limit=850):
        return html.escape(value[:limit] + ("…" if len(value) > limit else ""))

    convocation = bill.number.rsplit("-", 1)[1]
    heading = "⚡ Новый законопроект!" if reason else "🔔 Изменение статуса законопроекта"
    lines = [f"<b>{heading}</b>", "",
             f'📜 <a href="{html.escape(bill.url, quote=True)}">Законопроект № {esc(bill.number)}</a>',
             esc(bill.title), f"Дата регистрации: {bill.registered}"]
    if bill.initiators:
        lines.extend(["", f"<b>Инициаторы:</b> {esc(bill.initiators)}"])
    lines.append("")
    if event:
        lines.append(f"✔️ <b>{esc(event.name, 260)}</b>")
        if event.date:
            lines.append(f"Дата: {event.date}")
        if event.detail:
            lines.append(f"📄 {esc(event.detail, 420)}")
    elif previous:
        lines.append(f"Предыдущий статус: {esc(previous, 240)}")
    if bill.status and (not event or clean(bill.status) != clean(event.name)):
        lines.append(f"<b>Текущий статус:</b> {esc(bill.status, 290)}")
    lines.extend(["", f"🗄 Законопроект {convocation}-го созыва"])
    if reason:
        lines.append(f"<b>Почему проект попал в подборку</b> — {esc(reason, 240)}")
    return "\n".join(lines)


class DumaPortal:
    def __init__(self, context, url):
        self.context = context
        self.url = url
        self.list_page = None
        self.card_page = None

    async def open(self, page, url):
        response = await page.goto(url, wait_until="domcontentloaded", timeout=30000)
        if response is None or not response.ok:
            raise RuntimeError(f"СОЗД недоступна (HTTP {response.status if response else '?'})")

    async def listing(self, previous):
        last_error = "Список СОЗД не изменился после перехода"
        for _ in range(25):
            try:
                items = listing_entries(await self.list_page.content(), self.list_page.url)
                if tuple(item.number for item in items) != previous:
                    return items
            except ValueError as error:
                last_error = str(error)
            await asyncio.sleep(1)
        raise RuntimeError(last_error)

    async def next_page(self):
        page = self.list_page
        next_link = page.locator(
            Portal.NEXT + ', .pagination-next, a[aria-label="Далее"], '
            '.pagination [title="Следующая страница"]'
        ).filter(visible=True).first
        if not await next_link.count():
            next_link = page.locator(".pagination, .pager").get_by_text(
                re.compile(r"^(?:следующая|далее|впер[её]д|›|»)$", re.I), exact=True
            ).filter(visible=True).first
        if not await next_link.count():
            current = page.locator(
                '[aria-current=page], .pagination .active, .pagination .current, .pager .active'
            ).filter(visible=True).first
            if await current.count():
                number = clean(await current.inner_text())
                if number.isdecimal():
                    next_link = page.locator('.pagination, .pager, nav').get_by_text(
                        str(int(number) + 1), exact=True
                    ).filter(visible=True).first
                    if not await next_link.count():
                        return False
        if not await next_link.count():
            return None
        if await next_link.evaluate("e => !!e.closest('[disabled], [aria-disabled=true], .disabled')"):
            return False
        await next_link.click(timeout=10000)
        return True

    async def read(self, item):
        if self.card_page is None:
            self.card_page = await self.context.new_page()
        await self.open(self.card_page, item.url)
        last_error = None
        for _ in range(16):
            try:
                return parse_bill(await self.card_page.content(), item)
            except ValueError as error:
                last_error = error
                await asyncio.sleep(0.7)
        raise last_error

    async def discover(self, since):
        if self.list_page is None:
            self.list_page = await self.context.new_page()
        await self.open(self.list_page, self.url)
        previous = None
        seen_pages = set()
        oldest_previous = None
        while True:
            items = await self.listing(previous)
            if not items:
                return
            signature = tuple(item.number for item in items)
            if signature in seen_pages:
                raise RuntimeError("СОЗД повторила страницу выдачи")
            seen_pages.add(signature)
            dates = []
            for item in items:
                bill = None
                if not item.registered:
                    bill = await self.read(item)
                    item.registered = bill.registered
                registered = date.fromisoformat(item.registered)
                dates.append(registered)
                if registered >= since:
                    yield item, bill
            recent, oldest = max(dates), min(dates)
            if dates != sorted(dates, reverse=True) or (
                    oldest_previous is not None and recent > oldest_previous):
                raise RuntimeError("В СОЗД выдача должна идти от новых дат регистрации к старым")
            if recent < since:
                return
            advance = await self.next_page()
            if advance is False:
                return
            if advance is None:
                if oldest < since:
                    return
                raise RuntimeError("Не удалось подтвердить последнюю страницу или найти пагинацию СОЗД")
            previous = signature
            oldest_previous = oldest

    async def reason(self, bill, keywords):
        for text in (bill.title, bill.summary):
            if reason := keywords.find(text):
                return reason
        failures = 0
        for url, label in bill.attachments.items():
            try:
                response = await self.context.request.get(url, timeout=25000)
                try:
                    if not response.ok or int(response.headers.get("content-length", "0")) > ATTACHMENT_LIMIT:
                        raise ValueError("Документ недоступен или слишком велик")
                    data = await response.body()
                    if len(data) > ATTACHMENT_LIMIT:
                        raise ValueError("Документ слишком велик")
                    description = response.headers.get("content-disposition", "")
                    text = await asyncio.to_thread(extract_document, data, f"{url} {label} {description}")
                    if not text.strip():
                        raise ValueError("У документа отсутствует текстовый слой")
                    if reason := keywords.find(text):
                        return reason
                finally:
                    await response.dispose()
            except Exception as error:
                failures += 1
                logging.warning("СОЗД № %s: вложение не проверено (%s)", bill.number, type(error).__name__)
        if failures:
            raise RuntimeError(f"Не удалось проверить вложения: {failures}")
        return None


class Watch:
    def __init__(self, path, start):
        self.db = sqlite3.connect(path)
        self.db.row_factory = sqlite3.Row
        with self.db:
            self.db.executescript("""
                CREATE TABLE IF NOT EXISTS duma_meta (key TEXT PRIMARY KEY, value TEXT NOT NULL);
                CREATE TABLE IF NOT EXISTS duma_bills (
                    number TEXT PRIMARY KEY, item TEXT NOT NULL, registered TEXT NOT NULL,
                    tracked INTEGER NOT NULL DEFAULT 0, reason TEXT NOT NULL DEFAULT '',
                    status TEXT NOT NULL DEFAULT '', seen TEXT NOT NULL DEFAULT '[]',
                    next_check TEXT DEFAULT ''
                );
                CREATE TABLE IF NOT EXISTS duma_outbox (
                    id INTEGER PRIMARY KEY, number TEXT NOT NULL, body TEXT NOT NULL,
                    sent INTEGER NOT NULL DEFAULT 0, next_attempt TEXT NOT NULL DEFAULT ''
                );
            """)
            self.db.execute("INSERT OR IGNORE INTO duma_meta VALUES ('start', ?)", (start.isoformat(),))

    def since(self, today):
        values = dict(self.db.execute("SELECT key, value FROM duma_meta"))
        start = date.fromisoformat(values["start"])
        last = date.fromisoformat(values.get("scanned", values["start"]))
        return max(start, min(today, last) - timedelta(days=2))

    def scanned(self, today):
        with self.db:
            self.db.execute("INSERT OR REPLACE INTO duma_meta VALUES ('scanned', ?)", (today.isoformat(),))
            oldest = (today - timedelta(days=3)).isoformat()
            self.db.execute("DELETE FROM duma_bills WHERE tracked=0 AND registered < ? "
                            "AND next_check IS NULL",
                            (oldest,))

    def add(self, item):
        with self.db:
            self.db.execute(
                "INSERT OR IGNORE INTO duma_bills (number, item, registered) VALUES (?, ?, ?)",
                (item.number, json.dumps(asdict(item), ensure_ascii=False), item.registered),
            )

    def due(self, now):
        return self.db.execute("SELECT * FROM duma_bills WHERE next_check<=? ORDER BY tracked, number",
                               (now.isoformat(),)).fetchall()

    def delay(self, number, when):
        with self.db:
            self.db.execute("UPDATE duma_bills SET next_check=? WHERE number=?", (when.isoformat(), number))

    def exclude(self, number):
        with self.db:
            self.db.execute("UPDATE duma_bills SET next_check=NULL WHERE number=?", (number,))

    def observe(self, row, bill, reason):
        if not bill.status and bill.events:
            bill.status = bill.events[-1].name
        status = clean(bill.status) or row["status"]
        old = set(json.loads(row["seen"]))
        notes = []
        if not row["tracked"]:
            first = next((event for event in bill.events if re.search(
                r"регистрац|\(внесение\)", event.name, re.I)), None)
            notes.append(notice(bill, first, reason))
        else:
            changes = [event for event in bill.events if event.key not in old]
            notes.extend(notice(bill, event) for event in changes)
            if not changes and status and status.casefold() != row["status"].casefold():
                notes.append(notice(bill, previous=row["status"]))
        seen = sorted(old | {event.key for event in bill.events})
        with self.db:
            self.db.execute("UPDATE duma_bills SET tracked=1, reason=?, status=?, seen=?, next_check='' WHERE number=?",
                            (reason, status, json.dumps(seen), bill.number))
            self.db.executemany("INSERT INTO duma_outbox (number, body) VALUES (?, ?)",
                                ((bill.number, note) for note in notes))

    def pending(self, now):
        return self.db.execute("""SELECT item.* FROM duma_outbox item WHERE item.sent=0
            AND item.next_attempt<=? AND NOT EXISTS (
                SELECT 1 FROM duma_outbox older WHERE older.number=item.number AND older.sent=0
                AND older.id<item.id
            ) ORDER BY item.id LIMIT 1""", (now.isoformat(),)).fetchone()

    def delivered(self, item):
        with self.db:
            self.db.execute("UPDATE duma_outbox SET sent=1 WHERE id=?", (item["id"],))

    def delivery_retry(self, item, when):
        with self.db:
            self.db.execute("UPDATE duma_outbox SET next_attempt=? WHERE id=?",
                            (when.isoformat(), item["id"]))


async def check(portal, watch, keywords, sender):
    now = datetime.now(MOSCOW)
    today = now.date()
    found = {}
    failures = 0
    try:
        async for item, bill in portal.discover(watch.since(today)):
            watch.add(item)
            if bill:
                found[item.number] = bill
        watch.scanned(today)
    except Exception as error:
        failures += 1
        logging.warning("Ошибка списка СОЗД: %s", error)
    for row in watch.due(now):
        item = ListedBill(**json.loads(row["item"]))
        try:
            bill = found.get(item.number) or await portal.read(item)
            if row["tracked"]:
                reason = row["reason"]
            else:
                reason = await portal.reason(bill, keywords)
            if reason:
                watch.observe(row, bill, reason)
            elif (today - date.fromisoformat(item.registered)).days < 3:
                watch.delay(item.number, now + timedelta(hours=1))
            else:
                watch.exclude(item.number)
        except Exception as error:
            failures += 1
            watch.delay(item.number, now + timedelta(minutes=5))
            logging.warning("СОЗД № %s: %s", item.number, error)
    sent = 0
    while item := watch.pending(datetime.now(MOSCOW)):
        try:
            await sender(item["body"])
            watch.delivered(item)
            sent += 1
        except TelegramError as error:
            failures += 1
            watch.delivery_retry(item, datetime.now(MOSCOW) + timedelta(seconds=max(60, error.retry_after)))
            logging.warning("Отправка СОЗД № %s: %s", item["number"], error)
            break
    logging.info("Проверка СОЗД завершена. Уведомлений: %d. Ошибок: %d", sent, failures)
    return failures


async def run(args):
    token = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
    chat = os.getenv("TELEGRAM_CHAT_ID", "").strip()
    if not args.dry_run and (not re.fullmatch(r"\d+:[\w-]+", token) or not chat):
        raise SystemExit("Задайте TELEGRAM_BOT_TOKEN и TELEGRAM_CHAT_ID.")
    interval = int(os.getenv("POLL_INTERVAL_SECONDS", "300"))
    if interval < 30 or args.days < 1:
        raise SystemExit("Интервал должен быть от 30 секунд, --days от 1.")
    keyword_path = Path(os.getenv("DUMA_KEYWORDS_PATH", Path(__file__).with_name("keywords.txt")))
    keywords = Keywords(keyword_path.read_text(encoding="utf-8-sig"))
    path = ":memory:"
    if not args.dry_run:
        path = Path(os.getenv("DUMA_DATABASE_PATH", "data/duma.sqlite3"))
        path.parent.mkdir(parents=True, exist_ok=True)
    watch = Watch(path, datetime.now(MOSCOW).date() - timedelta(days=args.days - 1))
    try:
        async with async_playwright() as playwright:
            browser = await playwright.chromium.launch(executable_path=os.getenv("CHROMIUM_EXECUTABLE") or None)
            context = await browser.new_context()
            portal = DumaPortal(context, os.getenv("DUMA_LIST_URL") or LIST_URL)

            async def sender(body):
                if args.dry_run:
                    print(body, flush=True)
                else:
                    await asyncio.sleep(1.1)
                    await send(context.request, token, chat, body, preview=True)

            while True:
                failures = await check(portal, watch, keywords, sender)
                if args.once or args.dry_run:
                    return int(bool(failures))
                await asyncio.sleep(interval)
    finally:
        watch.db.close()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Мониторинг внесения и рассмотрения законопроектов Госдумы")
    parser.add_argument("--once", action="store_true", help="выполнить одну проверку")
    parser.add_argument("--dry-run", action="store_true", help="проверить без Telegram и постоянной базы")
    parser.add_argument("--days", type=int, default=1, help="глубина первой проверки в календарных днях")
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
    raise SystemExit(asyncio.run(run(parser.parse_args())))
