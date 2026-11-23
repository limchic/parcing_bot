import argparse
import asyncio
import html
import io
import json
import logging
import os
import re
import sqlite3
import subprocess
import tempfile
import zipfile
from dataclasses import asdict, dataclass
from datetime import date, datetime, timedelta
from pathlib import Path
from urllib.parse import urljoin, urlsplit
from zoneinfo import ZoneInfo

from bs4 import BeautifulSoup
from defusedxml.ElementTree import fromstring
from playwright.async_api import TimeoutError as PlaywrightTimeout, async_playwright
from pypdf import PdfReader

PORTAL = "https://regulation.gov.ru/projects/?type=Grid"
MOSCOW = ZoneInfo("Europe/Moscow")
MONTHS = "января февраля марта апреля мая июня июля августа сентября октября ноября декабря".split()
PROJECT_ID = re.compile(r"\b\d{2}/\d{2}/\d{2}-\d{2}/\d{5,}\b")
CARD_PATH = re.compile(r"/projects?/\d+(?:/|$)|/publicview(?:/|$)|/npa/\d+", re.I)
MINISTRY = re.compile(
    r"\b(?:минтранс\w*|минэкономразвити\w*|минфин\w*)(?:\s+россии)?\b|"
    r"министерств\w*\s+(?:транспорт\w*|экономическ\w*\s+развити\w*|финанс\w*)"
    r"\s+(?:российской федерации|россии)\b", re.I,
)
TOPIC = re.compile(
    r"\b(?:железнодорож\w*|ж\.?\s*/\s*д\.?|транспорт\w*|"
    r"пассажирск\w*\s+(?:\w+\s+){0,2}перевоз\w*|"
    r"перевоз\w*\s+(?:\w+\s+){0,2}пассажир\w*|"
    r"подведомственн\w*\s+(?:\w+\s+){0,2}(?:организац|учрежден|предприят)\w*)\b|"
    r"\bОКВЭД(?:\s*2)?\s*[:№-]?\s*(?:49|50|51|52)(?:\.\d{1,2}){0,2}\b|"
    r"\b(?:08\.11\.2007.{0,12}259|10\.01\.2003.{0,12}(?:17|18)|"
    r"09\.02\.2007.{0,12}16)[\s‑–-]*ФЗ\b", re.I,
)
ATTACHMENT = re.compile(r"\.(?:docx?|pdf|rtf|txt)(?:$|[?#\s])|download|скачать", re.I)
ATTACHMENT_LIMIT = 25 * 1024 * 1024


@dataclass
class Project:
    id: str
    title: str
    url: str
    published: str
    developer: str = ""
    keywords: str = ""
    initiator: str = ""
    status: str = ""
    deadline: str = ""


def clean(value):
    return " ".join(value.split())


def portal_date(value):
    for pattern, fmt in ((r"\b\d{2}\.\d{2}\.\d{4}\b", "%d.%m.%Y"),
                         (r"\b\d{4}-\d{2}-\d{2}\b", "%Y-%m-%d")):
        if match := re.search(pattern, value):
            return datetime.strptime(match[0], fmt).date()
    if match := re.search(r"(\d{1,2})\s+(" + "|".join(MONTHS) + r")\s+(\d{4})", value.lower()):
        return date(int(match[3]), MONTHS.index(match[2]) + 1, int(match[1]))
    return None


def same_origin(base, href):
    result = urljoin(base, href)
    target, origin = urlsplit(result), urlsplit(base)
    if target.scheme == origin.scheme and target.netloc == origin.netloc:
        return result
    return None


def parse_listing(markup, base):
    soup = BeautifulSoup(markup, "html.parser")
    for table in soup.select("table, [role=grid], [role=table]"):
        headers = [clean(cell.get_text(" ", strip=True)).lower()
                   for cell in table.select("th, [role=columnheader]")]
        published_column = next((i for i, label in enumerate(headers)
                                 if label.startswith("дата публ")), None)
        if published_column is None:
            continue
        developer_column = next((i for i, label in enumerate(headers)
                                 if label.startswith(("орган гос", "разработчик"))), None)
        keywords_column = next((i for i, label in enumerate(headers)
                                if label.startswith("ключевые слова")), None)
        projects = []
        for row in table.select("tr, [role=row]"):
            cells = row.select("td, [role=gridcell], [role=cell]")
            if not cells:
                continue
            values = [clean(cell.get_text(" ", strip=True)) for cell in cells]
            identifier = PROJECT_ID.search(" ".join(values))
            if not identifier:
                if len(cells) == 1 and re.search(r"нет данных|ничего не найдено|проектов нет",
                                                  values[0], re.I):
                    continue
                raise ValueError("В таблице обнаружена строка без ID проекта")
            published = portal_date(values[published_column])
            links = [(same_origin(base, link["href"]), clean(link.get_text(" ", strip=True)))
                     for link in row.select("a[href]")]
            link = next(((url, title) for url, title in links
                         if url and title and CARD_PATH.search(urlsplit(url).path)), None)
            if link is None:
                link = next(((url, title) for url, title in links
                             if url and title == values[0] and url != base), None)
            if not (published and link):
                raise ValueError(f"Не найдена дата публикации или карточка {identifier[0]}")
            projects.append(Project(identifier[0], link[1], link[0], published.isoformat(),
                                    values[developer_column] if developer_column is not None else "",
                                    values[keywords_column] if keywords_column is not None else ""))
        if projects or re.search(r"нет данных|ничего не найдено|проектов нет",
                                 table.get_text(" ", strip=True), re.I):
            return projects
        raise ValueError("Таблица проектов пока пуста")
    raise ValueError("На портале не найдена таблица с датой публикации")


LABELS = {
    "developer": r"разработчик(?: проекта)?|орган государственной власти",
    "initiator": r"инициатор(?: проекта)?",
    "status": r"(?:текущий )?статус(?: проекта)?|текущий этап|этап разработки",
    "deadline": r"(?:планируемая )?дата окончания (?:общественного |публичного )?обсуждения|"
                r"(?:срок|окончание) (?:общественного |публичного )?обсуждения|"
                r"публичное обсуждение до",
}


def field(soup, lines, expression):
    for node in soup.find_all(string=re.compile(rf"^\s*(?:{expression})\s*:?\s*$", re.I)):
        parent = node.parent
        for label in (parent, parent.parent):
            if label is None or not re.fullmatch(rf"(?:{expression})\s*:?",
                                                 clean(label.get_text(" ")), re.I):
                continue
            sibling = label.find_next_sibling()
            if sibling is not None and sibling.name not in ("script", "style"):
                value = clean(sibling.get_text(" "))
                if value:
                    return value
    match = re.search(rf"^\s*(?:{expression})\s*:\s*([^\n]+)", lines, re.I | re.M)
    return clean(match[1]) if match else ""


def enrich(project, markup):
    soup = BeautifulSoup(markup, "html.parser")
    body = soup.select_one("main, [role=main]") or soup.body or soup
    for node in body.select("script, style, nav, footer, header"):
        node.decompose()
    lines = body.get_text("\n", strip=True)
    if project.id not in lines and clean(project.title).casefold() not in clean(lines).casefold():
        raise ValueError(f"Карточка не содержит ID или название {project.id}")
    for key, expression in LABELS.items():
        value = field(body, lines, expression).strip()
        if value not in ("", "-", "—", "Не указано"):
            if key == "deadline":
                value = portal_date(value)
                if value:
                    project.deadline = value.isoformat()
            else:
                setattr(project, key, value)
    if not project.deadline:
        period = re.search(
            r"(?:период|срок)\s+(?:общественного |публичного )?обсуждения"
            r"[\s\S]{0,130}?\b(?:по|до)\s+([^\n]+)", lines, re.I)
        if period and (end := portal_date(period[1])):
            project.deadline = end.isoformat()
    attachments = {}
    for link in body.select("a[href]"):
        href = link["href"]
        label = clean(link.get_text(" ", strip=True)) or link.get("title", "")
        url = same_origin(project.url, href)
        if url and href and not href.startswith("#") and (
                link.has_attr("download") or ATTACHMENT.search(f"{href} {label}")):
            attachments[url] = label
    for value in (project.developer, project.initiator):
        if value:
            lines = re.sub(re.escape(value), "", lines, flags=re.I)
    return MINISTRY.sub("", lines), attachments


def evidence(text):
    text = clean(text)
    match = TOPIC.search(text)
    if match is None:
        return None
    left = max(0, match.start() - 55)
    right = min(len(text), match.end() + 85)
    return ("…" if left else "") + text[left:right].strip() + ("…" if right < len(text) else "")


def extract_document(data, filename):
    filename = filename.lower()
    if data.startswith(b"%PDF"):
        return "\n".join(page.extract_text() or "" for page in PdfReader(io.BytesIO(data)).pages)
    if data.startswith(b"PK"):
        with zipfile.ZipFile(io.BytesIO(data)) as archive:
            document = archive.getinfo("word/document.xml")
            if document.file_size > ATTACHMENT_LIMIT:
                raise ValueError("Документ превышает допустимый размер")
            root = fromstring(archive.read(document))
            namespace = "{http://schemas.openxmlformats.org/wordprocessingml/2006/main}"
            return "\n".join("".join(node.text or "" for node in para.iter(namespace + "t"))
                             for para in root.iter(namespace + "p"))
    if data.startswith(bytes.fromhex("d0cf11e0a1b11ae1")):
        with tempfile.NamedTemporaryFile(suffix=".doc") as document:
            document.write(data)
            document.flush()
            result = subprocess.run(["antiword", "-m", "UTF-8.txt", document.name],
                                    capture_output=True, timeout=30, check=True)
            return result.stdout.decode("utf-8")
    if data.startswith(b"{\\rtf"):
        from striprtf.striprtf import rtf_to_text
        return rtf_to_text(data.decode("latin-1"))
    if ".txt" in filename:
        try:
            return data.decode("utf-8-sig")
        except UnicodeDecodeError:
            return data.decode("cp1251")
    raise ValueError("Неизвестный формат вложения")


def message(project, reason):
    def esc(value, limit=300):
        return html.escape(value[:limit] + ("…" if len(value) > limit else ""))
    def display_date(value):
        return date.fromisoformat(value).strftime("%d.%m.%Y")

    lines = [f"<b>{esc(project.title, 700)}</b>",
             f"ID проекта: {esc(project.id)}",
             f"Разработчик: {esc(project.developer or 'не указан на портале')}"]
    if project.initiator:
        lines.append(f"Инициатор: {esc(project.initiator)}")
    lines.extend([f"Дата публикации: {display_date(project.published)}",
                  f"Текущий статус: {esc(project.status or 'не указан на портале')}"])
    if project.deadline:
        lines.append(f"Окончание обсуждения: {display_date(project.deadline)}")
    lines.extend([f'<a href="{html.escape(project.url, quote=True)}">Карточка проекта</a>',
                  f"<b>Почему проект попал в подборку</b> — {esc(reason)}"])
    return "\n".join(lines)


class Portal:
    NEXT = (
        '[rel=next], [aria-label*="Следующ" i], [title*="Следующ" i], '
        '[aria-label*="next" i], [title*="next page" i], [title="Next" i], '
        '.pagination .next, .pager .next, .k-pager-next, .dx-next-button, '
        '.mud-pagination-next-button, .ant-pagination-next, .p-paginator-next'
    )

    def __init__(self, context, url):
        self.context = context
        self.url = url
        self.list_page = None
        self.card_page = None

    async def listing(self):
        markup = await self.list_page.content()
        return parse_listing(markup, self.list_page.url)

    async def wait_listing(self, previous=None):
        for _ in range(45):
            try:
                projects = await self.listing()
                signature = tuple(project.id for project in projects)
                if signature != previous:
                    return projects
            except (ValueError, IndexError) as error:
                last_error = str(error)
            else:
                last_error = "Список проектов не изменился после перехода"
            await asyncio.sleep(1)
        raise RuntimeError(last_error)

    async def next_page(self):
        button = self.list_page.locator(self.NEXT).filter(visible=True).first
        if not await button.count():
            button = self.list_page.get_by_role("button", name=re.compile(
                r"^(?:далее|следующая(?: страница)?|вперёд)$", re.I
            )).filter(visible=True).first
        if not await button.count():
            current = self.list_page.locator(
                '[aria-current=page], .pagination .active, .pager .active'
            ).filter(visible=True).first
            if await current.count():
                number = clean(await current.inner_text())
                if number.isdecimal():
                    pagination = self.list_page.locator(
                        '.pagination, .pager, nav[aria-label*="страниц" i], '
                        'nav[aria-label*="pagination" i]'
                    )
                    button = pagination.get_by_text(str(int(number) + 1), exact=True).filter(
                        visible=True).first
                    if not await button.count():
                        return False
            if not await button.count():
                raise RuntimeError("Не удалось определить элемент пагинации портала")
        disabled = await button.evaluate(
            "e => !!e.closest('[disabled], [aria-disabled=true], .disabled, .k-disabled, .ant-pagination-disabled')"
        )
        if disabled:
            return False
        await button.click()
        return True

    async def scan(self, since):
        if self.list_page is None:
            self.list_page = await self.context.new_page()
        response = await self.list_page.goto(self.url, wait_until="domcontentloaded")
        if response is None or not response.ok:
            raise RuntimeError(f"Список проектов недоступен (HTTP {response.status if response else '?'})")
        projects = await self.wait_listing()
        previous_date = date.max
        seen_pages = set()
        while projects:
            signature = tuple(project.id for project in projects)
            if signature in seen_pages:
                raise RuntimeError("Портал повторил уже просмотренную страницу")
            seen_pages.add(signature)
            dates = [date.fromisoformat(project.published) for project in projects]
            if dates != sorted(dates, reverse=True) or dates[0] > previous_date:
                raise RuntimeError("Таблица должна быть отсортирована по дате публикации от новых к старым")
            for project, published in zip(projects, dates):
                if published >= since:
                    yield project
            if dates[-1] < since or not await self.next_page():
                return
            previous_date = dates[-1]
            projects = await self.wait_listing(signature)

    async def match(self, project):
        if self.card_page is None:
            self.card_page = await self.context.new_page()
        response = await self.card_page.goto(project.url, wait_until="domcontentloaded")
        if response is None or not response.ok:
            raise RuntimeError(f"Карточка недоступна (HTTP {response.status if response else '?'})")
        await self.card_page.locator("body").get_by_text(
            re.compile(re.escape(project.id) + "|" + re.escape(project.title), re.I)
        ).first.wait_for(timeout=15000)
        # Allow dynamically loaded fields and document links to finish rendering.
        try:
            await self.card_page.wait_for_load_state("networkidle", timeout=5000)
        except PlaywrightTimeout:
            pass
        card_text, attachments = enrich(project, await self.card_page.content())
        if not MINISTRY.search(project.initiator or project.developer):
            return None
        reason = evidence(" ".join((project.title, project.keywords))) or evidence(card_text)
        if reason:
            return reason
        failed = 0
        for url, label in attachments.items():
            try:
                response = await self.context.request.get(url, timeout=30000)
                try:
                    length = int(response.headers.get("content-length", "0"))
                    if not response.ok or length > ATTACHMENT_LIMIT:
                        raise ValueError("Вложение недоступно или слишком велико")
                    data = await response.body()
                    if len(data) > ATTACHMENT_LIMIT:
                        raise ValueError("Вложение слишком велико")
                    document = await asyncio.to_thread(extract_document, data, url + " " + label)
                    if not document.strip():
                        raise ValueError("В документе нет текстового слоя")
                    if reason := evidence(document):
                        return reason
                finally:
                    await response.dispose()
            except Exception as error:
                failed += 1
                logging.warning("Вложение проекта %s: %s", project.id, type(error).__name__)
        if failed:
            raise RuntimeError(f"Не проверено вложений: {failed}")
        return None


class Store:
    def __init__(self, path, first_date):
        self.db = sqlite3.connect(path)
        self.db.row_factory = sqlite3.Row
        with self.db:
            self.db.execute("""CREATE TABLE IF NOT EXISTS projects (
                id TEXT PRIMARY KEY, project TEXT NOT NULL, status TEXT NOT NULL,
                message TEXT, next_attempt TEXT NOT NULL DEFAULT '',
                attempts INTEGER NOT NULL DEFAULT 0
            )""")
            self.db.execute("CREATE TABLE IF NOT EXISTS meta (key TEXT PRIMARY KEY, value TEXT NOT NULL)")
            self.db.execute("INSERT OR IGNORE INTO meta VALUES ('first_date', ?)", (first_date.isoformat(),))

    def since(self, today, overlap):
        settings = dict(self.db.execute("SELECT key, value FROM meta").fetchall())
        start = date.fromisoformat(settings["first_date"])
        last = date.fromisoformat(settings.get("last_scan", start.isoformat()))
        return max(start, min(today, last) - timedelta(days=overlap))

    def scanned(self, today):
        with self.db:
            self.db.execute("INSERT OR REPLACE INTO meta VALUES ('last_scan', ?)", (today.isoformat(),))

    def add(self, project):
        with self.db:
            self.db.execute("INSERT OR IGNORE INTO projects (id, project, status) VALUES (?, ?, 'new')",
                            (project.id, json.dumps(asdict(project), ensure_ascii=False)))

    def pending(self, status):
        return self.db.execute("SELECT * FROM projects WHERE status = ? AND next_attempt <= ? ORDER BY rowid",
                               (status, datetime.now(MOSCOW).isoformat())).fetchall()

    def finish(self, identifier, status, body=None):
        with self.db:
            self.db.execute("UPDATE projects SET status=?, message=?, next_attempt='', attempts=0 WHERE id=?",
                            (status, body, identifier))

    def retry(self, row, seconds=0):
        delay = max(seconds, min(3600, 60 * 2 ** min(row["attempts"], 6)))
        with self.db:
            self.db.execute("UPDATE projects SET next_attempt=?, attempts=attempts+1 WHERE id=?",
                            ((datetime.now(MOSCOW) + timedelta(seconds=delay)).isoformat(), row["id"]))


class TelegramError(RuntimeError):
    def __init__(self, description, retry_after=0):
        super().__init__(description)
        self.retry_after = retry_after


async def send(request, token, chat, body, *, preview=False):
    try:
        response = await request.post(
            f"https://api.telegram.org/bot{token}/sendMessage",
            data={"chat_id": chat, "text": body, "parse_mode": "HTML",
                  "link_preview_options": {"is_disabled": not preview}},
            max_redirects=0, timeout=20000,
        )
    except Exception:
        raise TelegramError("Ошибка соединения с Telegram") from None
    try:
        try:
            payload = await response.json()
        except Exception:
            payload = {}
        if not (response.ok and payload.get("ok") is True):
            raise TelegramError(f"Telegram вернул HTTP {response.status}",
                                payload.get("parameters", {}).get("retry_after", 0))
    finally:
        await response.dispose()


async def cycle(portal, store, lookback, sender):
    today = datetime.now(MOSCOW).date()
    failures = 0
    try:
        async for project in portal.scan(store.since(today, lookback)):
            store.add(project)
        store.scanned(today)
    except Exception as error:
        failures += 1
        logging.warning("Ошибка просмотра списка: %s", error)
    for row in store.pending("new"):
        project = Project(**json.loads(row["project"]))
        try:
            reason = await portal.match(project)
            if reason:
                store.finish(project.id, "ready", message(project, reason))
            else:
                store.finish(project.id, "excluded")
        except Exception as error:
            failures += 1
            logging.warning("Карточка %s: %s", project.id, error)
            store.retry(row)
    for row in store.pending("ready"):
        try:
            await sender(row["message"])
            store.finish(row["id"], "sent")
            logging.info("Обработан проект %s", row["id"])
        except TelegramError as error:
            failures += 1
            logging.warning("Отправка %s: %s", row["id"], error)
            store.retry(row, error.retry_after)
            break
    return failures


async def run(args):
    token = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
    chat = os.getenv("TELEGRAM_CHAT_ID", "").strip()
    if not args.dry_run and (not re.fullmatch(r"\d+:[\w-]+", token) or not chat):
        raise SystemExit("Задайте TELEGRAM_BOT_TOKEN и TELEGRAM_CHAT_ID.")
    interval = int(os.getenv("POLL_INTERVAL_SECONDS", "300"))
    if interval < 30 or args.days < 1:
        raise SystemExit("Интервал должен быть от 30 секунд, --days от 1.")
    if args.dry_run:
        path = ":memory:"
    else:
        path = Path(os.getenv("DATABASE_PATH", "data/bot.sqlite3"))
        path.parent.mkdir(parents=True, exist_ok=True)
    store = Store(path, datetime.now(MOSCOW).date() - timedelta(days=args.days - 1))
    try:
        async with async_playwright() as playwright:
            browser = await playwright.chromium.launch(
                executable_path=os.getenv("CHROMIUM_EXECUTABLE") or None,
                args=["--no-sandbox", "--disable-gpu", "--disable-dev-shm-usage"],
                proxy={
                    "server": "http://IP_ТВОЕГО_ПРОКСИ:ПОРТ",
                    "username": "ТВОЙ_ЛОГИН_ПРОКСИ",
                    "password": "ТВОЙ_ПАРОЛЬ_ПРОКСИ"
                }
            )
            context = await browser.new_context()
            portal = Portal(context, os.getenv("REGULATION_LIST_URL", PORTAL))
            async def sender(body):
                if args.dry_run:
                    print(body, flush=True)
                else:
                    await send(context.request, token, chat, body)
                    await asyncio.sleep(1.1)
            while True:
                failures = await cycle(portal, store, 2, sender)
                logging.info("Проверка завершена. Ошибок: %d", failures)
                if args.once or args.dry_run:
                    return int(bool(failures))
                await asyncio.sleep(interval)
    finally:
        store.db.close()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Мониторинг проектов regulation.gov.ru")
    parser.add_argument("--once", action="store_true", help="выполнить одну проверку")
    parser.add_argument("--dry-run", action="store_true", help="вывести сообщения без отправки и записи в БД")
    parser.add_argument("--days", type=int, default=1, help="глубина первой проверки в календарных днях")
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
    raise SystemExit(asyncio.run(run(parser.parse_args())))

