FROM python:3.12-slim-bookworm
RUN apt-get update && apt-get install -y --no-install-recommends chromium antiword tzdata \
    && rm -rf /var/lib/apt/lists/*
ENV CHROMIUM_EXECUTABLE=/usr/bin/chromium
WORKDIR /app
COPY requirements.txt .
RUN --mount=type=secret,id=pip_ca \
    if [ -f /run/secrets/pip_ca ]; then export PIP_CERT=/run/secrets/pip_ca; fi \
    && pip install --no-cache-dir -r requirements.txt
COPY bot.py duma.py keywords.txt .
CMD ["python", "-u", "duma.py"]

