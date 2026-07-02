FROM python:3.11-slim

WORKDIR /app

COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

COPY . .

ENV PORT=8080
ENV DATA_DIR=/data

EXPOSE 8080

CMD gunicorn viaticos:app --bind 0.0.0.0:$PORT --workers 1 --timeout 120
