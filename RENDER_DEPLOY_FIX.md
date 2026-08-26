# Render deployment fix

- Python is pinned to 3.13.5 using `.python-version`.
- Do NOT create a top-level `types.py`; it shadows Python's standard-library `types` module.
- The PDF package is correctly kept under `pypdf/`.
- Start command remains `gunicorn app:app`.
