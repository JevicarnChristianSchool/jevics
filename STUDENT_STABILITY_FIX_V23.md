# Prime Optimum System — Student Stability Fix v23

## Student registration
- `/students/add` remains the single canonical POST route.
- Student profile data is authoritative in `students.db`.
- Grade is mandatory and normalized (`8` → `Grade 8`).
- The compatibility `school.db` student row is written using only columns that actually exist in the persistent database, preventing legacy-schema 500 errors.
- Student account creation and allocation are rolled back/cleaned up if registration fails.

## Automatic allocation
- Grade matching accepts both `8` and `Grade 8` style legacy class labels.
- A configured class teacher is automatically attached to the learner.
- Compulsory subjects and teacher subject assignments are collected for the learner's grade.
- Missing subject catalog records are safely created instead of causing registration to fail.
- Configured subject teachers are automatically attached.

## Production static assets
- Flask's implicit static route is disabled and replaced with an explicit production-safe `/static/<path>` route.
- Static files are served with conditional requests and cache headers from the known application static directory.

## Validation
- `app.py` Python compilation passes.
- No duplicate `/students/add` route exists.
- The student registration SQL is schema-tolerant for legacy `school.db` databases.
