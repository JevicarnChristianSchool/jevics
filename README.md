# Prime Institution OS V19

A modular institutional operating system for schools, colleges, TVET and similar institutions.

This release focuses on Reception/Gate operations, subject enrolment, teacher rosters and role-based academic performance.

## Main demonstration path
1. Admin publishes subjects in `/admin/subjects`.
2. Reception registers a learner at `/reception` and selects departments + subjects.
3. Teacher opens `/teacher/roster` to see only learners enrolled in that subject.
4. Teacher records marks and opens `/performance`.
5. Class teachers can see full assigned-class performance; ordinary subject teachers are scoped to their subjects.
6. Student opens `/students/<id>/subjects` to submit subject choices.
7. Reception displays the institution attendance QR. Staff use `/attendance` to scan it and record IN/OUT with location when available.
8. Reception can optionally enrol and verify faces; QR remains the default.

## Demo accounts
- demo.admin / DemoAdmin@123
- demo.teacher / DemoTeacher@123
- demo.student / DemoStudent@123

Set `SEED_DEMO_DATA=0` in production.

## Deployment
The repository pins the Python runtime to the 3.13 series for Render via `.python-version`.
Do not create or restore a top-level file named `types.py`: Python's standard library has a
module with that name, and a project-level `types.py` shadows it during Python startup.
Render uses `pip install -r requirements.txt` and `gunicorn app:app` as defined in `render.yaml`
and `Procfile`.


## Password recovery email
For self-service password reset, configure these Render environment variables: `MAIL_SERVER`, `MAIL_PORT` (default `587`), `MAIL_USERNAME`, `MAIL_PASSWORD`, `MAIL_FROM` (optional; defaults to `MAIL_USERNAME`), and `MAIL_USE_TLS` (`1` by default). The application uses a one-time reset link that expires after 30 minutes. If mail delivery is unavailable or the account has no registered email, Admin / ICT receives a recovery request instead.
