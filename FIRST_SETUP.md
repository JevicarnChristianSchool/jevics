# School Portal System — First Authentication Setup

1. Start the application with `py app.py` or `run-local.bat`.
2. Open `http://127.0.0.1:5000/`.
3. On a fresh build, use **First-time Administrator setup** and create the school's Administrator account.
4. After the Administrator is created, `/register` is locked.
5. New installations start with the **Login Page disabled** for non-Administrator users. Teacher, Student and Parent role buttons therefore go directly to their dashboards after those accounts exist.
6. Hidden staff entry points are `/admin`, `/ict`, `/finance`, and `/librarian`; Admin always authenticates.
7. In Admin → Users, use **Login Page Access** to enable authentication for Teacher, Student, Parent, ICT, Finance and Librarian users. Changing the setting requires confirmation and the current Admin password.
8. Administrator can create any school role and disable any account except the currently signed-in Administrator and the protected system account. The last active Administrator cannot be disabled.
9. ICT can create ICT, Finance, Teacher, Student, and Parent accounts, but cannot create or disable an Administrator.
10. Student and Parent accounts should be linked to their pupil when the account is created. Student/Parent dashboards are locked to that linked pupil and cannot be switched by editing the URL.
11. The application uses Flask's signed session cookie. For deployment, set a strong `SECRET_KEY` environment variable; the local build will otherwise generate and persist one in `instance/secret.key`.

The package preserves the existing school data, finance features, result controls, exam cards, QR verification, assignments, ICT customization, and portal branding.


## Demo workflow for presentations
The V18.1 build can seed a coherent demonstration institution on first startup. Default demo accounts are `demo.admin` / `DemoAdmin@123`, `demo.teacher` / `DemoTeacher@123`, and `demo.student` / `DemoStudent@123`. Set `SEED_DEMO_DATA=0` when using a clean production database.


## Password recovery email
For self-service password reset, configure these Render environment variables: `MAIL_SERVER`, `MAIL_PORT` (default `587`), `MAIL_USERNAME`, `MAIL_PASSWORD`, `MAIL_FROM` (optional; defaults to `MAIL_USERNAME`), and `MAIL_USE_TLS` (`1` by default). The application uses a one-time reset link that expires after 30 minutes. If mail delivery is unavailable or the account has no registered email, Admin / ICT receives a recovery request instead.
