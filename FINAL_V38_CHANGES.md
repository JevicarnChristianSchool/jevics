# Prime Institution Portal — V38 final phone/login/recovery pass

Implemented in this build:

- Library and E-Learning are protected portal destinations. They use the same account credentials as the rest of the school portal and return the user to the portal they originally selected after successful authentication.
- E-Learning now uses one unified sign-in form instead of separate student/staff login forms; the stored account role remains authoritative.
- Library access now supports Admin, ICT, Librarian, Teacher, Student and Parent accounts, with the existing class/subject filtering retained.
- Public About media now feeds the public landing page when a landing image has not separately been chosen. The first uploaded About image is also used as the front-page gallery fallback, avoiding the blank gallery placeholder.
- Public Portal Login now explicitly includes E-Learning and Library as portal destinations.
- Full Portal Backup is now a ZIP archive containing the persistent portal files, a transaction-consistent SQLite database snapshot, signing secret and uploaded portal assets. The legacy SQLite and JSON backup options remain available.
- Full Portal Restore accepts the full ZIP, validates the archive and database, keeps a safety database snapshot, then restores the saved persistent portal contents.
- PWA/service-worker cache version was raised to V38 so the new mobile CSS and templates can replace stale cached UI.
- Final phone CSS removes the public landing-page Menu button, keeps large top navigation controls and a left-side navigation rail, increases mobile readability and touch-target sizing, and prevents horizontal overflow. Authenticated pages also receive larger mobile controls and cleaner one-column layouts.

Note: runtime integration testing could not be executed in this container because the uploaded project dependencies (including Flask) are not installed here. Python syntax compilation of `app.py` completed successfully.

## V2 diagnostic follow-up — attendance live 500
2026-09-03: Fixed `/admin/attendance/live`. The SQL query contained 12 placeholders but only 10 bound parameters, causing repeated HTTP 500s during the dashboard's 5-second live attendance refresh. The parameter tuple now supplies all six start/end pairs. The exact query was replayed against the bundled school database successfully after the fix.

## V4 backup reliability patch — 2026-09-03
- Fixed full ZIP backup construction so the temporary ZIP cannot archive itself while it is being written.
- Fixed full ZIP archive enumeration so temporary SQLite snapshot files are excluded.
- Full portal backup creation failures are now recorded in the persistent system-error ledger and surfaced to the admin instead of becoming an unexplained 500.
- Changed SQLite backup download to use SQLite's transaction-consistent backup API, so WAL-mode changes are included in the downloaded rollback copy.
- SQLite backup download failures are now recorded in the persistent system-error ledger and surfaced to the admin.
