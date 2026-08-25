# Prime Optimum v22 — Student/People/Allocation Reliability Fix

## The 500 error
The previous `/students/add` handler attempted to insert an `age` column into deployments whose `students` table did not yet contain that column. The migration now explicitly guarantees `age` and `grade_category` columns before any learner write, and the canonical handler is `/students/add` only.

## Student data store
A dedicated `students.db` is now maintained under the configured persistent data directory. It is the authoritative learner-profile store for registration, while `school.db` retains a compatibility learner index because the wider school modules use foreign keys to learner IDs. IDs remain aligned.

The dedicated store is automatically created, integrity-checked, recovered if corrupt, and backfilled from the existing school learner index.

## Grade and routing logic
A learner must provide a grade. Numeric input such as `8` is normalized to `Grade 8`. The same value is stored as `grade_category`.

On registration the system automatically:
1. Creates the student in `students.db`.
2. Mirrors the same learner ID into the school compatibility index.
3. Creates the Student portal account.
4. Finds the configured class teacher for that grade and allocates the learner to that teacher.
5. Finds all compulsory subjects and all subjects taught for that grade.
6. Enrols the learner into subjects that exist in the subject catalogue.
7. Links the learner to the configured subject teacher for each matching class/subject assignment.

Existing learners are routed through the same allocation rules on startup so the change applies to the current population too.

## People navigation
Admin and ICT now have one **People** dropdown containing:
- Students
- Employees
- Allocate

`/allocate` is the canonical short path for the learner/teacher allocation workspace. `/admin/student-allocation` remains available as the descriptive path.

## Allocation workspace
The allocation workspace is explicitly designed for Admin/ICT to:
- assign individual learners to teachers;
- allocate by grade/class;
- assign class teachers;
- assign subject teachers;
- review the current learner ↔ teacher map;
- manage department leadership.

When a class teacher is assigned to a grade, all active learners in that grade are automatically routed to that class teacher and the configured subject mappings are backfilled.

## Failure safety
If learner/account creation fails, the handler cleans up the dedicated student record, compatibility student row, and Student portal account so a failed request does not leave a partial learner.

A generic Flask 500 handler now logs the exception server-side and returns a controlled error page rather than exposing an unhandled stack trace.

## Backup
The dedicated learner store can be downloaded independently at `/backup/students` by the root administrator. The existing school database backup remains available at `/backup/download`.

## Validation performed
- `python3 -m py_compile app.py` passes.
- SQL smoke test for dedicated student insertion passes.
- Grade normalization smoke test passes (`8` → `Grade 8`).
- Class-teacher allocation SQL passes.
- Subject-teacher allocation SQL passes.
- Static route inventory reports no duplicate route paths.
- Legacy `/student/add` and `/admin/students/add` aliases were removed from the final build.

A live Flask/HTTP browser test could not be executed in this environment because Flask is not installed locally and outbound package installation is unavailable. The Render logs supplied in the conversation confirm the deployed service itself starts under Gunicorn; the corrected code targets the failing application path directly.
