# Prime v24 — Student & Portal Crash Fix

## Production failure fixed
The previous build registered the explicit `/static/<path:filename>` route under the endpoint name `prime_static` while existing templates consistently call `url_for('static', filename=...)`. That made `/`, `/login`, and the 500 error template fail with Flask `BuildError` before student workflows could run.

v24 restores the canonical Flask endpoint name `static` while retaining the explicit production asset-serving implementation.

## Student registration behavior
The dedicated `students.db` is authoritative. Required learner fields remain:
- full name
- grade

Optional learner fields, legacy compatibility mirroring, student portal account creation, and automatic class/subject placement are now best-effort. A failure in any of those enrichment steps no longer rolls back an already-created learner.

Grade is normalized (`8` -> `Grade 8`) and the existing tolerant class/subject assignment logic remains active.

## Error safety
The final 500 handler is dependency-free HTML so an error cannot cascade into another template/static endpoint failure.

## Validation
- Python compilation passes.
- Static route endpoint declaration is `static`.
- No template references `prime_static`.
