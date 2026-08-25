# Prime stability baseline

This build is deliberately based on the known-good project structure. Future changes should follow this rule:

- Desktop/PC templates and desktop CSS are the baseline and must not be replaced for a phone-only improvement.
- Phone changes belong under `@media (max-width: 820px)` or in phone-specific templates/routes.
- Functional/permission changes are separate from presentation changes.
- Before every future development pass, compare the changed-file list against this baseline and do not delete routes/templates without an explicit reason.
- Reception, Librarian, Driver, Admin, Teacher, Student and Finance routes remain present.
