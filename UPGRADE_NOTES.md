# V19 — Reception, Subject Enrolment & Role-Based Performance

## Major additions
- Restored `/reception` as a live Reception / Gate Office workspace.
- Institution staff QR displayed at reception for IN / OUT attendance.
- Authentication-ready acceptance: valid institution members can be accepted; invalid users are rejected once authentication is enforced.
- Human-readable GPS location remains attached to staff attendance events.
- Visitor register now stores full name, ID/passport number, phone, reason, time-in and time-out.
- Returning visitor search reuses prior identity details for a new visit.
- Reception can register learners, assign departments and approved subjects.
- Published subject catalogue for Admin / ICT.
- Learners can manage their subject selections; self-registration is recorded as Pending for approval.
- Teacher rosters are generated from actual student-subject enrolment.
- Teacher performance is scoped: class teachers can see their full assigned class; ordinary subject teachers see their subject-level cohort; senior academic roles have broader views.
- Added performance intelligence page for academic leadership.
- Optional browser-based face enrolment and face verification with QR remaining the default.
- Leaner profile presentation now emphasizes relevant academic/contact/support details instead of showing every field at once.
- Demo database is populated with subjects and student subject enrolments.

## Demo
- `demo.admin / DemoAdmin@123`
- `demo.teacher / DemoTeacher@123`
- `demo.student / DemoStudent@123`
- Set `SEED_DEMO_DATA=0` in production to disable demo seeding.

## Notes
- Face recognition requires a browser able to load the recognition models over HTTPS; QR is the recommended and offline-capable method.
