# Prime Optimum System

This release consolidates the fourth uploaded build as the production baseline. It keeps the mature Flask/SQLite feature set, removes obsolete duplicate dashboard paths, and adds a focused flashcard service.

## Canonical workspaces
- `/` public landing/auth entry
- `/dashboard` authenticated role dispatcher
- `/admin/dashboard` Admin workspace
- `/teacher/class-attendance` teacher attendance register
- `/admin/student-allocation` student-to-teacher allocation
- `/flashcards` teaching/admin deck management and learner study
- `/flashcards/<deck_id>/review` review mode

## Academic model
- Admin/ICT assign teachers to learners, classes, subjects and department leadership.
- Class teachers receive the whole class register.
- Teachers see only Admin-assigned classes/learners.
- Teachers can mark Present, Absent, Late or Excused and add absence notes.

## Flashcards
- Teacher/Admin/ICT create decks and cards.
- Decks may target a subject and class.
- Students see decks targeted to their class plus decks they own only when applicable.
- Per-user review progress is stored with simple spaced intervals.

## UI system
Responsive single-column mobile behavior, touch-friendly controls, compact tables, consistent focus states and a dark blue accessible palette are applied without changing business logic.
