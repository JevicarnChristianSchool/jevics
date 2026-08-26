# V32 — Public About Writer

- Public About is now written only from Admin → Public About.
- Public landing page renders About sections immediately after the welcome/hero area.
- Long sections can collapse behind “View more”; long media galleries can expand behind “View more media”.
- Each About section can accept multiple images and video files.
- Added a draft preview while writing and a “Load sample” structure.
- Save/refresh persists the institutional story through `school_settings.about_sections_json`.
- Existing institution/history fields are preserved; the Public About writer no longer clears them.
- `/institution` is read-only for authenticated users; only Admin sees the Public About Writer link.
- Admin dashboard now has a direct Public About entry under School settings/Public face.
