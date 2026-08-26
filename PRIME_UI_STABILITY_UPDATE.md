# Prime UI & Stability Update

## UI direction
- Public/institution navigation now follows a compact school-site pattern: Home, section links, and Portal Login in a flat neutral bar.
- Workspace text defaults to white/black/grey-neutral styling instead of blue/dark UI text.
- Institution history supports the existing three-image fields as a horizontally scrolling, snap-based gallery with previous/next controls.
- Existing institution image storage and crop-position fields are preserved.

## Stability
- Added non-fatal `safe_q()` reads for portal rendering.
- Hardened the Teacher dashboard's independent reads and markbook summaries so a secondary data problem does not take down the whole workspace.
- Hardened Parent, Librarian and Driver dashboard reads where their pages depended on direct database reads.
- Added a generic exception safety handler that logs the real exception server-side while returning a stable portal-style response instead of a traceback/debug page.
- 403/404/413 responses now use the same neutral portal presentation.
- Python cache/compiled artifacts are intentionally excluded from the deployment package.

## Preserved
No existing database schema, authentication model, role list, institution image storage fields, or portal feature files were intentionally removed.
