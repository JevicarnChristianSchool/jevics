# V39 — Unified portal authentication + refined phone landing

## Authentication
- Public portal launchers now point to the shared `/login` flow with an explicit post-login destination.
- Added `Library` as a secure login context alongside `E-Learning`.
- E-Learning no longer auto-inherits an already logged-in browser session from its public launcher.
- Library and E-Learning continue to enforce role checks after authentication; the selected portal never overrides the account's stored role.
- Existing protected dashboard routes remain account/role controlled.

## Mobile public UI
- Replaced the oversized green side-button rail with a compact, white, black-text mobile navigation.
- Added a neat horizontal primary row for Home, About, Calendar, Portals and Contacts.
- About and Portals open lightweight dropdown panels below the row.
- Added compact text-size controls (A− / A+) and Share to the mobile header.
- Removed the old mobile Menu button and the fixed left navigation rail.
- Public content now uses the full phone width with more restrained typography, spacing and controls.

## Cache
- Service-worker cache advanced to V39 so deployed phones can receive this version rather than continuing to use the V38 cache.
