# V40 — Attendance & Workforce Polish

- Admin Employees now surfaces today's check-in and check-out times, IN/OUT locations, client/device capture notes, and an attendance state.
- Attendance events now record a clear fallback note when location/device details are not supplied, while retaining the browser User-Agent when available.
- Added a durable `staff_category` field so Support Staff, Teaching Staff, Leadership and Professional/Office Staff are not forced into a human-facing Teacher label.
- Staff intake/edit screens now expose Support Staff and operational positions such as Cook, Driver, Cleaner, Security/Guard, Receptionist, Nurse/Matron, Lab Assistant and ICT Support.
- Account type uses a human-facing category while retaining existing portal security roles underneath.
- Existing staff accounts are automatically backfilled into sensible categories from workspace/role.
- Added clearer phone styling for Admin and selected role dashboards: readable dark text, clean white panels and subtle role accents rather than low-contrast grey-on-white controls.
