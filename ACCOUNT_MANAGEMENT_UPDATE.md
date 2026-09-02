# Account & Workspace Hardening Update

## Changes
- Admin dashboard now has a visible **Users, roles & access** management panel.
- Admin can edit existing users, including changing an existing Administrator account to another permitted role (except changing the currently signed-in Admin itself).
- Admin can archive, restore and permanently delete other accounts, with safeguards for the last active Administrator.
- Existing account edit screen now includes lifecycle controls and a broader staff workspace selector, including Reception.
- Added a clear **Support Staff** creation/edit profile. It uses the existing `Teacher` database role plus `Other Staff` workspace so no risky SQLite role-table migration is required.
- Non-teaching workspaces now take precedence during dashboard dispatch, preventing support workers from landing on Teacher dashboard.
- ICT navigation items now use real destinations instead of dead hash links where appropriate.
- ICT/admin staff directories expose edit, restore/delete and Admin direct-access controls according to permissions.
- Staff creation form exposes broader identity, position, contact, branch/unit and accountability fields.
