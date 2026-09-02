from pathlib import Path
p=Path('/mnt/data/jevics_work/app.py')
s=p.read_text()
# Improve role labels without changing DB constraint: add an explicit support-staff role alias mapped to existing workspace/role model.
old='''PUBLIC_ROLES = ("Teacher", "Student", "Parent", "Librarian", "Driver")\nHIDDEN_ROLES = ("Admin", "ICT", "Finance")\nQR_LOGIN_ROLES = {"Admin", "ICT", "Finance", "Teacher", "Librarian", "Driver"}\n'''
new='''PUBLIC_ROLES = ("Teacher", "Student", "Parent", "Librarian", "Driver")\nHIDDEN_ROLES = ("Admin", "ICT", "Finance")\n# "Support Staff" is a UI-level account profile backed by the existing Teacher\n# role plus a non-teaching workspace. This avoids another SQLite role migration\n# while giving administrators a proper, non-confusing option for support workers.\nSTAFF_PROFILE_LABELS = {\n    "Teaching": "Teacher", "Driver": "Driver", "Reception": "Reception staff",\n    "Guard": "Security / Guard", "Cook": "Catering / Cook", "Other Staff": "Support Staff",\n}\nQR_LOGIN_ROLES = {"Admin", "ICT", "Finance", "Teacher", "Librarian", "Driver"}\n'''
assert old in s
s=s.replace(old,new)
# Add navigation hrefs; old anchor behavior remains for ordinary section navigation.
old='''    anchor_map={"Home":"home","Assignments":"assignments","Submissions":"submissions","Flashcards":"flashcards","Online classes":"classes","Results":"results","My children":"children","Results & fees":"results","Teacher communication":"messages","Finance":"finance","Payments":"payments","Branding":"branding","Theme":"theme","Navigation order":"navigation","Elections":"elections","Library":"library","Institution":"institution","Members":"users"}\n    result=[]\n'''
new='''    anchor_map={"Home":"home","Assignments":"assignments","Submissions":"submissions","Flashcards":"flashcards","Online classes":"classes","Results":"results","My children":"children","Results & fees":"results","Teacher communication":"messages","Finance":"finance","Payments":"payments","Branding":"branding","Theme":"theme","Navigation order":"navigation","Elections":"elections","Library":"library","Institution":"institution","Members":"users"}\n    href_map={\n        "ICT": {"Home": url_for("ict_dashboard"), "Members": url_for("all_employees"), "Library": url_for("librarian_dashboard"),\n                "Elections": "#elections", "Branding": "#themes", "Theme": "#themes", "Navigation order": "#ict-tools"},\n        "Finance": {"Home": url_for("finance_dashboard"), "Finance": "#overview", "Payments": "#student-fees", "Library": url_for("librarian_dashboard")},\n    }.get(role, {})\n    result=[]\n'''
assert old in s
s=s.replace(old,new)
old='''            result.append({"key":key,"label":labels.get(key,key),"anchor":anchor_map[key]})\n    for key in allowed:\n        if key not in [r["key"] for r in result]:\n            result.append({"key":key,"label":labels.get(key,key),"anchor":anchor_map[key]})\n'''
new='''            result.append({"key":key,"label":labels.get(key,key),"anchor":anchor_map[key],"href":href_map.get(key, "#"+anchor_map[key])})\n    for key in allowed:\n        if key not in [r["key"] for r in result]:\n            result.append({"key":key,"label":labels.get(key,key),"anchor":anchor_map[key],"href":href_map.get(key, "#"+anchor_map[key])})\n'''
assert old in s
s=s.replace(old,new)
# In add_user, accept Support Staff UI alias and map cleanly.
old='''    role=request.form.get("role", "Teacher")\n    if role in {"Student", "Parent", "System"}:\n        flash("Student and parent records are not staff accounts. Use the administrator-only student intake.", "warning")\n        return redirect(request.referrer or url_for("admin_dashboard"))\n'''
new='''    role=request.form.get("role", "Teacher")\n    if role == "Support Staff":\n        role = "Teacher"\n        request_workspace = request.form.get("workspace_type", "Other Staff").strip() or "Other Staff"\n        if request_workspace == "Teaching":\n            request_workspace = "Other Staff"\n    else:\n        request_workspace = request.form.get("workspace_type", "Teaching").strip() or "Teaching"\n    if role in {"Student", "Parent", "System"}:\n        flash("Student and parent records are not staff accounts. Use the administrator-only student intake.", "warning")\n        return redirect(request.referrer or url_for("admin_dashboard"))\n'''
assert old in s
s=s.replace(old,new)
old='''    workspace_type=request.form.get("workspace_type", "Teaching").strip() or "Teaching"\n'''
new='''    workspace_type=request_workspace\n'''
# only first occurrence after add_user is desired; use segment
idx=s.index('def add_user():')
pos=s.index(old,idx)
s=s[:pos]+s[pos:].replace(old,new,1)
# Edit user: derive display role and map support staff alias.
old='''        role=request.form.get("role",user["role"])\n'''
new='''        role=request.form.get("role",user["role"])\n        if role == "Support Staff":\n            role = "Teacher"\n            submitted_workspace = request.form.get("workspace_type", "Other Staff").strip() or "Other Staff"\n            if submitted_workspace == "Teaching": submitted_workspace = "Other Staff"\n        else:\n            submitted_workspace = request.form.get("workspace_type", user["workspace_type"] if "workspace_type" in user.keys() else "Teaching").strip() or "Teaching"\n'''
assert old in s
s=s.replace(old,new,1)
old='''        workspace_type=request.form.get("workspace_type", user["workspace_type"] if "workspace_type" in user.keys() else "Teaching").strip() or "Teaching"\n        if workspace_type not in {"Teaching","Driver","Reception","Guard","Cook","Other Staff"}: workspace_type="Teaching"\n'''
new='''        workspace_type=submitted_workspace\n        if workspace_type not in {"Teaching","Driver","Reception","Guard","Cook","Other Staff"}: workspace_type="Teaching"\n'''
assert old in s
s=s.replace(old,new,1)
old='''    return render_template("user_edit.html", user=user, students=students, departments=depts, role_options=tuple(r for r in ALL_PORTAL_ROLES if r != "Student"), guardian_links=q("SELECT * FROM guardian_links WHERE guardian_user_id=? AND active=1",(user_id,)))\n'''
new='''    profile_role = "Support Staff" if user["role"] == "Teacher" and (user["workspace_type"] or "Teaching") != "Teaching" else user["role"]\n    return render_template("user_edit.html", user=user, students=students, departments=depts, role_options=("Admin","ICT","Finance","Teacher","Support Staff","Librarian","Driver","Parent"), profile_role=profile_role, guardian_links=q("SELECT * FROM guardian_links WHERE guardian_user_id=? AND active=1",(user_id,)))\n'''
assert old in s
s=s.replace(old,new,1)
# Allow ITCs to open edit for ordinary support accounts only, but keep restrictions.
p.write_text(s)
