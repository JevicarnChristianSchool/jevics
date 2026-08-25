@echo off
cd /d "%~dp0"
py -m pip install -r requirements.txt
if errorlevel 1 (
  echo.
  echo Dependency installation failed. Check your Python/pip installation.
  pause
  exit /b 1
)
py app.py
pause
