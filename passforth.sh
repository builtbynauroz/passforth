#!/bin/sh
# Passforth's client, run with what this machine has (ADR-0016): passforth.py on python3 3.9 or newer, else
# passforth.mjs on Node.js 18 or newer, else on Bun. They're the same client and share ~/.passforth.
# Its own folder without dirname: one process less on every hook.
case $0 in */*) dir=${0%/*} ;; *) dir=. ;; esac
if command -v python3 >/dev/null 2>&1 && python3 -I -S -c 'import sys; sys.exit(sys.version_info < (3, 9))' 2>/dev/null; then
  exec python3 -B "$dir/passforth.py" "$@"
fi
if command -v node >/dev/null 2>&1; then
  exec node "$dir/passforth.mjs" "$@"
fi
if command -v bun >/dev/null 2>&1; then
  exec bun "$dir/passforth.mjs" "$@"
fi
echo "passforth: needs python3 (3.9 or newer) or Node.js (18 or newer)" >&2
exit 1
