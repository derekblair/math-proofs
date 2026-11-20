#!/bin/bash
set -e
D=/root/math-fleet/lanes/argon-rule129-audit-20261026
mkdir -p "$D"
cd "$D"
PROMPT='Read BRIEF.md in this directory in full and execute it exactly. The predecessor dossier under audit is copied into this directory as SCREEN-DOSSIER.md; read that copy in full. Research only: no coding, no repo writes, no GitHub writes. Write DOSSIER.md incrementally, section by section, as you complete each part, so progress is visible on disk. Keep working until DOSSIER.md ends with the marker DOSSIER COMPLETE. Begin now.'
tmux kill-session -t argon-rule129-audit 2>/dev/null || true
tmux new-session -d -s argon-rule129-audit -c "$D" "/root/.local/bin/agy --dangerously-skip-permissions --model gemini-4-argon-high --print \"$PROMPT\" > argon-run.log 2>&1"
sleep 3
tmux ls | grep argon-rule129-audit
ps aux | grep -i "gemini-4-argon" | grep -v grep | head -3
