#!/bin/bash
cd /root/lane-work/codex-pr16-body-fix
export PATH=/root/.npm-global/bin:$PATH
/root/.npm-global/bin/codex exec --dangerously-bypass-approvals-and-sandbox -m gpt-6-astra -c model_reasoning_effort=ultra "/fast $(cat BRIEF.md)" < /dev/null > run.log 2>&1
