#!/bin/bash
cd ~/lane-work/codex-pr16-provenance-fix
export PATH=$HOME/.npm-global/bin:$HOME/.elan/bin:$PATH
$HOME/.npm-global/bin/codex exec --dangerously-bypass-approvals-and-sandbox -m gpt-6-astra -c model_reasoning_effort=ultra "/fast $(cat BRIEF.md)" < /dev/null > run.log 2>&1
