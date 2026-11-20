#!/bin/bash
export PATH=$HOME/.npm-global/bin:$HOME/.elan/bin:$PATH
name=codex-rule129-paper
dir=/root/lane-work/codex-rule129-paper
tmux kill-session -t "$name" 2>/dev/null
tmux new-session -d -s "$name" -c "$dir"
sleep 1
tmux send-keys -t "$name" 'codex --dangerously-bypass-approvals-and-sandbox -m gpt-6-astra -c model_reasoning_effort=\"ultra\" "Read BRIEF.md in this directory and carry out the task it describes end to end, autonomously. Keep STATUS.md updated as you work."' Enter
sleep 2
tmux ls | grep codex-
