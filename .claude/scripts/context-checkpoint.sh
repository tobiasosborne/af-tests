#!/bin/bash
# Context checkpoint hook - injects reminders at thresholds
# Only emits once per threshold crossing (with one reminder 5% later)

INPUT=$(cat)

# Session-specific flag directory using parent PID (Claude Code process)
# Falls back to hash of pwd+date if PPID not useful
SESSION_ID="${PPID:-$(echo "$(pwd)$(date +%Y%m%d)" | md5sum | cut -c1-8)}"
FLAG_DIR="/tmp/claude-checkpoint-flags-${SESSION_ID}"
mkdir -p "$FLAG_DIR"

# Extract context percentage (same logic as statusLine)
PCT=$(echo "$INPUT" | jq -r '
  if .context_window.current_usage then
    ((.context_window.current_usage.input_tokens +
      .context_window.current_usage.cache_creation_input_tokens +
      .context_window.current_usage.cache_read_input_tokens) * 100 /
      .context_window.context_window_size)
  else 0 end
' 2>/dev/null)

# Exit silently if we couldn't get percentage
[ -z "$PCT" ] || [ "$PCT" = "null" ] || [ "$PCT" = "0" ] && exit 0

# Threshold 1: 35% - First warning
if [ "$PCT" -ge 35 ] && [ "$PCT" -lt 50 ]; then
    if [ ! -f "$FLAG_DIR/warn35" ]; then
        touch "$FLAG_DIR/warn35"
        cat << 'EOF'
<context-checkpoint level="notice">
CONTEXT ~35% — Checkpoint Evaluation

Ask yourself: Can current task complete in remaining context?

IF NO → Checkpoint now:
  1. Commit what compiles
  2. Update HANDOFF.md
  3. bd create for remaining work
  4. Session complete. This IS success.

IF YES → Continue, but:
  - No "simplification" or rewrites
  - The urge to simplify IS your stop signal
</context-checkpoint>
EOF
    elif [ "$PCT" -ge 42 ] && [ ! -f "$FLAG_DIR/remind42" ]; then
        # One reminder at 42%
        touch "$FLAG_DIR/remind42"
        cat << 'EOF'
<context-checkpoint level="reminder">
Context 42% — Still on track? No simplification urges?
</context-checkpoint>
EOF
    fi
fi

# Threshold 2: 50% - Strong warning
if [ "$PCT" -ge 50 ] && [ "$PCT" -lt 65 ]; then
    if [ ! -f "$FLAG_DIR/warn50" ]; then
        touch "$FLAG_DIR/warn50"
        cat << 'EOF'
<context-checkpoint level="warning">
CONTEXT 50% — CHECKPOINT NOW

STOP proof work. Execute immediately:
  1. lake build (capture current state)
  2. git commit -m "WIP: [description]"
  3. Update HANDOFF.md with goal state
  4. bd create --title="Continue: [task]" --priority=1
  5. bd sync

Incomplete documented work > thrashing to finish.
Do NOT attempt "one more approach".
Do NOT "simplify" or "clean up".
</context-checkpoint>
EOF
    elif [ "$PCT" -ge 58 ] && [ ! -f "$FLAG_DIR/remind58" ]; then
        touch "$FLAG_DIR/remind58"
        cat << 'EOF'
<context-checkpoint level="warning">
Context 58% — Why are you still working? Checkpoint protocol NOW.
</context-checkpoint>
EOF
    fi
fi

# Threshold 3: 65% - Hard stop
if [ "$PCT" -ge 65 ]; then
    if [ ! -f "$FLAG_DIR/warn65" ]; then
        touch "$FLAG_DIR/warn65"
        cat << 'EOF'
<context-checkpoint level="critical">
CONTEXT 65% — HARD STOP

You are past safe working context. Further proof work risks:
- Lost progress from compaction
- Thrashing and destructive "simplification"

ONLY allowed actions:
- Commit existing work (git add && git commit)
- Write HANDOFF.md
- Create follow-up issue (bd create)
- bd sync
- End session

ANY proof modification now is forbidden.
</context-checkpoint>
EOF
    fi
fi
