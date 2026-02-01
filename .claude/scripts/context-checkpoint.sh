#!/bin/bash
# Context checkpoint hook - injects reminders at thresholds
# Outputs JSON with additionalContext so warnings appear in Claude's context
# Supports parallel sessions via session-specific temp files

# Read hook input (contains session_id)
INPUT=$(cat)

# Extract session_id from hook input (PostToolUse provides this!)
SESSION_ID=$(echo "$INPUT" | jq -r '.session_id // empty' 2>/dev/null)
[ -z "$SESSION_ID" ] && exit 0  # Can't work without session ID

# Session-specific files (written by statusLine)
PCT_FILE="/tmp/claude-context-pct-${SESSION_ID}"
FLAG_DIR="/tmp/claude-checkpoint-flags-${SESSION_ID}"

# Read percentage from session-specific file
PCT=$(cat "$PCT_FILE" 2>/dev/null)

# Exit if no percentage available
[ -z "$PCT" ] || [ "$PCT" = "0" ] && exit 0

mkdir -p "$FLAG_DIR"

# Function to output JSON with additionalContext
emit_warning() {
    local msg="$1"
    # Escape for JSON
    msg=$(echo "$msg" | sed 's/\\/\\\\/g' | sed 's/"/\\"/g' | sed ':a;N;$!ba;s/\n/\\n/g')
    echo "{\"additionalContext\": \"$msg\"}"
}

# Threshold 1: 35% - First warning
if [ "$PCT" -ge 35 ] && [ "$PCT" -lt 50 ]; then
    if [ ! -f "$FLAG_DIR/warn35" ]; then
        touch "$FLAG_DIR/warn35"
        emit_warning "⚠️ CONTEXT ~35% — Checkpoint Evaluation

Ask yourself: Can current task complete in remaining context?

IF NO → Checkpoint now:
  1. Commit what compiles
  2. Update HANDOFF.md
  3. bd create for remaining work
  4. Session complete. This IS success.

IF YES → Continue, but:
  - No 'simplification' or rewrites
  - The urge to simplify IS your stop signal"
    elif [ "$PCT" -ge 42 ] && [ ! -f "$FLAG_DIR/remind42" ]; then
        touch "$FLAG_DIR/remind42"
        emit_warning "⚠️ Context 42% — Still on track? No simplification urges?"
    fi
fi

# Threshold 2: 50% - Strong warning
if [ "$PCT" -ge 50 ] && [ "$PCT" -lt 65 ]; then
    if [ ! -f "$FLAG_DIR/warn50" ]; then
        touch "$FLAG_DIR/warn50"
        emit_warning "🛑 CONTEXT 50% — CHECKPOINT NOW

STOP proof work. Execute immediately:
  1. lake build (capture current state)
  2. git commit -m 'WIP: [description]'
  3. Update HANDOFF.md with goal state
  4. bd create --title='Continue: [task]' --priority=1
  5. bd sync

Incomplete documented work > thrashing to finish.
Do NOT attempt 'one more approach'.
Do NOT 'simplify' or 'clean up'."
    elif [ "$PCT" -ge 58 ] && [ ! -f "$FLAG_DIR/remind58" ]; then
        touch "$FLAG_DIR/remind58"
        emit_warning "🛑 Context 58% — Why are you still working? Checkpoint protocol NOW."
    fi
fi

# Threshold 3: 65% - Hard stop
if [ "$PCT" -ge 65 ]; then
    if [ ! -f "$FLAG_DIR/warn65" ]; then
        touch "$FLAG_DIR/warn65"
        emit_warning "🚨 CONTEXT 65% — HARD STOP

You are past safe working context. Further proof work risks:
- Lost progress from compaction
- Thrashing and destructive 'simplification'

ONLY allowed actions:
- Commit existing work (git add && git commit)
- Write HANDOFF.md
- Create follow-up issue (bd create)
- bd sync
- End session

ANY proof modification now is forbidden."
    fi
fi
