#!/bin/bash
# Context checkpoint hook - injects reminders at thresholds
# Outputs JSON with hookSpecificOutput.additionalContext for Claude visibility
# Supports parallel sessions via session-specific temp files

# Read hook input (contains session_id)
INPUT=$(cat)

# Extract session_id from hook input
SESSION_ID=$(echo "$INPUT" | jq -r '.session_id // empty' 2>/dev/null)
[ -z "$SESSION_ID" ] && exit 0

# Session-specific files
PCT_FILE="/tmp/claude-context-pct-${SESSION_ID}"
FLAG_DIR="/tmp/claude-checkpoint-flags-${SESSION_ID}"

# Read percentage
PCT=$(cat "$PCT_FILE" 2>/dev/null)
[ -z "$PCT" ] || [ "$PCT" = "0" ] && exit 0

mkdir -p "$FLAG_DIR"

# Output JSON with correct hookSpecificOutput format
emit_warning() {
    local msg="$1"
    msg=$(echo "$msg" | sed 's/\\/\\\\/g' | sed 's/"/\\"/g' | sed ':a;N;$!ba;s/\n/\\n/g')
    cat << EOF
{"hookSpecificOutput":{"hookEventName":"PostToolUse","additionalContext":"$msg"}}
EOF
}

# Threshold 1: 35%
if [ "$PCT" -ge 35 ] && [ "$PCT" -lt 50 ]; then
    if [ ! -f "$FLAG_DIR/warn35" ]; then
        touch "$FLAG_DIR/warn35"
        emit_warning "⚠️ CONTEXT ~35% — Checkpoint Evaluation. Can current task complete in remaining context? IF NO: Commit what compiles, update HANDOFF.md, bd create for remaining work. IF YES: Continue but NO simplification or rewrites."
    elif [ "$PCT" -ge 42 ] && [ ! -f "$FLAG_DIR/remind42" ]; then
        touch "$FLAG_DIR/remind42"
        emit_warning "⚠️ Context 42% — Still on track? No simplification urges?"
    fi
fi

# Threshold 2: 50%
if [ "$PCT" -ge 50 ] && [ "$PCT" -lt 65 ]; then
    if [ ! -f "$FLAG_DIR/warn50" ]; then
        touch "$FLAG_DIR/warn50"
        emit_warning "🛑 CONTEXT 50% — CHECKPOINT NOW. STOP proof work. Commit, update HANDOFF.md, bd create, bd sync. Do NOT simplify or clean up."
    elif [ "$PCT" -ge 58 ] && [ ! -f "$FLAG_DIR/remind58" ]; then
        touch "$FLAG_DIR/remind58"
        emit_warning "🛑 Context 58% — Why are you still working? Checkpoint protocol NOW."
    fi
fi

# Threshold 3: 65%
if [ "$PCT" -ge 65 ]; then
    if [ ! -f "$FLAG_DIR/warn65" ]; then
        touch "$FLAG_DIR/warn65"
        emit_warning "🚨 CONTEXT 65% — HARD STOP. Only allowed: git commit, HANDOFF.md, bd create, bd sync, end session. ANY proof modification is forbidden."
    fi
fi
