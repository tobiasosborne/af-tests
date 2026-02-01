#!/bin/bash
# Context checkpoint hook - STRONG warnings that agents cannot ignore

INPUT=$(cat)
SESSION_ID=$(echo "$INPUT" | jq -r '.session_id // empty' 2>/dev/null)
[ -z "$SESSION_ID" ] && exit 0

PCT_FILE="/tmp/claude-context-pct-${SESSION_ID}"
FLAG_DIR="/tmp/claude-checkpoint-flags-${SESSION_ID}"
PCT=$(cat "$PCT_FILE" 2>/dev/null)
[ -z "$PCT" ] || [ "$PCT" = "0" ] && exit 0

mkdir -p "$FLAG_DIR"

emit_warning() {
    local msg="$1"
    msg=$(echo "$msg" | sed 's/\\/\\\\/g' | sed 's/"/\\"/g' | sed ':a;N;$!ba;s/\n/\\n/g')
    cat << EOF
{"hookSpecificOutput":{"hookEventName":"PostToolUse","additionalContext":"$msg"}}
EOF
}

# 35% - Evaluate and decide (agent decides, no user prompt)
if [ "$PCT" -ge 35 ] && [ "$PCT" -lt 50 ]; then
    if [ ! -f "$FLAG_DIR/warn35" ]; then
        touch "$FLAG_DIR/warn35"
        emit_warning "🚨 CHECKPOINT - CONTEXT AT 35% 🚨

EVALUATE NOW: Can current task complete in remaining context?

IF NO → Checkpoint immediately:
1. Commit what compiles
2. Update HANDOFF.md
3. Create follow-up issues (bd create)
4. End session. This IS success.

IF YES → Continue, but these actions are FORBIDDEN:
- 'Simplifying' code
- 'Cleaning up' code
- Rewriting or refactoring
- Any changes not directly required for current task

The urge to simplify IS YOUR SIGNAL TO STOP."
    elif [ "$PCT" -ge 42 ] && [ ! -f "$FLAG_DIR/remind42" ]; then
        touch "$FLAG_DIR/remind42"
        emit_warning "🚨 42% - Remember: NO simplification. NO cleanup. Stay focused on current task only."
    fi
fi

# 50% - Strong warning
if [ "$PCT" -ge 50 ] && [ "$PCT" -lt 60 ]; then
    if [ ! -f "$FLAG_DIR/warn50" ]; then
        touch "$FLAG_DIR/warn50"
        emit_warning "🛑 CONTEXT AT 50% - CHECKPOINT STRONGLY RECOMMENDED 🛑

You should checkpoint now unless task is nearly complete.

FORBIDDEN ACTIONS:
- Writing new features
- 'Simplifying' anything
- 'One more try' on stuck problems
- Any refactoring

If stuck on current approach for 3+ attempts, STOP and checkpoint."
    fi
fi

# 60% - MUST ASK USER
if [ "$PCT" -ge 60 ] && [ "$PCT" -lt 70 ]; then
    if [ ! -f "$FLAG_DIR/warn60" ]; then
        touch "$FLAG_DIR/warn60"
        emit_warning "🛑🛑🛑 MANDATORY USER CHECK - CONTEXT AT 60% 🛑🛑🛑

YOU MUST STOP AND ASK THE USER THIS EXACT QUESTION:

'We are at 60% context. Should I: (A) Commit current work and end session, or (B) Continue with current task?'

DO NOT CONTINUE WORKING UNTIL USER RESPONDS.
DO NOT 'SIMPLIFY' OR 'CLEAN UP' CODE.
DO NOT MAKE THIS DECISION YOURSELF - ASK THE USER."
    fi
fi

# 70% - HARD STOP
if [ "$PCT" -ge 70 ]; then
    if [ ! -f "$FLAG_DIR/warn70" ]; then
        touch "$FLAG_DIR/warn70"
        emit_warning "🚫🚫🚫 CRITICAL - 70% - HARD STOP 🚫🚫🚫

STOP ALL CODE WORK IMMEDIATELY.

Execute now:
1. git commit current work
2. Update HANDOFF.md
3. Tell user: 'Context at 70%. Session must end.'

ANY further code changes are FORBIDDEN."
    fi
fi
