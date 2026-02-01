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

# 35% - STOP and evaluate
if [ "$PCT" -ge 35 ] && [ "$PCT" -lt 50 ]; then
    if [ ! -f "$FLAG_DIR/warn35" ]; then
        touch "$FLAG_DIR/warn35"
        emit_warning "🚨🚨🚨 MANDATORY CHECKPOINT - CONTEXT AT 35% 🚨🚨🚨

YOU MUST STOP AND RESPOND TO THE USER WITH THIS EXACT QUESTION:

'We are at 35% context. I need to checkpoint. Should I: (A) Commit current work and end session, or (B) Continue if task is nearly complete?'

DO NOT CONTINUE WORKING UNTIL USER RESPONDS.
DO NOT 'SIMPLIFY' OR 'CLEAN UP' CODE - THIS IS FORBIDDEN.
DO NOT REWRITE OR REFACTOR - THIS IS FORBIDDEN.

The urge to simplify IS YOUR SIGNAL TO STOP."
    elif [ "$PCT" -ge 42 ] && [ ! -f "$FLAG_DIR/remind42" ]; then
        touch "$FLAG_DIR/remind42"
        emit_warning "🚨 CHECKPOINT REMINDER - 42% - Did you ask the user about checkpointing? If not, ASK NOW. DO NOT SIMPLIFY CODE."
    fi
fi

# 50% - HARD STOP
if [ "$PCT" -ge 50 ] && [ "$PCT" -lt 65 ]; then
    if [ ! -f "$FLAG_DIR/warn50" ]; then
        touch "$FLAG_DIR/warn50"
        emit_warning "🛑🛑🛑 MANDATORY STOP - CONTEXT AT 50% 🛑🛑🛑

STOP ALL PROOF/CODE WORK IMMEDIATELY.

Execute this sequence NOW:
1. git add [files] && git commit -m 'WIP: [state]'
2. Update HANDOFF.md
3. Tell user: 'Context at 50%. I have committed current work. Session should end.'

FORBIDDEN ACTIONS:
- Writing more code
- 'Simplifying' anything
- 'One more try'
- Any refactoring"
    elif [ "$PCT" -ge 58 ] && [ ! -f "$FLAG_DIR/remind58" ]; then
        touch "$FLAG_DIR/remind58"
        emit_warning "🛑 58% - WHY ARE YOU STILL WORKING? Execute checkpoint protocol NOW. No exceptions."
    fi
fi

# 65% - ABSOLUTE STOP
if [ "$PCT" -ge 65 ]; then
    if [ ! -f "$FLAG_DIR/warn65" ]; then
        touch "$FLAG_DIR/warn65"
        emit_warning "🚫🚫🚫 CRITICAL - 65% - ABSOLUTE STOP 🚫🚫🚫

YOU ARE FORBIDDEN FROM ANY FURTHER CODE CHANGES.

ONLY ALLOWED ACTIONS:
- git commit (existing work only)
- Tell user session must end

ANY other action violates your instructions."
    fi
fi
