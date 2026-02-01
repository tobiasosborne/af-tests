#!/bin/bash
# Install Claude Code hooks for af-tests project
# Run this on each device to set up context checkpoint warnings
#
# IMPORTANT: The checkpoint hook requires a special statusLine that writes
# context percentage to /tmp/claude-context-pct. PostToolUse hooks do NOT
# receive context_window data - only statusLine does.

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CLAUDE_DIR="$HOME/.claude"
SCRIPTS_DIR="$CLAUDE_DIR/scripts"
SETTINGS_FILE="$CLAUDE_DIR/settings.json"

echo "Installing af-tests Claude Code hooks..."

# Create scripts directory
mkdir -p "$SCRIPTS_DIR"

# Copy the checkpoint script
cp "$SCRIPT_DIR/context-checkpoint.sh" "$SCRIPTS_DIR/"
chmod +x "$SCRIPTS_DIR/context-checkpoint.sh"
echo "✓ Installed context-checkpoint.sh"

# Check if settings.json exists
if [ ! -f "$SETTINGS_FILE" ]; then
    echo "⚠ No settings.json found. Creating with required configuration."
    cat > "$SETTINGS_FILE" << 'SETTINGS'
{
  "hooks": {
    "PostToolUse": [
      {
        "matcher": "",
        "hooks": [
          {
            "type": "command",
            "command": "~/.claude/scripts/context-checkpoint.sh"
          }
        ]
      }
    ]
  },
  "statusLine": {
    "type": "command",
    "command": "input=$(cat); user=$(whoami); host=$(hostname -s); dir=$(pwd); usage=$(echo \"$input\" | jq '.context_window.current_usage'); if [ \"$usage\" != \"null\" ]; then current=$(echo \"$usage\" | jq '.input_tokens + .cache_creation_input_tokens + .cache_read_input_tokens'); size=$(echo \"$input\" | jq '.context_window.context_window_size'); pct=$((current * 100 / size)); echo \"$pct\" > /tmp/claude-context-pct; sid=$(echo \"$input\" | jq -r '.session_id // empty'); [ -n \"$sid\" ] && echo \"$sid\" > /tmp/claude-session-id; filled=$((pct / 5)); empty=$((20 - filled)); bar=''; i=0; while [ $i -lt $filled ]; do bar=\"${bar}█\"; i=$((i + 1)); done; i=0; while [ $i -lt $empty ]; do bar=\"${bar}░\"; i=$((i + 1)); done; printf '\\033[01;32m%s@%s\\033[00m:\\033[01;34m%s\\033[00m \\033[2m[\\033[00m%s \\033[01;33m%d%%\\033[00m\\033[2m]\\033[00m' \"$user\" \"$host\" \"$dir\" \"$bar\" \"$pct\"; else printf '\\033[01;32m%s@%s\\033[00m:\\033[01;34m%s\\033[00m' \"$user\" \"$host\" \"$dir\"; fi"
  }
}
SETTINGS
    echo "✓ Created settings.json with hooks and statusLine"
else
    echo ""
    echo "⚠ settings.json already exists. Manual configuration needed."
    echo ""
    echo "1. Add PostToolUse hook (if not present):"
    echo ""
    cat << 'EOF'
    "PostToolUse": [
      {
        "matcher": "",
        "hooks": [
          {
            "type": "command",
            "command": "~/.claude/scripts/context-checkpoint.sh"
          }
        ]
      }
    ]
EOF
    echo ""
    echo "2. CRITICAL: Add/update statusLine to write context % to file:"
    echo "   (The checkpoint hook reads from /tmp/claude-context-pct)"
    echo ""
    echo "   See .claude/scripts/statusline-template.txt for the required command."
    echo ""
    echo "   Or run: claude config edit"
fi

echo ""
echo "Done. Restart Claude Code to activate."
