#!/bin/bash
# Install Claude Code hooks for af-tests project
# Run this on each device to set up context checkpoint warnings

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CLAUDE_DIR="$HOME/.claude"
SCRIPTS_DIR="$CLAUDE_DIR/scripts"
SETTINGS_FILE="$CLAUDE_DIR/settings.json"

echo "Installing af-tests Claude Code hooks..."

# Create scripts directory
mkdir -p "$SCRIPTS_DIR"

# Copy/symlink the checkpoint script
cp "$SCRIPT_DIR/context-checkpoint.sh" "$SCRIPTS_DIR/"
chmod +x "$SCRIPTS_DIR/context-checkpoint.sh"
echo "✓ Installed context-checkpoint.sh"

# Check if settings.json exists
if [ ! -f "$SETTINGS_FILE" ]; then
    echo "⚠ No settings.json found. Creating minimal one."
    echo '{"hooks":{}}' > "$SETTINGS_FILE"
fi

# Check if PostToolUse hook already configured
if grep -q "PostToolUse" "$SETTINGS_FILE"; then
    echo "✓ PostToolUse hook already configured in settings.json"
else
    echo ""
    echo "⚠ Add this to your ~/.claude/settings.json hooks section:"
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
    echo "Or run: claude config edit"
fi

echo ""
echo "Done. Restart Claude Code to activate."
