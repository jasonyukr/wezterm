# CopyMode `MoveBackwardWhitespaceWord`

{{since('nightly')}}

Moves the CopyMode cursor position backwards to the start of the current
or previous whitespace delimited word.

Unlike [MoveBackwardWord](MoveBackwardWord.md), which uses unicode word
boundaries and so treats a run of punctuation as a word of its own, any
contiguous run of non-whitespace is considered to be a single word, so
`--flag=value` is one word rather than five.

A word that was soft-wrapped across multiple lines is treated as the
single word that it is.

```lua
local wezterm = require 'wezterm'
local act = wezterm.action

return {
  key_tables = {
    copy_mode = {
      {
        key = 'B',
        mods = 'SHIFT',
        action = act.CopyMode 'MoveBackwardWhitespaceWord',
      },
    },
  },
}
```

See also: [MoveForwardWhitespaceWord](MoveForwardWhitespaceWord.md).
