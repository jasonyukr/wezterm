# CopyMode `MoveForwardWhitespaceWord`

{{since('nightly')}}

Moves the CopyMode cursor position forwards to the start of the next
whitespace delimited word.

Unlike [MoveForwardWord](MoveForwardWord.md), which uses unicode word
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
        key = 'W',
        mods = 'SHIFT',
        action = act.CopyMode 'MoveForwardWhitespaceWord',
      },
    },
  },
}
```

See also: [MoveBackwardWhitespaceWord](MoveBackwardWhitespaceWord.md).
