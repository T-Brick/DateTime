# DateTime

This is a work-in-progress DateTime package for Lean which implements some
utilities for working with [ISO 8601](https://en.wikipedia.org/wiki/ISO_8601).

Contributions welcome! <3

# Usage

Add the following to your `lakefile.lean`:

```lean
require datetime from git "https://github.com/T-Brick/DateTime" @ "main"
```

Then you can add and use it in your projects:

```lean
import DateTime

#eval DateTime.now                      -- The current system-wide time (UTC)
#eval DateTime.current_millis           -- Number of milliseconds since epoch


open DateTime.Notation                  -- Examples using notation

#eval date% 2024-02-29                  -- 2024-02-29
#eval date% 2024-06                     -- 2024-06
#eval date% "2024-10-23"                -- Except.ok 2024-10-23
#eval date% 2024-10-23 + 28 days        -- 2024-11-20
#eval time% 14:54:32 + 13min            -- 15:07:32
#eval time_offset% 14:54:32-07:00       -- 14:54:32-07:00
#eval datetime% "2024-02-18T22:57:10Z"  -- Except.ok 2024-02-18T22:57:10Z
```

