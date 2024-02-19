/- Copyright (c) 2024 Theodora Brick.

Authors: Thea Brick
-/
import «DateTime»

def main : IO Unit := return

-- Here's an example of using some notation
#eval date% 2024-02-29                  -- 2024-02-29
#eval date% 2024-06                     -- 2024-06
#eval date% "2024-10-23"                -- Except.ok 2024-10-23
#eval date% 2024-10-23 + 28 days        -- 2024-11-20
#eval time% 14:54:32 + 13min            -- 15:07:32
#eval time_offset% 14:54:32-07:00       -- 14:54:32-07:00
#eval datetime% "2024-02-18T22:57:10Z"  -- Except.ok 2024-02-18T22:57:10Z
