/- Copyright (c) 2024 Theodora Brick.

Authors: Thea Brick
-/

import DateTime.Utils

namespace DateTime.Time

/- Tehnically ISO 8601 allows for 24:00:00 to be used -/
def Hour := Fin 25
deriving Inhabited, DecidableEq

namespace Hour

def to_hh : Hour → String
  | ⟨h, _⟩ => (toString h).leftpad0 2
instance : Repr Hour := ⟨fun h _ => h.to_hh⟩


def parse_hh (s : String) : Except String (Hour × String) := do
  if s.length ≥ 2 then
    if let some h := (s.extract ⟨0⟩ ⟨2⟩).toNat? then
      if prop : h < 25
      then return ⟨⟨h, prop⟩, s.drop 2⟩
      else throw s!"Parsed hour {h} which is not less than 25"
  throw s!"Could not parse hh from {s}"

end Hour


def Minute := Fin 60
deriving Inhabited, DecidableEq

namespace Minute

def to_mm : Minute → String
  | ⟨m, _⟩ => (toString m).leftpad0 2
instance : Repr Minute := ⟨fun m _ => m.to_mm⟩


def parse_mm (s : String) : Except String (Minute × String) := do
  if s.length ≥ 2 then
    if let some m := (s.extract ⟨0⟩ ⟨2⟩).toNat? then
      if prop : m < 60
      then return ⟨⟨m, prop⟩, s.drop 2⟩
      else throw s!"Parsed minute {m} which is not less than 60"
  throw s!"Could not parse hh from {s}"

end Minute

/- Use 61 because of leap seconds -/
def Second := Fin 61
deriving Inhabited, DecidableEq

namespace Second

def to_ss : Second → String
  | ⟨s, _⟩ => (toString s).leftpad0 2
instance : Repr Second := ⟨fun s _ => s.to_ss⟩


def parse_ss (s : String) : Except String (Second × String) := do
  if s.length ≥ 2 then
    if let some sec := (s.extract ⟨0⟩ ⟨2⟩).toNat? then
      if prop : sec < 61
      then return ⟨⟨sec, prop⟩, s.drop 2⟩
      else throw s!"Parsed second {sec} which is not less than 61"
  throw s!"Could not parse hh from {s}"

end Second

end Time

structure Time where
  hour   : Time.Hour
  minute : Time.Minute
  second : Time.Second
  wf : hour.val = 24 → minute.val = 0 ∧ second.val = 0
deriving DecidableEq

namespace Time

def midnight : Time :=
  ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, by simp⟩
def noon : Time :=
  ⟨⟨12, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, by simp⟩
def end_of_day : Time :=
  ⟨⟨24, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, by simp⟩

instance : Inhabited Time := ⟨midnight⟩


def add_carry : Time → Time → (Time × Nat)
  | ⟨h₁, m₁, s₁, _⟩, ⟨h₂, m₂, s₂, _⟩ =>
    let s := s₁.val + s₂.val
    let m := m₁.val + m₂.val + (s / 60)
    let h := h₁.val + h₂.val + (m / 60)
    let time :=
      { hour   := ⟨h % 24, by
                    have := Nat.mod_lt h (y := 24) (by decide)
                    exact Nat.lt_trans this (Nat.lt_succ_self _)
                  ⟩
        minute := ⟨m % 60, by exact Nat.mod_lt m (by decide)⟩
        second := ⟨s % 60, by
                    have := Nat.mod_lt s (y := 60) (by decide)
                    exact Nat.lt_trans this (Nat.lt_succ_self _)
                  ⟩
        wf := by
          simp; intro p
          have := Nat.mod_lt h (y := 24) (by decide)
          simp [p] at this
      }
    (time, h / 24)

@[inline] def add (t₁ t₂ : Time) : Time := add_carry t₁ t₂ |>.1
instance : HAdd Time Time Time := ⟨add⟩


def basic_format : Time → String
  | ⟨h, m, s, _⟩ => s!"T{h.to_hh}{m.to_mm}{s.to_ss}"

def extended_format (include_T := true) : Time → String
  | ⟨h, m, s, _⟩ =>
    s!"{if include_T then "T" else ""}{h.to_hh}:{m.to_mm}:{s.to_ss}"
instance : Repr Time := ⟨fun t _ => t.extended_format (include_T := false)⟩


private def parse_basic_hour_min (str : String)
    : Except String (Time × String) := do
  let s := str
  let (hh, s) ← Hour.parse_hh s

  try
    let (mm, s) ← Minute.parse_mm s
    if p :  hh.val ≠ 24 ∨ mm.val = 0 then
      return ⟨⟨hh, mm, ⟨0, by decide⟩, by intro h; simp [h] at *; exact p⟩, s⟩
    else throw s!"Minutes must be zero when the hour is 24"
  catch _ =>
    return ⟨⟨hh, ⟨0, by decide⟩, ⟨0, by decide⟩, by simp⟩, s⟩

def parse_basic_format' (str : String) : Except String (Time × String) := do
  let s := str
  if ¬s.startsWith "T" then throw s!"Time is missing 'T' in {str}"
  let s := s.drop 1

  let (hh_mm, s) ← parse_basic_hour_min s
  let hh := hh_mm.hour
  let mm := hh_mm.minute

  try
    let (ss, s) ← Second.parse_ss s
    if p : hh.val ≠ 24 ∨ (mm.val = 0 ∧ ss.val = 0)
    then return ⟨⟨hh, mm, ss, by intro h; simp [h] at *; exact p⟩, s⟩
    else throw s!"Minutes and seconds must be zero when the hour is 24"
  catch _ =>
    return ⟨hh_mm, s⟩

def parse_basic_format (str : String) : Except String Time := do
  let (time, s) ← parse_basic_format' str
  if s = "" then return time
  else throw s!"Could not parse basic format time from {str}"

private def parse_extended_hour_min (str : String)
    : Except String (Time × String) := do
  let s := str
  let (hh, s) ← Hour.parse_hh s
  -- if s = "" then return ⟨⟨hh, ⟨0, by decide⟩, ⟨0, by decide⟩, by simp⟩, s⟩
  if ¬s.startsWith ":" then
    return ⟨⟨hh, ⟨0, by decide⟩, ⟨0, by decide⟩, by simp⟩, s⟩
  let s := s.drop 1

  let (mm, s) ← Minute.parse_mm s
  if p :  hh.val ≠ 24 ∨ mm.val = 0 then
    return ⟨⟨hh, mm, ⟨0, by decide⟩, by intro h; simp [h] at *; exact p⟩, s⟩
  else throw s!"Minutes must be zero when the hour is 24"

def parse_extended_format' (str : String) : Except String (Time × String) := do
  let s := if str.startsWith "T" then str.drop 1 else str

  let (hh_mm, s) ← parse_extended_hour_min s
  let hh := hh_mm.hour
  let mm := hh_mm.minute
  if ¬s.startsWith ":" then return ⟨hh_mm, s⟩
  let s := s.drop 1

  let (ss, s) ← Second.parse_ss s
  if p : hh.val ≠ 24 ∨ (mm.val = 0 ∧ ss.val = 0)
  then return ⟨⟨hh, mm, ss, by intro h; simp [h] at *; exact p⟩, s⟩
  else throw s!"Minutes and seconds must be zero when the hour is 24"

def parse_extended_format (str : String) : Except String Time := do
  let (time, s) ← parse_extended_format' str
  if s = "" then return time
  else throw s!"Could not parse extended format time from {str}"

def parse (str : String) : Except String Time := do
  try parse_basic_format str
  catch _ =>
    try parse_extended_format str
    catch _ => throw s!"Could not parse time from {str}"


structure Offset where
  time          : Time
  offset_add    : Bool
  offset_hour   : Hour
  offset_minute : Minute
deriving Inhabited, DecidableEq

def UTC (time : Time) : Offset := ⟨time, true, ⟨0, by decide⟩, ⟨0, by decide⟩⟩
def UTC.midnight   : Offset := UTC .midnight
def UTC.noon       : Offset := UTC .noon
def UTC.end_of_day : Offset := UTC .end_of_day

namespace Offset

def add_carry (t₁ : Time.Offset) (t₂ : Time) : (Time.Offset × Nat) :=
  let (time', days) := t₁.time.add_carry t₂
  ({ t₁ with time := time' }, days)
def add (t₁ : Time.Offset) (t₂ : Time) : Time.Offset := t₁.add_carry t₂ |>.1
instance : HAdd Time.Offset Time Time.Offset := ⟨add⟩

def basic_format : Offset → String
  | ⟨time, add?, hour, min⟩ =>
    if hour.val = 0 ∧ min.val = 0 then s!"{time.basic_format}Z" else
    let c := if add? then "+" else "-"
    s!"{time.basic_format}{c}{hour.to_hh}{min.to_mm}"

def extended_format : Offset → String
  | ⟨time, add?, hour, min⟩ =>
    if hour.val = 0 ∧ min.val = 0 then s!"{time.extended_format}Z" else
    let c := if add? then "+" else "-"
    s!"{time.extended_format}{c}{hour.to_hh}:{min.to_mm}"
instance : Repr Time.Offset := ⟨fun t _ => t.extended_format⟩


private def parse_basic_offset_component (time : Time) (str : String)
    : Except String Offset := do
  if str = "Z" then return ⟨time, true, ⟨0, by decide⟩, ⟨0, by decide⟩⟩
  let plus := str.startsWith "+"
  let neg  := str.startsWith "-"
  if ¬plus && ¬neg then throw s!"No offset information in {str}"
  let s := str.drop 1
  let (offset, s) ← parse_basic_hour_min s
  if s = "" then return ⟨time, plus, offset.hour, offset.minute⟩
  throw s!"Could not parse basic format time offset from {str}"

private def parse_extended_offset_component (time : Time) (str : String)
    : Except String Offset := do
  if str = "Z" then return ⟨time, true, ⟨0, by decide⟩, ⟨0, by decide⟩⟩
  let plus := str.startsWith "+"
  let neg  := str.startsWith "-"
  if ¬plus && ¬neg then throw s!"No offset information in {str}"
  let s := str.drop 1
  let (offset, s) ← parse_extended_hour_min s
  if s = "" then return ⟨time, plus, offset.hour, offset.minute⟩
  throw s!"Could not parse extended format time offset from {str}"

private def parse_offset_component (time : Time) (str : String)
    : Except String Offset := do
  try parse_basic_offset_component time str
  catch _ =>
    try parse_extended_offset_component time str
    catch _ => throw s!"Could not parse time offset from {str}"

def parse (str : String) : Except String Offset := do
  try let (time, s) ← parse_basic_format' str
      parse_offset_component time s
  catch _ =>
    try let (time, s) ← parse_extended_format' str
        parse_offset_component time s
    catch _ => throw s!"Could not parse time+offset from {str}"

end Offset

end Time
