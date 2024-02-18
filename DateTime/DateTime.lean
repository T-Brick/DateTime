/- Copyright (c) 2024 Theodora Brick.

Authors: Thea Brick
-/

import DateTime.Calendar
import DateTime.Time

structure DateTime where
  date : DateTime.Calendar.Date
  time : DateTime.Time
deriving Repr

structure DateTime.Offset where
  date : DateTime.Calendar.Date
  time : DateTime.Time.Offset
deriving Repr

namespace DateTime

def add (dt : DateTime) (year mon day : Nat) (time : Time) : DateTime :=
  let (time', days) := dt.time.add_carry time
  let date' := dt.date.add_ymd year mon (day + days)
  ⟨date', time'⟩

def add_time (dt : DateTime) : Time → DateTime := add dt 0 0 0
def add_ymd (dt : DateTime) (year mon day : Nat) : DateTime :=
  add dt year mon day Time.midnight

instance : HAdd DateTime Time DateTime := ⟨add_time⟩
instance : HAdd DateTime (Nat × Nat × Nat) DateTime :=
  ⟨fun dt (y, m, d) => add_ymd dt y m d⟩

def basic_format : DateTime → String
  | ⟨date, time⟩ => s!"{date.basic_format}{time.basic_format}"

def extended_format : DateTime → String
  | ⟨date, time⟩ => s!"{date.extended_format}{time.extended_format}"

def parse (str : String) : Except String DateTime := do
  match str.split (fun | 'T' => true | _ => false) with
  | date_str :: time_str :: [] =>
    let date ← Calendar.Date.parse date_str
    let time ← Time.parse time_str
    return ⟨date, time⟩
  | _ => throw s!"Failed to split date and time in string {str}"



namespace Offset

def add (dt : Offset) (year mon day : Nat) (time : Time) : Offset :=
  let (time', days) := dt.time.add_carry time
  let date' := dt.date.add_ymd year mon (day + days)
  ⟨date', time'⟩

def add_time (dt : DateTime.Offset) : Time → DateTime.Offset := add dt 0 0 0
def add_ymd (dt : DateTime.Offset) (year mon day : Nat) : DateTime.Offset :=
  add dt year mon day Time.midnight

instance : HAdd DateTime.Offset Time DateTime.Offset := ⟨add_time⟩
instance : HAdd DateTime.Offset (Nat × Nat × Nat) DateTime.Offset :=
  ⟨fun dt (y, m, d) => add_ymd dt y m d⟩


def basic_format : Offset → String
  | ⟨date, offset⟩ => s!"{date.basic_format}{offset.basic_format}"

def extended_format : Offset → String
  | ⟨date, offset⟩ => s!"{date.extended_format}{offset.extended_format}"

def parse (str : String) : Except String DateTime.Offset := do
  match str.split (fun | 'T' => true | _ => false) with
  | date_str :: time_str :: [] =>
    let date ← Calendar.Date.parse date_str
    let offset ← Time.Offset.parse time_str
    return ⟨date, offset⟩
  | _ => throw s!"Failed to split date and time offset in string {str}"

end Offset

end DateTime

