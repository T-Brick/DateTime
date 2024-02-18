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

