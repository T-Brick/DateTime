/- Copyright (c) 2024 Theodora Brick.

Authors: Thea Brick
-/

import DateTime.DateTime

/- Todo should these be scoped? -/
namespace DateTime.Notation

declare_syntax_cat date
syntax str : date
syntax num : date
syntax num noWs "-" noWs num : date
syntax num noWs "-" noWs num noWs "-" noWs num : date
syntax "date%" date : term

macro_rules
| `(date% $s:str) => `(Calendar.Date.parse $s)
| `(date% $y:num) => `(Calendar.Date.year $y)
| `(date% $y:num-$m:num) => `(Calendar.Date.year_month $y $m)
| `(date% $y:num-$m:num-$d:num) =>
  `(Calendar.Date.year_month_day $y $m ⟨$d, by decide⟩
      (by simp (config := {decide := true}))
   )


declare_syntax_cat eng_date_offset
syntax num "day"    : eng_date_offset
syntax num "days"   : eng_date_offset
syntax num "month"  : eng_date_offset
syntax num "months" : eng_date_offset
syntax num "year"   : eng_date_offset
syntax num "years"  : eng_date_offset
syntax "eng_date_offset%" eng_date_offset : term
syntax "date%" date "+" eng_date_offset : term

macro_rules
| `(date% $d:date + $off:eng_date_offset) =>
  `((date% $d:date) + (eng_date_offset% $off))
| `(eng_date_offset% $d:num day)    => `((0,0,$d))
| `(eng_date_offset% $d:num days)   => `((0,0,$d))
| `(eng_date_offset% $m:num month)  => `((0,$m,0))
| `(eng_date_offset% $m:num months) => `((0,$m,0))
| `(eng_date_offset% $y:num year)   => `(($y,0,0))
| `(eng_date_offset% $y:num years)  => `(($y,0,0))


declare_syntax_cat time
syntax str : time
syntax num : time
syntax num noWs ":" noWs num : time
syntax num noWs ":" noWs num noWs ":" noWs num : time
syntax "time%" time : term

macro_rules
| `(time% $str:str) => `(Time.parse $str)
| `(time% $h:num) =>
  `(Time.mk ⟨$h, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩ (by simp))
| `(time% $h:num:$m:num) =>
  `(Time.mk ⟨$h, by decide⟩ ⟨$m, by decide⟩ ⟨0, by decide⟩ (by simp))
| `(time% $h:num:$m:num:$s:num) =>
  `(Time.mk ⟨$h, by decide⟩ ⟨$m, by decide⟩ ⟨$s, by decide⟩ (by simp))


declare_syntax_cat eng_time
syntax num "h"        : eng_time
syntax num "hour"     : eng_time
syntax num "hours"    : eng_time
syntax num "m"        : eng_time
syntax num "min"      : eng_time
syntax num "minute"   : eng_time
syntax num "minutes"  : eng_time
syntax num "s"        : eng_time
syntax num "sec"      : eng_time
syntax num "second"   : eng_time
syntax num "seconds"  : eng_time
syntax "eng_time%" eng_time : term
syntax "time%" eng_time : term
syntax "time%" time "+" eng_time : term

macro_rules
| `(time% $e:eng_time) => `(eng_time% $e)
| `(time% $t:time + $e:eng_time) => `((time% $t:time) + (eng_time% $e))
| `(eng_time% $hh:num h)        => `(time% $hh:num:00:00)
| `(eng_time% $hh:num hour)     => `(time% $hh:num:00:00)
| `(eng_time% $hh:num hours)    => `(time% $hh:num:00:00)
| `(eng_time% $mm:num m)        => `(time% 00:$mm:num:00)
| `(eng_time% $mm:num min)      => `(time% 00:$mm:num:00)
| `(eng_time% $mm:num minute)   => `(time% 00:$mm:num:00)
| `(eng_time% $mm:num minutes)  => `(time% 00:$mm:num:00)
| `(eng_time% $ss:num s)        => `(time% 00:00:$ss:num)
| `(eng_time% $ss:num sec)      => `(time% 00:00:$ss:num)
| `(eng_time% $ss:num second)   => `(time% 00:00:$ss:num)
| `(eng_time% $ss:num seconds)  => `(time% 00:00:$ss:num)


declare_syntax_cat time_offset
syntax str : time_offset
syntax time "Z" : time_offset -- todo: this shouldn't have white space
syntax time noWs "+" noWs num : time_offset
syntax time noWs "+" noWs num noWs ":" noWs num : time_offset
syntax time noWs "-" noWs num : time_offset
syntax time noWs "-" noWs num noWs ":" noWs num : time_offset
syntax "time_offset%" time_offset : term

macro_rules
| `(time_offset% $str:str) => `(Time.Offset.parse $str)
| `(time_offset% $t:time Z) => `(Time.UTC (time% $t:time))
| `(time_offset% $t:time+$hh:num) =>
  `(Time.Offset.mk (time% $t:time) true ⟨$hh, by decide⟩ ⟨0, by decide⟩)
| `(time_offset% $t:time+$hh:num:$mm:num) =>
  `(Time.Offset.mk (time% $t:time) true ⟨$hh, by decide⟩ ⟨$mm, by decide⟩)
| `(time_offset% $t:time-$hh:num) =>
  `(Time.Offset.mk (time% $t:time) false ⟨$hh, by decide⟩ ⟨0, by decide⟩)
| `(time_offset% $t:time-$hh:num:$mm:num) =>
  `(Time.Offset.mk (time% $t:time) false ⟨$hh, by decide⟩ ⟨$mm, by decide⟩)


declare_syntax_cat datetime
syntax str : datetime
syntax date "T" time_offset : datetime -- todo should be noWs
syntax "datetime%" datetime : term

macro_rules
| `(datetime% $str:str) => `(DateTime.Offset.parse $str)
| `(datetime% $d:date T $t:time_offset) =>
  `(DateTime.Offset.mk (date% $d) (time_offset% $t))
