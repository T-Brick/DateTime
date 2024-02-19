/- Copyright (c) 2024 Theodora Brick.

Authors: Thea Brick
-/

import DateTime.DateTime

/- Todo should these be scoped? -/
namespace DateTime.Notation

declare_syntax_cat date
scoped syntax str : date
scoped syntax num : date
scoped syntax num noWs "-" noWs num : date
scoped syntax num noWs "-" noWs num noWs "-" noWs num : date
scoped syntax "date%" date : term

macro_rules
| `(date% $s:str) => `(Calendar.Date.parse $s)
| `(date% $y:num) => `(Calendar.Date.year $y)
| `(date% $y:num-$m:num) => `(Calendar.Date.year_month $y $m)
| `(date% $y:num-$m:num-$d:num) =>
  `(Calendar.Date.year_month_day $y $m ⟨$d, by decide⟩
      (by simp (config := {decide := true}))
   )


declare_syntax_cat eng_date_offset
scoped syntax num "day"    : eng_date_offset
scoped syntax num "days"   : eng_date_offset
scoped syntax num "month"  : eng_date_offset
scoped syntax num "months" : eng_date_offset
scoped syntax num "year"   : eng_date_offset
scoped syntax num "years"  : eng_date_offset
scoped syntax "eng_date_offset%" eng_date_offset : term
scoped syntax "date%" date "+" eng_date_offset : term

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
scoped syntax str : time
scoped syntax num : time
scoped syntax num noWs ":" noWs num : time
scoped syntax num noWs ":" noWs num noWs ":" noWs num : time
scoped syntax "time%" time : term

macro_rules
| `(time% $str:str) => `(Time.parse $str)
| `(time% $h:num) =>
  `(Time.mk ⟨$h, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩ (by simp))
| `(time% $h:num:$m:num) =>
  `(Time.mk ⟨$h, by decide⟩ ⟨$m, by decide⟩ ⟨0, by decide⟩ (by simp))
| `(time% $h:num:$m:num:$s:num) =>
  `(Time.mk ⟨$h, by decide⟩ ⟨$m, by decide⟩ ⟨$s, by decide⟩ (by simp))

declare_syntax_cat eng_time
scoped syntax num "h"        : eng_time
scoped syntax num "hour"     : eng_time
scoped syntax num "hours"    : eng_time
scoped syntax num "m"        : eng_time
scoped syntax num "min"      : eng_time
scoped syntax num "minute"   : eng_time
scoped syntax num "minutes"  : eng_time
scoped syntax num "s"        : eng_time
scoped syntax num "sec"      : eng_time
scoped syntax num "second"   : eng_time
scoped syntax num "seconds"  : eng_time
scoped syntax "eng_time%" eng_time : term
scoped syntax "time%" eng_time : term
scoped syntax "time%" time "+" eng_time : term

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
scoped syntax str : time_offset
scoped syntax time "Z" : time_offset -- todo: this shouldn't have white space
scoped syntax time noWs "+" noWs num : time_offset
scoped syntax time noWs "+" noWs num noWs ":" noWs num : time_offset
scoped syntax time noWs "-" noWs num : time_offset
scoped syntax time noWs "-" noWs num noWs ":" noWs num : time_offset
scoped syntax "time_offset%" time_offset : term

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
scoped syntax str : datetime
scoped syntax date "T" time_offset : datetime -- todo should be noWs
scoped syntax "datetime%" datetime : term

macro_rules
| `(datetime% $str:str) => `(DateTime.Offset.parse $str)
| `(datetime% $d:date T $t:time_offset) =>
  `(DateTime.Offset.mk (date% $d) (time_offset% $t))
