/- Copyright (c) 2024 Theodora Brick.

Authors: Thea Brick
-/

namespace DateTime

/-- A `String` that is the ISO representation of the current system-wide wall
    clock time up to the nearest second.
 -/
@[extern "lean_datetime_now_iso_sec"] opaque now_iso_seconds : IO String

/-- A `String` that is the ISO representation of the start datetime of the
    system's current epoch with seconds precision. Usually this is the Unix
    epoch (1970-01-01), but this is not necessarily guarenteed.
 -/
@[extern "lean_datetime_epoch_start_iso_sec"] opaque epoch_start_iso_seconds : IO String

/-- The current number of milliseconds since the start of the system's epoch.
    Usually, this is the number of milliseconds since the start of the Unix
    epoch (1970-01-01) but this is not guarenteed.

    This value is not guarenteed to be monotonic. Use `Lean.IO.monoMsNow` if a
    monotonically increasing time is needed.
 -/
@[extern "lean_datetime_current_millis"] opaque current_millis : IO Nat

/-- The current number of nanoseconds since the start of the system's epoch.
    Usually, this is the number of nanoseconds since the start of the Unix
    epoch (1970-01-01) but this is not guarenteed.

    This value is not guarenteed to be monotonic. Use `Lean.IO.monoNanosNow` if
    a monotonically increasing time is needed.
 -/
@[extern "lean_datetime_current_nanos"] opaque current_nanos : IO Nat
