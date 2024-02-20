/* Copyright (c) 2024 Theodora Brick.

Authors: Thea Brick
*/
#include <lean/lean.h>

/* DateTime.now_iso_seconds : IO String */
extern "C" LEAN_EXPORT lean_object * lean_datetime_now_iso_sec(lean_object * /* w */) {
    const auto now = std::chrono::system_clock::now();
    std::time_t now_time = std::chrono::system_clock::to_time_t(now);
    char buf[sizeof "YYYY-MM-DDThh:mm:ssZ"];
    strftime(buf, sizeof buf, "%FT%TZ", gmtime(&now_time));
    return lean_io_result_mk_ok(lean_mk_string(buf));
}

/* DateTime.epoch_start_iso_seconds : IO String */
extern "C" LEAN_EXPORT lean_object * lean_datetime_epoch_start_iso_sec(lean_object * /* w */) {
    const auto epoch = std::chrono::time_point<std::chrono::system_clock>();
    std::time_t epoch_time = std::chrono::system_clock::to_time_t(epoch);
    char buf[sizeof "YYYY-MM-DDThh:mm:ssZ"];
    strftime(buf, sizeof buf, "%FT%TZ", gmtime(&epoch_time));
    return lean_io_result_mk_ok(lean_mk_string(buf));
}

/* DateTime.current_millis : IO Nat */
extern "C" LEAN_EXPORT lean_object * lean_datetime_current_millis(lean_object * /* w */) {
    const auto now = std::chrono::system_clock::now();
    auto millis = std::chrono::duration_cast<std::chrono::milliseconds>(now.time_since_epoch()).count();
    return lean_io_result_mk_ok(lean_uint64_to_nat(millis));
}

/* DateTime.current_nanos : IO Nat */
extern "C" LEAN_EXPORT lean_object * lean_datetime_current_nanos(lean_object * /* w */) {
    const auto now = std::chrono::system_clock::now();
    auto millis = std::chrono::duration_cast<std::chrono::nanoseconds>(now.time_since_epoch()).count();
    return lean_io_result_mk_ok(lean_uint64_to_nat(millis));
}
