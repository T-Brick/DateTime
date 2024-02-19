#include <lean/lean.h>

/* DateTime.now_str : IO String */
extern "C" LEAN_EXPORT lean_object * lean_datetime_now_iso_sec(lean_object * /* w */) {
    auto now = std::chrono::system_clock::now();
    std::time_t now_time = std::chrono::system_clock::to_time_t(now);
    char buf[sizeof "YYYY-MM-DDThh:mm:ssZ"];
    strftime(buf, sizeof buf, "%FT%TZ", gmtime(&now_time));
    return lean_io_result_mk_ok(lean_mk_string(buf));
}


