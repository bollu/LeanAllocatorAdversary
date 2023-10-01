#include <lean/lean.h>
#include <unistd.h>

extern "C" LEAN_EXPORT lean_object *lean_get_page_size(lean_object * /* w */) {
    int out = getpagesize();
    return lean_io_result_mk_ok(lean_box_uint32(out));
}
