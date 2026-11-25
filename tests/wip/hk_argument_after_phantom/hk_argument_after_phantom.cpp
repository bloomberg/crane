#include "hk_argument_after_phantom.h"

bool HkArgumentAfterPhantom::count_list(const List<uint64_t> &xs) {
  auto _once1 = xs.length();
  std::shared_ptr<crane::array_storage<uint64_t>> arr =
      crane::st::new_list_array<uint64_t>(crane::st::extent(
          UINT64_C(0),
          (((_once1 - UINT64_C(1)) > _once1 ? 0 : (_once1 - UINT64_C(1))))),
                                          xs);
  return [&]() -> bool {
    auto _cs = count<void>(std::move(arr), xs.length());
    if (_cs.has_value()) {
      const List<uint64_t> &_x = *_cs;
      return false;
    } else {
      return true;
    }
  }();
}
