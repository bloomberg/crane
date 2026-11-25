#include "phantom_filler_not_written.h"

uint64_t PhantomFillerNotWritten::sum_list(const List<uint64_t> &xs) {
  auto _once1 = xs.length();
  std::shared_ptr<crane::array_storage<uint64_t>> arr =
      crane::st::new_list_array<uint64_t>(crane::st::extent(
          UINT64_C(0),
          (((_once1 - UINT64_C(1)) > _once1 ? 0 : (_once1 - UINT64_C(1))))),
                                          xs);
  return sum_from<std::monostate, void>(std::span<const uint64_t>{*arr},
                                        xs.length(), UINT64_C(0));
}

bool Sumbool::sumbool_of_bool(bool b) {
  if (b) {
    return true;
  } else {
    return false;
  }
}
