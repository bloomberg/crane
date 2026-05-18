#include "region_patch_write.h"

List<uint64_t> RegionPatchWrite::update_region(const List<uint64_t> &rom,
                                               uint64_t base,
                                               const List<uint64_t> &bytes) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(rom.v())) {
    return List<uint64_t>::nil();
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(rom.v());
    if (base <= 0) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(bytes.v())) {
        return List<uint64_t>::cons(a0, *a1);
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(bytes.v());
        return List<uint64_t>::cons(a00, update_region(*a1, UINT64_C(0), *a10));
      }
    } else {
      uint64_t n = base - 1;
      return List<uint64_t>::cons(a0, update_region(*a1, n, bytes));
    }
  }
}
