#include <region_patch_write.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>> RegionPatchWrite::update_region(
    const std::shared_ptr<List<unsigned int>> &rom, const unsigned int base,
    const std::shared_ptr<List<unsigned int>> &bytes) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(rom->v())) {
    return List<unsigned int>::nil();
  } else {
    const auto &_m = *std::get_if<typename List<unsigned int>::Cons>(&rom->v());
    if (base <= 0) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              bytes->v())) {
        return List<unsigned int>::cons(_m.d_a0, _m.d_a1);
      } else {
        const auto &_m0 =
            *std::get_if<typename List<unsigned int>::Cons>(&bytes->v());
        return List<unsigned int>::cons(_m0.d_a0,
                                        update_region(_m.d_a1, 0u, _m0.d_a1));
      }
    } else {
      unsigned int n = base - 1;
      return List<unsigned int>::cons(_m.d_a0,
                                      update_region(_m.d_a1, n, bytes));
    }
  }
}
