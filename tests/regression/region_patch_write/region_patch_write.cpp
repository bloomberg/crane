#include <region_patch_write.h>

List<unsigned int>
RegionPatchWrite::update_region(const List<unsigned int> &rom,
                                const unsigned int &base,
                                const List<unsigned int> &bytes) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(rom.v())) {
    return List<unsigned int>::nil();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(rom.v());
    if (base <= 0) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(bytes.v())) {
        return List<unsigned int>::cons(d_a0, *(d_a1));
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(bytes.v());
        return List<unsigned int>::cons(d_a00,
                                        update_region(*(d_a1), 0u, *(d_a10)));
      }
    } else {
      unsigned int n = base - 1;
      return List<unsigned int>::cons(d_a0, update_region(*(d_a1), n, bytes));
    }
  }
}
