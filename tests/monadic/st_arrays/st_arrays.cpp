#include "st_arrays.h"

uint64_t array_simp_fixed_init(STRefs) {
  std::shared_ptr<crane::array_storage<uint64_t>> arr =
      std::make_shared<crane::array_storage<uint64_t>>(
          crane::st::extent(UINT64_C(6)), UINT64_C(5));
  return std::span<const uint64_t>{*arr}[UINT64_C(1)];
}

std::pair<std::pair<uint64_t, uint64_t>, List<uint64_t>>
array_simp_list(STRefs) {
  std::shared_ptr<crane::array_storage<uint64_t>> arr =
      crane::st::new_list_array<uint64_t>(List<uint64_t>::cons(
          UINT64_C(5),
          List<uint64_t>::cons(
              UINT64_C(4),
              List<uint64_t>::cons(
                  UINT64_C(3),
                  List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil())))));
  uint64_t elem = std::span<const uint64_t>{*arr}[UINT64_C(0)];
  List<uint64_t> lst =
      crane::st::elems<List<uint64_t>>(std::span<const uint64_t>{*arr});
  return std::make_pair(std::make_pair(elem, lst.length()), lst);
}

List<uint64_t> swap_first_and_last_list(STRefs, const List<uint64_t> &xs) {
  std::shared_ptr<crane::array_storage<uint64_t>> arr =
      crane::st::new_list_array<uint64_t>(xs);
  auto _once1 = xs.length();
  std::swap(
      std::span<uint64_t>{*arr}[UINT64_C(0)],
      std::span<uint64_t>{*arr}[
          (((_once1 - UINT64_C(1)) > _once1 ? 0 : (_once1 - UINT64_C(1))))]);
  return crane::st::elems<List<uint64_t>>(std::span<const uint64_t>{*arr});
}

uint64_t StArrays::array_simp_fixed_init() {
  return ::array_simp_fixed_init(STRefs::BUILD_STREFS);
}

std::pair<std::pair<uint64_t, uint64_t>, List<uint64_t>>
StArrays::array_simp_list() {
  return ::array_simp_list(STRefs::BUILD_STREFS);
}

List<uint64_t> StArrays::swap_first_and_last_list(const List<uint64_t> &x0_) {
  return ::swap_first_and_last_list(STRefs::BUILD_STREFS, x0_);
}

uint64_t StArrays::nth(uint64_t n, const List<uint64_t> &l, uint64_t default0) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a0, _] = std::get<typename List<uint64_t>::Cons>(l.v());
      return a0;
    }
  } else {
    uint64_t m = n - 1;
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[_, a10] = std::get<typename List<uint64_t>::Cons>(l.v());
      return nth(m, *a10, default0);
    }
  }
}
