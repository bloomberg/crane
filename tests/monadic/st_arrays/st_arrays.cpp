#include "st_arrays.h"

uint64_t array_simp_fixed_init() {
  std::shared_ptr<crane::array_storage<uint64_t>> arr =
      std::make_shared<crane::array_storage<uint64_t>>(6uz, UINT64_C(5));
  return std::span{std::as_const(*arr)}[UINT64_C(1)];
}

std::pair<std::pair<uint64_t, uint64_t>, List<uint64_t>> array_simp_list() {
  std::shared_ptr<crane::array_storage<uint64_t>> arr =
      crane::st::new_list_array<uint64_t>(List<uint64_t>::cons(
          UINT64_C(5),
          List<uint64_t>::cons(
              UINT64_C(4),
              List<uint64_t>::cons(
                  UINT64_C(3),
                  List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil())))));
  uint64_t elem = std::span{std::as_const(*arr)}[UINT64_C(0)];
  List<uint64_t> lst =
      crane::st::elems<List<uint64_t>>(std::span{std::as_const(*arr)});
  return std::make_pair(std::make_pair(elem, lst.length()), lst);
}

List<uint64_t> swap_first_and_last_list(const List<uint64_t> &xs) {
  std::shared_ptr<crane::array_storage<uint64_t>> arr =
      crane::st::new_list_array<uint64_t>(xs);
  auto _once1 = xs.length();
  std::swap(
      std::span{*arr}[UINT64_C(0)],
      std::span{*arr}[_once1 - UINT64_C(1) > _once1 ? 0
                                                    : _once1 - UINT64_C(1)]);
  return crane::st::elems<List<uint64_t>>(std::span{std::as_const(*arr)});
}

uint64_t STArrays::array_simp_fixed_init() { return ::array_simp_fixed_init(); }

std::pair<std::pair<uint64_t, uint64_t>, List<uint64_t>>
STArrays::array_simp_list() {
  return ::array_simp_list();
}

List<uint64_t> STArrays::swap_first_and_last_list(const List<uint64_t> &x0_) {
  return ::swap_first_and_last_list(x0_);
}

uint64_t STArrays::nth(uint64_t n, const List<uint64_t> &l, uint64_t default0) {
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
