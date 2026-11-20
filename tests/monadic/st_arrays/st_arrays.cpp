#include "st_arrays.h"

uint64_t StArrays::array_simp_fixed_init() {
  auto _once1 = nat_idx::zero();
  auto _once2 = nat_idx::suc(
      nat_idx::suc(nat_idx::suc(nat_idx::suc(nat_idx::suc(nat_idx::zero())))));
  std::shared_ptr<crane::array_storage<uint64_t>> arr =
      std::make_shared<crane::array_storage<uint64_t>>(
          crane::st::extent(std::move(_once1), std::move(_once2)), UINT64_C(5));
  return std::span<const uint64_t>{*arr}[nat_idx::suc(nat_idx::zero())];
}

std::pair<std::pair<uint64_t, uint64_t>, List<uint64_t>>
StArrays::array_simp_list() {
  auto _once1 = nat_idx::zero();
  auto _once2 = nat_idx::suc(nat_idx::suc(nat_idx::suc(nat_idx::zero())));
  auto _once3 = List<uint64_t>::cons(
      UINT64_C(5),
      List<uint64_t>::cons(
          UINT64_C(4),
          List<uint64_t>::cons(
              UINT64_C(3),
              List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil()))));
  std::shared_ptr<crane::array_storage<uint64_t>> arr =
      crane::st::new_list_array<uint64_t>(
          crane::st::extent(std::move(_once1), std::move(_once2)),
          std::move(_once3));
  uint64_t elem = std::span<const uint64_t>{*arr}[nat_idx::zero()];
  List<uint64_t> lst =
      crane::st::elems<List<uint64_t>>(std::span<const uint64_t>{*arr});
  return std::make_pair(std::make_pair(elem, lst.length()), lst);
}

List<uint64_t> StArrays::swap_first_and_last_list(const List<uint64_t> &xs) {
  auto _once1 = xs.length();
  auto _once2 = nat_idx::zero();
  auto _once3 = nat_idx::fromNat(
      (((_once1 - UINT64_C(1)) > _once1 ? 0 : (_once1 - UINT64_C(1)))));
  std::shared_ptr<crane::array_storage<uint64_t>> arr =
      crane::st::new_list_array<uint64_t>(
          crane::st::extent(std::move(_once2), std::move(_once3)), xs);
  auto _once4 = xs.length();
  STMonad::template swapArray<StArrays::nat_stref>(
      nat_idx::zero(), std::span<uint64_t>{*arr}, nat_idx::zero(),
      nat_idx::fromNat(
          (((_once4 - UINT64_C(1)) > _once4 ? 0 : (_once4 - UINT64_C(1))))));
  return crane::st::elems<List<uint64_t>>(std::span<const uint64_t>{*arr});
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

List<uint64_t> ListDef::seq(uint64_t start, uint64_t len) {
  if (len <= 0) {
    return List<uint64_t>::nil();
  } else {
    uint64_t len0 = len - 1;
    return List<uint64_t>::cons(start, ListDef::seq((start + 1), len0));
  }
}
