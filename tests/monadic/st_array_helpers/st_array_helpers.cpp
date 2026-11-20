#include "st_array_helpers.h"

/// Only reads a cell.
uint64_t StArrayHelpers::peek(std::span<const uint64_t> arr, uint64_t i) {
  return arr[i];
}

/// Reads one cell and writes it back.
void StArrayHelpers::bump(std::span<uint64_t> arr, uint64_t i) {
  uint64_t v = std::span<const uint64_t>{arr}[i];
  arr[i] = (v + 1);
  return;
}

/// A write two calls deep.
void StArrayHelpers::middle(std::span<uint64_t> arr, uint64_t i) {
  arr[i] = UINT64_C(42);
  return;
}

void StArrayHelpers::outer(std::span<uint64_t> arr) {
  middle(arr, UINT64_C(0));
  middle(arr, UINT64_C(2));
  return;
}

/// Swaps the first and last cells: swapArray is called, not unfolded.
void StArrayHelpers::swap_ends(std::span<uint64_t> arr, uint64_t last) {
  STMonad::template swapArray<nat_ix_stref>(UINT64_C(0), arr, UINT64_C(0),
                                            last);
  return;
}

/// Returns one of its arrays: it keeps them, so takes them by value.
std::shared_ptr<crane::array_storage<uint64_t>>
StArrayHelpers::pick(bool b,
                     std::shared_ptr<crane::array_storage<uint64_t>> arr1,
                     std::shared_ptr<crane::array_storage<uint64_t>> arr2) {
  if (b) {
    return arr1;
  } else {
    return arr2;
  }
}

/// Writes its first array and passes both to pick, which keeps them:
/// by value too.
std::shared_ptr<crane::array_storage<uint64_t>> StArrayHelpers::write_then_pick(
    std::shared_ptr<crane::array_storage<uint64_t>> arr1,
    std::shared_ptr<crane::array_storage<uint64_t>> arr2) {
  std::span<uint64_t>{*arr1}[UINT64_C(1)] = UINT64_C(7);
  return pick(true, std::move(arr1), std::move(arr2));
}

/// Returns its array through the monad's Ret, a legacy mapping whose
/// argument Crane takes to be only read: borrowed, and copied where it is
/// returned.
std::shared_ptr<crane::array_storage<uint64_t>> StArrayHelpers::keep(
    const std::shared_ptr<crane::array_storage<uint64_t>> &arr) {
  std::span<uint64_t>{*arr}[UINT64_C(1)] = UINT64_C(7);
  return arr;
}

/// Recursive helpers keep the view: a tail-recursive write loop takes the
/// writable view, a non-tail-recursive read the read view.
void StArrayHelpers::zero_from(std::span<uint64_t> arr, uint64_t i,
                               uint64_t n) {
  if (n <= 0) {
    return;
  } else {
    uint64_t m = n - 1;
    arr[i] = UINT64_C(0);
    zero_from(arr, (i + 1), m);
    return;
  }
}

uint64_t StArrayHelpers::sum_from(std::span<const uint64_t> arr, uint64_t i,
                                  uint64_t n) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t m = n - 1;
    uint64_t x = arr[i];
    uint64_t r = sum_from(arr, (i + 1), m);
    return (x + r);
  }
}

/// Writes a cell, then refills the array canonically.
void StArrayHelpers::write_and_refill(
    const std::shared_ptr<crane::array_storage<uint64_t>> &arr, uint64_t v) {
  std::span<uint64_t>{*arr}[UINT64_C(0)] = v;
  std::ranges::fill(*arr, v);
  return;
}

/// Replaces its array, then writes the new one.
void StArrayHelpers::regrow_then_write(
    std::shared_ptr<crane::array_storage<uint64_t>> &arr, uint64_t n) {
  arr = std::make_shared<crane::array_storage<uint64_t>>(n, 0);
  std::span<uint64_t>{*arr}[UINT64_C(0)] = n;
  return;
}

/// A bool array: reads one cell and writes its negation back.
void StArrayHelpers::flip(std::span<bool> arr, uint64_t i) {
  bool b = std::span<const bool>{arr}[i];
  arr[i] = !(b);
  return;
}

List<uint64_t> StArrayHelpers::helpers_list(const List<uint64_t> &xs) {
  auto _once1 = xs.length();
  std::shared_ptr<crane::array_storage<uint64_t>> arr =
      crane::st::new_list_array<uint64_t>(crane::st::extent(
          UINT64_C(0),
          (((_once1 - UINT64_C(1)) > _once1 ? 0 : (_once1 - UINT64_C(1))))),
                                          xs);
  bump(std::span<uint64_t>{*arr}, UINT64_C(1));
  outer(std::span<uint64_t>{*arr});
  auto _once2 = xs.length();
  swap_ends(std::span<uint64_t>{*arr},
            (((_once2 - UINT64_C(1)) > _once2 ? 0 : (_once2 - UINT64_C(1)))));
  return crane::st::elems<List<uint64_t>>(std::span<const uint64_t>{*arr});
}

std::pair<List<uint64_t>, List<uint64_t>>
StArrayHelpers::keep_list(uint64_t n) {
  std::shared_ptr<crane::array_storage<uint64_t>> arr =
      std::make_shared<crane::array_storage<uint64_t>>(crane::st::extent(
          UINT64_C(0), (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1))))),
                                                       UINT64_C(3));
  std::shared_ptr<crane::array_storage<uint64_t>> other =
      std::make_shared<crane::array_storage<uint64_t>>(
          crane::st::extent(UINT64_C(0), UINT64_C(1)), UINT64_C(4));
  std::shared_ptr<crane::array_storage<uint64_t>> kept = keep(arr);
  std::shared_ptr<crane::array_storage<uint64_t>> picked =
      write_then_pick(std::move(kept), other);
  std::span<uint64_t>{*picked}[UINT64_C(0)] = UINT64_C(8);
  List<uint64_t> elems =
      crane::st::elems<List<uint64_t>>(std::span<const uint64_t>{*arr});
  List<uint64_t> others =
      crane::st::elems<List<uint64_t>>(std::span<const uint64_t>{*other});
  return std::make_pair(std::move(elems), std::move(others));
}

std::pair<uint64_t, List<uint64_t>> StArrayHelpers::refill_list(uint64_t n) {
  std::shared_ptr<crane::array_storage<uint64_t>> arr =
      std::make_shared<crane::array_storage<uint64_t>>(
          crane::st::extent(UINT64_C(0), UINT64_C(2)), UINT64_C(1));
  write_and_refill(arr, n);
  uint64_t first = peek(std::span<const uint64_t>{*arr}, UINT64_C(0));
  List<uint64_t> elems =
      crane::st::elems<List<uint64_t>>(std::span<const uint64_t>{*arr});
  return std::make_pair(first, std::move(elems));
}

std::pair<uint64_t, List<uint64_t>> StArrayHelpers::loops_list(uint64_t n) {
  std::shared_ptr<crane::array_storage<uint64_t>> arr =
      std::make_shared<crane::array_storage<uint64_t>>(crane::st::extent(
          UINT64_C(0), (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1))))),
                                                       UINT64_C(2));
  zero_from(std::span<uint64_t>{*arr}, UINT64_C(1), UINT64_C(2));
  uint64_t s = sum_from(std::span<const uint64_t>{*arr}, UINT64_C(0), n);
  List<uint64_t> elems =
      crane::st::elems<List<uint64_t>>(std::span<const uint64_t>{*arr});
  return std::make_pair(s, std::move(elems));
}

List<uint64_t> StArrayHelpers::regrow_list(uint64_t n) {
  std::shared_ptr<crane::array_storage<uint64_t>> arr =
      std::make_shared<crane::array_storage<uint64_t>>(
          crane::st::extent(UINT64_C(0), UINT64_C(1)), UINT64_C(5));
  regrow_then_write(arr, n);
  return crane::st::elems<List<uint64_t>>(std::span<const uint64_t>{*arr});
}

List<bool> StArrayHelpers::flip_list(const List<bool> &bs) {
  auto _once1 = bs.length();
  std::shared_ptr<crane::array_storage<bool>> arr =
      crane::st::new_list_array<bool>(crane::st::extent(
          UINT64_C(0),
          (((_once1 - UINT64_C(1)) > _once1 ? 0 : (_once1 - UINT64_C(1))))),
                                      bs);
  flip(std::span<bool>{*arr}, UINT64_C(0));
  flip(std::span<bool>{*arr}, UINT64_C(2));
  return crane::st::elems<List<bool>>(std::span<const bool>{*arr});
}

std::pair<bool, List<bool>> StArrayHelpers::bools_filled(uint64_t n) {
  auto _once1 = (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1))));
  auto _once2 = false;
  std::shared_ptr<crane::array_storage<bool>> arr =
      std::make_shared<crane::array_storage<bool>>(
          crane::st::extent(UINT64_C(0), std::move(_once1)), std::move(_once2));
  flip(std::span<bool>{*arr}, UINT64_C(1));
  bool b = std::span<const bool>{*arr}[UINT64_C(1)];
  List<bool> elems = crane::st::elems<List<bool>>(std::span<const bool>{*arr});
  return std::make_pair(b, std::move(elems));
}
