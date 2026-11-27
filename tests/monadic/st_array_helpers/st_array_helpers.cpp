#include "st_array_helpers.h"

/// Only reads a cell.
uint64_t StArrayHelpers::peek(std::span<const uint64_t> arr, uint64_t i) {
  return arr[i];
}

/// Reads one cell and writes it back.
void StArrayHelpers::bump(std::span<uint64_t> arr, uint64_t i) {
  uint64_t v = arr[i];
  arr[i] = (v + 1);
}

/// A write two calls deep.
void StArrayHelpers::middle(std::span<uint64_t> arr, uint64_t i) {
  arr[i] = UINT64_C(42);
}

void StArrayHelpers::outer(std::span<uint64_t> arr) {
  middle(arr, UINT64_C(0));
  middle(arr, UINT64_C(2));
}

/// Swaps the first and last cells: swapArray is called, not unfolded.
void StArrayHelpers::swap_ends(std::span<uint64_t> arr, uint64_t last) {
  std::swap(arr[UINT64_C(0)], arr[last]);
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
  std::span{*arr1}[UINT64_C(1)] = UINT64_C(7);
  return pick(true, std::move(arr1), std::move(arr2));
}

/// Returns its array through the monad's Ret, a legacy mapping whose
/// argument Crane takes to be only read: borrowed, and copied where it is
/// returned.
std::shared_ptr<crane::array_storage<uint64_t>> StArrayHelpers::keep(
    const std::shared_ptr<crane::array_storage<uint64_t>> &arr) {
  std::span{*arr}[UINT64_C(1)] = UINT64_C(7);
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
  std::span{*arr}[UINT64_C(0)] = v;
  std::ranges::fill(*arr, v);
}

/// Replaces its array, then writes the new one.
void StArrayHelpers::regrow_then_write(
    std::shared_ptr<crane::array_storage<uint64_t>> &arr, uint64_t n) {
  arr = std::make_shared<crane::array_storage<uint64_t>>(n, 0);
  std::span{*arr}[UINT64_C(0)] = n;
}

/// A bool array: reads one cell and writes its negation back.
void StArrayHelpers::flip(std::span<bool> arr, uint64_t i) {
  bool b = arr[i];
  arr[i] = !(b);
}

List<uint64_t> StArrayHelpers::helpers_list(const List<uint64_t> &xs) {
  std::shared_ptr<crane::array_storage<uint64_t>> arr =
      crane::st::new_list_array<uint64_t>(xs);
  bump(std::span{*arr}, UINT64_C(1));
  outer(std::span{*arr});
  auto _once1 = xs.length();
  swap_ends(std::span{*arr},
            (((_once1 - UINT64_C(1)) > _once1 ? 0 : (_once1 - UINT64_C(1)))));
  return crane::st::elems<List<uint64_t>>(std::span{std::as_const(*arr)});
}

std::pair<List<uint64_t>, List<uint64_t>>
StArrayHelpers::keep_list(uint64_t n) {
  std::shared_ptr<crane::array_storage<uint64_t>> arr =
      std::make_shared<crane::array_storage<uint64_t>>(crane::st::extent(n),
                                                       UINT64_C(3));
  std::shared_ptr<crane::array_storage<uint64_t>> other =
      std::make_shared<crane::array_storage<uint64_t>>(
          crane::st::extent(UINT64_C(2)), UINT64_C(4));
  std::shared_ptr<crane::array_storage<uint64_t>> picked =
      write_then_pick(keep(arr), other);
  std::span{*picked}[UINT64_C(0)] = UINT64_C(8);
  List<uint64_t> elems =
      crane::st::elems<List<uint64_t>>(std::span{std::as_const(*arr)});
  return std::make_pair(std::move(elems), crane::st::elems<List<uint64_t>>(
                                              std::span{std::as_const(*other)}));
}

std::pair<uint64_t, List<uint64_t>> StArrayHelpers::refill_list(uint64_t n) {
  std::shared_ptr<crane::array_storage<uint64_t>> arr =
      std::make_shared<crane::array_storage<uint64_t>>(
          crane::st::extent(UINT64_C(3)), UINT64_C(1));
  write_and_refill(arr, n);
  uint64_t first = peek(std::span{std::as_const(*arr)}, UINT64_C(0));
  return std::make_pair(
      first, crane::st::elems<List<uint64_t>>(std::span{std::as_const(*arr)}));
}

std::pair<uint64_t, List<uint64_t>> StArrayHelpers::loops_list(uint64_t n) {
  std::shared_ptr<crane::array_storage<uint64_t>> arr =
      std::make_shared<crane::array_storage<uint64_t>>(crane::st::extent(n),
                                                       UINT64_C(2));
  zero_from(std::span{*arr}, UINT64_C(1), UINT64_C(2));
  uint64_t s = sum_from(std::span{std::as_const(*arr)}, UINT64_C(0), n);
  return std::make_pair(
      s, crane::st::elems<List<uint64_t>>(std::span{std::as_const(*arr)}));
}

List<uint64_t> StArrayHelpers::regrow_list(uint64_t n) {
  std::shared_ptr<crane::array_storage<uint64_t>> arr =
      std::make_shared<crane::array_storage<uint64_t>>(
          crane::st::extent(UINT64_C(2)), UINT64_C(5));
  regrow_then_write(arr, n);
  return crane::st::elems<List<uint64_t>>(std::span{std::as_const(*arr)});
}

List<bool> StArrayHelpers::flip_list(const List<bool> &bs) {
  std::shared_ptr<crane::array_storage<bool>> arr =
      crane::st::new_list_array<bool>(bs);
  flip(std::span{*arr}, UINT64_C(0));
  flip(std::span{*arr}, UINT64_C(2));
  return crane::st::elems<List<bool>>(std::span{std::as_const(*arr)});
}

std::pair<bool, List<bool>> StArrayHelpers::bools_filled(uint64_t n) {
  std::shared_ptr<crane::array_storage<bool>> arr =
      std::make_shared<crane::array_storage<bool>>(crane::st::extent(n), false);
  flip(std::span{*arr}, UINT64_C(1));
  bool b = std::span{std::as_const(*arr)}[UINT64_C(1)];
  return std::make_pair(
      b, crane::st::elems<List<bool>>(std::span{std::as_const(*arr)}));
}
