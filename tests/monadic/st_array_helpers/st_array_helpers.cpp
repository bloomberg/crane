#include "st_array_helpers.h"

/// Only reads a cell.
uint64_t STArrayHelpers::peek(std::span<const uint64_t> arr, uint64_t i) {
  return arr[i];
}

/// Reads one cell and writes it back.
void STArrayHelpers::bump(std::span<uint64_t> arr, uint64_t i) {
  uint64_t v = arr[i];
  arr[i] = (v + 1);
}

/// A write two calls deep.
void STArrayHelpers::middle(std::span<uint64_t> arr, uint64_t i) {
  arr[i] = UINT64_C(42);
}

/// Writes only through middle, so still takes the writable view.
void STArrayHelpers::outer(std::span<uint64_t> arr) {
  middle(arr, UINT64_C(0));
  middle(arr, UINT64_C(2));
}

/// Swaps the first and last cells: ST.swap_array is called, not unfolded.
void STArrayHelpers::swap_ends(std::span<uint64_t> arr, uint64_t last) {
  std::swap(arr[UINT64_C(0)], arr[last]);
}

/// Returns one of its arrays: it keeps them, so takes them by value.
std::shared_ptr<crane::array_storage<uint64_t>>
STArrayHelpers::pick(bool b,
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
std::shared_ptr<crane::array_storage<uint64_t>> STArrayHelpers::write_then_pick(
    std::shared_ptr<crane::array_storage<uint64_t>> arr1,
    std::shared_ptr<crane::array_storage<uint64_t>> arr2) {
  std::span{*arr1}[UINT64_C(1)] = UINT64_C(7);
  return pick(true, std::move(arr1), std::move(arr2));
}

/// Returns its array through the monad's Ret, a legacy mapping whose
/// argument Crane takes to be only read: borrowed, and copied where it is
/// returned.
std::shared_ptr<crane::array_storage<uint64_t>> STArrayHelpers::keep(
    const std::shared_ptr<crane::array_storage<uint64_t>> &arr) {
  std::span{*arr}[UINT64_C(1)] = UINT64_C(7);
  return arr;
}

/// Zeroes n cells from i: a tail-recursive write loop keeps the
/// writable view.
void STArrayHelpers::zero_from(std::span<uint64_t> arr, uint64_t i,
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

/// Sums n cells from i: a non-tail-recursive read keeps the read view.
uint64_t STArrayHelpers::sum_from(std::span<const uint64_t> arr, uint64_t i,
                                  uint64_t n) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t m = n - 1;
    uint64_t x = arr[i];
    uint64_t r = sum_from(arr, (i + 1), m);
    return x + r;
  }
}

/// Writes a cell, then refills the array canonically.
void STArrayHelpers::write_and_refill(
    const std::shared_ptr<crane::array_storage<uint64_t>> &arr, uint64_t v) {
  std::span{*arr}[UINT64_C(0)] = v;
  std::ranges::fill(*arr, v);
}

/// Replaces its array, then writes the new one.
void STArrayHelpers::regrow_then_write(
    std::shared_ptr<crane::array_storage<uint64_t>> &arr, uint64_t n) {
  arr = std::make_shared<crane::array_storage<uint64_t>>(n, 0);
  std::span{*arr}[UINT64_C(0)] = n;
}

/// A bool array: reads one cell and writes its negation back.
void STArrayHelpers::flip(std::span<bool> arr, uint64_t i) {
  bool b = arr[i];
  arr[i] = !(b);
}

/// Drives bump, outer and swap_ends over an array made from xs.
List<uint64_t> STArrayHelpers::helpers_list(const List<uint64_t> &xs) {
  std::shared_ptr<crane::array_storage<uint64_t>> arr =
      crane::st::new_list_array<uint64_t>(xs);
  bump(std::span{*arr}, UINT64_C(1));
  outer(std::span{*arr});
  auto _once1 = xs.length();
  swap_ends(std::span{*arr},
            (_once1 - UINT64_C(1) > _once1 ? 0 : _once1 - UINT64_C(1)));
  return crane::st::elems<List<uint64_t>>(std::span{std::as_const(*arr)});
}

/// Writes through the array keep and write_then_pick return, then reads the
/// originals.
std::pair<List<uint64_t>, List<uint64_t>>
STArrayHelpers::keep_list(uint64_t n) {
  std::shared_ptr<crane::array_storage<uint64_t>> arr =
      std::make_shared<crane::array_storage<uint64_t>>(
          static_cast<std::size_t>(n), UINT64_C(3));
  std::shared_ptr<crane::array_storage<uint64_t>> other =
      std::make_shared<crane::array_storage<uint64_t>>(2uz, UINT64_C(4));
  std::shared_ptr<crane::array_storage<uint64_t>> picked =
      write_then_pick(keep(arr), other);
  std::span{*picked}[UINT64_C(0)] = UINT64_C(8);
  List<uint64_t> elems =
      crane::st::elems<List<uint64_t>>(std::span{std::as_const(*arr)});
  List<uint64_t> others =
      crane::st::elems<List<uint64_t>>(std::span{std::as_const(*other)});
  return std::make_pair(std::move(elems), std::move(others));
}

/// Drives write_and_refill, then reads the array back.
std::pair<uint64_t, List<uint64_t>> STArrayHelpers::refill_list(uint64_t n) {
  std::shared_ptr<crane::array_storage<uint64_t>> arr =
      std::make_shared<crane::array_storage<uint64_t>>(3uz, UINT64_C(1));
  write_and_refill(arr, n);
  uint64_t first = peek(std::span{std::as_const(*arr)}, UINT64_C(0));
  List<uint64_t> elems =
      crane::st::elems<List<uint64_t>>(std::span{std::as_const(*arr)});
  return std::make_pair(first, std::move(elems));
}

/// Drives the recursive helpers zero_from and sum_from.
std::pair<uint64_t, List<uint64_t>> STArrayHelpers::loops_list(uint64_t n) {
  std::shared_ptr<crane::array_storage<uint64_t>> arr =
      std::make_shared<crane::array_storage<uint64_t>>(
          static_cast<std::size_t>(n), UINT64_C(2));
  zero_from(std::span{*arr}, UINT64_C(1), UINT64_C(2));
  uint64_t s = sum_from(std::span{std::as_const(*arr)}, UINT64_C(0), n);
  List<uint64_t> elems =
      crane::st::elems<List<uint64_t>>(std::span{std::as_const(*arr)});
  return std::make_pair(s, std::move(elems));
}

/// Checks that the caller sees the array regrow_then_write reseated.
List<uint64_t> STArrayHelpers::regrow_list(uint64_t n) {
  std::shared_ptr<crane::array_storage<uint64_t>> arr =
      std::make_shared<crane::array_storage<uint64_t>>(2uz, UINT64_C(5));
  regrow_then_write(arr, n);
  return crane::st::elems<List<uint64_t>>(std::span{std::as_const(*arr)});
}

/// Flips cells 0 and 2 of a bool array made from bs.
List<bool> STArrayHelpers::flip_list(const List<bool> &bs) {
  std::shared_ptr<crane::array_storage<bool>> arr =
      crane::st::new_list_array<bool>(bs);
  flip(std::span{*arr}, UINT64_C(0));
  flip(std::span{*arr}, UINT64_C(2));
  return crane::st::elems<List<bool>>(std::span{std::as_const(*arr)});
}

/// Flips cell 1 of a bool array filled with false.
std::pair<bool, List<bool>> STArrayHelpers::bools_filled(uint64_t n) {
  std::shared_ptr<crane::array_storage<bool>> arr =
      std::make_shared<crane::array_storage<bool>>(static_cast<std::size_t>(n),
                                                   false);
  flip(std::span{*arr}, UINT64_C(1));
  bool b = std::span{std::as_const(*arr)}[UINT64_C(1)];
  List<bool> elems =
      crane::st::elems<List<bool>>(std::span{std::as_const(*arr)});
  return std::make_pair(b, std::move(elems));
}
