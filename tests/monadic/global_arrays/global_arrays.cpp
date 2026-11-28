#include "global_arrays.h"

/// Write i * i into each of the first k cells, last first.
void GlobalArrays::fill_squares(std::span<uint64_t> arr, uint64_t k) {
  if (k <= 0) {
    return;
  } else {
    uint64_t k_ = k - 1;
    arr[k_] = (k_ * k_);
    fill_squares(arr, k_);
    return;
  }
}

/// The squares below n, built in a fresh array.
List<uint64_t> GlobalArrays::squares(uint64_t n) {
  std::shared_ptr<crane::array_storage<uint64_t>> arr =
      std::make_shared<crane::array_storage<uint64_t>>(
          static_cast<std::size_t>(n), UINT64_C(0));
  fill_squares(std::span{*arr}, n);
  return crane::st::elems<List<uint64_t>>(std::span{std::as_const(*arr)});
}

/// The sum of the first k cells of arr, read one at a time.
uint64_t GlobalArrays::sum_cells(std::span<const uint64_t> arr, uint64_t k,
                                 uint64_t acc) {
  if (k <= 0) {
    return acc;
  } else {
    uint64_t k_ = k - 1;
    uint64_t x = arr[k_];
    return sum_cells(arr, k_, acc + x);
  }
}

/// The sum of xs, through an array made from it.
uint64_t GlobalArrays::sum_list(const List<uint64_t> &xs) {
  std::shared_ptr<crane::array_storage<uint64_t>> arr =
      crane::st::new_list_array<uint64_t>(xs);
  return sum_cells(std::span{std::as_const(*arr)}, xs.length(), UINT64_C(0));
}

/// xs with its first and last elements exchanged in an array.
List<uint64_t> GlobalArrays::swap_ends(const List<uint64_t> &xs) {
  std::shared_ptr<crane::array_storage<uint64_t>> arr =
      crane::st::new_list_array<uint64_t>(xs);
  auto _once1 = xs.length();
  std::swap(
      std::span{*arr}[UINT64_C(0)],
      std::span{*arr}[_once1 - UINT64_C(1) > _once1 ? 0
                                                    : _once1 - UINT64_C(1)]);
  return crane::st::elems<List<uint64_t>>(std::span{std::as_const(*arr)});
}

/// A written cell reads back the new value, its neighbours the default.
std::pair<uint64_t, uint64_t> GlobalArrays::write_then_read() {
  std::shared_ptr<crane::array_storage<uint64_t>> arr =
      std::make_shared<crane::array_storage<uint64_t>>(3uz, UINT64_C(7));
  std::span{*arr}[UINT64_C(1)] = UINT64_C(42);
  uint64_t a = std::span{std::as_const(*arr)}[UINT64_C(1)];
  uint64_t b = std::span{std::as_const(*arr)}[UINT64_C(2)];
  return std::make_pair(a, b);
}

/// Arrays and references share the store: a reference made after an array
/// reads back its own value.
uint64_t GlobalArrays::array_then_ref() {
  std::shared_ptr<crane::array_storage<uint64_t>> arr =
      std::make_shared<crane::array_storage<uint64_t>>(2uz, UINT64_C(1));
  std::shared_ptr<uint64_t> r = std::make_shared<uint64_t>(UINT64_C(5));
  std::span{*arr}[UINT64_C(0)] = UINT64_C(9);
  uint64_t x = *r;
  uint64_t y = std::span{std::as_const(*arr)}[UINT64_C(0)];
  return x + y;
}
