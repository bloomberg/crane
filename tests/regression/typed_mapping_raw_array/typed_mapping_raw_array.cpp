#include "typed_mapping_raw_array.h"

/// Reads: the pointer by value.
uint64_t TypedMappingRawArray::get_cell(std::vector<uint64_t> *x0_,
                                        uint64_t x1_) {
  return (*x0_)[x1_];
}

/// Writes through the pointer, two calls deep: by value at each level.
std::vector<uint64_t> *
TypedMappingRawArray::set_cell(std::vector<uint64_t> *x0_, uint64_t x1_,
                               uint64_t x2_) {
  return raw_support::set(x0_, x1_, x2_);
}

std::vector<uint64_t> *
TypedMappingRawArray::set_middle(std::vector<uint64_t> *a, uint64_t i) {
  return set_cell(a, i, (i + 1));
}

uint64_t TypedMappingRawArray::set_outer(std::vector<uint64_t> *a) {
  return get_cell(set_middle(a, UINT64_C(1)), UINT64_C(1));
}

/// Reseats the pointer: std::vector<A>*&.
uint64_t TypedMappingRawArray::reseat_cell(std::vector<uint64_t> *&a,
                                           uint64_t n) {
  return (*raw_support::reseat(a, n))[UINT64_C(0)];
}

/// A bool array, read and written.
bool TypedMappingRawArray::flip_cell(std::vector<bool> *a, uint64_t i) {
  return (*raw_support::set(a, i, !((*a)[i])))[i];
}

std::pair<uint64_t, uint64_t> TypedMappingRawArray::run_nat(uint64_t n) {
  std::vector<uint64_t> *a = raw_support::make<uint64_t>(n, UINT64_C(0));
  uint64_t w = set_outer(a);
  return std::make_pair(w, reseat_cell(a, UINT64_C(5)));
}

bool TypedMappingRawArray::run_bool(uint64_t n) {
  return flip_cell(raw_support::make<bool>(n, false), UINT64_C(0));
}
