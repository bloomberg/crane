#pragma once

#include <cstdint>
#include <typed_mapping_raw_array_support.h>
#include <utility>
#include <vector>

struct TypedMappingRawArray {
  /// Reads: the pointer by value.
  static uint64_t get_cell(std::vector<uint64_t> *x0_, uint64_t x1_);
  /// Writes through the pointer, two calls deep: by value at each level.
  static std::vector<uint64_t> *set_cell(std::vector<uint64_t> *x0_,
                                         uint64_t x1_, uint64_t x2_);
  static std::vector<uint64_t> *set_middle(std::vector<uint64_t> *a,
                                           uint64_t i);
  static uint64_t set_outer(std::vector<uint64_t> *a);
  /// Reseats the pointer: std::vector<A>*&.
  static uint64_t reseat_cell(std::vector<uint64_t> *&a, uint64_t n);
  /// A bool array, read and written.
  static bool flip_cell(std::vector<bool> *a, uint64_t i);
  static std::pair<uint64_t, uint64_t> run_nat(uint64_t n);
  static bool run_bool(uint64_t n);
};
