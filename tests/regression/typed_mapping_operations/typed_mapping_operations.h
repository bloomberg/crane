#pragma once

#include <cstddef>
#include <cstdint>
#include <memory>
#include <typed_mapping_operations_support.h>
#include <utility>
#include <vector>

struct TypedMappingOperations {
  static uint64_t counted(uint64_t n);
  static std::int64_t doubled(std::int64_t c);
  static uint64_t ordered(uint64_t x, uint64_t y);
  static uint64_t skipped(uint64_t x, uint64_t y);
  static uint64_t skipped_pure(uint64_t x, uint64_t y);
  static uint64_t size_of(const ops_support::buffer &x0_);
  static ops_support::buffer push_one(ops_support::buffer b);
  static std::pair<ops_support::buffer, uint64_t>
  push_keep(ops_support::buffer b);
  static ops_support::buffer checked_one(ops_support::buffer b);
  static uint64_t poke_twice(const std::shared_ptr<std::int64_t> &c);
  static uint64_t fresh_cell(uint64_t n);
  static bool boxed(uint64_t n, bool b);

  template <typename T1> static T1 box_third(const std::vector<T1> &b) {
    return T1(b[UINT64_C(2)]);
  }

  template <typename T1>
  static std::vector<T1> box_push_one(std::vector<T1> x0_, const T1 &x1_) {
    return [&]() -> std::vector<T1> {
      std::vector<T1> _r;
      _r = std::move(x0_);
      _r.push_back(T1(x1_));
      return _r;
    }();
  }
};
