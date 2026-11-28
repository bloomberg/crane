#pragma once

#include "crane_fn.h"
#include "obj.h"
#include <crane_itree.h>
#include <cstdint>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>
#include <variant>

template <typename Err> struct ExceptE;
struct Err;
enum class Refs;

template <typename Err> struct ExceptE {
  // DATA
  Err a0;

  // ACCESSORS
  ExceptE<Err> clone() const { return {a0}; }

  template <typename CraneU> operator ExceptE<CraneU>() const {
    return {[&]() -> CraneU {
      if constexpr (crane_convertible<CraneU, const Err &>) {
        return crane_convert<CraneU>(a0);
      } else {
        throw std::logic_error("unreachable: inactive constructor field at "
                               "this instantiation");
      }
    }()};
  }

  // CREATORS
  static ExceptE<Err> Throw_(Err a0) { return {std::move(a0)}; }
};

struct Err {
  // DATA
  std::string x;

  // ACCESSORS
  Err clone() const { return {x}; }

  // CREATORS
  static Err error(std::string x) { return {std::move(x)}; }
};

enum class Refs { BUILD_REFS };
/// written_only, run in C++.
uint64_t written_only();
/// read_by_dead_store, run in C++.
uint64_t read_by_dead_store();
/// written_in_branch, run in C++.
uint64_t written_in_branch(bool b);
/// written_in_unused_branch, run in C++.
uint64_t written_in_unused_branch(bool b);

struct STDeadStores {
  /// written_only, run in C++.
  static inline const uint64_t written_only = ::written_only();
  /// read_by_dead_store, run in C++.
  static inline const uint64_t read_by_dead_store = ::read_by_dead_store();
  /// written_in_branch, run in C++.
  static uint64_t written_in_branch(bool b);
  /// written_in_unused_branch, run in C++.
  static uint64_t written_in_unused_branch(bool b);
};
