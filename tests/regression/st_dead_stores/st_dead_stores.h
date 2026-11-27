#pragma once

#include "crane_fn.h"
#include "obj.h"
#include <concepts>
#include <crane_itree.h>
#include <cstdint>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>
#include <variant>

template <typename T1> struct code_const;
template <typename Err> struct ExceptE;
struct Err;
enum class STRefs;
template <typename I, typename V, typename A>
concept Code = requires {
  { I::code() } -> std::convertible_to<uint64_t>;
};

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

enum class STRefs { BUILD_STREFS };

template <typename T1> struct code_const {
  constexpr static uint64_t code() { return UINT64_C(0); }
};

uint64_t written_only(STRefs _x);
uint64_t read_by_dead_store(STRefs _x);
uint64_t written_in_branch(STRefs _x, bool b);
uint64_t written_in_unused_branch(STRefs _x, bool b);

struct StDeadStores {
  static inline const uint64_t written_only =
      ::written_only(STRefs::BUILD_STREFS);
  static inline const uint64_t read_by_dead_store =
      ::read_by_dead_store(STRefs::BUILD_STREFS);
  static uint64_t written_in_branch(bool b);
  static uint64_t written_in_unused_branch(bool b);
};
