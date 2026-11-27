#pragma once

#include "crane_fn.h"
#include "obj.h"
#include <concepts>
#include <crane_itree.h>
#include <cstdint>
#include <memory>
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

std::pair<uint64_t, uint64_t> new_and_read_both_nat();
uint64_t tree_simp_nat();
uint64_t tree_simp_another_nat();
void swap(uint64_t *v, uint64_t *w);
std::pair<uint64_t, uint64_t> swapped();
std::pair<bool, bool> new_and_read_both_bool();
bool tree_simp_bool();

struct StRefs {
  static inline const std::pair<uint64_t, uint64_t> new_and_read_both_nat =
      ::new_and_read_both_nat();
  static inline const uint64_t tree_simp_nat = ::tree_simp_nat();
  static inline const uint64_t tree_simp_another_nat =
      ::tree_simp_another_nat();
  static inline const std::pair<uint64_t, uint64_t> swapped = ::swapped();
  static inline const std::pair<bool, bool> new_and_read_both_bool =
      ::new_and_read_both_bool();
  static inline const bool tree_simp_bool = ::tree_simp_bool();
};
