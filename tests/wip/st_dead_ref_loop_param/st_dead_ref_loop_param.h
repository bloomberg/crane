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

struct nat_ix_stref;
template <typename Err> struct ExceptE;
struct Err;
struct STRefNat;
template <typename I, typename T>
concept STRefClass = requires {
  { I::mkSTRef(std::declval<T>()) } -> std::convertible_to<crane::obj>;
  { I::STRefToIx(std::declval<crane::obj>()) } -> std::convertible_to<T>;
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

struct STRefNat {
  // DATA
  uint64_t s;

  // ACCESSORS
  STRefNat clone() const { return {s}; }

  // CREATORS
  static STRefNat mkstref(uint64_t s) { return {s}; }

  uint64_t STRefToIxNat() const {
    const auto &[s] = *this;
    return s;
  }
};

struct nat_ix_stref {
  static crane::obj mkSTRef(uint64_t x) { return STRefNat::mkstref(x); }

  static uint64_t STRefToIx(crane::obj _p_a0) {
    STRefNat a0 = crane::any_cast<STRefNat>(_p_a0);
    return a0.STRefToIxNat();
  }
};

static_assert(STRefClass<nat_ix_stref, uint64_t>);

struct StDeadRefLoopParam {
  template <typename T1 = void> static uint64_t st_1() {
    std::shared_ptr<std::pair<uint64_t, uint64_t>> r0 =
        std::make_shared<std::pair<uint64_t, uint64_t>>(
            std::make_pair(UINT64_C(2), UINT64_C(1)));
    auto h =
        [](uint64_t k, uint64_t acc,
           const std::shared_ptr<std::pair<uint64_t, uint64_t>> &)
             -> uint64_t {
          // Loop replaces the tail recursion: each recursive call updates the
          // loop variables.
          uint64_t _loop_acc = acc;
          uint64_t _loop_k = k;
          while (true) {
            if (_loop_k <= 0) {
              return UINT64_C(5);
            } else {
              uint64_t k_ = _loop_k - 1;
              _loop_acc = UINT64_C(7);
              _loop_k = k_;
            }
          }
        };
    uint64_t y = h(UINT64_C(4), UINT64_C(1), r0);
    std::pair<uint64_t, uint64_t> x_ = *r0.get();
    const auto &[a, b] = x_;
    return (((y * UINT64_C(10)) + a) + b);
  }

  static inline const uint64_t result = st_1();
};
