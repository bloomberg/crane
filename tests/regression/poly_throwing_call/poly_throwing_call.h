#pragma once

#include "crane_fn.h"
#include "obj.h"
#include <cstdint>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>

template <typename Err> struct ExceptE;
struct Err;

struct Nat {};

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

struct PolyThrowingCall {
  template <typename T1> static T1 out_of_fuel() {
    return [&]() -> T1 {
      throw std::runtime_error(std::string("out of fuel"));
    }();
  }

  static uint64_t count(uint64_t fuel, uint64_t n);
  static bool flag(uint64_t fuel);
  static uint64_t ok();
  static bool flag_ok();
};
