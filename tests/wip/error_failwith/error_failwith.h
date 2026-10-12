#ifndef INCLUDED_ERROR_FAILWITH
#define INCLUDED_ERROR_FAILWITH

#include "crane_fn.h"
#include "obj.h"
#include <crane_itree.h>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <system_error>
#include <utility>

struct Empty_set;
template <typename Err> struct ExceptE;
struct Err;

struct Nat {};

struct Empty_set {
  Empty_set() = delete;
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
        throw std::logic_error(
            "unreachable: inactive constructor field at this instantiation");
      }
    }()};
  }

  // CREATORS
  static ExceptE<Err> Throw_(Err a0) { return {std::move(a0)}; }
};

struct Exception {
  template <typename T1, typename T2 = void, typename T3>
  static T3 throw0(const T1 &e);
};

struct Err {
  // DATA
  std::string x;

  // ACCESSORS
  Err clone() const { return {x}; }

  // CREATORS
  static Err error(std::string x) { return {std::move(x)}; }
};

struct Error {
  template <typename T1 = void, typename T2> static T2 failwith(std::string s);
};

struct ErrorFailwith {
  static uint64_t safe_div(uint64_t a, uint64_t b);
  static uint64_t result();
};

template <typename T1, typename T2, typename T3>
T3 Exception::throw0(const T1 &e) {
  return <T2, T3, T3>(ExceptE<T1>::Throw_(e), [](crane::obj) -> T3 {
    throw std::logic_error("absurd case");
  });
}

template <typename T1, typename T2> T2 Error::failwith(std::string s) {
  return Exception::template throw0<Err, crane::obj, T2>(
      Err::error(std::move(s)));
}

#endif // INCLUDED_ERROR_FAILWITH
