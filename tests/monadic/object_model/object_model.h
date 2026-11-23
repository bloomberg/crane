#pragma once

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <concepts>
#include <crane_itree.h>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>
#include <variant>

struct nat_ix_stref;
template <typename Err> struct ExceptE;
struct Err;
struct STRefNat;
template <typename S> struct Point;
template <typename S> struct Account;
template <typename S> struct BankAccountCollection;
template <typename I, typename T>
concept STRefClass = requires {
  { I::mkSTRef(std::declval<T>()) } -> std::convertible_to<crane::obj>;
  { I::STRefToIx(std::declval<crane::obj>()) } -> std::convertible_to<T>;
};

struct Z {};

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

template <typename S> struct Point {
  crane::fn<int64_t(std::monostate)> getX;
  crane::fn<void(int64_t)> moveD;
  crane::fn<int64_t(std::monostate)> offsetX;

  // ACCESSORS
  template <typename CraneU> operator Point<CraneU>() const {
    return {crane_convert<crane::fn<int64_t(std::monostate)>>(getX), moveD,
            crane_convert<crane::fn<int64_t(std::monostate)>>(offsetX)};
  }
};

template <typename S> struct Account {
  crane::fn<int64_t(std::monostate)> getBalance;
  crane::fn<int64_t(uint64_t)> deposit;
  crane::fn<std::optional<int64_t>(int64_t)> withdraw;

  // ACCESSORS
  template <typename CraneU> operator Account<CraneU>() const {
    return {crane_convert<crane::fn<int64_t(std::monostate)>>(getBalance),
            crane_convert<crane::fn<int64_t(uint64_t)>>(deposit),
            crane_convert<crane::fn<std::optional<int64_t>(int64_t)>>(withdraw)};
  }
};

template <typename S> struct BankAccountCollection {
  Account<S> checking;
  Account<S> saving;

  // ACCESSORS
  template <typename CraneU> operator BankAccountCollection<CraneU>() const {
    return {crane_convert<Account<CraneU>>(checking),
            crane_convert<Account<CraneU>>(saving)};
  }
};

std::pair<std::pair<int64_t, int64_t>, int64_t> testtoST1_ext();
std::pair<std::pair<std::pair<int64_t, int64_t>, int64_t>, int64_t>
testtoST2_ext();
std::pair<std::pair<std::pair<int64_t, int64_t>, bool>, int64_t>
acc_test1_ext();
std::pair<std::pair<std::pair<int64_t, bool>, int64_t>, int64_t>
acc_test2_ext();
std::pair<std::pair<std::pair<int64_t, bool>, int64_t>, int64_t>
bankacc_test1_ext();
