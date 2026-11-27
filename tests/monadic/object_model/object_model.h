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

template <typename T1> struct code_const;
template <typename Err> struct ExceptE;
struct Err;
struct Point;
struct Account;
struct BankAccountCollection;
template <typename I, typename V, typename A>
concept Code = requires {
  { I::code() } -> std::convertible_to<uint64_t>;
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

template <typename T1> struct code_const {
  constexpr static uint64_t code() { return UINT64_C(0); }
};

struct Point {
  crane::fn<int64_t(std::monostate)> getX;
  crane::fn<void(int64_t)> moveD;
  crane::fn<int64_t(std::monostate)> offsetX;
};

struct Account {
  crane::fn<int64_t(std::monostate)> getBalance;
  crane::fn<int64_t(uint64_t)> deposit;
  crane::fn<std::optional<int64_t>(int64_t)> withdraw;
};

struct BankAccountCollection {
  Account checking;
  Account saving;
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
