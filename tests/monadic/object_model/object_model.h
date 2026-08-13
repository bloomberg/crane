#ifndef INCLUDED_OBJECT_MODEL
#define INCLUDED_OBJECT_MODEL

#include <any>
#include <concepts>
#include <cstdint>
#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>

template <typename Err> struct ExceptE {
  // DATA
  Err a0;

  // ACCESSORS
  ExceptE<Err> clone() const { return {a0}; }

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

template <typename I, typename T>
concept STRefClass = requires {
  { I::mkSTRef(std::declval<T>()) } -> std::convertible_to<std::any>;
  { I::STRefToIx(std::declval<std::any>()) } -> std::convertible_to<T>;
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

template <typename S> struct Point {
  std::function<int64_t(std::monostate)> getX;
  std::function<void(int64_t)> moveD;
  std::function<int64_t(std::monostate)> offsetX;
};

template <typename S> struct Account {
  std::function<int64_t(std::monostate)> getBalance;
  std::function<int64_t(uint64_t)> deposit;
  std::function<std::optional<int64_t>(int64_t)> withdraw;
};

std::pair<std::pair<int64_t, int64_t>, int64_t> testtoST1_ext();
std::pair<std::pair<std::pair<int64_t, int64_t>, int64_t>, int64_t>
testtoST2_ext();
std::pair<std::pair<std::pair<int64_t, int64_t>, bool>, int64_t>
acc_test1_ext();
std::pair<std::pair<std::pair<int64_t, bool>, int64_t>, int64_t>
acc_test2_ext();

#endif // INCLUDED_OBJECT_MODEL
