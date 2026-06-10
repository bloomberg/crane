#ifndef INCLUDED_STMONAD
#define INCLUDED_STMONAD

#include <any>
#include <concepts>
#include <memory>
#include <optional>
#include <utility>
#include <variant>

template <typename I, typename T>
concept STRefClass = requires(T a0) {
  { I::mkSTRef(a0) } -> std::convertible_to<std::any>;
  { I::STRefToIx(a0) } -> std::convertible_to<T>;
};

template <typename _tcI0, typename T1 = void, typename T2 = void>
std::pair<uint64_t, uint64_t> newAndReadBoth() {
  uint64_t r1;
  r1 = UINT64_C(5);
  uint64_t r2;
  r2 = UINT64_C(6);
  uint64_t x1 = r1;
  uint64_t x2 = r2;
  return std::make_pair(x1, x2);
}

template <typename _tcI0, typename T1 = void, typename T2 = void>
uint64_t tree_simp() {
  uint64_t v;
  v = UINT64_C(5);
  return std::move(v);
}

template <typename _tcI0, typename T1 = void, typename T2 = void>
uint64_t tree_simp_another() {
  uint64_t v;
  v = UINT64_C(5);
  v = UINT64_C(6);
  uint64_t val = v;
  return val;
}

#endif // INCLUDED_STMONAD
