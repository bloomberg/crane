#ifndef INCLUDED_DEQUE_ANY_CAST_ELEMENT
#define INCLUDED_DEQUE_ANY_CAST_ELEMENT

#include "crane_fn.h"
#include <any>
#include <cstdint>
#include <deque>
#include <functional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A, typename P> struct SigT;
enum class Tag;

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  template <typename _U0, typename _U1> operator SigT<_U0, _U1>() const {
    return {[&]() -> _U0 {
              if constexpr (std::is_same_v<A, std::any>) {
                return crane_any_cast<_U0>(x);
              } else {
                if constexpr (std::is_constructible_v<_U0, const A &>) {
                  return _U0(x);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }
            }(),
            [&]() -> _U1 {
              if constexpr (std::is_same_v<P, std::any>) {
                return crane_any_cast<_U1>(a1);
              } else {
                if constexpr (std::is_constructible_v<_U1, const P &>) {
                  return _U1(a1);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }
            }()};
  }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }
};
enum class Tag { TAGA, TAGB };
using input_ty = std::any;
using output_ty = std::any;
using action_entry = SigT<Tag, std::function<output_ty(input_ty)>>;
const action_entry my_action =
    SigT<Tag, std::function<std::any(std::any)>>::existt(
        Tag::TAGA, crane_erase_fn([](const std::any &tup) -> std::any {
          const auto &[x, y0] =
              std::any_cast<std::pair<std::any, std::any>>(tup);
          const auto &[xs, y] =
              std::any_cast<std::pair<std::any, std::any>>(y0);
          return [](auto _a0, auto _a1) {
            _a1.push_front(_a0);
            return _a1;
          }(std::make_pair(std::any(std::any_cast<uint64_t>(x)),
                           std::any(std::any_cast<uint64_t>(y))),
                 std::any_cast<std::deque<std::any>>(xs));
        }));
SigT<Tag, output_ty>
apply_entry(const SigT<Tag, std::function<std::any(std::any)>> &e);
uint64_t get_length(const SigT<Tag, output_ty> &r);
const uint64_t test_result = get_length(apply_entry(my_action));

#endif // INCLUDED_DEQUE_ANY_CAST_ELEMENT
