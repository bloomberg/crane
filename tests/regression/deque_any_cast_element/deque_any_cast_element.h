#ifndef INCLUDED_DEQUE_ANY_CAST_ELEMENT
#define INCLUDED_DEQUE_ANY_CAST_ELEMENT

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <any>
#include <cstdint>
#include <deque>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A, typename P> struct SigT;
enum class Tag;
using input_ty = crane::obj;
using output_ty = crane::obj;

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  template <typename _U0, typename _U1> operator SigT<_U0, _U1>() const {
    return {[&]() -> _U0 {
              if constexpr (crane_convertible<_U0, const A &>) {
                return crane_convert<_U0>(x);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }(),
            [&]() -> _U1 {
              if constexpr (crane_convertible<_U1, const P &>) {
                return crane_convert<_U1>(a1);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
  }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }
};
enum class Tag { TAGA, TAGB };
using action_entry = SigT<Tag, crane::fn<output_ty(input_ty)>>;
const action_entry my_action =
    SigT<Tag, crane::fn<crane::obj(crane::obj)>>::existt(
        Tag::TAGA, crane_erase_fn([](const crane::obj &tup) -> crane::obj {
          const auto &[x, y0] =
              crane::any_cast<std::pair<crane::obj, crane::obj>>(tup);
          const auto &[xs, y] =
              crane::any_cast<std::pair<crane::obj, crane::obj>>(y0);
          return [](auto _a0, auto _a1) {
            _a1.push_front(_a0);
            return _a1;
          }(std::make_pair(crane::obj(crane::any_cast<uint64_t>(x)),
                           crane::obj(crane::any_cast<uint64_t>(y))),
                 crane::any_cast<std::deque<crane::obj>>(xs));
        }));
SigT<Tag, output_ty>
apply_entry(const SigT<Tag, crane::fn<crane::obj(crane::obj)>> &e);
uint64_t get_length(const SigT<Tag, output_ty> &r);
const uint64_t test_result = get_length(apply_entry(my_action));

#endif // INCLUDED_DEQUE_ANY_CAST_ELEMENT
