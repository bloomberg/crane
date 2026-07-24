#ifndef INCLUDED_DEQUE_ANY_CAST_ELEMENT
#define INCLUDED_DEQUE_ANY_CAST_ELEMENT

#include <any>
#include <cstdint>
#include <deque>
#include <functional>
#include <utility>
#include <variant>

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }
};
enum class Tag { TAGA, TAGB };
using input_ty = std::any;
using output_ty = std::any;
using action_entry = SigT<Tag, std::function<output_ty(input_ty)>>;
const action_entry my_action =
    SigT<Tag, std::function<std::any(std::any)>>::existt(
        Tag::TAGA, std::function<std::any(std::any)>([](const std::any &tup) {
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
