#ifndef INCLUDED_DEQUEANYCASTELEMENT
#define INCLUDED_DEQUEANYCASTELEMENT

#include <any>
#include <cstdint>
#include <deque>
#include <functional>
#include <utility>
#include <variant>

#include "Specif.h"

namespace DequeAnyCastElement {

enum class Tag { TAGA, TAGB };
using input_ty = std::any;
using output_ty = std::any;
using action_entry = Specif::SigT<Tag, std::function<output_ty(input_ty)>>;
const action_entry my_action =
    Specif::template SigT<Tag, std::function<std::any(std::any)>>::existt(
        Tag::TAGA, [](const auto &tup) {
          const auto &[x, y0] =
              std::any_cast<std::pair<std::any, std::any>>(tup);
          const auto &[xs, y] =
              std::any_cast<std::pair<std::any, std::any>>(y0);
          return [](auto _a0, auto _a1) {
            _a1.push_front(_a0);
            return _a1;
          }(std::make_pair(std::any(x), std::any(y)), [&]() {
            std::deque<std::pair<std::any, std::any>> _r;
            for (const auto &_e : std::any_cast<std::deque<std::any>>([&]() {
                   std::deque<std::pair<std::any, std::any>> _r;
                   for (const auto &_e :
                        std::any_cast<std::deque<std::any>>(xs))
                     _r.push_back([&]() {
                       const auto &_p =
                           std::any_cast<std::pair<std::any, std::any>>(_e);
                       return std::make_pair(_p.first, _p.second);
                     }());
                   return _r;
                 }()))
              _r.push_back([&]() {
                const auto &_p =
                    std::any_cast<std::pair<std::any, std::any>>(_e);
                return std::make_pair(_p.first, _p.second);
              }());
            return _r;
          }());
        });
Specif::SigT<Tag, output_ty>
apply_entry(const Specif::SigT<Tag, std::function<std::any(std::any)>> &e);
uint64_t get_length(const Specif::SigT<Tag, output_ty> &r);
const uint64_t test_result = get_length(apply_entry(my_action));

} // namespace DequeAnyCastElement

#endif // INCLUDED_DEQUEANYCASTELEMENT
