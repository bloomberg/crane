#ifndef INCLUDED_DEQUEACTIONMISMATCH
#define INCLUDED_DEQUEACTIONMISMATCH

#include <any>
#include <cstdint>
#include <deque>
#include <functional>
#include <utility>
#include <variant>

#include "Specif.h"

namespace DequeActionMismatch {

enum class Tag { TAGLIST, TAGNAT };
using sem_ty = std::any;
using action = Specif::SigT<Tag, std::function<sem_ty(sem_ty)>>;
const action base_action =
    Specif::template SigT<Tag, std::function<std::any(std::any)>>::existt(
        Tag::TAGLIST, [](const auto &) { return std::deque<std::any>{}; });
const action cons_action =
    Specif::template SigT<Tag, std::function<std::any(std::any)>>::existt(
        Tag::TAGLIST, [](const auto &xs) {
          return [](auto _a0, auto _a1) {
            _a1.push_front(_a0);
            return _a1;
          }(std::make_pair(UINT64_C(42), UINT64_C(99)), xs);
        });
Specif::SigT<Tag, sem_ty>
apply_action(const Specif::SigT<Tag, std::function<std::any(std::any)>> &a,
             Specif::SigT<Tag, sem_ty> v);
const Specif::SigT<Tag, sem_ty> chain = []() {
  auto v0 = Specif::template SigT<Tag, std::deque<std::any>>::existt(
      Tag::TAGLIST, std::deque<std::any>{});
  auto v1 = apply_action(base_action, std::move(v0));
  auto v2 = apply_action(cons_action, std::move(v1));
  return apply_action(cons_action, std::move(v2));
}();
uint64_t get_length(const Specif::SigT<Tag, sem_ty> &v);
uint64_t get_first(const Specif::SigT<Tag, sem_ty> &v);
const uint64_t test_length = get_length(chain);
const uint64_t test_first = get_first(chain);

} // namespace DequeActionMismatch

#endif // INCLUDED_DEQUEACTIONMISMATCH
