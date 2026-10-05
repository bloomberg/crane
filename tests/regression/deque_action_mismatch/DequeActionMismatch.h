#ifndef INCLUDED_DEQUEACTIONMISMATCH
#define INCLUDED_DEQUEACTIONMISMATCH

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <cstdint>
#include <deque>
#include <utility>
#include <variant>

#include "Specif.h"

namespace DequeActionMismatch {

enum class Tag;
using sem_ty = crane::obj;
enum class Tag { TAGLIST, TAGNAT };
using action = Specif::SigT<Tag, crane::fn<sem_ty(sem_ty)>>;
const action base_action =
    Specif::template SigT<Tag, crane::fn<crane::obj(crane::obj)>>::existt(
        Tag::TAGLIST, crane_erase_fn([](const crane::obj &) -> crane::obj {
          return std::deque<crane::obj>{};
        }));
const action cons_action =
    Specif::template SigT<Tag, crane::fn<crane::obj(crane::obj)>>::existt(
        Tag::TAGLIST,
        crane_erase_fn([](const crane::obj &_any_xs) -> crane::obj {
          std::deque<crane::obj> xs =
              crane::any_cast<std::deque<crane::obj>>(_any_xs);
          return [](auto _a0, auto _a1) {
            _a1.push_front(_a0);
            return _a1;
          }(std::make_pair(crane::obj(UINT64_C(42)), crane::obj(UINT64_C(99))),
                 xs);
        }));
Specif::SigT<Tag, sem_ty>
apply_action(const Specif::SigT<Tag, crane::fn<crane::obj(crane::obj)>> &a,
             Specif::SigT<Tag, sem_ty> v);
const Specif::SigT<Tag, sem_ty> chain = []() {
  Specif::SigT<Tag, sem_ty> v0 = Specif::template SigT<Tag, sem_ty>::existt(
      Tag::TAGLIST, std::deque<crane::obj>{});
  Specif::SigT<Tag, sem_ty> v1 = apply_action(base_action, std::move(v0));
  Specif::SigT<Tag, sem_ty> v2 = apply_action(cons_action, std::move(v1));
  Specif::SigT<Tag, sem_ty> v3 = apply_action(cons_action, std::move(v2));
  return v3;
}();
uint64_t get_length(const Specif::SigT<Tag, sem_ty> &v);
uint64_t get_first(const Specif::SigT<Tag, sem_ty> &v);
const uint64_t test_length = get_length(chain);
inline constexpr uint64_t test_first = UINT64_C(42);

} // namespace DequeActionMismatch

#endif // INCLUDED_DEQUEACTIONMISMATCH
