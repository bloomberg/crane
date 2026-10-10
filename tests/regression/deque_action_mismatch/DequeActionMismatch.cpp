#include "DequeActionMismatch.h"

#include "Specif.h"

namespace DequeActionMismatch {

Specif::SigT<Tag, sem_ty>
apply_action(const Specif::SigT<Tag, crane::fn<crane::obj(crane::obj)>> &a,
             const Specif::SigT<Tag, sem_ty> &v) {
  const auto &[x0, a1] = a;
  switch (x0) {
  case Tag::TAGLIST: {
    const auto &[x2, a10] = v;
    switch (x2) {
    case Tag::TAGLIST: {
      return Specif::template SigT<Tag, sem_ty>::existt(
          Tag::TAGLIST, crane_call_erased(a1, a10));
    }
    case Tag::TAGNAT: {
      return v;
    }
    default:
      std::unreachable();
    }
    break;
  }
  case Tag::TAGNAT: {
    const auto &[x2, a11] = v;
    switch (x2) {
    case Tag::TAGLIST: {
      return v;
    }
    case Tag::TAGNAT: {
      return Specif::template SigT<Tag, sem_ty>::existt(
          Tag::TAGNAT, crane_call_erased(a1, a11));
    }
    default:
      std::unreachable();
    }
    break;
  }
  default:
    std::unreachable();
  }
}

uint64_t get_length(const Specif::SigT<Tag, sem_ty> &v) {
  const auto &[x0, a1] = v;
  switch (x0) {
  case Tag::TAGLIST: {
    return static_cast<uint64_t>(
        crane::any_cast<std::deque<crane::obj>>(a1).size());
  }
  case Tag::TAGNAT: {
    return UINT64_C(0);
  }
  default:
    std::unreachable();
  }
}

uint64_t get_first(const Specif::SigT<Tag, sem_ty> &v) {
  const auto &[x, a1] = v;
  switch (x) {
  case Tag::TAGLIST: {
    auto _cs = crane::any_cast<std::deque<crane::obj>>(a1);
    if (_cs.empty()) {
      return UINT64_C(0);
    } else {
      const auto &p = _cs.front();
      std::deque<crane::obj> _x(_cs.begin() + 1, _cs.end());
      const auto &[x1, _x0] =
          crane::any_cast<std::pair<crane::obj, crane::obj>>(p);
      return crane::any_cast<uint64_t>(x1);
    }
    break;
  }
  case Tag::TAGNAT: {
    return UINT64_C(0);
  }
  default:
    std::unreachable();
  }
}

} // namespace DequeActionMismatch
