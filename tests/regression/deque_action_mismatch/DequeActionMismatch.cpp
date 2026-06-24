#include "DequeActionMismatch.h"

#include "Specif.h"

namespace DequeActionMismatch {

Specif::SigT<Tag, sem_ty>
apply_action(const Specif::SigT<Tag, std::function<std::any(std::any)>> &a,
             Specif::SigT<Tag, sem_ty> v) {
  const auto &[x0, a1] = a;
  switch (x0) {
  case Tag::TAGLIST: {
    auto &[x2, a10] = v;
    switch (std::move(x2)) {
    case Tag::TAGLIST: {
      return Specif::template SigT<Tag, std::any>::existt(Tag::TAGLIST,
                                                          a1(std::move(a10)));
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
    auto &[x2, a11] = v;
    switch (std::move(x2)) {
    case Tag::TAGLIST: {
      return v;
    }
    case Tag::TAGNAT: {
      return Specif::template SigT<Tag, std::any>::existt(Tag::TAGNAT,
                                                          a1(std::move(a11)));
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
        std::any_cast<std::deque<std::pair<std::any, std::any>>>(a1).size());
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
    auto _cs = std::any_cast<std::deque<std::pair<std::any, std::any>>>(a1);
    if (_cs.empty()) {
      return UINT64_C(0);
    } else {
      const auto &p = _cs.front();
      std::decay_t<decltype(_cs)> _x(_cs.begin() + 1, _cs.end());
      const auto &[x1, _x0] = std::any_cast<std::pair<std::any, std::any>>(p);
      return std::any_cast<uint64_t>(x1);
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
