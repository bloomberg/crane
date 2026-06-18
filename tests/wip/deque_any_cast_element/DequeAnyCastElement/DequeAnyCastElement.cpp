#include "DequeAnyCastElement.h"

#include "Specif.h"

namespace DequeAnyCastElement {

Specif::SigT<Tag, output_ty>
apply_entry(const Specif::SigT<Tag, std::function<std::any(std::any)>> &e) {
  const auto &[x0, a1] = e;
  switch (x0) {
  case Tag::TAGA: {
    return Specif::template SigT<Tag, std::any>::existt(
        Tag::TAGA,
        a1(std::make_pair(UINT64_C(10),
                          std::make_pair(
                              [](auto _a0, auto _a1) {
                                _a1.push_front(_a0);
                                return _a1;
                              }(std::make_pair(UINT64_C(1), UINT64_C(2)),
                                [](auto _a0, auto _a1) {
                                  _a1.push_front(_a0);
                                  return _a1;
                                }(std::make_pair(UINT64_C(3), UINT64_C(4)),
                                  std::deque<std::pair<uint64_t, uint64_t>>{})),
                              UINT64_C(20)))));
  }
  case Tag::TAGB: {
    return Specif::template SigT<Tag, std::any>::existt(Tag::TAGB,
                                                        a1(UINT64_C(5)));
  }
  default:
    std::unreachable();
  }
}

uint64_t get_length(const Specif::SigT<Tag, output_ty> &r) {
  const auto &[x0, a1] = r;
  switch (x0) {
  case Tag::TAGA: {
    return static_cast<uint64_t>(
        std::any_cast<std::deque<std::pair<uint64_t, uint64_t>>>(a1).size());
  }
  case Tag::TAGB: {
    return std::any_cast<uint64_t>(a1);
  }
  default:
    std::unreachable();
  }
}

} // namespace DequeAnyCastElement
