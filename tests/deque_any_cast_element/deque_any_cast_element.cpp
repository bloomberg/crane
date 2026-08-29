#include "deque_any_cast_element.h"

SigT<Tag, output_ty>
apply_entry(const SigT<Tag, std::function<std::any(std::any)>> &e) {
  const auto &[x0, a1] = e;
  switch (x0) {
  case Tag::TAGA: {
    return SigT<Tag, std::any>::existt(
        Tag::TAGA,
        a1(std::make_pair(
            std::any(UINT64_C(10)),
            std::any(std::make_pair(
                std::any([](auto _a0, auto _a1) {
                  _a1.push_front(_a0);
                  return _a1;
                }(std::make_pair(std::any(UINT64_C(1)), std::any(UINT64_C(2))),
                         [](auto _a0, auto _a1) {
                           _a1.push_front(_a0);
                           return _a1;
                         }(std::make_pair(std::any(UINT64_C(3)),
                                          std::any(UINT64_C(4))),
                           std::deque<std::any>{}))),
                std::any(UINT64_C(20)))))));
  }
  case Tag::TAGB: {
    return SigT<Tag, std::any>::existt(Tag::TAGB, a1(UINT64_C(5)));
  }
  default:
    std::unreachable();
  }
}

uint64_t get_length(const SigT<Tag, output_ty> &r) {
  const auto &[x0, a1] = r;
  switch (x0) {
  case Tag::TAGA: {
    return static_cast<uint64_t>(
        std::any_cast<std::deque<std::any>>(a1).size());
  }
  case Tag::TAGB: {
    return std::any_cast<uint64_t>(a1);
  }
  default:
    std::unreachable();
  }
}
