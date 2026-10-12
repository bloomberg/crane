#include "family_call_result_mapped_list.h"

uint64_t
FamilyCallResultMappedList::size(const FamilyCallResultMappedList::ty &t,
                                 FamilyCallResultMappedList::den n) {
  if (std::holds_alternative<typename FamilyCallResultMappedList::ty::TNat>(
          t.v())) {
    return crane::any_cast<uint64_t>(std::move(n));
  } else {
    const auto &[a0] =
        std::get<typename FamilyCallResultMappedList::ty::TList>(t.v());
    const FamilyCallResultMappedList::ty &a0_value = *a0;
    return [](auto _f, const auto &_l, auto _a) {
      for (const auto &_x : _l)
        _a = _f(_a, _x);
      return _a;
    }(crane_erase_fn<uint64_t>(
               [=](uint64_t acc, FamilyCallResultMappedList::den x) {
                 return (acc + size(a0_value, x));
               }),
           crane::any_cast<std::deque<crane::obj>>(std::move(n)), UINT64_C(0));
  }
}

FamilyCallResultMappedList::den FamilyCallResultMappedList::mk(uint64_t n) {
  return ListDef::seq(UINT64_C(0), n);
}

std::deque<uint64_t> ListDef::seq(uint64_t start, uint64_t len) {
  if (len <= 0) {
    return std::deque<uint64_t>{};
  } else {
    uint64_t len0 = len - 1;
    return [](auto _a0, auto _a1) {
      _a1.push_front(_a0);
      return _a1;
    }(start, ListDef::seq((start + 1), len0));
  }
}
