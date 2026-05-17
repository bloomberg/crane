#include "partial_apply.h"

List<uint64_t> PartialApply::inc_all(const List<uint64_t> &l) {
  return l.template map<uint64_t>([](uint64_t x) { return (x + 1); });
}

List<std::pair<uint64_t, uint64_t>>
PartialApply::tag_all(const List<uint64_t> &l) {
  return l.template map<std::pair<uint64_t, uint64_t>>(
      [](uint64_t x) { return std::make_pair(UINT64_C(1), x); });
}

List<std::optional<uint64_t>> PartialApply::wrap_all(const List<uint64_t> &l) {
  return l.template map<std::optional<uint64_t>>(
      [](uint64_t x) { return std::make_optional<uint64_t>(x); });
}

List<std::function<List<uint64_t>(List<uint64_t>)>>
PartialApply::prepend_each(const List<uint64_t> &l) {
  return l.template map<std::function<List<uint64_t>(List<uint64_t>)>>(
      [](uint64_t x) {
        return [=](List<uint64_t> x0) mutable {
          return List<uint64_t>::cons(x, x0);
        };
      });
}

List<PartialApply::tagged<bool>> PartialApply::tag_with(uint64_t n,
                                                        const List<bool> &l) {
  return l.template map<PartialApply::tagged<bool>>(
      [=](bool x) mutable { return tagged<bool>::tag(n, x); });
}

List<std::pair<uint64_t, std::pair<uint64_t, uint64_t>>>
PartialApply::double_tag(const List<uint64_t> &l) {
  return l.template map<std::pair<uint64_t, std::pair<uint64_t, uint64_t>>>(
      [](uint64_t x) { return std::make_pair(x, std::make_pair(x, x)); });
}

uint64_t PartialApply::sum_with_init(uint64_t init, const List<uint64_t> &l) {
  return l.template fold_left<uint64_t>(
      [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); }, init);
}
