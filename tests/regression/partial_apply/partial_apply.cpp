#include <partial_apply.h>

List<unsigned int> PartialApply::inc_all(const List<unsigned int> &l) {
  return l.template map<unsigned int>([](unsigned int x) { return (x + 1); });
}

List<std::pair<unsigned int, unsigned int>>
PartialApply::tag_all(const List<unsigned int> &l) {
  return l.template map<std::pair<unsigned int, unsigned int>>(
      [](unsigned int x) { return std::make_pair(1u, x); });
}

List<std::optional<unsigned int>>
PartialApply::wrap_all(const List<unsigned int> &l) {
  return l.template map<std::optional<unsigned int>>(
      [](unsigned int x) { return std::make_optional<unsigned int>(x); });
}

List<std::function<List<unsigned int>(List<unsigned int>)>>
PartialApply::prepend_each(const List<unsigned int> &l) {
  return l.template map<std::function<List<unsigned int>(List<unsigned int>)>>(
      [](unsigned int x) {
        return [=](List<unsigned int> x0) mutable {
          return List<unsigned int>::cons(x, x0);
        };
      });
}

List<PartialApply::tagged<bool>> PartialApply::tag_with(unsigned int n,
                                                        const List<bool> &l) {
  return l.template map<PartialApply::tagged<bool>>(
      [=](bool x) mutable { return tagged<bool>::tag(n, x); });
}

List<std::pair<unsigned int, std::pair<unsigned int, unsigned int>>>
PartialApply::double_tag(const List<unsigned int> &l) {
  return l.template map<
      std::pair<unsigned int, std::pair<unsigned int, unsigned int>>>(
      [](unsigned int x) { return std::make_pair(x, std::make_pair(x, x)); });
}

unsigned int PartialApply::sum_with_init(const unsigned int &init,
                                         const List<unsigned int> &l) {
  return l.template fold_left<unsigned int>(
      [](unsigned int _x0, unsigned int _x1) -> unsigned int {
        return (_x0 + _x1);
      },
      init);
}
