#include <partial_apply.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>>
PartialApply::inc_all(const std::shared_ptr<List<unsigned int>> &l) {
  return l->template map<unsigned int>([](unsigned int x) { return (x + 1); });
}

std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
PartialApply::tag_all(const std::shared_ptr<List<unsigned int>> &l) {
  return l->template map<std::pair<unsigned int, unsigned int>>(
      [](unsigned int x) { return std::make_pair(1u, x); });
}

std::shared_ptr<List<std::optional<unsigned int>>>
PartialApply::wrap_all(const std::shared_ptr<List<unsigned int>> &l) {
  return l->template map<std::optional<unsigned int>>(
      [](unsigned int x) { return std::make_optional<unsigned int>(x); });
}

std::shared_ptr<List<std::function<
    std::shared_ptr<List<unsigned int>>(std::shared_ptr<List<unsigned int>>)>>>
PartialApply::prepend_each(const std::shared_ptr<List<unsigned int>> &l) {
  return l->template map<std::function<std::shared_ptr<List<unsigned int>>(
      std::shared_ptr<List<unsigned int>>)>>([](unsigned int x) {
    return [=](std::shared_ptr<List<unsigned int>> x0) mutable {
      return List<unsigned int>::ctor::Cons_(x, x0);
    };
  });
}

std::shared_ptr<List<std::shared_ptr<PartialApply::tagged<bool>>>>
PartialApply::tag_with(const unsigned int n,
                       const std::shared_ptr<List<bool>> &l) {
  return l->template map<std::shared_ptr<PartialApply::tagged<bool>>>(
      [=](bool x) mutable { return tagged<bool>::ctor::Tag_(n, x); });
}

std::shared_ptr<
    List<std::pair<unsigned int, std::pair<unsigned int, unsigned int>>>>
PartialApply::double_tag(const std::shared_ptr<List<unsigned int>> &l) {
  return l->template map<
      std::pair<unsigned int, std::pair<unsigned int, unsigned int>>>(
      [](unsigned int x) { return std::make_pair(x, std::make_pair(x, x)); });
}

__attribute__((pure)) unsigned int
PartialApply::sum_with_init(const unsigned int init,
                            const std::shared_ptr<List<unsigned int>> &l) {
  return l->template fold_left<unsigned int>(
      [](unsigned int _x0, unsigned int _x1) -> unsigned int {
        return (_x0 + _x1);
      },
      init);
}
