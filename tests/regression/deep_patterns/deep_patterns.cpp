#include <deep_patterns.h>

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

__attribute__((pure)) unsigned int DeepPatterns::deep_option(
    const std::optional<std::optional<std::optional<unsigned int>>> x) {
  if (x.has_value()) {
    std::optional<std::optional<unsigned int>> o = *x;
    if (o.has_value()) {
      std::optional<unsigned int> o0 = *o;
      if (o0.has_value()) {
        unsigned int n = *o0;
        return n;
      } else {
        return 1u;
      }
    } else {
      return 2u;
    }
  } else {
    return 3u;
  }
}

__attribute__((pure)) unsigned int
DeepPatterns::deep_pair(const std::pair<std::pair<unsigned int, unsigned int>,
                                        std::pair<unsigned int, unsigned int>>
                            p) {
  std::pair<unsigned int, unsigned int> p0 = p.first;
  std::pair<unsigned int, unsigned int> p1 = p.second;
  unsigned int a = p0.first;
  unsigned int b = p0.second;
  unsigned int c = p1.first;
  unsigned int d = p1.second;
  return (((a + b) + c) + d);
}

__attribute__((pure)) unsigned int
DeepPatterns::list_shape(const std::shared_ptr<List<unsigned int>> &l) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::Nil _args) -> unsigned int {
            return 0u;
          },
          [](const typename List<unsigned int>::Cons _args) -> unsigned int {
            unsigned int x = _args.d_a0;
            std::shared_ptr<List<unsigned int>> l0 = _args.d_a1;
            return std::visit(
                Overloaded{
                    [&](const typename List<unsigned int>::Nil _args)
                        -> unsigned int { return std::move(x); },
                    [&](const typename List<unsigned int>::Cons _args)
                        -> unsigned int {
                      unsigned int y = _args.d_a0;
                      std::shared_ptr<List<unsigned int>> l1 = _args.d_a1;
                      return std::visit(
                          Overloaded{
                              [&](const typename List<unsigned int>::Nil _args)
                                  -> unsigned int {
                                return (std::move(x) + std::move(y));
                              },
                              [&](const typename List<unsigned int>::Cons _args)
                                  -> unsigned int {
                                unsigned int z = _args.d_a0;
                                std::shared_ptr<List<unsigned int>> l2 =
                                    _args.d_a1;
                                return std::visit(
                                    Overloaded{
                                        [&](const typename List<unsigned int>::
                                                Nil _args) -> unsigned int {
                                          return (
                                              (std::move(x) + std::move(y)) +
                                              std::move(z));
                                        },
                                        [&](const typename List<unsigned int>::
                                                Cons _args) -> unsigned int {
                                          std::shared_ptr<List<unsigned int>>
                                              rest = _args.d_a1;
                                          return (
                                              ((std::move(x) + std::move(y)) +
                                               std::move(z)) +
                                              std::move(rest)->length());
                                        }},
                                    std::move(l2)->v());
                              }},
                          std::move(l1)->v());
                    }},
                std::move(l0)->v());
          }},
      l->v());
}

__attribute__((pure)) unsigned int
DeepPatterns::deep_sum(const std::shared_ptr<DeepPatterns::outer> &o) {
  return std::visit(
      Overloaded{
          [](const typename DeepPatterns::outer::OLeft _args) -> unsigned int {
            std::shared_ptr<DeepPatterns::inner> i = _args.d_a0;
            return std::visit(
                Overloaded{[](const typename DeepPatterns::inner::ILeft _args)
                               -> unsigned int {
                             unsigned int n = _args.d_a0;
                             return std::move(n);
                           },
                           [](const typename DeepPatterns::inner::IRight _args)
                               -> unsigned int {
                             bool b = _args.d_a0;
                             if (std::move(b)) {
                               return 1u;
                             } else {
                               return 0u;
                             }
                           }},
                std::move(i)->v());
          },
          [](const typename DeepPatterns::outer::ORight _args) -> unsigned int {
            unsigned int n = _args.d_a0;
            return (std::move(n) + 100u);
          }},
      o->v());
}

__attribute__((pure)) unsigned int DeepPatterns::complex_match(
    const std::optional<
        std::pair<unsigned int, std::shared_ptr<List<unsigned int>>>>
        x) {
  if (x.has_value()) {
    std::pair<unsigned int, std::shared_ptr<List<unsigned int>>> p = *x;
    unsigned int n = p.first;
    std::shared_ptr<List<unsigned int>> l = p.second;
    return std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil _args) -> unsigned int {
              return n;
            },
            [&](const typename List<unsigned int>::Cons _args) -> unsigned int {
              unsigned int m = _args.d_a0;
              std::shared_ptr<List<unsigned int>> l0 = _args.d_a1;
              return std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args)
                          -> unsigned int { return (n + std::move(m)); },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> unsigned int {
                        std::shared_ptr<List<unsigned int>> rest = _args.d_a1;
                        return ((n + std::move(m)) + std::move(rest)->length());
                      }},
                  std::move(l0)->v());
            }},
        l->v());
  } else {
    return 0u;
  }
}

__attribute__((pure)) unsigned int
DeepPatterns::guarded_match(const std::pair<unsigned int, unsigned int> p) {
  unsigned int a = p.first;
  unsigned int b = p.second;
  if (a <= b) {
    return (((b - a) > b ? 0 : (b - a)));
  } else {
    return (((a - b) > a ? 0 : (a - b)));
  }
}

__attribute__((pure)) unsigned int DeepPatterns::match_pair_list(
    const std::shared_ptr<DeepPatterns::mylist<
        std::shared_ptr<DeepPatterns::pair<unsigned int, unsigned int>>>> &l) {
  return std::visit(
      Overloaded{
          [](const typename DeepPatterns::mylist<std::shared_ptr<
                 DeepPatterns::pair<unsigned int, unsigned int>>>::Nil _args)
              -> unsigned int { return 0u; },
          [](const typename DeepPatterns::mylist<std::shared_ptr<
                 DeepPatterns::pair<unsigned int, unsigned int>>>::Cons _args)
              -> unsigned int {
            std::shared_ptr<DeepPatterns::pair<unsigned int, unsigned int>> p =
                _args.d_a0;
            return std::visit(
                Overloaded{[](const typename DeepPatterns::pair<
                               unsigned int, unsigned int>::Pair0 _args)
                               -> unsigned int {
                  unsigned int x = _args.d_a0;
                  return std::move(x);
                }},
                std::move(p)->v());
          }},
      l->v());
}

__attribute__((pure)) unsigned int DeepPatterns::match_two(
    const std::shared_ptr<DeepPatterns::mylist<unsigned int>> &l) {
  return std::visit(
      Overloaded{
          [](const typename DeepPatterns::mylist<unsigned int>::Nil _args)
              -> unsigned int { return 0u; },
          [](const typename DeepPatterns::mylist<unsigned int>::Cons _args)
              -> unsigned int {
            unsigned int x = _args.d_a0;
            std::shared_ptr<DeepPatterns::mylist<unsigned int>> m = _args.d_a1;
            return std::visit(
                Overloaded{
                    [&](const typename DeepPatterns::mylist<unsigned int>::Nil
                            _args) -> unsigned int { return std::move(x); },
                    [&](const typename DeepPatterns::mylist<unsigned int>::Cons
                            _args) -> unsigned int { return std::move(x); }},
                std::move(m)->v());
          }},
      l->v());
}

__attribute__((pure)) unsigned int DeepPatterns::match_triple(
    const std::shared_ptr<
        DeepPatterns::mylist<std::shared_ptr<DeepPatterns::mylist<
            std::shared_ptr<DeepPatterns::mylist<unsigned int>>>>>> &l) {
  return std::visit(
      Overloaded{
          [](const typename DeepPatterns::mylist<
              std::shared_ptr<DeepPatterns::mylist<
                  std::shared_ptr<DeepPatterns::mylist<unsigned int>>>>>::Nil
                 _args) -> unsigned int { return 0u; },
          [](const typename DeepPatterns::mylist<
              std::shared_ptr<DeepPatterns::mylist<
                  std::shared_ptr<DeepPatterns::mylist<unsigned int>>>>>::Cons
                 _args) -> unsigned int {
            std::shared_ptr<DeepPatterns::mylist<
                std::shared_ptr<DeepPatterns::mylist<unsigned int>>>>
                m = _args.d_a0;
            return std::visit(
                Overloaded{
                    [](const typename DeepPatterns::mylist<std::shared_ptr<
                           DeepPatterns::mylist<unsigned int>>>::Nil _args)
                        -> unsigned int { return 1u; },
                    [](const typename DeepPatterns::mylist<std::shared_ptr<
                           DeepPatterns::mylist<unsigned int>>>::Cons _args)
                        -> unsigned int {
                      std::shared_ptr<DeepPatterns::mylist<unsigned int>> m1 =
                          _args.d_a0;
                      return std::visit(
                          Overloaded{
                              [](const typename DeepPatterns::mylist<
                                  unsigned int>::Nil _args) -> unsigned int {
                                return 2u;
                              },
                              [](const typename DeepPatterns::mylist<
                                  unsigned int>::Cons _args) -> unsigned int {
                                unsigned int n = _args.d_a0;
                                return std::move(n);
                              }},
                          std::move(m1)->v());
                    }},
                std::move(m)->v());
          }},
      l->v());
}

__attribute__((pure)) unsigned int DeepPatterns::deep_wildcard(
    const std::shared_ptr<DeepPatterns::pair<
        std::shared_ptr<DeepPatterns::pair<unsigned int, unsigned int>>,
        std::shared_ptr<DeepPatterns::pair<unsigned int, unsigned int>>>> &p) {
  return std::visit(
      Overloaded{
          [](const typename DeepPatterns::pair<
              std::shared_ptr<DeepPatterns::pair<unsigned int, unsigned int>>,
              std::shared_ptr<DeepPatterns::pair<unsigned int, unsigned int>>>::
                 Pair0 _args) -> unsigned int {
            std::shared_ptr<DeepPatterns::pair<unsigned int, unsigned int>> p0 =
                _args.d_a0;
            std::shared_ptr<DeepPatterns::pair<unsigned int, unsigned int>> p1 =
                _args.d_a1;
            return std::visit(
                Overloaded{[&](const typename DeepPatterns::pair<
                               unsigned int, unsigned int>::Pair0 _args)
                               -> unsigned int {
                  unsigned int a = _args.d_a0;
                  return std::visit(
                      Overloaded{[&](const typename DeepPatterns::pair<
                                     unsigned int, unsigned int>::Pair0 _args)
                                     -> unsigned int { return std::move(a); }},
                      std::move(p1)->v());
                }},
                std::move(p0)->v());
          }},
      p->v());
}
