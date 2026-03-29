#include <deep_patterns.h>

#include <memory>
#include <optional>
#include <type_traits>
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
            return std::visit(
                Overloaded{
                    [&](const typename List<unsigned int>::Nil _args0)
                        -> unsigned int { return _args.d_a0; },
                    [&](const typename List<unsigned int>::Cons _args0)
                        -> unsigned int {
                      return std::visit(
                          Overloaded{
                              [&](const typename List<unsigned int>::Nil _args1)
                                  -> unsigned int {
                                return (_args.d_a0 + _args0.d_a0);
                              },
                              [&](const typename List<unsigned int>::Cons
                                      _args1) -> unsigned int {
                                return std::visit(
                                    Overloaded{
                                        [&](const typename List<unsigned int>::
                                                Nil _args2) -> unsigned int {
                                          return ((_args.d_a0 + _args0.d_a0) +
                                                  _args1.d_a0);
                                        },
                                        [&](const typename List<unsigned int>::
                                                Cons _args2) -> unsigned int {
                                          return (((_args.d_a0 + _args0.d_a0) +
                                                   _args1.d_a0) +
                                                  _args2.d_a1->length());
                                        }},
                                    _args1.d_a1->v());
                              }},
                          _args0.d_a1->v());
                    }},
                _args.d_a1->v());
          }},
      l->v());
}

__attribute__((pure)) unsigned int
DeepPatterns::deep_sum(const std::shared_ptr<DeepPatterns::outer> &o) {
  return std::visit(
      Overloaded{
          [](const typename DeepPatterns::outer::OLeft _args) -> unsigned int {
            return std::visit(
                Overloaded{[](const typename DeepPatterns::inner::ILeft _args0)
                               -> unsigned int { return _args0.d_a0; },
                           [](const typename DeepPatterns::inner::IRight _args0)
                               -> unsigned int {
                             if (_args0.d_a0) {
                               return 1u;
                             } else {
                               return 0u;
                             }
                           }},
                _args.d_a0->v());
          },
          [](const typename DeepPatterns::outer::ORight _args) -> unsigned int {
            return (_args.d_a0 + 100u);
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
              return std::visit(
                  Overloaded{[&](const typename List<unsigned int>::Nil _args0)
                                 -> unsigned int { return (n + _args.d_a0); },
                             [&](const typename List<unsigned int>::Cons _args0)
                                 -> unsigned int {
                               return ((n + _args.d_a0) +
                                       _args0.d_a1->length());
                             }},
                  _args.d_a1->v());
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
            return std::visit(
                Overloaded{[](const typename DeepPatterns::pair<
                               unsigned int, unsigned int>::Pair0 _args0)
                               -> unsigned int { return _args0.d_a0; }},
                _args.d_a0->v());
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
            return std::visit(
                Overloaded{
                    [&](const typename DeepPatterns::mylist<unsigned int>::Nil
                            _args0) -> unsigned int { return _args.d_a0; },
                    [&](const typename DeepPatterns::mylist<unsigned int>::Cons
                            _args0) -> unsigned int { return _args.d_a0; }},
                _args.d_a1->v());
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
            return std::visit(
                Overloaded{
                    [](const typename DeepPatterns::mylist<std::shared_ptr<
                           DeepPatterns::mylist<unsigned int>>>::Nil _args0)
                        -> unsigned int { return 1u; },
                    [](const typename DeepPatterns::mylist<std::shared_ptr<
                           DeepPatterns::mylist<unsigned int>>>::Cons _args0)
                        -> unsigned int {
                      return std::visit(
                          Overloaded{
                              [](const typename DeepPatterns::mylist<
                                  unsigned int>::Nil _args1) -> unsigned int {
                                return 2u;
                              },
                              [](const typename DeepPatterns::mylist<
                                  unsigned int>::Cons _args1) -> unsigned int {
                                return _args1.d_a0;
                              }},
                          _args0.d_a0->v());
                    }},
                _args.d_a0->v());
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
            return std::visit(
                Overloaded{[&](const typename DeepPatterns::pair<
                               unsigned int, unsigned int>::Pair0 _args0)
                               -> unsigned int {
                  return std::visit(
                      Overloaded{[&](const typename DeepPatterns::pair<
                                     unsigned int, unsigned int>::Pair0 _args1)
                                     -> unsigned int { return _args0.d_a0; }},
                      _args.d_a1->v());
                }},
                _args.d_a0->v());
          }},
      p->v());
}
