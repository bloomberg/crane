#include <mergesort_fuel.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// * Split
__attribute__((pure)) std::pair<std::shared_ptr<List<unsigned int>>,
                                std::shared_ptr<List<unsigned int>>>
MergesortFuel::split(const std::shared_ptr<List<unsigned int>> &l) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::Nil)
              -> std::pair<std::shared_ptr<List<unsigned int>>,
                           std::shared_ptr<List<unsigned int>>> {
            return std::make_pair(List<unsigned int>::nil(),
                                  List<unsigned int>::nil());
          },
          [](const typename List<unsigned int>::Cons _args)
              -> std::pair<std::shared_ptr<List<unsigned int>>,
                           std::shared_ptr<List<unsigned int>>> {
            return std::visit(
                Overloaded{
                    [&](const typename List<unsigned int>::Nil)
                        -> std::pair<std::shared_ptr<List<unsigned int>>,
                                     std::shared_ptr<List<unsigned int>>> {
                      return std::make_pair(
                          List<unsigned int>::cons(_args.d_a0,
                                                   List<unsigned int>::nil()),
                          List<unsigned int>::nil());
                    },
                    [&](const typename List<unsigned int>::Cons _args0)
                        -> std::pair<std::shared_ptr<List<unsigned int>>,
                                     std::shared_ptr<List<unsigned int>>> {
                      std::shared_ptr<List<unsigned int>> l1 =
                          split(_args0.d_a1).first;
                      std::shared_ptr<List<unsigned int>> l2 =
                          split(_args0.d_a1).second;
                      return std::make_pair(
                          List<unsigned int>::cons(_args.d_a0, l1),
                          List<unsigned int>::cons(_args0.d_a0, l2));
                    }},
                _args.d_a1->v());
          }},
      l->v());
}

/// * Merge
std::shared_ptr<List<unsigned int>>
MergesortFuel::merge(std::shared_ptr<List<unsigned int>> l1,
                     const std::shared_ptr<List<unsigned int>> &l2) {
  std::function<std::shared_ptr<List<unsigned int>>(
      std::shared_ptr<List<unsigned int>>)>
      merge_aux;
  merge_aux = [&](std::shared_ptr<List<unsigned int>> l3)
      -> std::shared_ptr<List<unsigned int>> {
    return std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil)
                -> std::shared_ptr<List<unsigned int>> { return l3; },
            [&](const typename List<unsigned int>::Cons _args)
                -> std::shared_ptr<List<unsigned int>> {
              return std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil)
                          -> std::shared_ptr<List<unsigned int>> { return l1; },
                      [&](const typename List<unsigned int>::Cons _args0)
                          -> std::shared_ptr<List<unsigned int>> {
                        if (Compare_dec::le_lt_dec(_args.d_a0, _args0.d_a0)) {
                          return List<unsigned int>::cons(
                              _args.d_a0, merge(_args.d_a1, l3));
                        } else {
                          return List<unsigned int>::cons(
                              _args0.d_a0, merge_aux(_args0.d_a1));
                        }
                      }},
                  l3->v());
            }},
        l1->v());
  };
  return merge_aux(l2);
}

/// * Fuel-based merge sort
std::shared_ptr<List<unsigned int>>
MergesortFuel::msort_go(const unsigned int fuel,
                        std::shared_ptr<List<unsigned int>> l) {
  if (fuel <= 0) {
    return l;
  } else {
    unsigned int fuel_ = fuel - 1;
    if (l.use_count() == 1 && l->v().index() == 0) {
      auto &_rf = std::get<0>(l->v_mut());
      return l;
    } else {
      return std::visit(
          Overloaded{[](const typename List<unsigned int>::Nil)
                         -> std::shared_ptr<List<unsigned int>> {
                       return List<unsigned int>::nil();
                     },
                     [&](const typename List<unsigned int>::Cons _args)
                         -> std::shared_ptr<List<unsigned int>> {
                       return std::visit(
                           Overloaded{
                               [&](const typename List<unsigned int>::Nil)
                                   -> std::shared_ptr<List<unsigned int>> {
                                 return List<unsigned int>::cons(
                                     _args.d_a0, List<unsigned int>::nil());
                               },
                               [&](const typename List<unsigned int>::Cons)
                                   -> std::shared_ptr<List<unsigned int>> {
                                 std::shared_ptr<List<unsigned int>> l1 =
                                     split(l).first;
                                 std::shared_ptr<List<unsigned int>> l2 =
                                     split(l).second;
                                 return merge(msort_go(fuel_, l1),
                                              msort_go(fuel_, l2));
                               }},
                           _args.d_a1->v());
                     }},
          l->v());
    }
  }
}

/// * Top-level sort and correctness
std::shared_ptr<List<unsigned int>>
MergesortFuel::msort(const std::shared_ptr<List<unsigned int>> &l) {
  return msort_go(l->length(), l);
}

__attribute__((pure)) bool Compare_dec::le_lt_dec(const unsigned int n,
                                                  const unsigned int m) {
  if (n <= 0) {
    return true;
  } else {
    unsigned int n0 = n - 1;
    if (m <= 0) {
      return false;
    } else {
      unsigned int n1 = m - 1;
      if (Compare_dec::le_lt_dec(n0, n1)) {
        return true;
      } else {
        return false;
      }
    }
  }
}
