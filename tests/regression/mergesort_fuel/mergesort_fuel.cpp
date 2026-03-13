#include <mergesort_fuel.h>

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

/// * Split
__attribute__((pure)) std::pair<std::shared_ptr<List<unsigned int>>,
                                std::shared_ptr<List<unsigned int>>>
MergesortFuel::split(const std::shared_ptr<List<unsigned int>> &l) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::Nil _args)
              -> std::pair<std::shared_ptr<List<unsigned int>>,
                           std::shared_ptr<List<unsigned int>>> {
            return std::make_pair(List<unsigned int>::ctor::Nil_(),
                                  List<unsigned int>::ctor::Nil_());
          },
          [](const typename List<unsigned int>::Cons _args)
              -> std::pair<std::shared_ptr<List<unsigned int>>,
                           std::shared_ptr<List<unsigned int>>> {
            unsigned int x = _args.d_a0;
            std::shared_ptr<List<unsigned int>> l0 = _args.d_a1;
            return std::visit(
                Overloaded{
                    [&](const typename List<unsigned int>::Nil _args)
                        -> std::pair<std::shared_ptr<List<unsigned int>>,
                                     std::shared_ptr<List<unsigned int>>> {
                      return std::make_pair(
                          List<unsigned int>::ctor::Cons_(
                              std::move(x), List<unsigned int>::ctor::Nil_()),
                          List<unsigned int>::ctor::Nil_());
                    },
                    [&](const typename List<unsigned int>::Cons _args)
                        -> std::pair<std::shared_ptr<List<unsigned int>>,
                                     std::shared_ptr<List<unsigned int>>> {
                      unsigned int y = _args.d_a0;
                      std::shared_ptr<List<unsigned int>> rest = _args.d_a1;
                      std::shared_ptr<List<unsigned int>> l1 =
                          split(rest).first;
                      std::shared_ptr<List<unsigned int>> l2 =
                          split(rest).second;
                      return std::make_pair(
                          List<unsigned int>::ctor::Cons_(x, std::move(l1)),
                          List<unsigned int>::ctor::Cons_(std::move(y),
                                                          std::move(l2)));
                    }},
                std::move(l0)->v());
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
            [&](const typename List<unsigned int>::Nil _args)
                -> std::shared_ptr<List<unsigned int>> {
              return std::move(l3);
            },
            [&](const typename List<unsigned int>::Cons _args)
                -> std::shared_ptr<List<unsigned int>> {
              unsigned int a1 = _args.d_a0;
              std::shared_ptr<List<unsigned int>> l1_ = _args.d_a1;
              return std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args)
                          -> std::shared_ptr<List<unsigned int>> { return l1; },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> std::shared_ptr<List<unsigned int>> {
                        unsigned int a2 = _args.d_a0;
                        std::shared_ptr<List<unsigned int>> l2_ = _args.d_a1;
                        if (Compare_dec::le_lt_dec(a1, a2)) {
                          return List<unsigned int>::ctor::Cons_(
                              std::move(a1),
                              merge(std::move(l1_), std::move(l3)));
                        } else {
                          return List<unsigned int>::ctor::Cons_(
                              std::move(a2), merge_aux(std::move(l2_)));
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
    return std::move(l);
  } else {
    unsigned int fuel_ = fuel - 1;
    return std::visit(
        Overloaded{
            [](const typename List<unsigned int>::Nil _args)
                -> std::shared_ptr<List<unsigned int>> {
              return List<unsigned int>::ctor::Nil_();
            },
            [&](const typename List<unsigned int>::Cons _args)
                -> std::shared_ptr<List<unsigned int>> {
              unsigned int x = _args.d_a0;
              std::shared_ptr<List<unsigned int>> l0 = _args.d_a1;
              return std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args)
                          -> std::shared_ptr<List<unsigned int>> {
                        return List<unsigned int>::ctor::Cons_(
                            std::move(x), List<unsigned int>::ctor::Nil_());
                      },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> std::shared_ptr<List<unsigned int>> {
                        std::shared_ptr<List<unsigned int>> l1 = split(l).first;
                        std::shared_ptr<List<unsigned int>> l2 =
                            split(l).second;
                        return merge(msort_go(fuel_, l1), msort_go(fuel_, l2));
                      }},
                  std::move(l0)->v());
            }},
        l->v());
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
