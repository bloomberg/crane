#include <sort.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>>
Sort::sort_cons_prog(const unsigned int a,
                     const std::shared_ptr<List<unsigned int>> &,
                     const std::shared_ptr<List<unsigned int>> &l_) {
  return std::visit(
      Overloaded{
          [&](const typename List<unsigned int>::Nil) -> auto {
            return Sig<std::shared_ptr<List<unsigned int>>>::exist(
                List<unsigned int>::cons(a, List<unsigned int>::nil()));
          },
          [&](const typename List<unsigned int>::Cons _args) -> auto {
            std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>> s =
                sort_cons_prog(a, _args.d_a1, _args.d_a1);
            return std::visit(
                Overloaded{
                    [&](const typename Sig<
                        std::shared_ptr<List<unsigned int>>>::Exist _args0)
                        -> std::shared_ptr<
                            Sig<std::shared_ptr<List<unsigned int>>>> {
                      bool s0 = Compare_dec::le_lt_dec(a, _args.d_a0);
                      if (s0) {
                        return Sig<std::shared_ptr<List<unsigned int>>>::exist(
                            List<unsigned int>::cons(
                                a, List<unsigned int>::cons(_args.d_a0,
                                                            _args.d_a1)));
                      } else {
                        return Sig<std::shared_ptr<List<unsigned int>>>::exist(
                            List<unsigned int>::cons(_args.d_a0, _args0.d_x));
                      }
                    }},
                s->v());
          }},
      l_->v());
}

std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>>
Sort::isort(const std::shared_ptr<List<unsigned int>> &l) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::Nil) -> auto {
            return Sig<std::shared_ptr<List<unsigned int>>>::exist(
                List<unsigned int>::nil());
          },
          [](const typename List<unsigned int>::Cons _args) -> auto {
            return std::visit(
                Overloaded{
                    [&](const typename Sig<
                        std::shared_ptr<List<unsigned int>>>::Exist _args0)
                        -> std::shared_ptr<
                            Sig<std::shared_ptr<List<unsigned int>>>> {
                      return sort_cons_prog(_args.d_a0, _args.d_a1, _args0.d_x);
                    }},
                isort(_args.d_a1)->v());
          }},
      l->v());
}

std::shared_ptr<List<unsigned int>>
Sort::merge(std::shared_ptr<List<unsigned int>> l1,
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

std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>>
Sort::merge_prog(const std::shared_ptr<List<unsigned int>> &,
                 const std::shared_ptr<List<unsigned int>> &l1,
                 const std::shared_ptr<List<unsigned int>> &l2) {
  return Sig<std::shared_ptr<List<unsigned int>>>::exist(merge(l1, l2));
}

std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>>
Sort::msort(const std::shared_ptr<List<unsigned int>> &_x0) {
  return div_conq_split(
      Sig<std::shared_ptr<List<unsigned int>>>::exist(
          List<unsigned int>::nil()),
      [](unsigned int a) {
        return Sig<std::shared_ptr<List<unsigned int>>>::exist(
            List<unsigned int>::cons(a, List<unsigned int>::nil()));
      },
      [](std::shared_ptr<List<unsigned int>> ls,
         std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>> x,
         std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>> x0) {
        return std::visit(
            Overloaded{[&](const typename Sig<
                           std::shared_ptr<List<unsigned int>>>::Exist _args)
                           -> std::shared_ptr<
                               Sig<std::shared_ptr<List<unsigned int>>>> {
              return std::visit(
                  Overloaded{
                      [&](const typename Sig<
                          std::shared_ptr<List<unsigned int>>>::Exist _args0)
                          -> std::shared_ptr<
                              Sig<std::shared_ptr<List<unsigned int>>>> {
                        return merge_prog(ls, _args.d_x, _args0.d_x);
                      }},
                  x0->v());
            }},
            x->v());
      },
      _x0);
}

std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>>
Sort::pair_merge_prog(const unsigned int, const unsigned int,
                      const std::shared_ptr<List<unsigned int>> &,
                      const std::shared_ptr<List<unsigned int>> &l_,
                      const std::shared_ptr<List<unsigned int>> &l_0) {
  return Sig<std::shared_ptr<List<unsigned int>>>::exist(merge(l_0, l_));
}

std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>>
Sort::psort(const std::shared_ptr<List<unsigned int>> &_x0) {
  return div_conq_pair(
      Sig<std::shared_ptr<List<unsigned int>>>::exist(
          List<unsigned int>::nil()),
      [](unsigned int a) {
        return Sig<std::shared_ptr<List<unsigned int>>>::exist(
            List<unsigned int>::cons(a, List<unsigned int>::nil()));
      },
      [](unsigned int a1, unsigned int a2) {
        bool s = Compare_dec::le_lt_dec(a1, a2);
        if (s) {
          return Sig<std::shared_ptr<List<unsigned int>>>::exist(
              List<unsigned int>::cons(
                  a1, List<unsigned int>::cons(a2, List<unsigned int>::nil())));
        } else {
          return Sig<std::shared_ptr<List<unsigned int>>>::exist(
              List<unsigned int>::cons(
                  a2, List<unsigned int>::cons(a1, List<unsigned int>::nil())));
        }
      },
      [](unsigned int a1, unsigned int a2,
         std::shared_ptr<List<unsigned int>> l,
         std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>> x,
         std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>> x0) {
        return std::visit(
            Overloaded{[&](const typename Sig<
                           std::shared_ptr<List<unsigned int>>>::Exist _args)
                           -> std::shared_ptr<
                               Sig<std::shared_ptr<List<unsigned int>>>> {
              return std::visit(
                  Overloaded{
                      [&](const typename Sig<
                          std::shared_ptr<List<unsigned int>>>::Exist _args0)
                          -> std::shared_ptr<
                              Sig<std::shared_ptr<List<unsigned int>>>> {
                        return pair_merge_prog(a1, a2, l, _args0.d_x,
                                               _args.d_x);
                      }},
                  x0->v());
            }},
            x->v());
      },
      _x0);
}

std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>>
Sort::qsort(const std::shared_ptr<List<unsigned int>> &_x0) {
  return div_conq_pivot(
      Compare_dec::le_dec,
      Sig<std::shared_ptr<List<unsigned int>>>::exist(
          List<unsigned int>::nil()),
      [](unsigned int a, std::shared_ptr<List<unsigned int>>,
         std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>> x,
         std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>> x0) {
        return std::visit(
            Overloaded{[&](const typename Sig<
                           std::shared_ptr<List<unsigned int>>>::Exist _args)
                           -> std::shared_ptr<
                               Sig<std::shared_ptr<List<unsigned int>>>> {
              return std::visit(
                  Overloaded{
                      [&](const typename Sig<
                          std::shared_ptr<List<unsigned int>>>::Exist _args0)
                          -> std::shared_ptr<
                              Sig<std::shared_ptr<List<unsigned int>>>> {
                        return Sig<std::shared_ptr<List<unsigned int>>>::exist(
                            merge(_args.d_x,
                                  List<unsigned int>::cons(a, _args0.d_x)));
                      }},
                  x0->v());
            }},
            x->v());
      },
      _x0);
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

__attribute__((pure)) bool Compare_dec::le_gt_dec(const unsigned int _x0,
                                                  const unsigned int _x1) {
  return Compare_dec::le_lt_dec(_x0, _x1);
}

__attribute__((pure)) bool Compare_dec::le_dec(const unsigned int n,
                                               const unsigned int m) {
  bool s = Compare_dec::le_gt_dec(n, m);
  if (s) {
    return true;
  } else {
    return false;
  }
}
