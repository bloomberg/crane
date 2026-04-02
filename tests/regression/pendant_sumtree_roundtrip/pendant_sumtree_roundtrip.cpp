#include <pendant_sumtree_roundtrip.h>

#include <functional>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) bool PeanoNat::eqb(const unsigned int n,
                                         const unsigned int m) {
  if (n <= 0) {
    if (m <= 0) {
      return true;
    } else {
      unsigned int _x = m - 1;
      return false;
    }
  } else {
    unsigned int n_ = n - 1;
    if (m <= 0) {
      return false;
    } else {
      unsigned int m_ = m - 1;
      return PeanoNat::eqb(n_, m_);
    }
  }
}

__attribute__((pure)) unsigned int PeanoNat::max(const unsigned int n,
                                                 const unsigned int m) {
  if (n <= 0) {
    return std::move(m);
  } else {
    unsigned int n_ = n - 1;
    if (m <= 0) {
      return n;
    } else {
      unsigned int m_ = m - 1;
      return (PeanoNat::max(n_, m_) + 1);
    }
  }
}

__attribute__((pure)) unsigned int
PendantSumtreeRoundtripCase::digit_to_nat(const std::shared_ptr<T> &d) {
  return std::visit(
      Overloaded{[](const typename Sig<unsigned int>::Exist _args) -> auto {
        return _args.d_x;
      }},
      d->to_nat(10u)->v());
}

__attribute__((pure)) PendantSumtreeRoundtripCase::digit
PendantSumtreeRoundtripCase::digit_of_nat(const unsigned int n) {
  return Fin::of_nat_lt(n, 10u);
}

__attribute__((pure)) unsigned int PendantSumtreeRoundtripCase::value_digits(
    const unsigned int _x, const std::shared_ptr<T0<std::shared_ptr<T>>> &ds) {
  return std::visit(
      Overloaded{[](const typename T0<std::shared_ptr<T>>::Nil _args)
                     -> unsigned int { return 0u; },
                 [](const typename T0<std::shared_ptr<T>>::Cons _args)
                     -> unsigned int {
                   return (digit_to_nat(_args.d_h) +
                           (10u * value_digits(_args.d_n, _args.d_a2)));
                 }},
      ds->v());
}

__attribute__((pure))
std::optional<std::shared_ptr<T0<PendantSumtreeRoundtripCase::digit>>>
PendantSumtreeRoundtripCase::list_to_vector_opt(
    const unsigned int n, const std::shared_ptr<List<std::shared_ptr<T>>> &xs) {
  if (n <= 0) {
    return std::visit(
        Overloaded{
            [](const typename List<std::shared_ptr<T>>::Nil0 _args)
                -> std::optional<std::shared_ptr<T0<std::shared_ptr<T>>>> {
              return std::make_optional<
                  std::shared_ptr<T0<std::shared_ptr<T>>>>(
                  T0<std::shared_ptr<T>>::nil());
            },
            [](const typename List<std::shared_ptr<T>>::Cons0 _args)
                -> std::optional<std::shared_ptr<T0<std::shared_ptr<T>>>> {
              return std::optional<std::shared_ptr<T0<std::shared_ptr<T>>>>();
            }},
        xs->v());
  } else {
    unsigned int n_ = n - 1;
    return std::visit(
        Overloaded{
            [](const typename List<std::shared_ptr<T>>::Nil0 _args0)
                -> std::optional<std::shared_ptr<T0<std::shared_ptr<T>>>> {
              return std::optional<std::shared_ptr<T0<std::shared_ptr<T>>>>();
            },
            [&](const typename List<std::shared_ptr<T>>::Cons0 _args0)
                -> std::optional<std::shared_ptr<T0<std::shared_ptr<T>>>> {
              if (list_to_vector_opt(n_, _args0.d_a1).has_value()) {
                std::shared_ptr<T0<std::shared_ptr<T>>> v =
                    *list_to_vector_opt(n_, _args0.d_a1);
                return std::make_optional<
                    std::shared_ptr<T0<std::shared_ptr<T>>>>(
                    T0<std::shared_ptr<T>>::cons(_args0.d_a0, n_, v));
              } else {
                return std::optional<std::shared_ptr<T0<std::shared_ptr<T>>>>();
              }
            }},
        xs->v());
  }
}

std::shared_ptr<List<std::shared_ptr<List<PendantSumtreeRoundtripCase::digit>>>>
PendantSumtreeRoundtripCase::encode_multi(
    const unsigned int n,
    const std::shared_ptr<List<std::shared_ptr<T0<std::shared_ptr<T>>>>>
        &nums) {
  return nums->template map<
      std::shared_ptr<List<PendantSumtreeRoundtripCase::digit>>>(
      [&](const std::shared_ptr<T0<PendantSumtreeRoundtripCase::digit>> &_x0)
          -> std::shared_ptr<List<PendantSumtreeRoundtripCase::digit>> {
        return Vector::template to_list<PendantSumtreeRoundtripCase::digit>(
            n, _x0);
      });
}

__attribute__((pure)) std::optional<std::shared_ptr<
    List<std::shared_ptr<T0<PendantSumtreeRoundtripCase::digit>>>>>
PendantSumtreeRoundtripCase::decode_multi(
    const unsigned int n,
    const std::shared_ptr<List<std::shared_ptr<List<std::shared_ptr<T>>>>>
        &segments) {
  std::shared_ptr<List<std::optional<std::shared_ptr<T0<std::shared_ptr<T>>>>>>
      decoded = segments->template map<std::optional<
          std::shared_ptr<T0<PendantSumtreeRoundtripCase::digit>>>>(
          [&](const std::shared_ptr<List<PendantSumtreeRoundtripCase::digit>>
                  &_x0)
              -> std::optional<
                  std::shared_ptr<T0<PendantSumtreeRoundtripCase::digit>>> {
            return list_to_vector_opt(n, _x0);
          });
  return std::move(decoded)
      ->template fold_right<std::optional<std::shared_ptr<
          List<std::shared_ptr<T0<PendantSumtreeRoundtripCase::digit>>>>>>(
          [](std::optional<std::shared_ptr<T0<std::shared_ptr<T>>>> ov,
             std::optional<
                 std::shared_ptr<List<std::shared_ptr<T0<std::shared_ptr<T>>>>>>
                 acc) {
            if (ov.has_value()) {
              std::shared_ptr<T0<std::shared_ptr<T>>> v = *ov;
              if (acc.has_value()) {
                std::shared_ptr<List<std::shared_ptr<T0<std::shared_ptr<T>>>>>
                    vs = *acc;
                return std::make_optional<std::shared_ptr<
                    List<std::shared_ptr<T0<std::shared_ptr<T>>>>>>(
                    List<std::shared_ptr<T0<std::shared_ptr<T>>>>::cons0(v,
                                                                         vs));
              } else {
                return std::optional<std::shared_ptr<
                    List<std::shared_ptr<T0<std::shared_ptr<T>>>>>>();
              }
            } else {
              return std::optional<std::shared_ptr<
                  List<std::shared_ptr<T0<std::shared_ptr<T>>>>>>();
            }
          },
          std::make_optional<
              std::shared_ptr<List<std::shared_ptr<T0<std::shared_ptr<T>>>>>>(
              List<std::shared_ptr<T0<std::shared_ptr<T>>>>::nil0()));
}

__attribute__((pure))
std::optional<std::shared_ptr<T0<PendantSumtreeRoundtripCase::digit>>>
PendantSumtreeRoundtripCase::pendant_digits(
    const unsigned int n,
    std::shared_ptr<PendantSumtreeRoundtripCase::CertifiedPendant> p) {
  if (decode_multi(
          n, encode_multi(
                 n, List<std::shared_ptr<T0<std::shared_ptr<T>>>>::cons0(
                        p->cp_digits,
                        List<std::shared_ptr<T0<std::shared_ptr<T>>>>::nil0())))
          .has_value()) {
    std::shared_ptr<List<std::shared_ptr<T0<std::shared_ptr<T>>>>> l =
        *decode_multi(
            n,
            encode_multi(
                n, List<std::shared_ptr<T0<std::shared_ptr<T>>>>::cons0(
                       p->cp_digits,
                       List<std::shared_ptr<T0<std::shared_ptr<T>>>>::nil0())));
    return std::visit(
        Overloaded{
            [](const typename List<
                std::shared_ptr<T0<std::shared_ptr<T>>>>::Nil0 _args)
                -> std::optional<std::shared_ptr<T0<std::shared_ptr<T>>>> {
              return std::optional<std::shared_ptr<T0<std::shared_ptr<T>>>>();
            },
            [](const typename List<
                std::shared_ptr<T0<std::shared_ptr<T>>>>::Cons0 _args)
                -> std::optional<std::shared_ptr<T0<std::shared_ptr<T>>>> {
              return std::visit(
                  Overloaded{
                      [&](const typename List<
                          std::shared_ptr<T0<std::shared_ptr<T>>>>::Nil0 _args0)
                          -> std::optional<
                              std::shared_ptr<T0<std::shared_ptr<T>>>> {
                        return std::make_optional<
                            std::shared_ptr<T0<std::shared_ptr<T>>>>(
                            _args.d_a0);
                      },
                      [](const typename List<std::shared_ptr<
                             T0<std::shared_ptr<T>>>>::Cons0 _args0)
                          -> std::optional<
                              std::shared_ptr<T0<std::shared_ptr<T>>>> {
                        return std::optional<
                            std::shared_ptr<T0<std::shared_ptr<T>>>>();
                      }},
                  _args.d_a1->v());
            }},
        l->v());
  } else {
    return std::optional<std::shared_ptr<T0<std::shared_ptr<T>>>>();
  }
}

__attribute__((pure)) std::optional<unsigned int>
PendantSumtreeRoundtripCase::pendant_value(
    const unsigned int n,
    const std::shared_ptr<PendantSumtreeRoundtripCase::CertifiedPendant> &p) {
  return Datatypes::template option_map<
      std::shared_ptr<T0<PendantSumtreeRoundtripCase::digit>>, unsigned int>(
      [&](const std::shared_ptr<T0<PendantSumtreeRoundtripCase::digit>> &_x0)
          -> unsigned int { return value_digits(n, _x0); },
      pendant_digits(n, p));
}

std::shared_ptr<List<std::optional<unsigned int>>>
PendantSumtreeRoundtripCase::ledger_values(
    const std::shared_ptr<List<std::shared_ptr<
        SigT<unsigned int,
             std::shared_ptr<PendantSumtreeRoundtripCase::CertifiedPendant>>>>>
        &l) {
  return std::visit(
      Overloaded{
          [](const typename List<std::shared_ptr<SigT<
                 unsigned int, std::shared_ptr<PendantSumtreeRoundtripCase::
                                                   CertifiedPendant>>>>::Nil0
                 _args) -> std::shared_ptr<List<std::optional<unsigned int>>> {
            return List<std::optional<unsigned int>>::nil0();
          },
          [](const typename List<std::shared_ptr<SigT<
                 unsigned int, std::shared_ptr<PendantSumtreeRoundtripCase::
                                                   CertifiedPendant>>>>::Cons0
                 _args) -> std::shared_ptr<List<std::optional<unsigned int>>> {
            return std::visit(
                Overloaded{
                    [&](const typename SigT<
                        unsigned int,
                        std::shared_ptr<PendantSumtreeRoundtripCase::
                                            CertifiedPendant>>::ExistT _args0)
                        -> std::shared_ptr<List<std::optional<unsigned int>>> {
                      return List<std::optional<unsigned int>>::cons0(
                          pendant_value(_args0.d_x, _args0.d_a1),
                          ledger_values(_args.d_a1));
                    }},
                _args.d_a0->v());
          }},
      l->v());
}

__attribute__((pure)) bool PendantSumtreeRoundtripCase::group_sums_validb(
    const unsigned int n,
    const std::shared_ptr<PendantSumtreeRoundtripCase::PendantGroup> &g) {
  if (pendant_value(n, g->pg_top).has_value()) {
    unsigned int top_val = *pendant_value(n, g->pg_top);
    std::shared_ptr<List<std::optional<unsigned int>>> pendant_vals =
        g->pg_pendants->template map<std::optional<unsigned int>>(
            [&](const std::shared_ptr<
                PendantSumtreeRoundtripCase::CertifiedPendant> &_x0)
                -> std::optional<unsigned int> {
              return pendant_value(n, _x0);
            });
    std::optional<unsigned int> sum_opt =
        std::move(pendant_vals)
            ->template fold_right<std::optional<unsigned int>>(
                [](std::optional<unsigned int> ov,
                   std::optional<unsigned int> acc) {
                  if (ov.has_value()) {
                    unsigned int v = *ov;
                    if (acc.has_value()) {
                      unsigned int a = *acc;
                      return std::make_optional<unsigned int>((v + a));
                    } else {
                      return std::optional<unsigned int>();
                    }
                  } else {
                    return std::optional<unsigned int>();
                  }
                },
                std::make_optional<unsigned int>(0u));
    if (sum_opt.has_value()) {
      unsigned int s = *sum_opt;
      return PeanoNat::eqb(top_val, std::move(s));
    } else {
      return false;
    }
  } else {
    return false;
  }
}

std::shared_ptr<PendantSumtreeRoundtripCase::CertifiedPendant>
PendantSumtreeRoundtripCase::sumtree_top(
    const unsigned int _x,
    const std::shared_ptr<PendantSumtreeRoundtripCase::SumTree> &st) {
  return std::visit(
      Overloaded{
          [](const typename PendantSumtreeRoundtripCase::SumTree::SumLeaf _args)
              -> std::shared_ptr<
                  PendantSumtreeRoundtripCase::CertifiedPendant> {
            return _args.d_a0;
          },
          [](const typename PendantSumtreeRoundtripCase::SumTree::SumNode _args)
              -> std::shared_ptr<
                  PendantSumtreeRoundtripCase::CertifiedPendant> {
            return _args.d_a0;
          }},
      st->v());
}

std::shared_ptr<
    List<std::shared_ptr<PendantSumtreeRoundtripCase::CertifiedPendant>>>
PendantSumtreeRoundtripCase::sumtree_leaves(
    const unsigned int n,
    const std::shared_ptr<PendantSumtreeRoundtripCase::SumTree> &st) {
  return std::visit(
      Overloaded{
          [](const typename PendantSumtreeRoundtripCase::SumTree::SumLeaf _args)
              -> std::shared_ptr<List<std::shared_ptr<
                  PendantSumtreeRoundtripCase::CertifiedPendant>>> {
            return List<std::shared_ptr<
                PendantSumtreeRoundtripCase::CertifiedPendant>>::
                cons0(_args.d_a0,
                      List<std::shared_ptr<PendantSumtreeRoundtripCase::
                                               CertifiedPendant>>::nil0());
          },
          [&](const typename PendantSumtreeRoundtripCase::SumTree::SumNode
                  _args)
              -> std::shared_ptr<List<std::shared_ptr<
                  PendantSumtreeRoundtripCase::CertifiedPendant>>> {
            return _args.d_a1
                ->template map<std::shared_ptr<List<std::shared_ptr<
                    PendantSumtreeRoundtripCase::CertifiedPendant>>>>(
                    [&](const std::shared_ptr<
                        PendantSumtreeRoundtripCase::SumTree> &_x0)
                        -> std::shared_ptr<List<std::shared_ptr<
                            PendantSumtreeRoundtripCase::CertifiedPendant>>> {
                      return sumtree_leaves(n, _x0);
                    })
                ->template concat<std::shared_ptr<
                    PendantSumtreeRoundtripCase::CertifiedPendant>>();
          }},
      st->v());
}

__attribute__((pure)) unsigned int PendantSumtreeRoundtripCase::sumtree_depth(
    const unsigned int n,
    const std::shared_ptr<PendantSumtreeRoundtripCase::SumTree> &st) {
  return std::visit(
      Overloaded{
          [](const typename PendantSumtreeRoundtripCase::SumTree::SumLeaf _args)
              -> unsigned int { return 1u; },
          [&](const typename PendantSumtreeRoundtripCase::SumTree::SumNode
                  _args) -> unsigned int {
            return (
                _args.d_a1
                    ->template map<unsigned int>(
                        [&](const std::shared_ptr<
                            PendantSumtreeRoundtripCase::SumTree> &_x0)
                            -> unsigned int { return sumtree_depth(n, _x0); })
                    ->template fold_right<unsigned int>(PeanoNat::max, 0u) +
                1);
          }},
      st->v());
}

__attribute__((pure)) bool PendantSumtreeRoundtripCase::sumtree_validb_aux(
    const unsigned int n, const unsigned int fuel,
    const std::shared_ptr<PendantSumtreeRoundtripCase::SumTree> &st) {
  if (fuel <= 0) {
    return true;
  } else {
    unsigned int fuel_ = fuel - 1;
    return std::visit(
        Overloaded{
            [](const typename PendantSumtreeRoundtripCase::SumTree::SumLeaf
                   _args) -> bool { return true; },
            [&](const typename PendantSumtreeRoundtripCase::SumTree::SumNode
                    _args) -> bool {
              std::shared_ptr<List<std::shared_ptr<
                  PendantSumtreeRoundtripCase::CertifiedPendant>>>
                  child_tops = _args.d_a1->template map<std::shared_ptr<
                      PendantSumtreeRoundtripCase::CertifiedPendant>>(
                      [&](const std::shared_ptr<
                          PendantSumtreeRoundtripCase::SumTree> &_x0)
                          -> std::shared_ptr<
                              PendantSumtreeRoundtripCase::CertifiedPendant> {
                        return sumtree_top(n, _x0);
                      });
              std::unique_ptr<PendantSumtreeRoundtripCase::PendantGroup> g =
                  std::make_unique<PendantSumtreeRoundtripCase::PendantGroup>(
                      PendantGroup{_args.d_a0, child_tops});
              return (
                  group_sums_validb(n, std::move(g)) &&
                  _args.d_a1->forallb(
                      [&](const std::shared_ptr<
                          PendantSumtreeRoundtripCase::SumTree> &_x0) -> bool {
                        return sumtree_validb_aux(n, fuel_, _x0);
                      }));
            }},
        st->v());
  }
}

__attribute__((pure)) bool PendantSumtreeRoundtripCase::sumtree_validb(
    const unsigned int n,
    const std::shared_ptr<PendantSumtreeRoundtripCase::SumTree> &st) {
  return sumtree_validb_aux(n, sumtree_depth(n, st), st);
}

__attribute__((pure)) std::optional<unsigned int>
PendantSumtreeRoundtripCase::sumtree_leaf_total(
    const unsigned int n,
    const std::shared_ptr<PendantSumtreeRoundtripCase::SumTree> &st) {
  std::shared_ptr<List<std::optional<unsigned int>>> vals =
      sumtree_leaves(n, st)->template map<std::optional<unsigned int>>(
          [&](const std::shared_ptr<
              PendantSumtreeRoundtripCase::CertifiedPendant> &_x0)
              -> std::optional<unsigned int> { return pendant_value(n, _x0); });
  return std::move(vals)->template fold_right<std::optional<unsigned int>>(
      [](std::optional<unsigned int> ov, std::optional<unsigned int> acc) {
        if (ov.has_value()) {
          unsigned int v = *ov;
          if (acc.has_value()) {
            unsigned int a = *acc;
            return std::make_optional<unsigned int>((v + a));
          } else {
            return std::optional<unsigned int>();
          }
        } else {
          return std::optional<unsigned int>();
        }
      },
      std::make_optional<unsigned int>(0u));
}

__attribute__((pure)) bool PendantSumtreeRoundtripCase::nat_list_eqb(
    const std::shared_ptr<List<unsigned int>> &xs,
    const std::shared_ptr<List<unsigned int>> &ys) {
  return std::visit(
      Overloaded{
          [&](const typename List<unsigned int>::Nil0 _args) -> bool {
            return std::visit(
                Overloaded{[](const typename List<unsigned int>::Nil0 _args0)
                               -> bool { return true; },
                           [](const typename List<unsigned int>::Cons0 _args0)
                               -> bool { return false; }},
                ys->v());
          },
          [&](const typename List<unsigned int>::Cons0 _args) -> bool {
            return std::visit(
                Overloaded{[](const typename List<unsigned int>::Nil0 _args0)
                               -> bool { return false; },
                           [&](const typename List<unsigned int>::Cons0 _args0)
                               -> bool {
                             return (PeanoNat::eqb(_args.d_a0, _args0.d_a0) &&
                                     nat_list_eqb(_args.d_a1, _args0.d_a1));
                           }},
                ys->v());
          }},
      xs->v());
}

__attribute__((pure)) bool PendantSumtreeRoundtripCase::option_nat_eqb(
    const std::optional<unsigned int> x, const std::optional<unsigned int> y) {
  if (x.has_value()) {
    unsigned int a = *x;
    if (y.has_value()) {
      unsigned int b = *y;
      return PeanoNat::eqb(a, b);
    } else {
      return false;
    }
  } else {
    if (y.has_value()) {
      unsigned int _x = *y;
      return false;
    } else {
      return true;
    }
  }
}

__attribute__((pure)) bool PendantSumtreeRoundtripCase::option_nat_is_some(
    const std::optional<unsigned int> x) {
  if (x.has_value()) {
    unsigned int _x = *x;
    return true;
  } else {
    return false;
  }
}

std::shared_ptr<T0<PendantSumtreeRoundtripCase::digit>>
PendantSumtreeRoundtripCase::digit_vec1(std::shared_ptr<T> a) {
  return T0<std::shared_ptr<T>>::cons(a, 0u, T0<std::shared_ptr<T>>::nil());
}

std::shared_ptr<T0<PendantSumtreeRoundtripCase::digit>>
PendantSumtreeRoundtripCase::digit_vec3(std::shared_ptr<T> a,
                                        std::shared_ptr<T> b,
                                        std::shared_ptr<T> c) {
  return T0<std::shared_ptr<T>>::cons(
      a, 2u,
      T0<std::shared_ptr<T>>::cons(
          b, 1u,
          T0<std::shared_ptr<T>>::cons(c, 0u, T0<std::shared_ptr<T>>::nil())));
}

std::shared_ptr<T> Fin::of_nat_lt(const unsigned int p, const unsigned int n) {
  if (n <= 0) {
    throw std::logic_error("absurd case");
  } else {
    unsigned int n_ = n - 1;
    if (p <= 0) {
      return T::f1(n_);
    } else {
      unsigned int p_ = p - 1;
      return T::fs(n_, Fin::of_nat_lt(p_, n_));
    }
  }
}
