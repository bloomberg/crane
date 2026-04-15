#include <pendant_sumtree_roundtrip.h>

#include <algorithm>
#include <functional>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
PendantSumtreeRoundtripCase::digit_to_nat(const std::shared_ptr<T> &d) {
  auto &&_sv = d->to_nat(10u);
  const auto &_m = *std::get_if<typename Sig<unsigned int>::Exist>(&_sv->v());
  return _m.d_x;
}

__attribute__((pure)) PendantSumtreeRoundtripCase::digit
PendantSumtreeRoundtripCase::digit_of_nat(const unsigned int n) {
  return Fin::of_nat_lt(n, 10u);
}

__attribute__((pure)) unsigned int PendantSumtreeRoundtripCase::value_digits(
    const unsigned int, const std::shared_ptr<T0<std::shared_ptr<T>>> &ds) {
  if (std::holds_alternative<typename T0<std::shared_ptr<T>>::Nil>(ds->v())) {
    return 0u;
  } else {
    const auto &_m =
        *std::get_if<typename T0<std::shared_ptr<T>>::Cons>(&ds->v());
    return (digit_to_nat(_m.d_h) + (10u * value_digits(_m.d_n, _m.d_a2)));
  }
}

__attribute__((pure))
std::optional<std::shared_ptr<T0<PendantSumtreeRoundtripCase::digit>>>
PendantSumtreeRoundtripCase::list_to_vector_opt(
    const unsigned int n, const std::shared_ptr<List<std::shared_ptr<T>>> &xs) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<std::shared_ptr<T>>::Nil0>(
            xs->v())) {
      return std::make_optional<std::shared_ptr<T0<std::shared_ptr<T>>>>(
          T0<std::shared_ptr<T>>::nil());
    } else {
      return std::optional<std::shared_ptr<T0<std::shared_ptr<T>>>>();
    }
  } else {
    unsigned int n_ = n - 1;
    if (std::holds_alternative<typename List<std::shared_ptr<T>>::Nil0>(
            xs->v())) {
      return std::optional<std::shared_ptr<T0<std::shared_ptr<T>>>>();
    } else {
      const auto &_m0 =
          *std::get_if<typename List<std::shared_ptr<T>>::Cons0>(&xs->v());
      auto _cs = list_to_vector_opt(n_, _m0.d_a1);
      if (_cs.has_value()) {
        const std::shared_ptr<T0<std::shared_ptr<T>>> &v = *_cs;
        return std::make_optional<std::shared_ptr<T0<std::shared_ptr<T>>>>(
            T0<std::shared_ptr<T>>::cons(_m0.d_a0, n_, v));
      } else {
        return std::optional<std::shared_ptr<T0<std::shared_ptr<T>>>>();
      }
    }
  }
}

std::shared_ptr<List<std::shared_ptr<List<PendantSumtreeRoundtripCase::digit>>>>
PendantSumtreeRoundtripCase::encode_multi(
    const unsigned int n,
    const std::shared_ptr<List<std::shared_ptr<T0<std::shared_ptr<T>>>>>
        &nums) {
  return nums
      ->template map<std::shared_ptr<List<PendantSumtreeRoundtripCase::digit>>>(
          [=](const std::shared_ptr<T0<PendantSumtreeRoundtripCase::digit>>
                  &_x0) mutable
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
          [=](const std::shared_ptr<List<PendantSumtreeRoundtripCase::digit>>
                  &_x0) mutable
              -> std::optional<
                  std::shared_ptr<T0<PendantSumtreeRoundtripCase::digit>>> {
            return list_to_vector_opt(n, _x0);
          });
  return std::move(decoded)
      ->template fold_right<std::optional<std::shared_ptr<
          List<std::shared_ptr<T0<PendantSumtreeRoundtripCase::digit>>>>>>(
          [](const std::optional<std::shared_ptr<T0<std::shared_ptr<T>>>> ov,
             const std::optional<
                 std::shared_ptr<List<std::shared_ptr<T0<std::shared_ptr<T>>>>>>
                 acc) {
            if (ov.has_value()) {
              const std::shared_ptr<T0<std::shared_ptr<T>>> &v = *ov;
              if (acc.has_value()) {
                const std::shared_ptr<
                    List<std::shared_ptr<T0<std::shared_ptr<T>>>>> &vs = *acc;
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
    const std::shared_ptr<PendantSumtreeRoundtripCase::CertifiedPendant> &p) {
  auto _cs = decode_multi(
      n, encode_multi(
             n, List<std::shared_ptr<T0<std::shared_ptr<T>>>>::cons0(
                    p->cp_digits,
                    List<std::shared_ptr<T0<std::shared_ptr<T>>>>::nil0())));
  if (_cs.has_value()) {
    const std::shared_ptr<List<std::shared_ptr<T0<std::shared_ptr<T>>>>> &l =
        *_cs;
    if (std::holds_alternative<
            typename List<std::shared_ptr<T0<std::shared_ptr<T>>>>::Nil0>(
            l->v())) {
      return std::optional<std::shared_ptr<T0<std::shared_ptr<T>>>>();
    } else {
      const auto &_m = *std::get_if<
          typename List<std::shared_ptr<T0<std::shared_ptr<T>>>>::Cons0>(
          &l->v());
      auto &&_sv = _m.d_a1;
      if (std::holds_alternative<
              typename List<std::shared_ptr<T0<std::shared_ptr<T>>>>::Nil0>(
              _sv->v())) {
        return std::make_optional<std::shared_ptr<T0<std::shared_ptr<T>>>>(
            _m.d_a0);
      } else {
        return std::optional<std::shared_ptr<T0<std::shared_ptr<T>>>>();
      }
    }
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
      [=](const std::shared_ptr<T0<PendantSumtreeRoundtripCase::digit>>
              &_x0) mutable -> unsigned int { return value_digits(n, _x0); },
      pendant_digits(n, p));
}

std::shared_ptr<List<std::optional<unsigned int>>>
PendantSumtreeRoundtripCase::ledger_values(
    const std::shared_ptr<List<std::shared_ptr<
        SigT<unsigned int,
             std::shared_ptr<PendantSumtreeRoundtripCase::CertifiedPendant>>>>>
        &l) {
  if (std::holds_alternative<typename List<std::shared_ptr<
          SigT<unsigned int, std::shared_ptr<PendantSumtreeRoundtripCase::
                                                 CertifiedPendant>>>>::Nil0>(
          l->v())) {
    return List<std::optional<unsigned int>>::nil0();
  } else {
    const auto &_m = *std::get_if<typename List<std::shared_ptr<
        SigT<unsigned int,
             std::shared_ptr<PendantSumtreeRoundtripCase::CertifiedPendant>>>>::
                                      Cons0>(&l->v());
    auto &&_sv0 = _m.d_a0;
    const auto &_m0 = *std::get_if<typename SigT<
        unsigned int,
        std::shared_ptr<PendantSumtreeRoundtripCase::CertifiedPendant>>::
                                       ExistT>(&_sv0->v());
    return List<std::optional<unsigned int>>::cons0(
        pendant_value(_m0.d_x, _m0.d_a1), ledger_values(_m.d_a1));
  }
}

__attribute__((pure)) bool PendantSumtreeRoundtripCase::group_sums_validb(
    const unsigned int n,
    const std::shared_ptr<PendantSumtreeRoundtripCase::PendantGroup> &g) {
  auto _cs = pendant_value(n, g->pg_top);
  if (_cs.has_value()) {
    const unsigned int &top_val = *_cs;
    std::shared_ptr<List<std::optional<unsigned int>>> pendant_vals =
        g->pg_pendants->template map<std::optional<unsigned int>>(
            [=](const std::shared_ptr<
                PendantSumtreeRoundtripCase::CertifiedPendant> &_x0) mutable
                -> std::optional<unsigned int> {
              return pendant_value(n, _x0);
            });
    std::optional<unsigned int> sum_opt =
        std::move(pendant_vals)
            ->template fold_right<std::optional<unsigned int>>(
                [](const std::optional<unsigned int> ov,
                   const std::optional<unsigned int> acc) {
                  if (ov.has_value()) {
                    const unsigned int &v = *ov;
                    if (acc.has_value()) {
                      const unsigned int &a = *acc;
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
      const unsigned int &s = *sum_opt;
      return top_val == s;
    } else {
      return false;
    }
  } else {
    return false;
  }
}

std::shared_ptr<PendantSumtreeRoundtripCase::CertifiedPendant>
PendantSumtreeRoundtripCase::sumtree_top(
    const unsigned int,
    const std::shared_ptr<PendantSumtreeRoundtripCase::SumTree> &st) {
  if (std::holds_alternative<
          typename PendantSumtreeRoundtripCase::SumTree::SumLeaf>(st->v())) {
    const auto &_m =
        *std::get_if<typename PendantSumtreeRoundtripCase::SumTree::SumLeaf>(
            &st->v());
    return _m.d_a0;
  } else {
    const auto &_m =
        *std::get_if<typename PendantSumtreeRoundtripCase::SumTree::SumNode>(
            &st->v());
    return _m.d_a0;
  }
}

std::shared_ptr<
    List<std::shared_ptr<PendantSumtreeRoundtripCase::CertifiedPendant>>>
PendantSumtreeRoundtripCase::sumtree_leaves(
    const unsigned int n,
    const std::shared_ptr<PendantSumtreeRoundtripCase::SumTree> &st) {
  if (std::holds_alternative<
          typename PendantSumtreeRoundtripCase::SumTree::SumLeaf>(st->v())) {
    const auto &_m =
        *std::get_if<typename PendantSumtreeRoundtripCase::SumTree::SumLeaf>(
            &st->v());
    return List<
        std::shared_ptr<PendantSumtreeRoundtripCase::CertifiedPendant>>::
        cons0(_m.d_a0,
              List<std::shared_ptr<
                  PendantSumtreeRoundtripCase::CertifiedPendant>>::nil0());
  } else {
    const auto &_m =
        *std::get_if<typename PendantSumtreeRoundtripCase::SumTree::SumNode>(
            &st->v());
    return _m.d_a1
        ->template map<std::shared_ptr<List<
            std::shared_ptr<PendantSumtreeRoundtripCase::CertifiedPendant>>>>(
            [=](const std::shared_ptr<PendantSumtreeRoundtripCase::SumTree>
                    &_x0) mutable
                -> std::shared_ptr<List<std::shared_ptr<
                    PendantSumtreeRoundtripCase::CertifiedPendant>>> {
              return sumtree_leaves(n, _x0);
            })
        ->template concat<
            std::shared_ptr<PendantSumtreeRoundtripCase::CertifiedPendant>>();
  }
}

__attribute__((pure)) unsigned int PendantSumtreeRoundtripCase::sumtree_depth(
    const unsigned int n,
    const std::shared_ptr<PendantSumtreeRoundtripCase::SumTree> &st) {
  if (std::holds_alternative<
          typename PendantSumtreeRoundtripCase::SumTree::SumLeaf>(st->v())) {
    return 1u;
  } else {
    const auto &_m =
        *std::get_if<typename PendantSumtreeRoundtripCase::SumTree::SumNode>(
            &st->v());
    return (
        _m.d_a1
            ->template map<unsigned int>(
                [=](const std::shared_ptr<PendantSumtreeRoundtripCase::SumTree>
                        &_x0) mutable -> unsigned int {
                  return sumtree_depth(n, _x0);
                })
            ->template fold_right<unsigned int>(
                [](unsigned int _x0, unsigned int _x1) -> unsigned int {
                  return std::max(_x0, _x1);
                },
                0u) +
        1);
  }
}

__attribute__((pure)) bool PendantSumtreeRoundtripCase::sumtree_validb_aux(
    const unsigned int n, const unsigned int fuel,
    const std::shared_ptr<PendantSumtreeRoundtripCase::SumTree> &st) {
  if (fuel <= 0) {
    return true;
  } else {
    unsigned int fuel_ = fuel - 1;
    if (std::holds_alternative<
            typename PendantSumtreeRoundtripCase::SumTree::SumLeaf>(st->v())) {
      return true;
    } else {
      const auto &_m =
          *std::get_if<typename PendantSumtreeRoundtripCase::SumTree::SumNode>(
              &st->v());
      std::shared_ptr<
          List<std::shared_ptr<PendantSumtreeRoundtripCase::CertifiedPendant>>>
          child_tops = _m.d_a1->template map<
              std::shared_ptr<PendantSumtreeRoundtripCase::CertifiedPendant>>(
              [=](const std::shared_ptr<PendantSumtreeRoundtripCase::SumTree>
                      &_x0) mutable
                  -> std::shared_ptr<
                      PendantSumtreeRoundtripCase::CertifiedPendant> {
                return sumtree_top(n, _x0);
              });
      std::shared_ptr<PendantSumtreeRoundtripCase::PendantGroup> g =
          std::make_shared<PendantSumtreeRoundtripCase::PendantGroup>(
              PendantGroup{_m.d_a0, child_tops});
      return (
          group_sums_validb(n, std::move(g)) &&
          _m.d_a1->forallb(
              [=](const std::shared_ptr<PendantSumtreeRoundtripCase::SumTree>
                      &_x0) mutable -> bool {
                return sumtree_validb_aux(n, fuel_, _x0);
              }));
    }
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
          [=](const std::shared_ptr<
              PendantSumtreeRoundtripCase::CertifiedPendant> &_x0) mutable
              -> std::optional<unsigned int> { return pendant_value(n, _x0); });
  return std::move(vals)->template fold_right<std::optional<unsigned int>>(
      [](const std::optional<unsigned int> ov,
         const std::optional<unsigned int> acc) {
        if (ov.has_value()) {
          const unsigned int &v = *ov;
          if (acc.has_value()) {
            const unsigned int &a = *acc;
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
  if (std::holds_alternative<typename List<unsigned int>::Nil0>(xs->v())) {
    if (std::holds_alternative<typename List<unsigned int>::Nil0>(ys->v())) {
      return true;
    } else {
      return false;
    }
  } else {
    const auto &_m = *std::get_if<typename List<unsigned int>::Cons0>(&xs->v());
    if (std::holds_alternative<typename List<unsigned int>::Nil0>(ys->v())) {
      return false;
    } else {
      const auto &_m0 =
          *std::get_if<typename List<unsigned int>::Cons0>(&ys->v());
      return (_m.d_a0 == _m0.d_a0 && nat_list_eqb(_m.d_a1, _m0.d_a1));
    }
  }
}

__attribute__((pure)) bool PendantSumtreeRoundtripCase::option_nat_eqb(
    const std::optional<unsigned int> x, const std::optional<unsigned int> y) {
  if (x.has_value()) {
    const unsigned int &a = *x;
    if (y.has_value()) {
      const unsigned int &b = *y;
      return a == b;
    } else {
      return false;
    }
  } else {
    if (y.has_value()) {
      const unsigned int &_x = *y;
      return false;
    } else {
      return true;
    }
  }
}

__attribute__((pure)) bool PendantSumtreeRoundtripCase::option_nat_is_some(
    const std::optional<unsigned int> x) {
  if (x.has_value()) {
    const unsigned int &_x = *x;
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
