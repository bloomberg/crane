#include "pendant_sumtree_roundtrip.h"

uint64_t PendantSumtreeRoundtripCase::digit_to_nat(const T &d) {
  const auto &_sv = d.to_nat(UINT64_C(10));
  const auto &[x] = _sv;
  return x;
}

PendantSumtreeRoundtripCase::digit
PendantSumtreeRoundtripCase::digit_of_nat(uint64_t n) {
  return Fin::of_nat_lt(n, UINT64_C(10));
}

uint64_t PendantSumtreeRoundtripCase::value_digits(uint64_t, const T0<T> &ds) {
  if (std::holds_alternative<typename T0<T>::Nil>(ds.v())) {
    return UINT64_C(0);
  } else {
    const auto &[h, n, a2] = std::get<typename T0<T>::Cons>(ds.v());
    return (digit_to_nat(h) + (UINT64_C(10) * value_digits(n, *a2)));
  }
}

std::optional<T0<PendantSumtreeRoundtripCase::digit>>
PendantSumtreeRoundtripCase::list_to_vector_opt(uint64_t n, const List<T> &xs) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<T>::Nil0>(xs.v())) {
      return std::make_optional<T0<T>>(T0<T>::nil());
    } else {
      return std::optional<T0<T>>();
    }
  } else {
    uint64_t n_ = n - 1;
    if (std::holds_alternative<typename List<T>::Nil0>(xs.v())) {
      return std::optional<T0<T>>();
    } else {
      const auto &[a00, a10] = std::get<typename List<T>::Cons0>(xs.v());
      auto _cs = list_to_vector_opt(n_, *a10);
      if (_cs.has_value()) {
        const T0<T> &v = *_cs;
        return std::make_optional<T0<T>>(T0<T>::cons(a00, n_, v));
      } else {
        return std::optional<T0<T>>();
      }
    }
  }
}

List<List<PendantSumtreeRoundtripCase::digit>>
PendantSumtreeRoundtripCase::encode_multi(uint64_t n, const List<T0<T>> &nums) {
  return nums.template map<List<PendantSumtreeRoundtripCase::digit>>(
      [=](T0<PendantSumtreeRoundtripCase::digit> _x0) mutable
          -> List<PendantSumtreeRoundtripCase::digit> {
        return Vector::template to_list<PendantSumtreeRoundtripCase::digit>(
            n, _x0);
      });
}

std::optional<List<T0<PendantSumtreeRoundtripCase::digit>>>
PendantSumtreeRoundtripCase::decode_multi(uint64_t n,
                                          const List<List<T>> &segments) {
  List<std::optional<T0<T>>> decoded =
      segments
          .template map<std::optional<T0<PendantSumtreeRoundtripCase::digit>>>(
              [=](List<PendantSumtreeRoundtripCase::digit> _x0) mutable
                  -> std::optional<T0<PendantSumtreeRoundtripCase::digit>> {
                return list_to_vector_opt(n, _x0);
              });
  return std::move(decoded)
      .template fold_right<
          std::optional<List<T0<PendantSumtreeRoundtripCase::digit>>>>(
          [](const std::optional<T0<T>> &ov,
             const std::optional<List<T0<T>>> &acc) {
            if (ov.has_value()) {
              const T0<T> &v = *ov;
              if (acc.has_value()) {
                const List<T0<T>> &vs = *acc;
                return std::make_optional<List<T0<T>>>(
                    List<T0<T>>::cons0(v, vs));
              } else {
                return std::optional<List<T0<T>>>();
              }
            } else {
              return std::optional<List<T0<T>>>();
            }
          },
          std::make_optional<List<T0<T>>>(List<T0<T>>::nil0()));
}

std::optional<T0<PendantSumtreeRoundtripCase::digit>>
PendantSumtreeRoundtripCase::pendant_digits(
    uint64_t n, const PendantSumtreeRoundtripCase::CertifiedPendant &p) {
  auto _cs = decode_multi(
      n, encode_multi(n, List<T0<T>>::cons0(p.cp_digits, List<T0<T>>::nil0())));
  if (_cs.has_value()) {
    const List<T0<T>> &l = *_cs;
    if (std::holds_alternative<typename List<T0<T>>::Nil0>(l.v())) {
      return std::optional<T0<T>>();
    } else {
      const auto &[a0, a1] = std::get<typename List<T0<T>>::Cons0>(l.v());
      auto &&_sv = *a1;
      if (std::holds_alternative<typename List<T0<T>>::Nil0>(_sv.v())) {
        return std::make_optional<T0<T>>(a0);
      } else {
        return std::optional<T0<T>>();
      }
    }
  } else {
    return std::optional<T0<T>>();
  }
}

std::optional<uint64_t> PendantSumtreeRoundtripCase::pendant_value(
    uint64_t n, const PendantSumtreeRoundtripCase::CertifiedPendant &p) {
  return Datatypes::template option_map<T0<PendantSumtreeRoundtripCase::digit>,
                                        uint64_t>(
      [=](T0<PendantSumtreeRoundtripCase::digit> _x0) mutable -> uint64_t {
        return value_digits(n, _x0);
      },
      pendant_digits(n, p));
}

List<std::optional<uint64_t>> PendantSumtreeRoundtripCase::ledger_values(
    const List<SigT<uint64_t, PendantSumtreeRoundtripCase::CertifiedPendant>>
        &l) {
  if (std::holds_alternative<typename List<
          SigT<uint64_t, PendantSumtreeRoundtripCase::CertifiedPendant>>::Nil0>(
          l.v())) {
    return List<std::optional<uint64_t>>::nil0();
  } else {
    const auto &[a0, a1] = std::get<typename List<
        SigT<uint64_t, PendantSumtreeRoundtripCase::CertifiedPendant>>::Cons0>(
        l.v());
    const auto &[x0, a10] = a0;
    return List<std::optional<uint64_t>>::cons0(pendant_value(x0, a10),
                                                ledger_values(*a1));
  }
}

bool PendantSumtreeRoundtripCase::group_sums_validb(
    uint64_t n, const PendantSumtreeRoundtripCase::PendantGroup &g) {
  auto _cs = pendant_value(n, g.pg_top);
  if (_cs.has_value()) {
    const uint64_t &top_val = *_cs;
    List<std::optional<uint64_t>> pendant_vals =
        g.pg_pendants.template map<std::optional<uint64_t>>(
            [=](PendantSumtreeRoundtripCase::CertifiedPendant _x0) mutable
                -> std::optional<uint64_t> { return pendant_value(n, _x0); });
    std::optional<uint64_t> sum_opt =
        std::move(pendant_vals)
            .template fold_right<std::optional<uint64_t>>(
                [](const std::optional<uint64_t> &ov,
                   const std::optional<uint64_t> &acc) {
                  if (ov.has_value()) {
                    const uint64_t &v = *ov;
                    if (acc.has_value()) {
                      const uint64_t &a = *acc;
                      return std::make_optional<uint64_t>((v + a));
                    } else {
                      return std::optional<uint64_t>();
                    }
                  } else {
                    return std::optional<uint64_t>();
                  }
                },
                std::make_optional<uint64_t>(UINT64_C(0)));
    if (sum_opt.has_value()) {
      const uint64_t &s = *sum_opt;
      return top_val == s;
    } else {
      return false;
    }
  } else {
    return false;
  }
}

PendantSumtreeRoundtripCase::CertifiedPendant
PendantSumtreeRoundtripCase::sumtree_top(
    uint64_t, const PendantSumtreeRoundtripCase::SumTree &st) {
  if (std::holds_alternative<
          typename PendantSumtreeRoundtripCase::SumTree::SumLeaf>(st.v())) {
    const auto &[a0] =
        std::get<typename PendantSumtreeRoundtripCase::SumTree::SumLeaf>(
            st.v());
    return a0;
  } else {
    const auto &[a0, a1] =
        std::get<typename PendantSumtreeRoundtripCase::SumTree::SumNode>(
            st.v());
    return a0;
  }
}

List<PendantSumtreeRoundtripCase::CertifiedPendant>
PendantSumtreeRoundtripCase::sumtree_leaves(
    uint64_t n, const PendantSumtreeRoundtripCase::SumTree &st) {
  if (std::holds_alternative<
          typename PendantSumtreeRoundtripCase::SumTree::SumLeaf>(st.v())) {
    const auto &[a0] =
        std::get<typename PendantSumtreeRoundtripCase::SumTree::SumLeaf>(
            st.v());
    return List<PendantSumtreeRoundtripCase::CertifiedPendant>::cons0(
        a0, List<PendantSumtreeRoundtripCase::CertifiedPendant>::nil0());
  } else {
    const auto &[a0, a1] =
        std::get<typename PendantSumtreeRoundtripCase::SumTree::SumNode>(
            st.v());
    const List<PendantSumtreeRoundtripCase::SumTree> &a1_value = *a1;
    return a1_value
        .template map<List<PendantSumtreeRoundtripCase::CertifiedPendant>>(
            [=](PendantSumtreeRoundtripCase::SumTree _x0) mutable
                -> List<PendantSumtreeRoundtripCase::CertifiedPendant> {
              return sumtree_leaves(n, _x0);
            })
        .template concat<PendantSumtreeRoundtripCase::CertifiedPendant>();
  }
}

uint64_t PendantSumtreeRoundtripCase::sumtree_depth(
    uint64_t n, const PendantSumtreeRoundtripCase::SumTree &st) {
  if (std::holds_alternative<
          typename PendantSumtreeRoundtripCase::SumTree::SumLeaf>(st.v())) {
    return UINT64_C(1);
  } else {
    const auto &[a0, a1] =
        std::get<typename PendantSumtreeRoundtripCase::SumTree::SumNode>(
            st.v());
    const List<PendantSumtreeRoundtripCase::SumTree> &a1_value = *a1;
    return (a1_value
                .template map<uint64_t>(
                    [=](PendantSumtreeRoundtripCase::SumTree _x0) mutable
                        -> uint64_t { return sumtree_depth(n, _x0); })
                .template fold_right<uint64_t>(
                    [](uint64_t _x0, uint64_t _x1) -> uint64_t {
                      return std::max(_x0, _x1);
                    },
                    UINT64_C(0)) +
            1);
  }
}

bool PendantSumtreeRoundtripCase::sumtree_validb_aux(
    uint64_t n, uint64_t fuel, const PendantSumtreeRoundtripCase::SumTree &st) {
  if (fuel <= 0) {
    return true;
  } else {
    uint64_t fuel_ = fuel - 1;
    if (std::holds_alternative<
            typename PendantSumtreeRoundtripCase::SumTree::SumLeaf>(st.v())) {
      return true;
    } else {
      const auto &[a0, a1] =
          std::get<typename PendantSumtreeRoundtripCase::SumTree::SumNode>(
              st.v());
      const List<PendantSumtreeRoundtripCase::SumTree> &a1_value = *a1;
      List<PendantSumtreeRoundtripCase::CertifiedPendant> child_tops =
          a1_value.template map<PendantSumtreeRoundtripCase::CertifiedPendant>(
              [=](PendantSumtreeRoundtripCase::SumTree _x0) mutable
                  -> PendantSumtreeRoundtripCase::CertifiedPendant {
                return sumtree_top(n, _x0);
              });
      PendantSumtreeRoundtripCase::PendantGroup g =
          PendantGroup{a0, child_tops};
      return (
          group_sums_validb(n, std::move(g)) &&
          a1_value.forallb(
              [=](PendantSumtreeRoundtripCase::SumTree _x0) mutable -> bool {
                return sumtree_validb_aux(n, fuel_, _x0);
              }));
    }
  }
}

bool PendantSumtreeRoundtripCase::sumtree_validb(
    uint64_t n, const PendantSumtreeRoundtripCase::SumTree &st) {
  return sumtree_validb_aux(n, sumtree_depth(n, st), st);
}

std::optional<uint64_t> PendantSumtreeRoundtripCase::sumtree_leaf_total(
    uint64_t n, const PendantSumtreeRoundtripCase::SumTree &st) {
  List<std::optional<uint64_t>> vals =
      sumtree_leaves(n, st).template map<std::optional<uint64_t>>(
          [=](PendantSumtreeRoundtripCase::CertifiedPendant _x0) mutable
              -> std::optional<uint64_t> { return pendant_value(n, _x0); });
  return std::move(vals).template fold_right<std::optional<uint64_t>>(
      [](const std::optional<uint64_t> &ov,
         const std::optional<uint64_t> &acc) {
        if (ov.has_value()) {
          const uint64_t &v = *ov;
          if (acc.has_value()) {
            const uint64_t &a = *acc;
            return std::make_optional<uint64_t>((v + a));
          } else {
            return std::optional<uint64_t>();
          }
        } else {
          return std::optional<uint64_t>();
        }
      },
      std::make_optional<uint64_t>(UINT64_C(0)));
}

bool PendantSumtreeRoundtripCase::nat_list_eqb(const List<uint64_t> &xs,
                                               const List<uint64_t> &ys) {
  if (std::holds_alternative<typename List<uint64_t>::Nil0>(xs.v())) {
    if (std::holds_alternative<typename List<uint64_t>::Nil0>(ys.v())) {
      return true;
    } else {
      return false;
    }
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons0>(xs.v());
    if (std::holds_alternative<typename List<uint64_t>::Nil0>(ys.v())) {
      return false;
    } else {
      const auto &[a00, a10] = std::get<typename List<uint64_t>::Cons0>(ys.v());
      return (a0 == a00 && nat_list_eqb(*a1, *a10));
    }
  }
}

bool PendantSumtreeRoundtripCase::option_nat_eqb(
    const std::optional<uint64_t> &x, const std::optional<uint64_t> &y) {
  if (x.has_value()) {
    const uint64_t &a = *x;
    if (y.has_value()) {
      const uint64_t &b = *y;
      return a == b;
    } else {
      return false;
    }
  } else {
    if (y.has_value()) {
      const uint64_t &_x = *y;
      return false;
    } else {
      return true;
    }
  }
}

bool PendantSumtreeRoundtripCase::option_nat_is_some(
    const std::optional<uint64_t> &x) {
  if (x.has_value()) {
    const uint64_t &_x = *x;
    return true;
  } else {
    return false;
  }
}

T0<PendantSumtreeRoundtripCase::digit>
PendantSumtreeRoundtripCase::digit_vec1(T a) {
  return T0<T>::cons(std::move(a), UINT64_C(0), T0<T>::nil());
}

T0<PendantSumtreeRoundtripCase::digit>
PendantSumtreeRoundtripCase::digit_vec3(T a, T b, T c) {
  return T0<T>::cons(
      std::move(a), UINT64_C(2),
      T0<T>::cons(std::move(b), UINT64_C(1),
                  T0<T>::cons(std::move(c), UINT64_C(0), T0<T>::nil())));
}

T Fin::of_nat_lt(uint64_t p, uint64_t n) {
  if (n <= 0) {
    throw std::logic_error("absurd case");
  } else {
    uint64_t n_ = n - 1;
    if (p <= 0) {
      return T::f1(n_);
    } else {
      uint64_t p_ = p - 1;
      return T::fs(n_, Fin::of_nat_lt(p_, n_));
    }
  }
}
