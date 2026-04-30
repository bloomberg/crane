#include <pendant_sumtree_roundtrip.h>

unsigned int PendantSumtreeRoundtripCase::digit_to_nat(const T &d) {
  auto &&_sv = d.to_nat(10u);
  const auto &[d_x] = std::get<typename Sig<unsigned int>::Exist>(_sv.v());
  return d_x;
}

PendantSumtreeRoundtripCase::digit
PendantSumtreeRoundtripCase::digit_of_nat(const unsigned int &n) {
  return Fin::of_nat_lt(n, 10u);
}

unsigned int PendantSumtreeRoundtripCase::value_digits(const unsigned int &,
                                                       const T0<T> &ds) {
  if (std::holds_alternative<typename T0<T>::Nil>(ds.v())) {
    return 0u;
  } else {
    const auto &[d_h, d_n, d_a2] = std::get<typename T0<T>::Cons>(ds.v());
    return (digit_to_nat(d_h) + (10u * value_digits(d_n, *(d_a2))));
  }
}

std::optional<T0<PendantSumtreeRoundtripCase::digit>>
PendantSumtreeRoundtripCase::list_to_vector_opt(const unsigned int &n,
                                                const List<T> &xs) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<T>::Nil0>(xs.v())) {
      return std::make_optional<T0<T>>(T0<T>::nil());
    } else {
      return std::optional<T0<T>>();
    }
  } else {
    unsigned int n_ = n - 1;
    if (std::holds_alternative<typename List<T>::Nil0>(xs.v())) {
      return std::optional<T0<T>>();
    } else {
      const auto &[d_a00, d_a10] = std::get<typename List<T>::Cons0>(xs.v());
      auto _cs = list_to_vector_opt(n_, *(d_a10));
      if (_cs.has_value()) {
        const T0<T> &v = *_cs;
        return std::make_optional<T0<T>>(T0<T>::cons(d_a00, n_, v));
      } else {
        return std::optional<T0<T>>();
      }
    }
  }
}

List<List<PendantSumtreeRoundtripCase::digit>>
PendantSumtreeRoundtripCase::encode_multi(unsigned int n,
                                          const List<T0<T>> &nums) {
  return nums.template map<List<PendantSumtreeRoundtripCase::digit>>(
      [=](T0<PendantSumtreeRoundtripCase::digit> _x0) mutable
          -> List<PendantSumtreeRoundtripCase::digit> {
        return Vector::template to_list<PendantSumtreeRoundtripCase::digit>(
            n, _x0);
      });
}

std::optional<List<T0<PendantSumtreeRoundtripCase::digit>>>
PendantSumtreeRoundtripCase::decode_multi(unsigned int n,
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
    const unsigned int &n,
    const PendantSumtreeRoundtripCase::CertifiedPendant &p) {
  auto _cs = decode_multi(
      n, encode_multi(n, List<T0<T>>::cons0(p.cp_digits, List<T0<T>>::nil0())));
  if (_cs.has_value()) {
    const List<T0<T>> &l = *_cs;
    if (std::holds_alternative<typename List<T0<T>>::Nil0>(l.v())) {
      return std::optional<T0<T>>();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T0<T>>::Cons0>(l.v());
      auto &&_sv = *(d_a1);
      if (std::holds_alternative<typename List<T0<T>>::Nil0>(_sv.v())) {
        return std::make_optional<T0<T>>(d_a0);
      } else {
        return std::optional<T0<T>>();
      }
    }
  } else {
    return std::optional<T0<T>>();
  }
}

std::optional<unsigned int> PendantSumtreeRoundtripCase::pendant_value(
    unsigned int n, const PendantSumtreeRoundtripCase::CertifiedPendant &p) {
  return Datatypes::template option_map<T0<PendantSumtreeRoundtripCase::digit>,
                                        unsigned int>(
      [=](T0<PendantSumtreeRoundtripCase::digit> _x0) mutable -> unsigned int {
        return value_digits(n, _x0);
      },
      pendant_digits(n, p));
}

List<std::optional<unsigned int>> PendantSumtreeRoundtripCase::ledger_values(
    const List<
        SigT<unsigned int, PendantSumtreeRoundtripCase::CertifiedPendant>> &l) {
  if (std::holds_alternative<typename List<SigT<
          unsigned int, PendantSumtreeRoundtripCase::CertifiedPendant>>::Nil0>(
          l.v())) {
    return List<std::optional<unsigned int>>::nil0();
  } else {
    const auto &[d_a0, d_a1] = std::get<typename List<SigT<
        unsigned int, PendantSumtreeRoundtripCase::CertifiedPendant>>::Cons0>(
        l.v());
    const auto &[d_x0, d_a10] = std::get<typename SigT<
        unsigned int, PendantSumtreeRoundtripCase::CertifiedPendant>::ExistT>(
        d_a0.v());
    return List<std::optional<unsigned int>>::cons0(pendant_value(d_x0, d_a10),
                                                    ledger_values(*(d_a1)));
  }
}

bool PendantSumtreeRoundtripCase::group_sums_validb(
    unsigned int n, const PendantSumtreeRoundtripCase::PendantGroup &g) {
  auto _cs = pendant_value(n, g.pg_top);
  if (_cs.has_value()) {
    const unsigned int &top_val = *_cs;
    List<std::optional<unsigned int>> pendant_vals =
        g.pg_pendants.template map<std::optional<unsigned int>>(
            [=](PendantSumtreeRoundtripCase::CertifiedPendant _x0) mutable
                -> std::optional<unsigned int> {
              return pendant_value(n, _x0);
            });
    std::optional<unsigned int> sum_opt =
        std::move(pendant_vals)
            .template fold_right<std::optional<unsigned int>>(
                [](const std::optional<unsigned int> &ov,
                   const std::optional<unsigned int> &acc) {
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

PendantSumtreeRoundtripCase::CertifiedPendant
PendantSumtreeRoundtripCase::sumtree_top(
    const unsigned int &, const PendantSumtreeRoundtripCase::SumTree &st) {
  if (std::holds_alternative<
          typename PendantSumtreeRoundtripCase::SumTree::SumLeaf>(st.v())) {
    const auto &[d_a0] =
        std::get<typename PendantSumtreeRoundtripCase::SumTree::SumLeaf>(
            st.v());
    return d_a0;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename PendantSumtreeRoundtripCase::SumTree::SumNode>(
            st.v());
    return d_a0;
  }
}

List<PendantSumtreeRoundtripCase::CertifiedPendant>
PendantSumtreeRoundtripCase::sumtree_leaves(
    unsigned int n, const PendantSumtreeRoundtripCase::SumTree &st) {
  if (std::holds_alternative<
          typename PendantSumtreeRoundtripCase::SumTree::SumLeaf>(st.v())) {
    const auto &[d_a0] =
        std::get<typename PendantSumtreeRoundtripCase::SumTree::SumLeaf>(
            st.v());
    return List<PendantSumtreeRoundtripCase::CertifiedPendant>::cons0(
        d_a0, List<PendantSumtreeRoundtripCase::CertifiedPendant>::nil0());
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename PendantSumtreeRoundtripCase::SumTree::SumNode>(
            st.v());
    List<PendantSumtreeRoundtripCase::SumTree> d_a1_value =
        List<PendantSumtreeRoundtripCase::SumTree>(*(d_a1));
    return d_a1_value
        .template map<List<PendantSumtreeRoundtripCase::CertifiedPendant>>(
            [=](PendantSumtreeRoundtripCase::SumTree _x0) mutable
                -> List<PendantSumtreeRoundtripCase::CertifiedPendant> {
              return sumtree_leaves(n, _x0);
            })
        .template concat<PendantSumtreeRoundtripCase::CertifiedPendant>();
  }
}

unsigned int PendantSumtreeRoundtripCase::sumtree_depth(
    unsigned int n, const PendantSumtreeRoundtripCase::SumTree &st) {
  if (std::holds_alternative<
          typename PendantSumtreeRoundtripCase::SumTree::SumLeaf>(st.v())) {
    return 1u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename PendantSumtreeRoundtripCase::SumTree::SumNode>(
            st.v());
    List<PendantSumtreeRoundtripCase::SumTree> d_a1_value =
        List<PendantSumtreeRoundtripCase::SumTree>(*(d_a1));
    return (d_a1_value
                .template map<unsigned int>(
                    [=](PendantSumtreeRoundtripCase::SumTree _x0) mutable
                        -> unsigned int { return sumtree_depth(n, _x0); })
                .template fold_right<unsigned int>(
                    [](unsigned int _x0, unsigned int _x1) -> unsigned int {
                      return std::max(_x0, _x1);
                    },
                    0u) +
            1);
  }
}

bool PendantSumtreeRoundtripCase::sumtree_validb_aux(
    unsigned int n, const unsigned int &fuel,
    const PendantSumtreeRoundtripCase::SumTree &st) {
  if (fuel <= 0) {
    return true;
  } else {
    unsigned int fuel_ = fuel - 1;
    if (std::holds_alternative<
            typename PendantSumtreeRoundtripCase::SumTree::SumLeaf>(st.v())) {
      return true;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename PendantSumtreeRoundtripCase::SumTree::SumNode>(
              st.v());
      List<PendantSumtreeRoundtripCase::SumTree> d_a1_value =
          List<PendantSumtreeRoundtripCase::SumTree>(*(d_a1));
      List<PendantSumtreeRoundtripCase::CertifiedPendant> child_tops =
          d_a1_value
              .template map<PendantSumtreeRoundtripCase::CertifiedPendant>(
                  [=](PendantSumtreeRoundtripCase::SumTree _x0) mutable
                      -> PendantSumtreeRoundtripCase::CertifiedPendant {
                    return sumtree_top(n, _x0);
                  });
      PendantSumtreeRoundtripCase::PendantGroup g =
          PendantGroup{d_a0, child_tops};
      return (
          group_sums_validb(n, std::move(g)) &&
          d_a1_value.forallb(
              [=](PendantSumtreeRoundtripCase::SumTree _x0) mutable -> bool {
                return sumtree_validb_aux(n, fuel_, _x0);
              }));
    }
  }
}

bool PendantSumtreeRoundtripCase::sumtree_validb(
    const unsigned int &n, const PendantSumtreeRoundtripCase::SumTree &st) {
  return sumtree_validb_aux(n, sumtree_depth(n, st), st);
}

std::optional<unsigned int> PendantSumtreeRoundtripCase::sumtree_leaf_total(
    unsigned int n, const PendantSumtreeRoundtripCase::SumTree &st) {
  List<std::optional<unsigned int>> vals =
      sumtree_leaves(n, st).template map<std::optional<unsigned int>>(
          [=](PendantSumtreeRoundtripCase::CertifiedPendant _x0) mutable
              -> std::optional<unsigned int> { return pendant_value(n, _x0); });
  return std::move(vals).template fold_right<std::optional<unsigned int>>(
      [](const std::optional<unsigned int> &ov,
         const std::optional<unsigned int> &acc) {
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

bool PendantSumtreeRoundtripCase::nat_list_eqb(const List<unsigned int> &xs,
                                               const List<unsigned int> &ys) {
  if (std::holds_alternative<typename List<unsigned int>::Nil0>(xs.v())) {
    if (std::holds_alternative<typename List<unsigned int>::Nil0>(ys.v())) {
      return true;
    } else {
      return false;
    }
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons0>(xs.v());
    if (std::holds_alternative<typename List<unsigned int>::Nil0>(ys.v())) {
      return false;
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename List<unsigned int>::Cons0>(ys.v());
      return (d_a0 == d_a00 && nat_list_eqb(*(d_a1), *(d_a10)));
    }
  }
}

bool PendantSumtreeRoundtripCase::option_nat_eqb(
    const std::optional<unsigned int> &x,
    const std::optional<unsigned int> &y) {
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

bool PendantSumtreeRoundtripCase::option_nat_is_some(
    const std::optional<unsigned int> &x) {
  if (x.has_value()) {
    const unsigned int &_x = *x;
    return true;
  } else {
    return false;
  }
}

T0<PendantSumtreeRoundtripCase::digit>
PendantSumtreeRoundtripCase::digit_vec1(T a) {
  return T0<T>::cons(std::move(a), 0u, T0<T>::nil());
}

T0<PendantSumtreeRoundtripCase::digit>
PendantSumtreeRoundtripCase::digit_vec3(T a, T b, T c) {
  return T0<T>::cons(std::move(a), 2u,
                     T0<T>::cons(std::move(b), 1u,
                                 T0<T>::cons(std::move(c), 0u, T0<T>::nil())));
}

T Fin::of_nat_lt(const unsigned int &p, const unsigned int &n) {
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
