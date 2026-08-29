#include "deep_patterns.h"

uint64_t DeepPatterns::deep_option(
    const std::optional<std::optional<std::optional<uint64_t>>> &x) {
  if (x.has_value()) {
    const std::optional<std::optional<uint64_t>> &o = *x;
    if (o.has_value()) {
      const std::optional<uint64_t> &o0 = *o;
      if (o0.has_value()) {
        const uint64_t &n = *o0;
        return n;
      } else {
        return UINT64_C(1);
      }
    } else {
      return UINT64_C(2);
    }
  } else {
    return UINT64_C(3);
  }
}

uint64_t
DeepPatterns::deep_pair(const std::pair<std::pair<uint64_t, uint64_t>,
                                        std::pair<uint64_t, uint64_t>> &p) {
  const auto &[p0, p1] = p;
  const auto &[a, b] = p0;
  const auto &[c, d] = p1;
  return (((a + b) + c) + d);
}

uint64_t DeepPatterns::list_shape(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    auto &&_sv0 = *a1;
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
      return a0;
    } else {
      const auto &[a00, a10] =
          std::get<typename List<uint64_t>::Cons>(_sv0.v());
      auto &&_sv1 = *a10;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv1.v())) {
        return (a0 + a00);
      } else {
        const auto &[a01, a11] =
            std::get<typename List<uint64_t>::Cons>(_sv1.v());
        auto &&_sv2 = *a11;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv2.v())) {
          return ((a0 + a00) + a01);
        } else {
          const auto &[a02, a12] =
              std::get<typename List<uint64_t>::Cons>(_sv2.v());
          return (((a0 + a00) + a01) + a12->length());
        }
      }
    }
  }
}

uint64_t DeepPatterns::deep_sum(const DeepPatterns::outer &o) {
  if (std::holds_alternative<typename DeepPatterns::outer::OLeft>(o.v())) {
    const auto &[a0] = std::get<typename DeepPatterns::outer::OLeft>(o.v());
    auto &&_sv0 = *a0;
    if (std::holds_alternative<typename DeepPatterns::inner::ILeft>(_sv0.v())) {
      const auto &[a00] =
          std::get<typename DeepPatterns::inner::ILeft>(_sv0.v());
      return a00;
    } else {
      const auto &[a00] =
          std::get<typename DeepPatterns::inner::IRight>(_sv0.v());
      if (a00) {
        return UINT64_C(1);
      } else {
        return UINT64_C(0);
      }
    }
  } else {
    const auto &[a0] = std::get<typename DeepPatterns::outer::ORight>(o.v());
    return (a0 + UINT64_C(100));
  }
}

uint64_t DeepPatterns::complex_match(
    const std::optional<std::pair<uint64_t, List<uint64_t>>> &x) {
  if (x.has_value()) {
    const std::pair<uint64_t, List<uint64_t>> &p = *x;
    const auto &[n, l] = p;
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
      return n;
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
        return (n + a0);
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_sv0.v());
        return ((n + a0) + a10->length());
      }
    }
  } else {
    return UINT64_C(0);
  }
}

uint64_t DeepPatterns::guarded_match(const std::pair<uint64_t, uint64_t> &p) {
  const auto &[a, b] = p;
  if (a <= b) {
    return (((b - a) > b ? 0 : (b - a)));
  } else {
    return (((a - b) > a ? 0 : (a - b)));
  }
}

uint64_t DeepPatterns::match_pair_list(
    const DeepPatterns::mylist<DeepPatterns::pair<uint64_t, uint64_t>> &l) {
  if (std::holds_alternative<typename DeepPatterns::mylist<
          DeepPatterns::pair<uint64_t, uint64_t>>::Nil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] = std::get<typename DeepPatterns::mylist<
        DeepPatterns::pair<uint64_t, uint64_t>>::Cons>(l.v());
    const auto &[a00, a10] = a0;
    return a00;
  }
}

uint64_t DeepPatterns::match_two(const DeepPatterns::mylist<uint64_t> &l) {
  if (std::holds_alternative<typename DeepPatterns::mylist<uint64_t>::Nil>(
          l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename DeepPatterns::mylist<uint64_t>::Cons>(l.v());
    return a0;
  }
}

uint64_t DeepPatterns::match_triple(
    const DeepPatterns::mylist<
        DeepPatterns::mylist<DeepPatterns::mylist<uint64_t>>> &l) {
  if (std::holds_alternative<typename DeepPatterns::mylist<
          DeepPatterns::mylist<DeepPatterns::mylist<uint64_t>>>::Nil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] = std::get<typename DeepPatterns::mylist<
        DeepPatterns::mylist<DeepPatterns::mylist<uint64_t>>>::Cons>(l.v());
    if (std::holds_alternative<
            typename DeepPatterns::mylist<DeepPatterns::mylist<uint64_t>>::Nil>(
            a0.v())) {
      return UINT64_C(1);
    } else {
      const auto &[a00, a10] = std::get<
          typename DeepPatterns::mylist<DeepPatterns::mylist<uint64_t>>::Cons>(
          a0.v());
      if (std::holds_alternative<typename DeepPatterns::mylist<uint64_t>::Nil>(
              a00.v())) {
        return UINT64_C(2);
      } else {
        const auto &[a01, a11] =
            std::get<typename DeepPatterns::mylist<uint64_t>::Cons>(a00.v());
        return a01;
      }
    }
  }
}

uint64_t DeepPatterns::deep_wildcard(
    const DeepPatterns::pair<DeepPatterns::pair<uint64_t, uint64_t>,
                             DeepPatterns::pair<uint64_t, uint64_t>> &p) {
  const auto &[a0, a1] = p;
  const auto &[a00, a10] = a0;
  return a00;
}
