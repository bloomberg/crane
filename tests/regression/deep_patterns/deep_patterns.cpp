#include "deep_patterns.h"

unsigned int DeepPatterns::deep_option(
    const std::optional<std::optional<std::optional<unsigned int>>> &x) {
  if (x.has_value()) {
    const std::optional<std::optional<unsigned int>> &o = *x;
    if (o.has_value()) {
      const std::optional<unsigned int> &o0 = *o;
      if (o0.has_value()) {
        const unsigned int &n = *o0;
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

unsigned int DeepPatterns::deep_pair(
    const std::pair<std::pair<unsigned int, unsigned int>,
                    std::pair<unsigned int, unsigned int>> &p) {
  const std::pair<unsigned int, unsigned int> &p0 = p.first;
  const std::pair<unsigned int, unsigned int> &p1 = p.second;
  const unsigned int &a = p0.first;
  const unsigned int &b = p0.second;
  const unsigned int &c = p1.first;
  const unsigned int &d = p1.second;
  return (((a + b) + c) + d);
}

unsigned int DeepPatterns::list_shape(const List<unsigned int> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return 0u;
  } else {
    const auto &[a0, a1] = std::get<typename List<unsigned int>::Cons>(l.v());
    auto &&_sv0 = *a1;
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0.v())) {
      return a0;
    } else {
      const auto &[a00, a10] =
          std::get<typename List<unsigned int>::Cons>(_sv0.v());
      auto &&_sv1 = *a10;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv1.v())) {
        return (a0 + a00);
      } else {
        const auto &[a01, a11] =
            std::get<typename List<unsigned int>::Cons>(_sv1.v());
        auto &&_sv2 = *a11;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _sv2.v())) {
          return ((a0 + a00) + a01);
        } else {
          const auto &[a02, a12] =
              std::get<typename List<unsigned int>::Cons>(_sv2.v());
          return (((a0 + a00) + a01) + (*a12).length());
        }
      }
    }
  }
}

unsigned int DeepPatterns::deep_sum(const DeepPatterns::outer &o) {
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
        return 1u;
      } else {
        return 0u;
      }
    }
  } else {
    const auto &[a0] = std::get<typename DeepPatterns::outer::ORight>(o.v());
    return (a0 + 100u);
  }
}

unsigned int DeepPatterns::complex_match(
    const std::optional<std::pair<unsigned int, List<unsigned int>>> &x) {
  if (x.has_value()) {
    const std::pair<unsigned int, List<unsigned int>> &p = *x;
    const unsigned int &n = p.first;
    const List<unsigned int> &l = p.second;
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
      return n;
    } else {
      const auto &[a0, a1] = std::get<typename List<unsigned int>::Cons>(l.v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0.v())) {
        return (n + a0);
      } else {
        const auto &[a00, a10] =
            std::get<typename List<unsigned int>::Cons>(_sv0.v());
        return ((n + a0) + (*a10).length());
      }
    }
  } else {
    return 0u;
  }
}

unsigned int
DeepPatterns::guarded_match(const std::pair<unsigned int, unsigned int> &p) {
  const unsigned int &a = p.first;
  const unsigned int &b = p.second;
  if (a <= b) {
    return (((b - a) > b ? 0 : (b - a)));
  } else {
    return (((a - b) > a ? 0 : (a - b)));
  }
}

unsigned int DeepPatterns::match_pair_list(
    const DeepPatterns::mylist<DeepPatterns::pair<unsigned int, unsigned int>>
        &l) {
  if (std::holds_alternative<typename DeepPatterns::mylist<
          DeepPatterns::pair<unsigned int, unsigned int>>::Nil>(l.v())) {
    return 0u;
  } else {
    const auto &[a0, a1] = std::get<typename DeepPatterns::mylist<
        DeepPatterns::pair<unsigned int, unsigned int>>::Cons>(l.v());
    const auto &[a00, a10] = std::get<
        typename DeepPatterns::pair<unsigned int, unsigned int>::Pair0>(a0.v());
    return a00;
  }
}

unsigned int
DeepPatterns::match_two(const DeepPatterns::mylist<unsigned int> &l) {
  if (std::holds_alternative<typename DeepPatterns::mylist<unsigned int>::Nil>(
          l.v())) {
    return 0u;
  } else {
    const auto &[a0, a1] =
        std::get<typename DeepPatterns::mylist<unsigned int>::Cons>(l.v());
    return a0;
  }
}

unsigned int DeepPatterns::match_triple(
    const DeepPatterns::mylist<
        DeepPatterns::mylist<DeepPatterns::mylist<unsigned int>>> &l) {
  if (std::holds_alternative<typename DeepPatterns::mylist<
          DeepPatterns::mylist<DeepPatterns::mylist<unsigned int>>>::Nil>(
          l.v())) {
    return 0u;
  } else {
    const auto &[a0, a1] = std::get<typename DeepPatterns::mylist<
        DeepPatterns::mylist<DeepPatterns::mylist<unsigned int>>>::Cons>(l.v());
    if (std::holds_alternative<typename DeepPatterns::mylist<
            DeepPatterns::mylist<unsigned int>>::Nil>(a0.v())) {
      return 1u;
    } else {
      const auto &[a00, a10] = std::get<typename DeepPatterns::mylist<
          DeepPatterns::mylist<unsigned int>>::Cons>(a0.v());
      if (std::holds_alternative<
              typename DeepPatterns::mylist<unsigned int>::Nil>(a00.v())) {
        return 2u;
      } else {
        const auto &[a01, a11] =
            std::get<typename DeepPatterns::mylist<unsigned int>::Cons>(
                a00.v());
        return a01;
      }
    }
  }
}

unsigned int DeepPatterns::deep_wildcard(
    const DeepPatterns::pair<DeepPatterns::pair<unsigned int, unsigned int>,
                             DeepPatterns::pair<unsigned int, unsigned int>>
        &p) {
  const auto &[a0, a1] = std::get<typename DeepPatterns::pair<
      DeepPatterns::pair<unsigned int, unsigned int>,
      DeepPatterns::pair<unsigned int, unsigned int>>::Pair0>(p.v());
  const auto &[a00, a10] =
      std::get<typename DeepPatterns::pair<unsigned int, unsigned int>::Pair0>(
          a0.v());
  return a00;
}
