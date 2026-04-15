#include <deep_patterns.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int DeepPatterns::deep_option(
    const std::optional<std::optional<std::optional<unsigned int>>> x) {
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

__attribute__((pure)) unsigned int
DeepPatterns::deep_pair(const std::pair<std::pair<unsigned int, unsigned int>,
                                        std::pair<unsigned int, unsigned int>>
                            p) {
  const std::pair<unsigned int, unsigned int> &p0 = p.first;
  const std::pair<unsigned int, unsigned int> &p1 = p.second;
  const unsigned int &a = p0.first;
  const unsigned int &b = p0.second;
  const unsigned int &c = p1.first;
  const unsigned int &d = p1.second;
  return (((a + b) + c) + d);
}

__attribute__((pure)) unsigned int
DeepPatterns::list_shape(const std::shared_ptr<List<unsigned int>> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
    return 0u;
  } else {
    const auto &_m = *std::get_if<typename List<unsigned int>::Cons>(&l->v());
    auto &&_sv0 = _m.d_a1;
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0->v())) {
      return _m.d_a0;
    } else {
      const auto &_m0 =
          *std::get_if<typename List<unsigned int>::Cons>(&_sv0->v());
      auto &&_sv1 = _m0.d_a1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv1->v())) {
        return (_m.d_a0 + _m0.d_a0);
      } else {
        const auto &_m1 =
            *std::get_if<typename List<unsigned int>::Cons>(&_sv1->v());
        auto &&_sv2 = _m1.d_a1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _sv2->v())) {
          return ((_m.d_a0 + _m0.d_a0) + _m1.d_a0);
        } else {
          const auto &_m2 =
              *std::get_if<typename List<unsigned int>::Cons>(&_sv2->v());
          return (((_m.d_a0 + _m0.d_a0) + _m1.d_a0) + _m2.d_a1->length());
        }
      }
    }
  }
}

__attribute__((pure)) unsigned int
DeepPatterns::deep_sum(const std::shared_ptr<DeepPatterns::outer> &o) {
  if (std::holds_alternative<typename DeepPatterns::outer::OLeft>(o->v())) {
    const auto &_m = *std::get_if<typename DeepPatterns::outer::OLeft>(&o->v());
    auto &&_sv0 = _m.d_a0;
    if (std::holds_alternative<typename DeepPatterns::inner::ILeft>(
            _sv0->v())) {
      const auto &_m0 =
          *std::get_if<typename DeepPatterns::inner::ILeft>(&_sv0->v());
      return _m0.d_a0;
    } else {
      const auto &_m0 =
          *std::get_if<typename DeepPatterns::inner::IRight>(&_sv0->v());
      if (_m0.d_a0) {
        return 1u;
      } else {
        return 0u;
      }
    }
  } else {
    const auto &_m =
        *std::get_if<typename DeepPatterns::outer::ORight>(&o->v());
    return (_m.d_a0 + 100u);
  }
}

__attribute__((pure)) unsigned int DeepPatterns::complex_match(
    const std::optional<
        std::pair<unsigned int, std::shared_ptr<List<unsigned int>>>>
        x) {
  if (x.has_value()) {
    const std::pair<unsigned int, std::shared_ptr<List<unsigned int>>> &p = *x;
    const unsigned int &n = p.first;
    const std::shared_ptr<List<unsigned int>> &l = p.second;
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
      return n;
    } else {
      const auto &_m = *std::get_if<typename List<unsigned int>::Cons>(&l->v());
      auto &&_sv0 = _m.d_a1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0->v())) {
        return (n + _m.d_a0);
      } else {
        const auto &_m0 =
            *std::get_if<typename List<unsigned int>::Cons>(&_sv0->v());
        return ((n + _m.d_a0) + _m0.d_a1->length());
      }
    }
  } else {
    return 0u;
  }
}

__attribute__((pure)) unsigned int
DeepPatterns::guarded_match(const std::pair<unsigned int, unsigned int> p) {
  const unsigned int &a = p.first;
  const unsigned int &b = p.second;
  if (a <= b) {
    return (((b - a) > b ? 0 : (b - a)));
  } else {
    return (((a - b) > a ? 0 : (a - b)));
  }
}

__attribute__((pure)) unsigned int DeepPatterns::match_pair_list(
    const std::shared_ptr<DeepPatterns::mylist<
        std::shared_ptr<DeepPatterns::pair<unsigned int, unsigned int>>>> &l) {
  if (std::holds_alternative<typename DeepPatterns::mylist<std::shared_ptr<
          DeepPatterns::pair<unsigned int, unsigned int>>>::Nil>(l->v())) {
    return 0u;
  } else {
    const auto &_m = *std::get_if<typename DeepPatterns::mylist<
        std::shared_ptr<DeepPatterns::pair<unsigned int, unsigned int>>>::Cons>(
        &l->v());
    auto &&_sv0 = _m.d_a0;
    const auto &_m0 = *std::get_if<
        typename DeepPatterns::pair<unsigned int, unsigned int>::Pair0>(
        &_sv0->v());
    return _m0.d_a0;
  }
}

__attribute__((pure)) unsigned int DeepPatterns::match_two(
    const std::shared_ptr<DeepPatterns::mylist<unsigned int>> &l) {
  if (std::holds_alternative<typename DeepPatterns::mylist<unsigned int>::Nil>(
          l->v())) {
    return 0u;
  } else {
    const auto &_m =
        *std::get_if<typename DeepPatterns::mylist<unsigned int>::Cons>(
            &l->v());
    return _m.d_a0;
  }
}

__attribute__((pure)) unsigned int DeepPatterns::match_triple(
    const std::shared_ptr<
        DeepPatterns::mylist<std::shared_ptr<DeepPatterns::mylist<
            std::shared_ptr<DeepPatterns::mylist<unsigned int>>>>>> &l) {
  if (std::holds_alternative<
          typename DeepPatterns::mylist<std::shared_ptr<DeepPatterns::mylist<
              std::shared_ptr<DeepPatterns::mylist<unsigned int>>>>>::Nil>(
          l->v())) {
    return 0u;
  } else {
    const auto &_m = *std::get_if<
        typename DeepPatterns::mylist<std::shared_ptr<DeepPatterns::mylist<
            std::shared_ptr<DeepPatterns::mylist<unsigned int>>>>>::Cons>(
        &l->v());
    auto &&_sv0 = _m.d_a0;
    if (std::holds_alternative<typename DeepPatterns::mylist<
            std::shared_ptr<DeepPatterns::mylist<unsigned int>>>::Nil>(
            _sv0->v())) {
      return 1u;
    } else {
      const auto &_m0 = *std::get_if<typename DeepPatterns::mylist<
          std::shared_ptr<DeepPatterns::mylist<unsigned int>>>::Cons>(
          &_sv0->v());
      auto &&_sv1 = _m0.d_a0;
      if (std::holds_alternative<
              typename DeepPatterns::mylist<unsigned int>::Nil>(_sv1->v())) {
        return 2u;
      } else {
        const auto &_m1 =
            *std::get_if<typename DeepPatterns::mylist<unsigned int>::Cons>(
                &_sv1->v());
        return _m1.d_a0;
      }
    }
  }
}

__attribute__((pure)) unsigned int DeepPatterns::deep_wildcard(
    const std::shared_ptr<DeepPatterns::pair<
        std::shared_ptr<DeepPatterns::pair<unsigned int, unsigned int>>,
        std::shared_ptr<DeepPatterns::pair<unsigned int, unsigned int>>>> &p) {
  const auto &_m = *std::get_if<typename DeepPatterns::pair<
      std::shared_ptr<DeepPatterns::pair<unsigned int, unsigned int>>,
      std::shared_ptr<DeepPatterns::pair<unsigned int, unsigned int>>>::Pair0>(
      &p->v());
  auto &&_sv0 = _m.d_a0;
  const auto &_m0 = *std::get_if<
      typename DeepPatterns::pair<unsigned int, unsigned int>::Pair0>(
      &_sv0->v());
  return _m0.d_a0;
}
