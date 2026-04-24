#include <name_clash_nested_deep.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Four levels of nested matching.
__attribute__((pure)) unsigned int
NameClashNestedDeep::deep4(const NameClashNestedDeep::mylist &a,
                           const NameClashNestedDeep::mylist &b,
                           const NameClashNestedDeep::mylist &c,
                           const NameClashNestedDeep::mylist &d) {
  if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
          a.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename NameClashNestedDeep::mylist::MyCons>(a.v());
    if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
            b.v())) {
      return d_a0;
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename NameClashNestedDeep::mylist::MyCons>(b.v());
      if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
              c.v())) {
        return (d_a0 + d_a00);
      } else {
        const auto &[d_a01, d_a11] =
            std::get<typename NameClashNestedDeep::mylist::MyCons>(c.v());
        if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
                d.v())) {
          return ((d_a0 + d_a00) + d_a01);
        } else {
          const auto &[d_a02, d_a12] =
              std::get<typename NameClashNestedDeep::mylist::MyCons>(d.v());
          return (((d_a0 + d_a00) + d_a01) + d_a02);
        }
      }
    }
  }
}

/// Match in a let, then match on the let result.
__attribute__((pure)) unsigned int
NameClashNestedDeep::let_match_chain(const NameClashNestedDeep::mylist &xs,
                                     const NameClashNestedDeep::mylist &ys) {
  unsigned int hd_x = [&]() {
    if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
            xs.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename NameClashNestedDeep::mylist::MyCons>(xs.v());
      return d_a0;
    }
  }();
  unsigned int hd_y = [&]() {
    if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
            ys.v())) {
      return 0u;
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename NameClashNestedDeep::mylist::MyCons>(ys.v());
      return d_a00;
    }
  }();
  NameClashNestedDeep::mylist combined =
      mylist::mycons((hd_x + hd_y), mylist::mynil());
  if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
          combined.v())) {
    return 0u;
  } else {
    const auto &[d_a01, d_a11] =
        std::get<typename NameClashNestedDeep::mylist::MyCons>(combined.v());
    return d_a01;
  }
}

/// Matching where the same list is matched multiple times.
__attribute__((pure)) unsigned int
NameClashNestedDeep::multi_match_same(const NameClashNestedDeep::mylist &xs) {
  unsigned int first = [&]() {
    if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
            xs.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename NameClashNestedDeep::mylist::MyCons>(xs.v());
      return d_a0;
    }
  }();
  NameClashNestedDeep::mylist tail = [&]() {
    if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
            xs.v())) {
      return mylist::mynil();
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename NameClashNestedDeep::mylist::MyCons>(xs.v());
      return *(d_a10);
    }
  }();
  unsigned int second = [&]() {
    if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
            tail.v())) {
      return 0u;
    } else {
      const auto &[d_a01, d_a11] =
          std::get<typename NameClashNestedDeep::mylist::MyCons>(tail.v());
      return d_a01;
    }
  }();
  return (first + second);
}

/// Nested match where inner match scrutinee is a field from outer match.
__attribute__((pure)) unsigned int
NameClashNestedDeep::nested_field_match(const NameClashNestedDeep::mylist &xs) {
  if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
          xs.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename NameClashNestedDeep::mylist::MyCons>(xs.v());
    auto &&_sv0 = *(d_a1);
    if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
            _sv0.v())) {
      return 1u;
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename NameClashNestedDeep::mylist::MyCons>(_sv0.v());
      auto &&_sv1 = *(d_a10);
      if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
              _sv1.v())) {
        return 2u;
      } else {
        const auto &[d_a01, d_a11] =
            std::get<typename NameClashNestedDeep::mylist::MyCons>(_sv1.v());
        return d_a01;
      }
    }
  }
}
