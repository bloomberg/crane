#include "name_clash_nested_deep.h"

/// Four levels of nested matching.
unsigned int NameClashNestedDeep::deep4(const NameClashNestedDeep::mylist &a,
                                        const NameClashNestedDeep::mylist &b,
                                        const NameClashNestedDeep::mylist &c,
                                        const NameClashNestedDeep::mylist &d) {
  if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
          a.v())) {
    return 0u;
  } else {
    const auto &[a0, a1] =
        std::get<typename NameClashNestedDeep::mylist::MyCons>(a.v());
    if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
            b.v())) {
      return a0;
    } else {
      const auto &[a00, a10] =
          std::get<typename NameClashNestedDeep::mylist::MyCons>(b.v());
      if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
              c.v())) {
        return (a0 + a00);
      } else {
        const auto &[a01, a11] =
            std::get<typename NameClashNestedDeep::mylist::MyCons>(c.v());
        if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
                d.v())) {
          return ((a0 + a00) + a01);
        } else {
          const auto &[a02, a12] =
              std::get<typename NameClashNestedDeep::mylist::MyCons>(d.v());
          return (((a0 + a00) + a01) + a02);
        }
      }
    }
  }
}

/// Match in a let, then match on the let result.
unsigned int
NameClashNestedDeep::let_match_chain(const NameClashNestedDeep::mylist &xs,
                                     const NameClashNestedDeep::mylist &ys) {
  unsigned int hd_x = [&]() {
    if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
            xs.v())) {
      return 0u;
    } else {
      const auto &[a0, a1] =
          std::get<typename NameClashNestedDeep::mylist::MyCons>(xs.v());
      return a0;
    }
  }();
  unsigned int hd_y = [&]() {
    if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
            ys.v())) {
      return 0u;
    } else {
      const auto &[a00, a10] =
          std::get<typename NameClashNestedDeep::mylist::MyCons>(ys.v());
      return a00;
    }
  }();
  NameClashNestedDeep::mylist combined =
      mylist::mycons((hd_x + hd_y), mylist::mynil());
  if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
          combined.v_mut())) {
    return 0u;
  } else {
    auto &[a01, a11] = std::get<typename NameClashNestedDeep::mylist::MyCons>(
        combined.v_mut());
    return a01;
  }
}

/// Matching where the same list is matched multiple times.
unsigned int
NameClashNestedDeep::multi_match_same(const NameClashNestedDeep::mylist &xs) {
  unsigned int first = [&]() {
    if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
            xs.v())) {
      return 0u;
    } else {
      const auto &[a0, a1] =
          std::get<typename NameClashNestedDeep::mylist::MyCons>(xs.v());
      return a0;
    }
  }();
  NameClashNestedDeep::mylist tail = [&]() {
    if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
            xs.v())) {
      return mylist::mynil();
    } else {
      const auto &[a00, a10] =
          std::get<typename NameClashNestedDeep::mylist::MyCons>(xs.v());
      return *a10;
    }
  }();
  unsigned int second = [&]() {
    if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
            tail.v_mut())) {
      return 0u;
    } else {
      auto &[a01, a11] =
          std::get<typename NameClashNestedDeep::mylist::MyCons>(tail.v_mut());
      return a01;
    }
  }();
  return (first + second);
}

/// Nested match where inner match scrutinee is a field from outer match.
unsigned int
NameClashNestedDeep::nested_field_match(const NameClashNestedDeep::mylist &xs) {
  if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
          xs.v())) {
    return 0u;
  } else {
    const auto &[a0, a1] =
        std::get<typename NameClashNestedDeep::mylist::MyCons>(xs.v());
    auto &&_sv0 = *a1;
    if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
            _sv0.v())) {
      return 1u;
    } else {
      const auto &[a00, a10] =
          std::get<typename NameClashNestedDeep::mylist::MyCons>(_sv0.v());
      auto &&_sv1 = *a10;
      if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
              _sv1.v())) {
        return 2u;
      } else {
        const auto &[a01, a11] =
            std::get<typename NameClashNestedDeep::mylist::MyCons>(_sv1.v());
        return a01;
      }
    }
  }
}
