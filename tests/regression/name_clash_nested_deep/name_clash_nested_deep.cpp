#include "name_clash_nested_deep.h"

/// Four levels of nested matching.
uint64_t NameClashNestedDeep::deep4(const NameClashNestedDeep::mylist &a,
                                    const NameClashNestedDeep::mylist &b,
                                    const NameClashNestedDeep::mylist &c,
                                    const NameClashNestedDeep::mylist &d) {
  if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
          a.v())) {
    return UINT64_C(0);
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
uint64_t
NameClashNestedDeep::let_match_chain(const NameClashNestedDeep::mylist &xs,
                                     const NameClashNestedDeep::mylist &ys) {
  uint64_t hd_x = [&]() {
    if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
            xs.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] =
          std::get<typename NameClashNestedDeep::mylist::MyCons>(xs.v());
      return a0;
    }
  }();
  uint64_t hd_y = [&]() {
    if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
            ys.v())) {
      return UINT64_C(0);
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
    return UINT64_C(0);
  } else {
    auto &[a01, a11] = std::get<typename NameClashNestedDeep::mylist::MyCons>(
        combined.v_mut());
    return a01;
  }
}

/// Matching where the same list is matched multiple times.
uint64_t
NameClashNestedDeep::multi_match_same(const NameClashNestedDeep::mylist &xs) {
  uint64_t first = [&]() {
    if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
            xs.v())) {
      return UINT64_C(0);
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
  uint64_t second = [&]() {
    if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
            tail.v_mut())) {
      return UINT64_C(0);
    } else {
      auto &[a01, a11] =
          std::get<typename NameClashNestedDeep::mylist::MyCons>(tail.v_mut());
      return a01;
    }
  }();
  return (first + second);
}

/// Nested match where inner match scrutinee is a field from outer match.
uint64_t
NameClashNestedDeep::nested_field_match(const NameClashNestedDeep::mylist &xs) {
  if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
          xs.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename NameClashNestedDeep::mylist::MyCons>(xs.v());
    auto &&_sv0 = *a1;
    if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
            _sv0.v())) {
      return UINT64_C(1);
    } else {
      const auto &[a00, a10] =
          std::get<typename NameClashNestedDeep::mylist::MyCons>(_sv0.v());
      auto &&_sv1 = *a10;
      if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
              _sv1.v())) {
        return UINT64_C(2);
      } else {
        const auto &[a01, a11] =
            std::get<typename NameClashNestedDeep::mylist::MyCons>(_sv1.v());
        return a01;
      }
    }
  }
}
