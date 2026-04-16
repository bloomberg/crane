#include <name_clash_nested_deep.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Four levels of nested matching.
__attribute__((pure)) unsigned int NameClashNestedDeep::deep4(
    const std::shared_ptr<NameClashNestedDeep::mylist> &a,
    const std::shared_ptr<NameClashNestedDeep::mylist> &b,
    const std::shared_ptr<NameClashNestedDeep::mylist> &c,
    const std::shared_ptr<NameClashNestedDeep::mylist> &d) {
  if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
          a->v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename NameClashNestedDeep::mylist::MyCons>(a->v());
    if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
            b->v())) {
      return d_a0;
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename NameClashNestedDeep::mylist::MyCons>(b->v());
      if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
              c->v())) {
        return (d_a0 + d_a00);
      } else {
        const auto &[d_a01, d_a11] =
            std::get<typename NameClashNestedDeep::mylist::MyCons>(c->v());
        if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
                d->v())) {
          return ((d_a0 + d_a00) + d_a01);
        } else {
          const auto &[d_a02, d_a12] =
              std::get<typename NameClashNestedDeep::mylist::MyCons>(d->v());
          return (((d_a0 + d_a00) + d_a01) + d_a02);
        }
      }
    }
  }
}

/// Match in a let, then match on the let result.
__attribute__((pure)) unsigned int NameClashNestedDeep::let_match_chain(
    const std::shared_ptr<NameClashNestedDeep::mylist> &xs,
    const std::shared_ptr<NameClashNestedDeep::mylist> &ys) {
  unsigned int hd_x = [&]() {
    if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
            xs->v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename NameClashNestedDeep::mylist::MyCons>(xs->v());
      return d_a0;
    }
  }();
  unsigned int hd_y = [&]() {
    if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
            ys->v())) {
      return 0u;
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename NameClashNestedDeep::mylist::MyCons>(ys->v());
      return d_a00;
    }
  }();
  std::shared_ptr<NameClashNestedDeep::mylist> combined =
      mylist::mycons((hd_x + hd_y), mylist::mynil());
  if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
          combined->v())) {
    return 0u;
  } else {
    const auto &[d_a01, d_a11] =
        std::get<typename NameClashNestedDeep::mylist::MyCons>(combined->v());
    return d_a01;
  }
}

/// Matching where the same list is matched multiple times.
__attribute__((pure)) unsigned int NameClashNestedDeep::multi_match_same(
    const std::shared_ptr<NameClashNestedDeep::mylist> &xs) {
  unsigned int first = [&]() {
    if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
            xs->v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename NameClashNestedDeep::mylist::MyCons>(xs->v());
      return d_a0;
    }
  }();
  std::shared_ptr<NameClashNestedDeep::mylist> tail = [&]() {
    if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
            xs->v())) {
      return mylist::mynil();
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename NameClashNestedDeep::mylist::MyCons>(xs->v());
      return d_a10;
    }
  }();
  unsigned int second = [&]() {
    if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
            tail->v())) {
      return 0u;
    } else {
      const auto &[d_a01, d_a11] =
          std::get<typename NameClashNestedDeep::mylist::MyCons>(tail->v());
      return d_a01;
    }
  }();
  return (first + second);
}

/// Nested match where inner match scrutinee is a field from outer match.
__attribute__((pure)) unsigned int NameClashNestedDeep::nested_field_match(
    const std::shared_ptr<NameClashNestedDeep::mylist> &xs) {
  if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
          xs->v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename NameClashNestedDeep::mylist::MyCons>(xs->v());
    if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
            d_a1->v())) {
      return 1u;
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename NameClashNestedDeep::mylist::MyCons>(d_a1->v());
      if (std::holds_alternative<typename NameClashNestedDeep::mylist::MyNil>(
              d_a10->v())) {
        return 2u;
      } else {
        const auto &[d_a01, d_a11] =
            std::get<typename NameClashNestedDeep::mylist::MyCons>(d_a10->v());
        return d_a01;
      }
    }
  }
}
