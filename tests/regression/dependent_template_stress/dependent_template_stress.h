#ifndef INCLUDED_DEPENDENT_TEMPLATE_STRESS
#define INCLUDED_DEPENDENT_TEMPLATE_STRESS

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename M>
concept Container = requires {
  typename M::t;
  typename M::inner;
  typename M::elem;
};
template <typename M>
concept NestedContainer = requires {
  typename M::outer;
  typename M::middle;
  typename M::inner;
};

struct DependentTemplateStress {
  template <Container C> struct UseContainer {
    static const typename C::template t<unsigned int> &make_nat_container() {
      static const typename C::template t<unsigned int> v =
          C::template empty<unsigned int>;
      return v;
    }

    static const typename C::template inner<unsigned int> &make_inner_nat() {
      static const typename C::template inner<unsigned int> v =
          C::template wrap<unsigned int>(0u);
      return v;
    }

    static const typename C::template t<bool> &make_bool_container() {
      static const typename C::template t<bool> v = C::template empty<bool>;
      return v;
    }

    static const typename C::template t<unsigned int> &use_both() {
      static const typename C::template t<unsigned int> v =
          C::template singleton<unsigned int>(42u);
      return v;
    }

    __attribute__((pure)) static typename C::template t<unsigned int>
    complex_use(const unsigned int _x0) {
      return C::template singleton<unsigned int>(_x0);
    }
  };

  template <NestedContainer N> struct UseNested {
    static const typename N::template outer<unsigned int> &make_outer_nat() {
      static const typename N::template outer<unsigned int> v =
          N::template mk_outer<unsigned int>(
              N::template mk_middle<unsigned int>(
                  N::template mk_inner<unsigned int>(0u)));
      return v;
    }

    static const typename N::template middle<bool> &make_middle_bool() {
      static const typename N::template middle<bool> v =
          N::template mk_middle<bool>(N::template mk_inner<bool>(true));
      return v;
    }

    static const typename N::template outer<unsigned int> &get_outer() {
      static const typename N::template outer<unsigned int> v =
          make_outer_nat();
      return v;
    }
  };

  template <Container C1, Container C2> struct Compose {
    static const typename C1::template t<unsigned int> &use_c1() {
      static const typename C1::template t<unsigned int> v =
          C1::template empty<unsigned int>;
      return v;
    }

    static const typename C2::template t<bool> &use_c2() {
      static const typename C2::template t<bool> v = C2::template empty<bool>;
      return v;
    }

    static const typename C1::template inner<unsigned int> &use_c1_inner() {
      static const typename C1::template inner<unsigned int> v =
          C1::template wrap<unsigned int>(0u);
      return v;
    }

    static const typename C2::template inner<bool> &use_c2_inner() {
      static const typename C2::template inner<bool> v =
          C2::template wrap<bool>(true);
      return v;
    }
  };
};

#endif // INCLUDED_DEPENDENT_TEMPLATE_STRESS
