#ifndef INCLUDED_DEPENDENT_TEMPLATE_STRESS
#define INCLUDED_DEPENDENT_TEMPLATE_STRESS

template <typename M>
concept Container = requires {
  typename M::template t<void>;
  typename M::template inner<void>;
  typename M::elem;
};
template <typename M>
concept NestedContainer = requires {
  typename M::template outer<void>;
  typename M::template middle<void>;
  typename M::template inner<void>;
};

struct DependentTemplateStress {
  template <Container C> struct UseContainer {
    static const typename C::template t<uint64_t> &make_nat_container() {
      static const typename C::template t<uint64_t> v =
          C::template empty<uint64_t>;
      return v;
    }

    static const typename C::template inner<uint64_t> &make_inner_nat() {
      static const typename C::template inner<uint64_t> v =
          C::template wrap<uint64_t>(UINT64_C(0));
      return v;
    }

    static const typename C::template t<bool> &make_bool_container() {
      static const typename C::template t<bool> v = C::template empty<bool>;
      return v;
    }

    static const typename C::template t<uint64_t> &use_both() {
      static const typename C::template t<uint64_t> v =
          C::template singleton<uint64_t>(UINT64_C(42));
      return v;
    }

    static typename C::template t<uint64_t> complex_use(uint64_t _x0) {
      return C::template singleton<uint64_t>(_x0);
    }
  };

  template <NestedContainer N> struct UseNested {
    static const typename N::template outer<uint64_t> &make_outer_nat() {
      static const typename N::template outer<uint64_t> v =
          N::template mk_outer<uint64_t>(N::template mk_middle<uint64_t>(
              N::template mk_inner<uint64_t>(UINT64_C(0))));
      return v;
    }

    static const typename N::template middle<bool> &make_middle_bool() {
      static const typename N::template middle<bool> v =
          N::template mk_middle<bool>(N::template mk_inner<bool>(true));
      return v;
    }

    static const typename N::template outer<uint64_t> &get_outer() {
      static const typename N::template outer<uint64_t> v = make_outer_nat();
      return v;
    }
  };

  template <Container C1, Container C2> struct Compose {
    static const typename C1::template t<uint64_t> &use_c1() {
      static const typename C1::template t<uint64_t> v =
          C1::template empty<uint64_t>;
      return v;
    }

    static const typename C2::template t<bool> &use_c2() {
      static const typename C2::template t<bool> v = C2::template empty<bool>;
      return v;
    }

    static const typename C1::template inner<uint64_t> &use_c1_inner() {
      static const typename C1::template inner<uint64_t> v =
          C1::template wrap<uint64_t>(UINT64_C(0));
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
