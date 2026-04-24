#ifndef INCLUDED_DEPENDENT_TEMPLATE_STRESS
#define INCLUDED_DEPENDENT_TEMPLATE_STRESS

#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> struct is_shared_ptr : std::false_type {};

template <typename T>
struct is_shared_ptr<std::shared_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  return x ? std::make_shared<T>(x->clone()) : nullptr;
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using TargetBare = std::remove_cvref_t<Target>;
  using SourceBare = std::remove_cvref_t<Source>;
  if constexpr (is_unique_ptr<TargetBare>::value) {
    using Inner = typename is_unique_ptr<TargetBare>::element_type;
    if constexpr (is_unique_ptr<SourceBare>::value) {
      using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires {
                             typename Inner::crane_element_type;
                             x->template clone_as<
                                 typename Inner::crane_element_type>();
                           }) {
        return std::make_unique<Inner>(
            x->template clone_as<typename Inner::crane_element_type>());
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x.clone());
      }
    }
  } else if constexpr (is_shared_ptr<TargetBare>::value) {
    using Inner = typename is_shared_ptr<TargetBare>::element_type;
    if constexpr (is_shared_ptr<SourceBare>::value) {
      using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else if constexpr (is_unique_ptr<SourceBare>::value) {
      if (!x)
        return nullptr;
      if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_shared<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x.clone());
      }
    }
  } else if constexpr (std::is_same_v<TargetBare, SourceBare>) {
    return clone_value(x);
  } else if constexpr (is_unique_ptr<SourceBare>::value) {
    using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (is_shared_ptr<SourceBare>::value) {
    using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (requires {
                         typename TargetBare::crane_element_type;
                         x.template clone_as<
                             typename TargetBare::crane_element_type>();
                       }) {
    return x.template clone_as<typename TargetBare::crane_element_type>();
  } else if constexpr (requires { x.template clone_as<TargetBare>(); }) {
    return x.template clone_as<TargetBare>();
  } else {
    return Target(x);
  }
}

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
    complex_use(const unsigned int &_x0) {
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
