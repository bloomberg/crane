#ifndef INCLUDED_IND_PARAM
#define INCLUDED_IND_PARAM

#include <concepts>
#include <type_traits>
#include <utility>
#include <variant>

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
  typename M::elem;
  typename M::t;
  { M::size(std::declval<typename M::t>()) } -> std::same_as<unsigned int>;
};

struct IndParam {
  template <Container C> struct Wrapper {
    using wrapped = typename C::t;

    struct result {
      // TYPES
      struct Ok {
        typename C::t d_a0;
      };

      struct Err {
        unsigned int d_a0;
      };

      using variant_t = std::variant<Ok, Err>;

    private:
      // DATA
      variant_t d_v_;

    public:
      // CREATORS
      result() {}

      explicit result(Ok _v) : d_v_(std::move(_v)) {}

      explicit result(Err _v) : d_v_(std::move(_v)) {}

      result(const result &_other) : d_v_(std::move(_other.clone().d_v_)) {}

      result(result &&_other) : d_v_(std::move(_other.d_v_)) {}

      __attribute__((pure)) result &operator=(const result &_other) {
        d_v_ = std::move(_other.clone().d_v_);
        return *this;
      }

      __attribute__((pure)) result &operator=(result &&_other) {
        d_v_ = std::move(_other.d_v_);
        return *this;
      }

      // ACCESSORS
      __attribute__((pure)) result clone() const {
        auto &&_sv = *(this);
        if (std::holds_alternative<Ok>(_sv.v())) {
          const auto &[d_a0] = std::get<Ok>(_sv.v());
          return result(Ok{clone_as_value<T>(d_a0)});
        } else {
          const auto &[d_a0] = std::get<Err>(_sv.v());
          return result(Err{clone_as_value<unsigned int>(d_a0)});
        }
      }

      // CREATORS
      constexpr static result ok(typename C::t a0) {
        return result(Ok{std::move(a0)});
      }

      __attribute__((pure)) static result err(unsigned int a0) {
        return result(Err{std::move(a0)});
      }

      // MANIPULATORS
      __attribute__((pure)) variant_t &v_mut() { return d_v_; }

      // ACCESSORS
      __attribute__((pure)) result *operator->() { return this; }

      __attribute__((pure)) const result *operator->() const { return this; }

      __attribute__((pure)) bool operator!=(std::nullptr_t) const {
        return true;
      }

      __attribute__((pure)) bool operator==(std::nullptr_t) const {
        return false;
      }

      // MANIPULATORS
      void reset() { *this = result(); }

      // ACCESSORS
      __attribute__((pure)) const variant_t &v() const { return d_v_; }
    };

    template <typename T1, MapsTo<T1, typename C::t> F0,
              MapsTo<T1, unsigned int> F1>
    static T1 result_rect(F0 &&f, F1 &&f0, const result &r) {
      if (std::holds_alternative<typename result::Ok>(r.v())) {
        const auto &[d_a0] = std::get<typename result::Ok>(r.v());
        return f(d_a0);
      } else {
        const auto &[d_a0] = std::get<typename result::Err>(r.v());
        return f0(d_a0);
      }
    }

    template <typename T1, MapsTo<T1, typename C::t> F0,
              MapsTo<T1, unsigned int> F1>
    static T1 result_rec(F0 &&f, F1 &&f0, const result &r) {
      if (std::holds_alternative<typename result::Ok>(r.v())) {
        const auto &[d_a0] = std::get<typename result::Ok>(r.v());
        return f(d_a0);
      } else {
        const auto &[d_a0] = std::get<typename result::Err>(r.v());
        return f0(d_a0);
      }
    }

    constexpr static result make_single(const typename C::elem e) {
      return result::ok(C::t::single(e));
    }

    constexpr static result make_pair(const typename C::elem e1,
                                      const typename C::elem e2) {
      return result::ok(C::t::pair(e1, e2));
    }

    __attribute__((pure)) static unsigned int get_size(const result &r) {
      if (std::holds_alternative<typename result::Ok>(r.v())) {
        const auto &[d_a0] = std::get<typename result::Ok>(r.v());
        return C::size(d_a0);
      } else {
        return 0u;
      }
    }

    static const result &empty_result() {
      static const result v = result::ok(C::t::empty());
      return v;
    }

    static const result &error_result() {
      static const result v = result::err(404u);
      return v;
    }
  };

  struct NatContainer {
    using elem = unsigned int;

    struct t {
      // TYPES
      struct Empty {};

      struct Single {
        elem d_a0;
      };

      struct Pair {
        elem d_a0;
        elem d_a1;
      };

      using variant_t = std::variant<Empty, Single, Pair>;

    private:
      // DATA
      variant_t d_v_;

    public:
      // CREATORS
      t() {}

      explicit t(Empty _v) : d_v_(_v) {}

      explicit t(Single _v) : d_v_(std::move(_v)) {}

      explicit t(Pair _v) : d_v_(std::move(_v)) {}

      t(const t &_other) : d_v_(std::move(_other.clone().d_v_)) {}

      t(t &&_other) : d_v_(std::move(_other.d_v_)) {}

      __attribute__((pure)) t &operator=(const t &_other) {
        d_v_ = std::move(_other.clone().d_v_);
        return *this;
      }

      __attribute__((pure)) t &operator=(t &&_other) {
        d_v_ = std::move(_other.d_v_);
        return *this;
      }

      // ACCESSORS
      __attribute__((pure)) t clone() const {
        auto &&_sv = *(this);
        if (std::holds_alternative<Empty>(_sv.v())) {
          return t(Empty{});
        } else if (std::holds_alternative<Single>(_sv.v())) {
          const auto &[d_a0] = std::get<Single>(_sv.v());
          return t(Single{clone_as_value<elem>(d_a0)});
        } else {
          const auto &[d_a0, d_a1] = std::get<Pair>(_sv.v());
          return t(
              Pair{clone_as_value<elem>(d_a0), clone_as_value<elem>(d_a1)});
        }
      }

      // CREATORS
      constexpr static t empty() { return t(Empty{}); }

      constexpr static t single(elem a0) { return t(Single{std::move(a0)}); }

      constexpr static t pair(elem a0, elem a1) {
        return t(Pair{std::move(a0), std::move(a1)});
      }

      // MANIPULATORS
      __attribute__((pure)) variant_t &v_mut() { return d_v_; }

      // ACCESSORS
      __attribute__((pure)) t *operator->() { return this; }

      __attribute__((pure)) const t *operator->() const { return this; }

      __attribute__((pure)) bool operator!=(std::nullptr_t) const {
        return true;
      }

      __attribute__((pure)) bool operator==(std::nullptr_t) const {
        return false;
      }

      // MANIPULATORS
      void reset() { *this = t(); }

      // ACCESSORS
      __attribute__((pure)) const variant_t &v() const { return d_v_; }
    };

    template <typename T1, MapsTo<T1, unsigned int> F1,
              MapsTo<T1, unsigned int, unsigned int> F2>
    static T1 t_rect(const T1 f, F1 &&f0, F2 &&f1, const t &t0) {
      if (std::holds_alternative<typename t::Empty>(t0.v())) {
        return f;
      } else if (std::holds_alternative<typename t::Single>(t0.v())) {
        const auto &[d_a0] = std::get<typename t::Single>(t0.v());
        return f0(d_a0);
      } else {
        const auto &[d_a0, d_a1] = std::get<typename t::Pair>(t0.v());
        return f1(d_a0, d_a1);
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F1,
              MapsTo<T1, unsigned int, unsigned int> F2>
    static T1 t_rec(const T1 f, F1 &&f0, F2 &&f1, const t &t0) {
      if (std::holds_alternative<typename t::Empty>(t0.v())) {
        return f;
      } else if (std::holds_alternative<typename t::Single>(t0.v())) {
        const auto &[d_a0] = std::get<typename t::Single>(t0.v());
        return f0(d_a0);
      } else {
        const auto &[d_a0, d_a1] = std::get<typename t::Pair>(t0.v());
        return f1(d_a0, d_a1);
      }
    }

    __attribute__((pure)) static unsigned int size(const t &c);
  };

  using NatWrapper = Wrapper<NatContainer>;
  static inline const NatWrapper::result test_single =
      NatWrapper::make_single(42u);
  static inline const NatWrapper::result test_pair =
      NatWrapper::make_pair(1u, 2u);
  static inline const unsigned int test_size_single =
      NatWrapper::get_size(test_single);
  static inline const unsigned int test_size_pair =
      NatWrapper::get_size(test_pair);
  static inline const unsigned int test_error =
      NatWrapper::get_size(NatWrapper::error_result());
};

#endif // INCLUDED_IND_PARAM
