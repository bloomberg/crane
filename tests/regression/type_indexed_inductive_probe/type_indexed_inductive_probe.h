#ifndef INCLUDED_TYPE_INDEXED_INDUCTIVE_PROBE
#define INCLUDED_TYPE_INDEXED_INDUCTIVE_PROBE

#include <any>
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

enum class Bool0 { e_TRUE0, e_FALSE0 };

struct TypeIndexedInductiveProbe {
  /// Regression test for type-indexed inductives with erased type parameters.
  ///
  /// Inductive wrap is indexed by a Set; the type parameter A is erased
  /// in C++, so the field d_a is typed std::any.  When matching w : wrap
  /// bool at the concrete index bool, the branch body b must be recovered
  /// via std::any_cast<Bool0>.  Previously Crane emitted a bare return d_a
  /// instead, causing a compile error:
  /// error: no viable conversion from 'std::any' to 'const Bool0'
  struct wrap {
    // TYPES
    struct Wrap0 {
      std::any d_a;
    };

    using variant_t = std::variant<Wrap0>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    wrap() {}

    explicit wrap(Wrap0 _v) : d_v_(std::move(_v)) {}

    wrap(const wrap &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    wrap(wrap &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) wrap &operator=(const wrap &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) wrap &operator=(wrap &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) wrap clone() const {
      auto &&_sv = *(this);
      const auto &[d_a] = std::get<Wrap0>(_sv.v());
      return wrap(Wrap0{clone_value(d_a)});
    }

    // CREATORS
    __attribute__((pure)) static wrap wrap0(std::any a) {
      return wrap(Wrap0{std::move(a)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) wrap *operator->() { return this; }

    __attribute__((pure)) const wrap *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = wrap(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename F0>
  static T1 wrap_rect(F0 &&f, const wrap &w0) {
    const auto &[d_a] = std::get<typename wrap::Wrap0>(w0.v());
    return std::any_cast<T1>(f(d_a));
  }

  template <typename T1, typename F0>
  static T1 wrap_rec(F0 &&f, const wrap &w0) {
    const auto &[d_a] = std::get<typename wrap::Wrap0>(w0.v());
    return std::any_cast<T1>(f(d_a));
  }

  static inline const wrap w = wrap::wrap0(Bool0::e_TRUE0);
  static inline const Bool0 sample = []() {
    auto &&_sv0 = w;
    const auto &[d_a0] = std::get<typename wrap::Wrap0>(_sv0.v());
    return std::any_cast<Bool0>(d_a0);
  }();
};

#endif // INCLUDED_TYPE_INDEXED_INDUCTIVE_PROBE
