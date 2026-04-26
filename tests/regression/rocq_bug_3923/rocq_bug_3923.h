#ifndef INCLUDED_ROCQ_BUG_3923
#define INCLUDED_ROCQ_BUG_3923

#include <concepts>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_unique<T>(x->clone()) : nullptr;
  } else {
    return x ? std::make_unique<T>(*x) : nullptr;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using T = std::remove_cvref_t<Target>;
  using S = std::remove_cvref_t<Source>;
  if constexpr (requires(const S &s) {
                  s.has_value();
                  *s;
                }) {
    if (!x.has_value())
      return T{};
    using TInner = std::remove_cvref_t<decltype(*std::declval<const T &>())>;
    return T{clone_as_value<TInner>(*x)};
  } else if constexpr (std::is_same_v<T, S>) {
    if constexpr (is_unique_ptr<T>::value) {
      return clone_value(x);
    } else if constexpr (requires { x.clone(); }) {
      return x.clone();
    } else {
      return x;
    }
  } else if constexpr (is_unique_ptr<S>::value) {
    if (!x)
      return T{};
    return clone_as_value<T>(*x);
  } else if constexpr (is_unique_ptr<T>::value) {
    using Inner = typename is_unique_ptr<T>::element_type;
    return std::make_unique<Inner>(clone_as_value<Inner>(x));
  } else {
    return T(x);
  }
}

enum class Unit { e_TT };
template <typename M>
concept TRIVIAL = requires { typename M::t; };
template <typename M>
concept CERTRUNTIMETYPES = requires {
  typename M::cert_fieldstore;
  requires(
      requires {
        {
          M::empty_fieldstore
        } -> std::convertible_to<typename M::cert_fieldstore>;
      } ||
      requires {
        {
          M::empty_fieldstore()
        } -> std::convertible_to<typename M::cert_fieldstore>;
      });
};

struct RocqBug3923 {
  template <TRIVIAL Key> struct MkStore {
    struct St {
      using t = Unit;
    };

    static_assert(TRIVIAL<St>);
  };

  template <TRIVIAL B> struct MkCertRuntimeTypes {
    using FieldStore = MkStore<B>;
    using cert_fieldstore = typename FieldStore::St::t;

    static cert_fieldstore empty_fieldstore() {
      throw std::logic_error("unrealized axiom: "
                             "CraneTestsRegression.rocq_bug_3923.RocqBug3923."
                             "RocqBug3923.MkCertRuntimeTypes.empty_fieldstore");
    }
  };
};

#endif // INCLUDED_ROCQ_BUG_3923
