#ifndef INCLUDED_ROCQ_BUG_3923
#define INCLUDED_ROCQ_BUG_3923

#include <concepts>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

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
