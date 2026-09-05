#ifndef INCLUDED_MODULE_PARAM_CLASS_INSTANCE
#define INCLUDED_MODULE_PARAM_CLASS_INSTANCE

#include <concepts>
#include <utility>

/// A module-type Parameter whose type is a typeclass instance produces an
/// ill-formed requires clause in the generated concept.
template <typename I, typename A>
concept Weigh = requires {
  { I::weigh(std::declval<A>()) } -> std::convertible_to<uint64_t>;
};

template <typename M>
concept CARRIER = requires {
  typename M::t;
  requires(
      requires {
        {
          M::inst
        }
        -> std::convertible_to<ModuleParamClassInstance::Weigh<typename M::t>>;
      } ||
      requires {
        {
          M::inst()
        }
        -> std::convertible_to<ModuleParamClassInstance::Weigh<typename M::t>>;
      });
  requires(
      requires {
        { M::sample } -> std::convertible_to<typename M::t>;
      } ||
      requires {
        { M::sample() } -> std::convertible_to<typename M::t>;
      });
};

struct ModuleParamClassInstance {
  template <CARRIER C> struct Doubler {
    static uint64_t twice(typename C::t x) {
      return (C::inst::weigh(x) + C::inst::weigh(x));
    }

    static const uint64_t &on_sample() {
      static const uint64_t v = twice(C::sample);
      return v;
    }
  };

  struct NatC {
    using t = uint64_t;

    struct inst {
      static uint64_t weigh(uint64_t n) { return n; }
    };

    static_assert(Weigh<inst, uint64_t>);
    static inline const t sample = UINT64_C(5);
  };

  using D = Doubler<NatC>;
  static inline const uint64_t total = (D::on_sample() + D::twice(UINT64_C(7)));
};

#endif // INCLUDED_MODULE_PARAM_CLASS_INSTANCE
