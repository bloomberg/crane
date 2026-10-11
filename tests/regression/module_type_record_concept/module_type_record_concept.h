#ifndef INCLUDED_MODULE_TYPE_RECORD_CONCEPT
#define INCLUDED_MODULE_TYPE_RECORD_CONCEPT

#include <cstdint>

template <typename M>
concept T = requires { typename M::pt; };

struct ModuleTypeRecordConcept {
  struct Impl {
    struct pt {
      uint64_t px;
    };
  };

  template <T X> struct Use {
    static uint64_t f(const typename X::pt &p) { return (p.px + 1); }
  };

  using U = Use<Impl>;
  static inline const uint64_t result = U::f(Impl::pt{UINT64_C(4)});
};

#endif // INCLUDED_MODULE_TYPE_RECORD_CONCEPT
