#ifndef INCLUDED_MODULE_NAMED_CRANE
#define INCLUDED_MODULE_NAMED_CRANE

#include <cstdint>

struct ModuleNamedCrane {
  struct crane_ {
    static constexpr uint64_t x = UINT64_C(2);
  };

  static constexpr uint64_t go = UINT64_C(2);
};

#endif // INCLUDED_MODULE_NAMED_CRANE
