#ifndef INCLUDED_MODULE_NAMED_STD
#define INCLUDED_MODULE_NAMED_STD

#include <cstdint>

struct ModuleNamedStd {
  struct std_ {
    static constexpr uint64_t x = UINT64_C(1);
  };

  static constexpr uint64_t go = UINT64_C(1);
};

#endif // INCLUDED_MODULE_NAMED_STD
