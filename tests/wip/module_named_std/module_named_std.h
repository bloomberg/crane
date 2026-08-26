#ifndef INCLUDED_MODULE_NAMED_STD
#define INCLUDED_MODULE_NAMED_STD

struct ModuleNamedStd {
  struct std_ {
    static inline const uint64_t x = UINT64_C(1);
  };

  static inline const uint64_t go = std::x;
};

#endif // INCLUDED_MODULE_NAMED_STD
