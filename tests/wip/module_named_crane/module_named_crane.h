#ifndef INCLUDED_MODULE_NAMED_CRANE
#define INCLUDED_MODULE_NAMED_CRANE

struct ModuleNamedCrane {
  struct crane_ {
    static inline const uint64_t x = UINT64_C(2);
  };

  static inline const uint64_t go = crane::x;
};

#endif // INCLUDED_MODULE_NAMED_CRANE
