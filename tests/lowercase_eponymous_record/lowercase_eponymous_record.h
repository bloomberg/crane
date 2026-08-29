#ifndef INCLUDED_LOWERCASE_EPONYMOUS_RECORD
#define INCLUDED_LOWERCASE_EPONYMOUS_RECORD

struct LowercaseEponymousRecord {
  struct state_Mod {
    struct state {
      uint64_t x;
      uint64_t y;
    };
  };

  static inline const state_Mod::state example =
      state_Mod::state{UINT64_C(0), UINT64_C(0)}.set_x(UINT64_C(42));
};

#endif // INCLUDED_LOWERCASE_EPONYMOUS_RECORD
