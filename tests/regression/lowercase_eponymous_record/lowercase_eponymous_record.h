#ifndef INCLUDED_LOWERCASE_EPONYMOUS_RECORD
#define INCLUDED_LOWERCASE_EPONYMOUS_RECORD

struct LowercaseEponymousRecord {
  struct state {
    uint64_t x;
    uint64_t y;

    state set_x(uint64_t n) const { return state{n, (*this).y}; }
  };

  static inline const state example =
      state{UINT64_C(0), UINT64_C(0)}.set_x(UINT64_C(42));
};

#endif // INCLUDED_LOWERCASE_EPONYMOUS_RECORD
