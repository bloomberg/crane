#ifndef INCLUDED_LOWERCASE_EPONYMOUS_RECORD
#define INCLUDED_LOWERCASE_EPONYMOUS_RECORD

struct LowercaseEponymousRecord {
  struct state {
    struct state0 {
      uint64_t x;
      uint64_t y;
    };

    static state0 set_x(uint64_t n, const state0 &s);
  };

  static inline const state::state0 example =
      state::set_x(UINT64_C(42), state::state0{UINT64_C(0), UINT64_C(0)});
};

#endif // INCLUDED_LOWERCASE_EPONYMOUS_RECORD
