#ifndef INCLUDED_KBP_MULTIBIT_DEFAULT
#define INCLUDED_KBP_MULTIBIT_DEFAULT

struct KbpMultibitDefault {
  struct state {
    uint64_t acc;

    // ACCESSORS
    state clone() const { return state{this->acc}; }
  };

  static state execute_kbp(const state &s);
  static inline const state sample = state{UINT64_C(3)};
  static inline const bool t = execute_kbp(sample).acc == UINT64_C(15);
};

#endif // INCLUDED_KBP_MULTIBIT_DEFAULT
