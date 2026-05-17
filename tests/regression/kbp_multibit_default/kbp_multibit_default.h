#ifndef INCLUDED_KBP_MULTIBIT_DEFAULT
#define INCLUDED_KBP_MULTIBIT_DEFAULT

struct KbpMultibitDefault {
  struct state {
    unsigned int acc;

    // ACCESSORS
    state clone() const { return state{(*this).acc}; }
  };

  static state execute_kbp(const state &s);
  static inline const state sample = state{3u};
  static inline const bool t = execute_kbp(sample).acc == 15u;
};

#endif // INCLUDED_KBP_MULTIBIT_DEFAULT
