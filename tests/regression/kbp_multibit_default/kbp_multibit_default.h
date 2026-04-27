#ifndef INCLUDED_KBP_MULTIBIT_DEFAULT
#define INCLUDED_KBP_MULTIBIT_DEFAULT

#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct KbpMultibitDefault {
  struct state {
    unsigned int acc;

    // ACCESSORS
    __attribute__((pure)) state clone() const { return state{(*(this)).acc}; }
  };

  __attribute__((pure)) static state execute_kbp(const state &s);
  static inline const state sample = state{3u};
  static inline const bool t = execute_kbp(sample).acc == 15u;
};

#endif // INCLUDED_KBP_MULTIBIT_DEFAULT
