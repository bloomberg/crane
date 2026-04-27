#ifndef INCLUDED_LOWERCASE_EPONYMOUS_RECORD
#define INCLUDED_LOWERCASE_EPONYMOUS_RECORD

#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct LowercaseEponymousRecord {
  struct state {
    unsigned int x;
    unsigned int y;

    __attribute__((pure)) state set_x(unsigned int n) const {
      return state{n, (*(this)).state::y};
    }
  };

  static inline const state example = state{0u, 0u}.set_x(42u);
};

#endif // INCLUDED_LOWERCASE_EPONYMOUS_RECORD
