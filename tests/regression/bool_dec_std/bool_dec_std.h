#ifndef INCLUDED_BOOL_DEC_STD
#define INCLUDED_BOOL_DEC_STD

#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct Bool {
  static bool bool_dec(const bool &b1, const bool &b2);
};

struct BoolDecStd {
  static bool eqb_dec(const bool &a, const bool &b);
  static inline const bool t1 = eqb_dec(true, true);
  static inline const bool t2 = eqb_dec(true, false);
};

#endif // INCLUDED_BOOL_DEC_STD
