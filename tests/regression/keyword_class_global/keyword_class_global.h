#ifndef INCLUDED_KEYWORD_CLASS_GLOBAL
#define INCLUDED_KEYWORD_CLASS_GLOBAL

#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct KeywordClassGlobal {
  __attribute__((pure)) static unsigned int class_(const unsigned int &n);
  static inline const unsigned int t = class_(4u);
};

#endif // INCLUDED_KEYWORD_CLASS_GLOBAL
