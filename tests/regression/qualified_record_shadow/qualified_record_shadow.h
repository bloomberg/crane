#ifndef INCLUDED_QUALIFIED_RECORD_SHADOW
#define INCLUDED_QUALIFIED_RECORD_SHADOW

#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct QualifiedRecordShadow {
  struct Shadow {
    unsigned int value;
  };

  __attribute__((pure)) static Shadow bump(const Shadow &x);
  static inline const Shadow t = bump(Shadow{1u});
};

#endif // INCLUDED_QUALIFIED_RECORD_SHADOW
