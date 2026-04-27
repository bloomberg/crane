#ifndef INCLUDED_QUALIFIED_SHADOW_ASCII
#define INCLUDED_QUALIFIED_SHADOW_ASCII

#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct QualifiedShadowAscii {
  struct Shadow {
    enum class shadow { e_MK };
  };

  __attribute__((pure)) static Shadow::shadow id_shadow(const Shadow::shadow x);
  static inline const Shadow::shadow t = id_shadow(Shadow::shadow::e_MK);
};

#endif // INCLUDED_QUALIFIED_SHADOW_ASCII
