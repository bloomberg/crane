#ifndef INCLUDED_QUALIFIED_SHADOW_ASCII
#define INCLUDED_QUALIFIED_SHADOW_ASCII

#include <utility>

struct QualifiedShadowAscii {
  struct Shadow {
    enum class shadow { MK };

    template <typename T1> static T1 shadow_rect(T1 f, shadow) { return f; }

    template <typename T1> static T1 shadow_rec(T1 f, shadow _x) {
      return shadow_rect<T1>(std::move(f), _x);
    }
  };

  static Shadow::shadow id_shadow(Shadow::shadow x);
  static inline const Shadow::shadow t = id_shadow(Shadow::shadow::MK);
};

#endif // INCLUDED_QUALIFIED_SHADOW_ASCII
