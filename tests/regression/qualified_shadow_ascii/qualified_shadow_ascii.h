#pragma once

#include <utility>

struct QualifiedShadowAscii {
  struct Shadow {
    enum class shadow { MK };

    template <typename T1> static T1 shadow_rect(T1 f) { return f; }

    template <typename T1> static T1 shadow_rec(T1 f) {
      return shadow_rect<T1>(std::move(f));
    }
  };

  static Shadow::shadow id_shadow();
  static inline const Shadow::shadow t = id_shadow();
};
