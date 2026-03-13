#ifndef INCLUDED_QUALIFIED_SHADOW_ASCII
#define INCLUDED_QUALIFIED_SHADOW_ASCII

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct QualifiedShadowAscii {
  struct Shadow {
    enum class shadow { e_MK };

    template <typename T1> static T1 shadow_rect(const T1 f, const shadow s) {
      return [&](void) {
        switch (s) {
        case shadow::e_MK: {
          return f;
        }
        }
      }();
    }

    template <typename T1> static T1 shadow_rec(const T1 f, const shadow s) {
      return [&](void) {
        switch (s) {
        case shadow::e_MK: {
          return f;
        }
        }
      }();
    }
  };

  __attribute__((pure)) static Shadow::shadow id_shadow(const Shadow::shadow x);
  static inline const Shadow::shadow t = id_shadow(Shadow::shadow::e_MK);
};

#endif // INCLUDED_QUALIFIED_SHADOW_ASCII
