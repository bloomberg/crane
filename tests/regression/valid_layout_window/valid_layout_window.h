#ifndef INCLUDED_VALID_LAYOUT_WINDOW
#define INCLUDED_VALID_LAYOUT_WINDOW

#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct ValidLayoutWindow {
  struct layout {
    unsigned int base_addr;
    unsigned int code_size;

    __attribute__((pure)) layout *operator->() { return this; }

    __attribute__((pure)) const layout *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) layout clone() const {
      return layout{
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).base_addr),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).code_size)};
    }
  };

  __attribute__((pure)) static bool valid_layoutb(const layout &l);
  static inline const unsigned int t = ([]() -> unsigned int {
    if (valid_layoutb(layout{128u, 256u})) {
      return 1u;
    } else {
      return 0u;
    }
  }() + []() -> unsigned int {
    if (valid_layoutb(layout{4090u, 20u})) {
      return 1u;
    } else {
      return 0u;
    }
  }());
};

#endif // INCLUDED_VALID_LAYOUT_WINDOW
