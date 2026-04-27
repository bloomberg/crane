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

    __attribute__((pure)) state *operator->() { return this; }

    __attribute__((pure)) const state *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) state clone() const {
      return state{[](auto &&__v) -> unsigned int {
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
      }((*this).acc)};
    }
  };

  __attribute__((pure)) static state execute_kbp(const state &s);
  static inline const state sample = state{3u};
  static inline const bool t = execute_kbp(sample).acc == 15u;
};

#endif // INCLUDED_KBP_MULTIBIT_DEFAULT
