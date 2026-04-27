#ifndef INCLUDED_SET_CUR_BANK_MODULO
#define INCLUDED_SET_CUR_BANK_MODULO

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct SetCurBankModulo {
  static inline const unsigned int NBANKS = 4u;

  struct state {
    unsigned int cur_bank;
    unsigned int acc;

    __attribute__((pure)) state *operator->() { return this; }

    __attribute__((pure)) const state *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) state clone() const {
      return state{
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
          }((*this).cur_bank),
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
          }((*this).acc)};
    }
  };

  __attribute__((pure)) static state set_cur_bank(const state &s,
                                                  const unsigned int &b);
  static inline const unsigned int t = set_cur_bank(state{0u, 9u}, 7u).cur_bank;
};

#endif // INCLUDED_SET_CUR_BANK_MODULO
