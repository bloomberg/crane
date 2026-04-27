#ifndef INCLUDED_USE_AFTER_MOVE
#define INCLUDED_USE_AFTER_MOVE

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct UseAfterMove {
  struct State {
    unsigned int value;
    unsigned int data;
    unsigned int flag;

    __attribute__((pure)) State *operator->() { return this; }

    __attribute__((pure)) const State *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) State clone() const {
      return State{
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
          }((*this).value),
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
          }((*this).data),
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
          }((*this).flag)};
    }
  };

  __attribute__((pure)) static std::pair<State, unsigned int> pattern1(State s);
  __attribute__((
      pure)) static std::pair<std::pair<State, unsigned int>, unsigned int>
  pattern2(State s);
  __attribute__((
      pure)) static std::pair<std::pair<State, unsigned int>, unsigned int>
  pattern3(State s);
  __attribute__((pure)) static std::pair<State, unsigned int>
  pattern4(State s1);
  __attribute__((pure)) static std::pair<State, unsigned int>
  pattern5(State s1);
  __attribute__((pure)) static std::pair<State, unsigned int> pattern6(State s);
  __attribute__((pure)) static std::pair<
      std::pair<std::pair<State, unsigned int>, unsigned int>, unsigned int>
  pattern7(State s);
};

#endif // INCLUDED_USE_AFTER_MOVE
