#ifndef INCLUDED_USE_AFTER_MOVE
#define INCLUDED_USE_AFTER_MOVE

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_unique<T>(x->clone()) : nullptr;
  } else {
    return x ? std::make_unique<T>(*x) : nullptr;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using T = std::remove_cvref_t<Target>;
  using S = std::remove_cvref_t<Source>;
  if constexpr (requires(const S &s) {
                  s.has_value();
                  *s;
                }) {
    if (!x.has_value())
      return T{};
    using TInner = std::remove_cvref_t<decltype(*std::declval<const T &>())>;
    return T{clone_as_value<TInner>(*x)};
  } else if constexpr (std::is_same_v<T, S>) {
    if constexpr (is_unique_ptr<T>::value) {
      return clone_value(x);
    } else if constexpr (requires { x.clone(); }) {
      return x.clone();
    } else {
      return x;
    }
  } else if constexpr (is_unique_ptr<S>::value) {
    if (!x)
      return T{};
    return clone_as_value<T>(*x);
  } else if constexpr (is_unique_ptr<T>::value) {
    using Inner = typename is_unique_ptr<T>::element_type;
    return std::make_unique<Inner>(clone_as_value<Inner>(x));
  } else {
    return T(x);
  }
}

struct UseAfterMove {
  struct State {
    unsigned int value;
    unsigned int data;
    unsigned int flag;

    __attribute__((pure)) State *operator->() { return this; }

    __attribute__((pure)) const State *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) State clone() const {
      return State{(*(this)).value, (*(this)).data, (*(this)).flag};
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
