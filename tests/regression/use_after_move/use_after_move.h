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
