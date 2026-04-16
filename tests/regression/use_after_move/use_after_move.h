#ifndef INCLUDED_USE_AFTER_MOVE
#define INCLUDED_USE_AFTER_MOVE

#include <memory>
#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct UseAfterMove {
  struct State {
    unsigned int value;
    unsigned int data;
    unsigned int flag;
  };

  __attribute__((pure)) static std::pair<std::shared_ptr<State>, unsigned int>
  pattern1(std::shared_ptr<State> s);
  __attribute__((pure)) static std::pair<
      std::pair<std::shared_ptr<State>, unsigned int>, unsigned int>
  pattern2(std::shared_ptr<State> s);
  __attribute__((pure)) static std::pair<
      std::pair<std::shared_ptr<State>, unsigned int>, unsigned int>
  pattern3(std::shared_ptr<State> s);
  __attribute__((pure)) static std::pair<std::shared_ptr<State>, unsigned int>
  pattern4(std::shared_ptr<State> s1);
  __attribute__((pure)) static std::pair<std::shared_ptr<State>, unsigned int>
  pattern5(std::shared_ptr<State> s1);
  __attribute__((pure)) static std::pair<std::shared_ptr<State>, unsigned int>
  pattern6(std::shared_ptr<State> s);
  __attribute__((pure)) static std::pair<
      std::pair<std::pair<std::shared_ptr<State>, unsigned int>, unsigned int>,
      unsigned int>
  pattern7(std::shared_ptr<State> s);
};

#endif // INCLUDED_USE_AFTER_MOVE
