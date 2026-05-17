#ifndef INCLUDED_USE_AFTER_MOVE
#define INCLUDED_USE_AFTER_MOVE

#include <utility>

struct UseAfterMove {
  struct State {
    uint64_t value;
    uint64_t data;
    uint64_t flag;

    // ACCESSORS
    State clone() const {
      return State{(*this).value, (*this).data, (*this).flag};
    }
  };

  static std::pair<State, uint64_t> pattern1(State s);
  static std::pair<std::pair<State, uint64_t>, uint64_t> pattern2(State s);
  static std::pair<std::pair<State, uint64_t>, uint64_t> pattern3(State s);
  static std::pair<State, uint64_t> pattern4(State s1);
  static std::pair<State, uint64_t> pattern5(State s1);
  static std::pair<State, uint64_t> pattern6(State s);
  static std::pair<std::pair<std::pair<State, uint64_t>, uint64_t>, uint64_t>
  pattern7(State s);
};

#endif // INCLUDED_USE_AFTER_MOVE
