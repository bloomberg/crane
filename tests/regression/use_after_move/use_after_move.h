#ifndef INCLUDED_USE_AFTER_MOVE
#define INCLUDED_USE_AFTER_MOVE

#include <utility>

struct UseAfterMove {
  struct State {
    uint64_t value;
    uint64_t data;
    uint64_t flag;
  };

  static std::pair<State, uint64_t> pattern1(const State &s);
  static std::pair<std::pair<State, uint64_t>, uint64_t>
  pattern2(const State &s);
  static std::pair<std::pair<State, uint64_t>, uint64_t>
  pattern3(const State &s);
  static std::pair<State, uint64_t> pattern4(const State &s1);
  static std::pair<State, uint64_t> pattern5(const State &s1);
  static std::pair<State, uint64_t> pattern6(const State &s);
  static std::pair<std::pair<std::pair<State, uint64_t>, uint64_t>, uint64_t>
  pattern7(const State &s);
};

#endif // INCLUDED_USE_AFTER_MOVE
