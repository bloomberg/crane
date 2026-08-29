#include "use_after_move.h"

std::pair<UseAfterMove::State, uint64_t>
UseAfterMove::pattern1(UseAfterMove::State s) {
  return std::make_pair(s, s.value);
}

std::pair<std::pair<UseAfterMove::State, uint64_t>, uint64_t>
UseAfterMove::pattern2(UseAfterMove::State s) {
  return std::make_pair(std::make_pair(s, s.value), s.data);
}

std::pair<std::pair<UseAfterMove::State, uint64_t>, uint64_t>
UseAfterMove::pattern3(UseAfterMove::State s) {
  return std::make_pair(std::make_pair(s, s.value), s.data);
}

std::pair<UseAfterMove::State, uint64_t>
UseAfterMove::pattern4(UseAfterMove::State s1) {
  return std::make_pair(s1, s1.value);
}

std::pair<UseAfterMove::State, uint64_t>
UseAfterMove::pattern5(UseAfterMove::State s1) {
  return std::make_pair(s1, s1.value);
}

std::pair<UseAfterMove::State, uint64_t>
UseAfterMove::pattern6(UseAfterMove::State s) {
  if (s.flag == UINT64_C(0)) {
    return std::make_pair(s, s.value);
  } else {
    return std::make_pair(s, s.data);
  }
}

std::pair<std::pair<std::pair<UseAfterMove::State, uint64_t>, uint64_t>,
          uint64_t>
UseAfterMove::pattern7(UseAfterMove::State s) {
  return std::make_pair(std::make_pair(std::make_pair(s, s.value), s.data),
                        s.flag);
}
