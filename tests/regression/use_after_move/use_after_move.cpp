#include "use_after_move.h"

std::pair<UseAfterMove::State, uint64_t>
UseAfterMove::pattern1(const UseAfterMove::State &s) {
  return std::make_pair(s, s.value);
}

std::pair<std::pair<UseAfterMove::State, uint64_t>, uint64_t>
UseAfterMove::pattern2(const UseAfterMove::State &s) {
  return std::make_pair(std::make_pair(s, s.value), s.data);
}

std::pair<std::pair<UseAfterMove::State, uint64_t>, uint64_t>
UseAfterMove::pattern3(const UseAfterMove::State &s) {
  return pattern2(s);
}

std::pair<UseAfterMove::State, uint64_t>
UseAfterMove::pattern4(const UseAfterMove::State &s1) {
  return pattern1(s1);
}

std::pair<UseAfterMove::State, uint64_t>
UseAfterMove::pattern5(const UseAfterMove::State &s1) {
  return pattern1(s1);
}

std::pair<UseAfterMove::State, uint64_t>
UseAfterMove::pattern6(const UseAfterMove::State &s) {
  if (s.flag == UINT64_C(0)) {
    return std::make_pair(s, s.value);
  } else {
    return std::make_pair(s, s.data);
  }
}

std::pair<std::pair<std::pair<UseAfterMove::State, uint64_t>, uint64_t>,
          uint64_t>
UseAfterMove::pattern7(const UseAfterMove::State &s) {
  return std::make_pair(std::make_pair(std::make_pair(s, s.value), s.data),
                        s.flag);
}
