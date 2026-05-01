#include <use_after_move.h>

std::pair<UseAfterMove::State, unsigned int>
UseAfterMove::pattern1(UseAfterMove::State s) {
  return std::make_pair(s, s.value);
}

std::pair<std::pair<UseAfterMove::State, unsigned int>, unsigned int>
UseAfterMove::pattern2(UseAfterMove::State s) {
  return std::make_pair(std::make_pair(s, s.value), s.data);
}

std::pair<std::pair<UseAfterMove::State, unsigned int>, unsigned int>
UseAfterMove::pattern3(UseAfterMove::State s) {
  return std::make_pair(std::make_pair(s, s.value), s.data);
}

std::pair<UseAfterMove::State, unsigned int>
UseAfterMove::pattern4(UseAfterMove::State s1) {
  return std::make_pair(s1, s1.value);
}

std::pair<UseAfterMove::State, unsigned int>
UseAfterMove::pattern5(UseAfterMove::State s1) {
  return std::make_pair(s1, s1.value);
}

std::pair<UseAfterMove::State, unsigned int>
UseAfterMove::pattern6(UseAfterMove::State s) {
  if (s.flag == 0u) {
    return std::make_pair(s, s.value);
  } else {
    return std::make_pair(s, s.data);
  }
}

std::pair<std::pair<std::pair<UseAfterMove::State, unsigned int>, unsigned int>,
          unsigned int>
UseAfterMove::pattern7(UseAfterMove::State s) {
  return std::make_pair(std::make_pair(std::make_pair(s, s.value), s.data),
                        s.flag);
}
