#include <use_after_move.h>

#include <memory>
#include <type_traits>
#include <utility>

__attribute__((pure))
std::pair<std::shared_ptr<UseAfterMove::State>, unsigned int>
UseAfterMove::pattern1(std::shared_ptr<UseAfterMove::State> s) {
  return std::make_pair(s, s->value);
}

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<UseAfterMove::State>, unsigned int>,
          unsigned int>
UseAfterMove::pattern2(std::shared_ptr<UseAfterMove::State> s) {
  return std::make_pair(std::make_pair(s, s->value), s->data);
}

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<UseAfterMove::State>, unsigned int>,
          unsigned int>
UseAfterMove::pattern3(std::shared_ptr<UseAfterMove::State> s) {
  return std::make_pair(std::make_pair(s, s->value), s->data);
}

__attribute__((pure))
std::pair<std::shared_ptr<UseAfterMove::State>, unsigned int>
UseAfterMove::pattern4(std::shared_ptr<UseAfterMove::State> s1) {
  return std::make_pair(s1, s1->value);
}

__attribute__((pure))
std::pair<std::shared_ptr<UseAfterMove::State>, unsigned int>
UseAfterMove::pattern5(std::shared_ptr<UseAfterMove::State> s1) {
  return std::make_pair(s1, s1->value);
}

__attribute__((pure))
std::pair<std::shared_ptr<UseAfterMove::State>, unsigned int>
UseAfterMove::pattern6(std::shared_ptr<UseAfterMove::State> s) {
  if (s->flag == 0u) {
    return std::make_pair(s, s->value);
  } else {
    return std::make_pair(s, s->data);
  }
}

__attribute__((pure)) std::pair<
    std::pair<std::pair<std::shared_ptr<UseAfterMove::State>, unsigned int>,
              unsigned int>,
    unsigned int>
UseAfterMove::pattern7(std::shared_ptr<UseAfterMove::State> s) {
  return std::make_pair(std::make_pair(std::make_pair(s, s->value), s->data),
                        s->flag);
}
