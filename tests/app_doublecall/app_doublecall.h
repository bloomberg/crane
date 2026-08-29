#ifndef INCLUDED_APP_DOUBLECALL
#define INCLUDED_APP_DOUBLECALL

#include <deque>

struct AppDoublecall {
  static std::deque<uint64_t> gen_list(uint64_t n);
  static std::deque<uint64_t> concat_two(uint64_t a, uint64_t b);
};

#endif // INCLUDED_APP_DOUBLECALL
