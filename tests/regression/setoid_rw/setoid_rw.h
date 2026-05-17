#ifndef INCLUDED_SETOID_RW
#define INCLUDED_SETOID_RW

#include <utility>

struct SetoidRw {
  static unsigned int mod3(unsigned int n);
  static unsigned int classify_mod3(unsigned int n);
  static unsigned int add_mod3(unsigned int x, unsigned int y);
  static inline const unsigned int test_mod3_0 = mod3(0u);
  static inline const unsigned int test_mod3_5 = mod3(5u);
  static inline const unsigned int test_mod3_9 = mod3(9u);
  static inline const unsigned int test_classify_6 = classify_mod3(6u);
  static inline const unsigned int test_classify_7 = classify_mod3(7u);
  static inline const unsigned int test_add_mod3 = add_mod3(5u, 7u);
};

#endif // INCLUDED_SETOID_RW
