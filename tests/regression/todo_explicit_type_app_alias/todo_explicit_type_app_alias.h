#ifndef INCLUDED_TODO_EXPLICIT_TYPE_APP_ALIAS
#define INCLUDED_TODO_EXPLICIT_TYPE_APP_ALIAS

#include <cstdint>

struct TodoExplicitTypeAppAlias {
  template <typename T1> static T1 id(T1 x) { return x; }

  static constexpr uint64_t test_value = UINT64_C(10);
};

#endif // INCLUDED_TODO_EXPLICIT_TYPE_APP_ALIAS
