#ifndef INCLUDED_TODO_EXPLICIT_TYPE_APP_ALIAS
#define INCLUDED_TODO_EXPLICIT_TYPE_APP_ALIAS

struct TodoExplicitTypeAppAlias {
  template <typename T1> static T1 id(T1 x) { return x; }

  static inline const uint64_t test_value = []() {
    return []() {
      uint64_t kept_nat = id(UINT64_C(9));
      bool kept_bool = id(true);
      return (kept_nat + (kept_bool ? UINT64_C(1) : UINT64_C(0)));
    }();
  }();
};

#endif // INCLUDED_TODO_EXPLICIT_TYPE_APP_ALIAS
