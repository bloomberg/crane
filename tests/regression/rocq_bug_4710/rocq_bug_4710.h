#ifndef INCLUDED_ROCQ_BUG_4710
#define INCLUDED_ROCQ_BUG_4710

#include <cstdint>

struct RocqBug4710 {
  struct Foo_ {
    uint64_t foo;
  };

  struct Foo2 {
    uint64_t foo2p;
    bool foo2b;
  };

  static uint64_t bla(const Foo2 &x);
  static bool bla_(uint64_t _x, const Foo2 &x);
  static inline const Foo_ test_foo = Foo_{UINT64_C(5)};
  static inline const Foo2 test_foo2 = Foo2{UINT64_C(10), true};
  static constexpr uint64_t test_bla = UINT64_C(10);
  static constexpr bool test_bla_ = true;
};

#endif // INCLUDED_ROCQ_BUG_4710
