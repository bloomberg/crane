#ifndef INCLUDED_ROCQ_BUG_4710
#define INCLUDED_ROCQ_BUG_4710

struct RocqBug4710 {
  struct Foo_ {
    uint64_t foo;

    // ACCESSORS
    Foo_ clone() const { return Foo_{(*this).foo}; }
  };

  struct Foo2 {
    uint64_t foo2p;
    bool foo2b;

    // ACCESSORS
    Foo2 clone() const { return Foo2{(*this).foo2p, (*this).foo2b}; }
  };

  static uint64_t bla(const Foo2 &x);
  static bool bla_(uint64_t _x, const Foo2 &x);
  static inline const Foo_ test_foo = Foo_{UINT64_C(5)};
  static inline const Foo2 test_foo2 = Foo2{UINT64_C(10), true};
  static inline const uint64_t test_bla = bla(test_foo2);
  static inline const bool test_bla_ = bla_(UINT64_C(0), test_foo2);
};

#endif // INCLUDED_ROCQ_BUG_4710
