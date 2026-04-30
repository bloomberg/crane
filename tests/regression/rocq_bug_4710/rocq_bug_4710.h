#ifndef INCLUDED_ROCQ_BUG_4710
#define INCLUDED_ROCQ_BUG_4710

#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct RocqBug4710 {
  struct Foo_ {
    unsigned int foo;

    // ACCESSORS
    Foo_ clone() const { return Foo_{(*(this)).foo}; }
  };

  struct Foo2 {
    unsigned int foo2p;
    bool foo2b;

    // ACCESSORS
    Foo2 clone() const { return Foo2{(*(this)).foo2p, (*(this)).foo2b}; }
  };

  static unsigned int bla(const Foo2 &x);
  static bool bla_(const unsigned int &_x, const Foo2 &x);
  static inline const Foo_ test_foo = Foo_{5u};
  static inline const Foo2 test_foo2 = Foo2{10u, true};
  static inline const unsigned int test_bla = bla(test_foo2);
  static inline const bool test_bla_ = bla_(0u, test_foo2);
};

#endif // INCLUDED_ROCQ_BUG_4710
