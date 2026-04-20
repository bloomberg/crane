#ifndef INCLUDED_ROCQ_BUG_4710
#define INCLUDED_ROCQ_BUG_4710

#include <memory>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct RocqBug4710 {
  struct Foo_ {
    unsigned int foo;
  };

  struct Foo2 {
    unsigned int foo2p;
    bool foo2b;
  };

  __attribute__((pure)) static unsigned int bla(const std::shared_ptr<Foo2> &x);
  __attribute__((pure)) static bool bla_(const unsigned int _x,
                                         const std::shared_ptr<Foo2> &x);
  static inline const std::shared_ptr<Foo_> test_foo =
      std::make_shared<Foo_>(Foo_{5u});
  static inline const std::shared_ptr<Foo2> test_foo2 =
      std::make_shared<Foo2>(Foo2{10u, true});
  static inline const unsigned int test_bla = bla(test_foo2);
  static inline const bool test_bla_ = bla_(0u, test_foo2);
};

#endif // INCLUDED_ROCQ_BUG_4710
