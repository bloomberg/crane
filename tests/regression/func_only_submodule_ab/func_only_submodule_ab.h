#ifndef INCLUDED_FUNC_ONLY_SUBMODULE_AB
#define INCLUDED_FUNC_ONLY_SUBMODULE_AB

#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct FuncOnlySubmoduleAb {
  struct Root {
    struct A {
      static unsigned int inc(unsigned int n);
    };

    struct B {
      static unsigned int dec(const unsigned int &_x0);
    };
  };

  static inline const unsigned int t = Root::A::inc(Root::B::dec(3u));
};

#endif // INCLUDED_FUNC_ONLY_SUBMODULE_AB
