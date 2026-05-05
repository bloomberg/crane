#ifndef INCLUDED_SEPEXTALIASCLASH
#define INCLUDED_SEPEXTALIASCLASH

#include <memory>
#include <optional>
#include <type_traits>

namespace SepExtAliasClash {

template <typename M>
concept Sig = requires { typename M::t; };

template <Sig S> struct ImplFn {
  constexpr static typename S::t foo(const typename S::t x) { return x; }
};

template <Sig ST> struct LemmasFn {
  using Impl = ImplFn<ST>;

  constexpr static typename ST::t bar(const typename ST::t _x0) {
    return Impl::foo(_x0);
  }
};

struct MySig {
  using t = unsigned int;
};

using Impl = ImplFn<MySig>;
using Lemmas = LemmasFn<MySig>;

} // namespace SepExtAliasClash

#endif // INCLUDED_SEPEXTALIASCLASH
