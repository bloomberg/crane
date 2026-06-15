#ifndef INCLUDED_SEPEXTALIASCLASH
#define INCLUDED_SEPEXTALIASCLASH

namespace SepExtAliasClash {

template <typename M>
concept Sig = requires { typename M::t; };

template <Sig S> struct ImplFn {
  static typename S::t foo(typename S::t x) { return x; }
};

template <Sig ST> struct LemmasFn {
  using Impl = ImplFn<ST>;

  static typename ST::t bar(typename ST::t _x0) { return Impl::foo(_x0); }
};

struct MySig {
  using t = uint64_t;
};

using Impl = ImplFn<MySig>;
using Lemmas = LemmasFn<MySig>;

} // namespace SepExtAliasClash

#endif // INCLUDED_SEPEXTALIASCLASH
