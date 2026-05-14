#include "SepExtAliasClash.h"

#include <cassert>

int main() {
  // Regression test: module alias inside a functor shares the same short name
  // as a top-level module alias.  Both 'Impl' at top level and 'Impl' inside
  // 'LemmasFn' should compile without an error_module_clash crash.

  // ImplFn<MySig>::foo is the identity function on unsigned int
  assert(SepExtAliasClash::Impl::foo(42u) == 42u);

  // LemmasFn<MySig>::bar calls Impl::foo (the inner alias) and returns the
  // same value
  assert(SepExtAliasClash::Lemmas::bar(7u) == 7u);

  return 0;
}
