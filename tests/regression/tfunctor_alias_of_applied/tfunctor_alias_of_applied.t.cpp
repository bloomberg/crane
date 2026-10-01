#include <tfunctor_alias_of_applied.h>

#include <cassert>
#include <iostream>

int main() {
  // (+1) over [mk_def 1 (mkCFG 2)] gives df_ty 2 and blk 3.
  assert(TfunctorAliasOfApplied::is_five);
  std::cout << "tfunctor_alias_of_applied: ok" << std::endl;
  return 0;
}
