#include "erased_nested_type_args.h"

EOU<Nat> ErasedNestedTypeArgs::use(const Nat &n) { return Ops_nat::madd(n, n); }
