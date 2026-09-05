#include <erased_pair_fn_call.h>
#include <cassert>
#include <iostream>
int main() { auto r = ErasedPairFnCall::total; std::cout << r << " (expect 5)\n"; assert(r == 5u); return 0; }
