#include <existential_ctor_erased_fn.h>
#include <cassert>
#include <iostream>
int main() { auto r = ExistentialCtorErasedFn::total; std::cout << r << " (expect 11)\n"; assert(r == 11u); return 0; }
