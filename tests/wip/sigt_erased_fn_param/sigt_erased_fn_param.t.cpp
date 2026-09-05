#include <sigt_erased_fn_param.h>
#include <cassert>
#include <iostream>
int main() { auto r = SigtErasedFnParam::total; std::cout << r << "\n"; assert(r == 9u); return 0; }
