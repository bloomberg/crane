#include <type_constructor_param_inductive.h>
#include <cassert>
#include <iostream>
int main() { auto r = TypeConstructorParamInductive::total; std::cout << r << " (expect 8)\n"; assert(r == 8u); return 0; }
