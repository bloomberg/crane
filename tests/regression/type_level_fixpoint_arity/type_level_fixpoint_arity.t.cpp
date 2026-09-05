#include <type_level_fixpoint_arity.h>
#include <cassert>
#include <iostream>
int main() { auto r = TypeLevelFixpointArity::total; std::cout << r << " (expect 24)\n"; assert(r == 24u); return 0; }
