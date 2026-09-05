#include <nested_concat_map.h>
#include <cassert>
#include <iostream>
int main() { auto r = NestedConcatMap::total; std::cout << r << " (expect 27)\n"; assert(r == 27u); return 0; }
