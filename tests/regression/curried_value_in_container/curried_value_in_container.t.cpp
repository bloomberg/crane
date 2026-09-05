#include <curried_value_in_container.h>
#include <cassert>
#include <iostream>
int main() { auto r = CurriedValueInContainer::total; std::cout << r << " (expect 27)\n"; assert(r == 27u); return 0; }
