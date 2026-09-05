#include <unit_returning_callback_map.h>
#include <cassert>
#include <iostream>
int main() { auto r = UnitReturningCallbackMap::total; std::cout << r << " (expect 7)\n"; assert(r == 7u); return 0; }
