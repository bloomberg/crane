#include <map_returns_closure.h>
#include <cassert>
#include <iostream>
int main() { auto r = MapReturnsClosure::total; std::cout << r << "\n"; assert(r == 36u); return 0; }
