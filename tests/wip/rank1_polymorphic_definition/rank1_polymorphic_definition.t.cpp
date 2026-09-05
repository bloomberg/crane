#include <rank1_polymorphic_definition.h>
#include <cassert>
#include <iostream>
int main() { auto r = Rank1PolymorphicDefinition::total; std::cout << r << " (expect 13)\n"; assert(r == 13u); return 0; }
