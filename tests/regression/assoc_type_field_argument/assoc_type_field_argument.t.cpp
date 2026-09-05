#include <assoc_type_field_argument.h>
#include <cassert>
#include <iostream>
int main() { auto r = AssocTypeFieldArgument::total; std::cout << r << " (expect 6)\n"; assert(r == 6u); return 0; }
