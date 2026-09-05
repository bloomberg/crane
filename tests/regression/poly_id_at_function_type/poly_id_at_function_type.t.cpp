#include <poly_id_at_function_type.h>
#include <cassert>
#include <iostream>
int main() { auto r = PolyIdAtFunctionType::total; std::cout << r << " (expect 23)\n"; assert(r == 23u); return 0; }
