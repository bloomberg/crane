#include <class_instance_at_function_type.h>
#include <cassert>
#include <iostream>
int main() { auto r = ClassInstanceAtFunctionType::total; std::cout << r << " (expect 35)\n"; assert(r == 35u); return 0; }
