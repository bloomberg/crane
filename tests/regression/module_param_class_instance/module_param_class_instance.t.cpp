#include <module_param_class_instance.h>
#include <cassert>
#include <iostream>
int main() { auto r = ModuleParamClassInstance::total; std::cout << r << " (expect 24)\n"; assert(r == 24u); return 0; }
