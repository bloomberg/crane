#include <monad_class_nested_bind.h>
#include <cassert>
#include <iostream>
int main() { auto r = MonadClassNestedBind::total; std::cout << r << " (expect 3)\n"; assert(r == 3u); return 0; }
