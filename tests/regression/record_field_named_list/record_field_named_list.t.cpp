#include <record_field_named_list.h>
#include <cassert>
#include <iostream>
int main() { auto r = RecordFieldNamedList::total; std::cout << r << " (expect 9)\n"; assert(r == 9u); return 0; }
