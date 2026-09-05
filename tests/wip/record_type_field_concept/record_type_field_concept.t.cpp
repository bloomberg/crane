#include <record_type_field_concept.h>
#include <cassert>
#include <iostream>
int main() { auto r = RecordTypeFieldConcept::total; std::cout << r << " (expect 22)\n"; assert(r == 22u); return 0; }
