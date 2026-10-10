// Differential test harness: prints canonical output for diffing against OCaml
#include "module.h"
#include <cstdio>
int main() {
    auto r1 = NatMap::find(1, mymap);
    printf("find(1)=%s\n", r1.has_value() ? (std::to_string(r1.value())).c_str() : "None");
    auto r2 = NatMap::find(2, mymap);
    printf("find(2)=%s\n", r2.has_value() ? (std::to_string(r2.value())).c_str() : "None");
    auto r3 = NatMap::find(3, mymap);
    printf("find(3)=%s\n", r3.has_value() ? (std::to_string(r3.value())).c_str() : "None");
    auto r4 = NatMap::find(4, mymap);
    printf("find(4)=%s\n", r4.has_value() ? (std::to_string(r4.value())).c_str() : "None");
    return 0;
}
