// Differential test harness: prints canonical output for diffing against OCaml
#include "mutual_mod.h"
#include <cstdio>
int main() {
    printf("test_even_len=%u\n", test_even_len);
    printf("test_odd_len=%u\n", test_odd_len);
    return 0;
}
