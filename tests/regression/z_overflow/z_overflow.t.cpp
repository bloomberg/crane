#include <z_overflow.h>
#include <cassert>
#include <cstdint>

int main() {
    assert(ZOverflow::z_fits == INT64_C(1000000000));
    assert(ZOverflow::big_z == INT64_C(9999999999));
    assert(ZOverflow::big_neg_z == INT64_C(-9999999999));
    assert(ZOverflow::z_pow2_33 == INT64_C(8589934592));

    // big_nat = 4294967296 = 2^32, fits correctly in uint64_t
    assert(ZOverflow::big_nat == UINT64_C(4294967296));

    return 0;
}
