#include <z_overflow.h>
#include <cassert>
#include <cstdint>

int main() {
    // This value fits in unsigned int, should be correct
    assert(ZOverflow::z_fits == INT64_C(1000000000));

    // BUG: These overflow unsigned int intermediates.
    // 9999999999 > 2^32, so the positive representation overflows.
    // Expected: 9999999999, Actual: 1410065407 (= 9999999999 mod 2^32)
    assert(ZOverflow::big_z == INT64_C(9999999999));
    assert(ZOverflow::big_neg_z == INT64_C(-9999999999));
    assert(ZOverflow::z_pow2_33 == INT64_C(8589934592));

    // NOTE: big_nat = 4294967296 wraps to 0 in unsigned int
    // (4294967296 = 2^32, which is 0 mod 2^32)
    // This is a fundamental limitation of nat -> unsigned int mapping.
    assert(ZOverflow::big_nat == 0u);

    return 0;
}
