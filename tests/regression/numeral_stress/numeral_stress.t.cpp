#include <numeral_stress.h>
#include <cassert>

int main() {
    // 1. Numeral in option
    assert(NumeralStress::opt_100.has_value());
    assert(*NumeralStress::opt_100 == 100u);
    assert(NumeralStress::opt_neg.has_value());
    assert(*NumeralStress::opt_neg == -50);

    // 2. Pair
    assert(NumeralStress::pair_nums.first == 42u);
    assert(NumeralStress::pair_nums.second == -7);

    // 4. Nat.add folding
    assert(NumeralStress::add_big == 3000u);

    // 5. Match on numeral
    assert(NumeralStress::match_numeral == 1u);

    // 6. Fixpoint with numeral arg
    assert(NumeralStress::test_count == 50u);

    // 8. Record with numerals
    assert(NumeralStress::origin->px == 0u);
    assert(NumeralStress::origin->py == 0u);
    assert(NumeralStress::far_point->px == 999u);
    assert(NumeralStress::far_point->py == 888u);

    // 9. Range check
    assert(NumeralStress::test_range == true);

    // 10. Mixed arith
    assert(NumeralStress::test_mixed == 142);

    return 0;
}
