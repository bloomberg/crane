#include <numeral_edge.h>
#include <cassert>

int main() {
    assert(NumeralEdge::nat_zero == 0u);
    assert(NumeralEdge::nat_one == 1u);
    assert(NumeralEdge::nat_ten == 10u);
    assert(NumeralEdge::nat_hundred == 100u);
    assert(NumeralEdge::n_zero == 0u);
    assert(NumeralEdge::z_zero == 0);
    assert(NumeralEdge::z_neg == -5);
    assert(NumeralEdge::z_neg_one == -1);
    assert(NumeralEdge::z_thousand == 1000);
    assert(NumeralEdge::n_large == 65535u);
    assert(NumeralEdge::nat_pow2_8 == 256u);
    assert(NumeralEdge::nat_pow2_16 == 65536u);
    assert(NumeralEdge::z_pow2_30 == 1073741824);
    assert(NumeralEdge::add_numerals == 300u);
    assert(NumeralEdge::mul_numerals == 200);
    assert(NumeralEdge::sub_numerals == 99);
    assert(NumeralEdge::test_arg == 43u);
    assert(NumeralEdge::some_nat.has_value());
    assert(*NumeralEdge::some_nat == 99u);
    assert(NumeralEdge::nat_pair.first == 10u);
    assert(NumeralEdge::nat_pair.second == 20u);
    assert(NumeralEdge::classify(0u) == 0u);
    assert(NumeralEdge::classify(1u) == 1u);
    assert(NumeralEdge::classify(5u) == 2u);
    assert(NumeralEdge::is_big(50u) == false);
    assert(NumeralEdge::is_big(100u) == true);
    assert(NumeralEdge::z_arith == 31);
    assert(NumeralEdge::z_pair.first == -42);
    assert(NumeralEdge::z_pair.second == 42);
    assert(NumeralEdge::n_to_nat_test == 255u);
    return 0;
}
