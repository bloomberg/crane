#include <effect_unit_stress.h>
#include <cassert>

int main() {
    EffectUnitStress::ret_tt_simple();
    EffectUnitStress::ret_tt_after_bind();
    EffectUnitStress::ret_tt_after_effect();
    EffectUnitStress::conditional_tt(true);
    EffectUnitStress::conditional_tt(false);
    EffectUnitStress::conditional_mixed(true);
    EffectUnitStress::conditional_mixed(false);
    assert(EffectUnitStress::nat_dispatch(0u) == "zero");
    assert(EffectUnitStress::nat_dispatch(1u) == "one");
    assert(EffectUnitStress::nat_dispatch(5u) == "many");
    assert(EffectUnitStress::nested_if_monadic(true, true) == "both");
    assert(EffectUnitStress::nested_if_monadic(true, false) == "first");
    assert(EffectUnitStress::nested_if_monadic(false, true) == "second");
    assert(EffectUnitStress::nested_if_monadic(false, false) == "neither");
    auto result = EffectUnitStress::safe_head(List<unsigned int>::nil());
    assert(!result.has_value());
    auto result2 = EffectUnitStress::safe_head(
        List<unsigned int>::cons(42u, List<unsigned int>::nil()));
    assert(result2.has_value());
    assert(*result2 == 42u);
    return 0;
}
