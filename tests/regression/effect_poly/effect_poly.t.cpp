#include <effect_poly.h>
#include <cassert>

int main() {
    // test_map_result: Ret 41 then S => 42
    assert(EffectPoly::test_map_result() == 42u);
    assert(EffectPoly::test_lift_nat() == 42u);
    assert(EffectPoly::test_lift_string() == "hello");
    assert(EffectPoly::test_lift_bool() == true);
    // test_when and test_unless just need to compile and not crash
    EffectPoly::test_when();
    EffectPoly::test_unless();
    // test_fold: 0 + 1 + 2 + 3 = 6
    assert(EffectPoly::test_fold() == 6u);
    return 0;
}
