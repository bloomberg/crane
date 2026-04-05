#include <effect_match_arg.h>
#include <cassert>
#include <cstdlib>
#include <iostream>

int main() {
    // 1. set_bool_value — ternary as value arg
    EffectMatchArg::set_bool_value(true, "TEST_FLAG");
    assert(std::string(std::getenv("TEST_FLAG")) == "yes");
    EffectMatchArg::set_bool_value(false, "TEST_FLAG");
    assert(std::string(std::getenv("TEST_FLAG")) == "no");

    // 2. set_bool_key — ternary as key arg
    EffectMatchArg::set_bool_key(true, "val_a");
    assert(std::string(std::getenv("KEY_A")) == "val_a");
    EffectMatchArg::set_bool_key(false, "val_b");
    assert(std::string(std::getenv("KEY_B")) == "val_b");

    // 4. print_conditional — should just print without crash
    EffectMatchArg::print_conditional(true);
    EffectMatchArg::print_conditional(false);

    // 5. get_conditional
    auto r = EffectMatchArg::get_conditional(true);
    assert(r.has_value());
    assert(*r == "val_a");

    // 6. round_trip_match
    auto r6 = EffectMatchArg::round_trip_match(true);
    assert(r6.has_value());
    assert(*r6 == "val");

    // Cleanup
    unsetenv("TEST_FLAG");
    unsetenv("KEY_A");
    unsetenv("KEY_B");
    unsetenv("X");

    std::cout << "effect_match_arg: all tests passed\n";
    return 0;
}
