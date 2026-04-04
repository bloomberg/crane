#include <effect_option_match.h>
#include <cassert>
#include <cstdlib>
#include <sstream>
#include <iostream>

int main() {
    // Setup: set some env vars for testing
    setenv("CRANE_TEST_A", "alpha", 1);

    // Redirect cin
    std::istringstream input("fallback\n");
    std::cin.rdbuf(input.rdbuf());

    // 1. show_or_default: existing var
    auto r1 = EffectOptionMatch::show_or_default("CRANE_TEST_A", "default");
    assert(r1 == "alpha");

    // 1b. show_or_default: missing var
    auto r1b = EffectOptionMatch::show_or_default("CRANE_MISSING", "default");
    assert(r1b == "default");

    // 4. set_and_verify
    auto r4 = EffectOptionMatch::set_and_verify("CRANE_TEST_B", "beta");
    assert(r4 == true);

    // 5. find_env_value: first exists
    auto r5 = EffectOptionMatch::find_env_value(
        List<std::string>::cons("CRANE_TEST_A",
            List<std::string>::cons("CRANE_TEST_B",
                List<std::string>::nil())));
    assert(r5.has_value());
    assert(*r5 == "alpha");

    // 5b. find_env_value: all missing
    auto r5b = EffectOptionMatch::find_env_value(
        List<std::string>::cons("CRANE_XXX",
            List<std::string>::cons("CRANE_YYY",
                List<std::string>::nil())));
    assert(!r5b.has_value());

    // Cleanup
    unsetenv("CRANE_TEST_A");
    unsetenv("CRANE_TEST_B");

    return 0;
}
