#include <effect_option_string.h>
#include <cassert>
#include <cstdlib>
#include <sstream>
#include <iostream>

int main() {
    std::istringstream input("hello\nworld\n");
    std::cin.rdbuf(input.rdbuf());

    // 1. let_option_match — env set
    setenv("TEST_VAR", "found_value", 1);
    auto r1 = EffectOptionString::let_option_match("TEST_VAR");
    assert(r1 == "found_value");
    // 1b. let_option_match — env not set
    unsetenv("TEST_VAR");
    auto r1b = EffectOptionString::let_option_match("TEST_VAR");
    assert(r1b == "unknown");

    // 2. bind_option_match
    setenv("TEST_VAR", "bound_value", 1);
    auto r2 = EffectOptionString::bind_option_match("TEST_VAR");
    assert(r2 == "bound_value");
    unsetenv("TEST_VAR");
    auto r2b = EffectOptionString::bind_option_match("TEST_VAR");
    assert(r2b == "fallback");

    // 3. option_effect_or_literal — env set: reads from stdin
    setenv("TEST_VAR", "x", 1);
    auto r3 = EffectOptionString::option_effect_or_literal("TEST_VAR");
    assert(r3 == "hello");
    // 3b. env not set: returns literal
    unsetenv("TEST_VAR");
    auto r3b = EffectOptionString::option_effect_or_literal("TEST_VAR");
    assert(r3b == "no_input");

    // 4. nested_option — both set
    setenv("N1", "alpha", 1);
    setenv("N2", "beta", 1);
    auto r4 = EffectOptionString::nested_option("N1", "N2");
    assert(r4 == "alpha/beta");
    // 4b. only first set
    unsetenv("N2");
    auto r4b = EffectOptionString::nested_option("N1", "N2");
    assert(r4b == "alpha");
    // 4c. neither set
    unsetenv("N1");
    auto r4c = EffectOptionString::nested_option("N1", "N2");
    assert(r4c == "none");

    // 5. option_then_effect — just runs, checks no crash
    setenv("TEST_VAR", "printed", 1);
    EffectOptionString::option_then_effect("TEST_VAR");
    unsetenv("TEST_VAR");
    EffectOptionString::option_then_effect("TEST_VAR");

    // 6. option_int
    setenv("TEST_VAR", "hello", 1);
    auto r6 = EffectOptionString::option_int("TEST_VAR");
    assert(r6 == 5); // "hello" has length 5
    unsetenv("TEST_VAR");
    auto r6b = EffectOptionString::option_int("TEST_VAR");
    assert(r6b == 0);

    // Cleanup
    unsetenv("TEST_VAR");
    unsetenv("N1");
    unsetenv("N2");

    return 0;
}
