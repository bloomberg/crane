#include <effect_bind_action.h>
#include <cassert>
#include <cstdlib>
#include <sstream>
#include <iostream>

int main() {
    // Redirect cin
    std::istringstream input("hello\nworld\n");
    std::cin.rdbuf(input.rdbuf());

    // 1. conditional_read with stdin
    auto r1 = EffectBindAction::conditional_read(true);
    assert(r1 == "hello");

    // 1b. conditional_read without stdin
    auto r1b = EffectBindAction::conditional_read(false);
    assert(r1b == "default");

    // 2. conditional_effect
    auto r2 = EffectBindAction::conditional_effect(false);
    assert(r2 == 0);

    // 3. maybe_override with env not set
    unsetenv("CRANE_BA_TEST");
    auto r3 = EffectBindAction::maybe_override("CRANE_BA_TEST", "fallback");
    assert(r3 == "fallback");

    // 3b. maybe_override with env set
    setenv("CRANE_BA_TEST", "override", 1);
    auto r3b = EffectBindAction::maybe_override("CRANE_BA_TEST", "fallback");
    assert(r3b == "override");

    // 5. echo_if
    auto r5 = EffectBindAction::echo_if(true);
    assert(r5 == "world");

    // 6. use_helper
    auto r6 = EffectBindAction::use_helper(true);
    assert(r6 == "yes");

    // 7. let_match_then_effect
    auto r7 = EffectBindAction::let_match_then_effect(0);
    assert(r7 == "zero");

    auto r7b = EffectBindAction::let_match_then_effect(5);
    assert(r7b == "other");

    // 8. discard_conditional
    auto r8 = EffectBindAction::discard_conditional(true);
    assert(r8 == 42);

    // Cleanup
    unsetenv("CRANE_BA_TEST");

    return 0;
}
