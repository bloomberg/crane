#include <effect_complex_return.h>
#include <cassert>
#include <cstdlib>
#include <sstream>
#include <iostream>

int main() {
    // Setup env
    setenv("CRANE_ECR_TEST", "envval", 1);

    // Redirect cin
    std::istringstream input("line1\nline2\nline3\nline4\nfallback\n");
    std::cin.rdbuf(input.rdbuf());

    // 1. read_pair
    auto [a, b] = EffectComplexReturn::read_pair();
    assert(a == "line1");
    assert(b == "line2");

    // 2. maybe_read: true
    auto r2 = EffectComplexReturn::maybe_read(true);
    assert(r2.has_value());
    assert(*r2 == "line3");

    // 2b. maybe_read: false
    auto r2b = EffectComplexReturn::maybe_read(false);
    assert(!r2b.has_value());

    // 5. elapsed_ms (just check it doesn't crash)
    auto elapsed = EffectComplexReturn::elapsed_ms();
    assert(elapsed >= 0);

    // 7. env_or_prompt: existing var
    auto r7 = EffectComplexReturn::env_or_prompt("CRANE_ECR_TEST");
    assert(r7 == "envval");

    // 7b. env_or_prompt: missing var -> reads from cin
    auto r7b = EffectComplexReturn::env_or_prompt("CRANE_MISSING_VAR");
    assert(r7b == "line4");

    // Cleanup
    unsetenv("CRANE_ECR_TEST");

    return 0;
}
