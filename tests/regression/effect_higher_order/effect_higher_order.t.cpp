#include <effect_higher_order.h>
#include <cassert>
#include <cstdlib>
#include <sstream>
#include <iostream>

int main() {
    // Setup
    setenv("CRANE_HO_A", "alpha", 1);

    std::istringstream input("hello\nworld\nbeta\n");
    std::cin.rdbuf(input.rdbuf());

    // 8. process_input
    auto r8 = EffectHigherOrder::process_input();
    assert(r8 == "[hello]");

    // 6. lookup_or_ask: existing
    auto r6a = EffectHigherOrder::lookup_or_ask("CRANE_HO_A");
    assert(r6a == "alpha");

    // 6. lookup_or_ask: missing -> reads from cin
    auto r6b = EffectHigherOrder::lookup_or_ask("CRANE_HO_NEW");
    assert(r6b == "world");

    // Verify set_env worked
    auto r6c = EffectHigherOrder::lookup_or_ask("CRANE_HO_NEW");
    assert(r6c == "world");

    // Cleanup
    unsetenv("CRANE_HO_A");
    unsetenv("CRANE_HO_NEW");

    return 0;
}
