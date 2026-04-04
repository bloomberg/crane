#include <effect_cross_module.h>
#include <cassert>
#include <sstream>
#include <iostream>

int main() {
    // Redirect cin for testing
    std::istringstream input("Alice\nBob\n");
    std::cin.rdbuf(input.rdbuf());

    // test_greet: just runs without error
    EffectCrossModule::test_greet();

    // test_ask_name: reads from cin
    auto name = EffectCrossModule::test_ask_name();
    assert(name == "Alice");

    // test_with_greeting: reads name, greets, returns length
    auto len = EffectCrossModule::test_with_greeting();
    assert(len == 3);  // "Bob" has length 3

    return 0;
}
