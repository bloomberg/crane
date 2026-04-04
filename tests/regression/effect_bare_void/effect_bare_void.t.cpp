#include <effect_bare_void.h>
#include <cassert>
#include <cstdlib>
#include <sstream>
#include <iostream>

int main() {
    std::istringstream input("hello\n");
    std::cin.rdbuf(input.rdbuf());

    // 1. just_print
    EffectBareVoid::just_print("test1");

    // 2. just_set
    EffectBareVoid::just_set("KEY", "value");
    assert(std::string(std::getenv("KEY")) == "value");

    // 3. print_then_ret
    EffectBareVoid::print_then_ret("test3");

    // 4. cond_print
    EffectBareVoid::cond_print(true, "printed");
    EffectBareVoid::cond_print(false, "not_printed");

    // 5. set_then_print
    EffectBareVoid::set_then_print("K2", "V2");
    assert(std::string(std::getenv("K2")) == "V2");

    // 6. just_read
    auto r6 = EffectBareVoid::just_read();
    assert(r6 == "hello");

    // 7. just_get_env
    setenv("TESTVAR", "envval", 1);
    auto r7 = EffectBareVoid::just_get_env("TESTVAR");
    assert(r7.has_value());
    assert(*r7 == "envval");

    // Cleanup
    unsetenv("KEY");
    unsetenv("K2");
    unsetenv("TESTVAR");

    return 0;
}
