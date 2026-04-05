#include <effect_complex_args.h>
#include <cassert>
#include <cstdlib>
#include <iostream>

int main() {
    // 1. set_prefixed — concatenated key
    EffectComplexArgs::set_prefixed("APP_", "NAME", "myapp");
    assert(std::string(std::getenv("APP_NAME")) == "myapp");

    // 2. set_with_value — concatenated value
    EffectComplexArgs::set_with_value("GREETING", "Hello, ", "World");
    assert(std::string(std::getenv("GREETING")) == "Hello, World");

    // 3. get_prefixed — concatenated name
    auto r3 = EffectComplexArgs::get_prefixed("APP_", "NAME");
    assert(r3.has_value());
    assert(*r3 == "myapp");

    // 4. print_concat
    EffectComplexArgs::print_concat("Hello", " World");

    // 5. round_trip — set then get with concatenated key
    auto r5 = EffectComplexArgs::round_trip("DB_", "HOST", "localhost");
    assert(r5.has_value());
    assert(*r5 == "localhost");

    // 6. deep_concat — nested concatenation
    EffectComplexArgs::deep_concat("A", "B", "C");
    assert(std::string(std::getenv("ABC")) == "value");

    // 7. chain_with_concat
    setenv("SRC", "original", 1);
    EffectComplexArgs::chain_with_concat("SRC");
    assert(std::string(std::getenv("COPY_SRC")) == "original");

    // 8. unset_prefixed
    setenv("DEL_KEY", "temp", 1);
    EffectComplexArgs::unset_prefixed("DEL_", "KEY");
    assert(std::getenv("DEL_KEY") == nullptr);

    // Cleanup
    unsetenv("APP_NAME");
    unsetenv("GREETING");
    unsetenv("DB_HOST");
    unsetenv("ABC");
    unsetenv("SRC");
    unsetenv("COPY_SRC");

    return 0;
}
