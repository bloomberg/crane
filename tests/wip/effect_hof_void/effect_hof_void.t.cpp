#include <effect_hof_void.h>
#include <cassert>
#include <cstdlib>
#include <iostream>

int main() {
    // 7. concrete_use — applies print_endline as callback
    auto r7 = EffectHofVoid::concrete_use();
    assert(r7 == "hello");

    // 8. concrete_set
    EffectHofVoid::concrete_set();
    assert(std::string(std::getenv("mykey")) == "myval");

    // 2. apply_then_return — with print_endline
    auto r2 = EffectHofVoid::apply_then_return(
        [](const std::string& s) { std::cout << s << '\n'; },
        "test_atr");
    assert(r2 == "test_atr");

    // 4. apply_if
    int count = 0;
    EffectHofVoid::apply_if(true,
        [&count](const std::string&) { count++; },
        "x");
    assert(count == 1);
    EffectHofVoid::apply_if(false,
        [&count](const std::string&) { count++; },
        "x");
    assert(count == 1); // not called

    // 6. apply_n
    int n_count = 0;
    auto r6 = EffectHofVoid::apply_n(
        [&n_count](const std::string&) { n_count++; },
        "tick", 3u);
    assert(r6 == 3u);
    assert(n_count == 3);

    // Cleanup
    unsetenv("mykey");

    return 0;
}
