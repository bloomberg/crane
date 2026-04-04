#include <effect_getline_stress.h>
#include <cassert>
#include <sstream>
#include <iostream>

int main() {
    // Redirect cin to provide test input
    std::istringstream input("hello\nworld\nfoo\nbar\nbaz\nqux\n");
    std::cin.rdbuf(input.rdbuf());

    // 1. get_or_default
    assert(EffectGetlineStress::get_or_default(false) == "default");
    assert(EffectGetlineStress::get_or_default(true) == "hello");

    // 2. get_nth_line
    assert(EffectGetlineStress::get_nth_line(0u) == "none");
    assert(EffectGetlineStress::get_nth_line(1u) == "world");

    // 4. read_and_echo (just runs without error)
    EffectGetlineStress::read_and_echo();

    // 6. concat_two_lines
    auto result = EffectGetlineStress::concat_two_lines();
    // reads "bar" and "baz"
    assert(result == "barbaz");

    // 5. get_line_length
    auto len = EffectGetlineStress::get_line_length();
    // reads "qux"
    assert(len == 3);

    return 0;
}
