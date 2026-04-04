#include <effect_nested_io.h>
#include <cassert>
#include <cstdlib>
#include <sstream>
#include <iostream>

int main() {
    std::istringstream input("alice\nbob\nfoo\nbar\nquit\nkey1\nval1\ngreeting\nstored_val\nhello\n");
    std::cin.rdbuf(input.rdbuf());

    // 1. read_optional — wraps stdin line in Some
    auto r1 = EffectNestedIo::read_optional();
    assert(r1.has_value());
    assert(*r1 == "alice");

    // 2. read_pair — reads line and returns pair with length
    auto [line2, len2] = EffectNestedIo::read_pair();
    assert(line2 == "bob");
    assert(len2 == 3);

    // 3. read_two_lines — reads two lines
    auto [a3, b3] = EffectNestedIo::read_two_lines();
    assert(a3 == "foo");
    assert(b3 == "bar");

    // 4. timed_read — reads "quit"
    auto [line4, t4] = EffectNestedIo::timed_read();
    assert(line4 == "quit");
    assert(t4 > 0);

    // 5. multi_read_store — reads two lines, stores in env
    auto [k5, v5] = EffectNestedIo::multi_read_store();
    assert(k5 == "key1");
    assert(v5 == "val1");

    // 6. read_and_greet — reads "greeting"
    auto r6 = EffectNestedIo::read_and_greet();
    assert(r6 == "Hello, greeting");

    // 7. read_and_store
    auto r7 = EffectNestedIo::read_and_store("MY_KEY");
    assert(r7 == "stored_val");

    // 8. read_length
    auto r8 = EffectNestedIo::read_length();
    assert(r8 == 5); // "hello" has length 5

    // Cleanup
    unsetenv("KEY");
    unsetenv("VALUE");
    unsetenv("MY_KEY");

    return 0;
}
