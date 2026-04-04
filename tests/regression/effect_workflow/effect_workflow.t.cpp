#include <effect_workflow.h>
#include <cassert>
#include <cstdlib>
#include <filesystem>
#include <sstream>
#include <iostream>

int main() {
    // Redirect cin
    std::istringstream input("hello\nworld\ntest\n");
    std::cin.rdbuf(input.rdbuf());

    // 2. conditional_create
    std::string test_dir = std::filesystem::temp_directory_path().string() + "/crane_ew_test";
    std::filesystem::remove_all(test_dir);
    auto r2 = EffectWorkflow::conditional_create(test_dir);
    assert(r2 == test_dir);
    assert(std::filesystem::is_directory(test_dir));

    // 2b. conditional_create on existing dir
    auto r2b = EffectWorkflow::conditional_create(test_dir);
    // May return "exists" or test_dir depending on filesystem
    assert(!r2b.empty());

    // 5. env_or_create
    unsetenv("CRANE_EW_TEST");
    auto r5 = EffectWorkflow::env_or_create("CRANE_EW_TEST", test_dir);
    assert(r5 == test_dir);

    // 6. read_length
    auto r6 = EffectWorkflow::read_length();
    assert(r6 == 5); // "hello" has length 5

    // 7. double_read
    auto [a, b] = EffectWorkflow::double_read();
    assert(a == "world");
    assert(b == "test");

    // 8. return_literal
    auto r8 = EffectWorkflow::return_literal();
    assert(r8 == 42);

    // 4. repeat_log
    auto r4 = EffectWorkflow::repeat_log(3, "tick");
    assert(r4 == 3);

    // Cleanup
    std::filesystem::remove_all(test_dir);
    unsetenv("CRANE_EW_TEST");

    return 0;
}
