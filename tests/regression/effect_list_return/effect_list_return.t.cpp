#include <effect_list_return.h>
#include <cassert>
#include <cstdlib>
#include <filesystem>
#include <sstream>
#include <iostream>

int main() {
    // Redirect cin
    std::istringstream input("testline\n");
    std::cin.rdbuf(input.rdbuf());

    // 2. make_and_check
    std::string test_dir = std::filesystem::temp_directory_path().string() + "/crane_elr_test";
    std::filesystem::remove_all(test_dir);
    auto r2 = EffectListReturn::make_and_check(test_dir);
    assert(r2 == true);
    assert(std::filesystem::is_directory(test_dir));

    // 1. list_files (empty dir)
    auto r1 = EffectListReturn::list_files(test_dir);
    // Just check it returns without error

    // 3. timestamped_line
    auto [t, line] = EffectListReturn::timestamped_line();
    assert(t > 0);
    assert(line == "testline");

    // 4. get_cwd
    auto cwd = EffectListReturn::get_cwd();
    assert(!cwd.empty());

    // 5. create_and_list (dir already exists, so create_directories returns false)
    std::string test_dir2 = test_dir + "/sub";
    auto [ok, files] = EffectListReturn::create_and_list(test_dir2);
    assert(ok == true);

    // Cleanup
    std::filesystem::remove_all(test_dir);

    return 0;
}
