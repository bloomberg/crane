#include <effect_dir_path.h>
#include <iostream>

int main() {
    // Smoke test: just verify the code compiles and links.
    // These functions use filesystem effects that require actual directories,
    // so we only verify compilation, not runtime behavior.
    std::cout << "effect_dir_path: compiled OK\n";
    return 0;
}
