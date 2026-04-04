#include <read_variable_capture.h>
#include <cassert>
#include <fstream>

int main() {
    // Create a test file
    {
        std::ofstream f("_test_rvc.txt");
        f << "hello from file";
    }

    // read_literal: reads from "file.txt" (may fail if file doesn't exist,
    // but the test is about compilation, not runtime)
    // auto r1 = ReadVariableCapture::read_literal();

    // read_variable: reads from a variable path - THIS is the bug test
    auto r2 = ReadVariableCapture::read_variable("_test_rvc.txt");
    assert(r2 == "hello from file");

    // read_and_check
    auto r3 = ReadVariableCapture::read_and_check("_test_rvc.txt");
    assert(r3 == "hello from file");

    auto r4 = ReadVariableCapture::read_and_check("_nonexistent_file.txt");
    assert(r4 == "");

    // Cleanup
    std::remove("_test_rvc.txt");

    return 0;
}
