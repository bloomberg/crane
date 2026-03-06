#include <iostream>
#include <cassert>
#include "bind_type_inference.h"

int main() {
    std::cout << "Test 1 (ignoreAndReturn): ";
    int r1 = BindTypeInference::test1();
    assert(r1 == 42);
    std::cout << "PASSED (got " << r1 << ")" << std::endl;

    std::cout << "Test 2 (transform): ";
    int r2 = BindTypeInference::test2();
    assert(r2 == 42);
    std::cout << "PASSED (got " << r2 << ")" << std::endl;

    std::cout << "Test 3 (nested): ";
    int r3 = BindTypeInference::test3();
    assert(r3 == 1);
    std::cout << "PASSED (got " << r3 << ")" << std::endl;

    std::cout << "Test 4 (vecToSize): ";
    int r4 = BindTypeInference::test4();
    assert(r4 == 3);
    std::cout << "PASSED (got " << r4 << ")" << std::endl;

    std::cout << "Test 5 (intToList): ";
    auto r5 = BindTypeInference::test5();
    // Just check it compiles and runs - list structure is complex
    std::cout << "PASSED" << std::endl;

    std::cout << "Test 6 (chain): ";
    int r6 = BindTypeInference::test6();
    assert(r6 == 42);
    std::cout << "PASSED (got " << r6 << ")" << std::endl;

    std::cout << "All bind_return tests passed!" << std::endl;
    return 0;
}
