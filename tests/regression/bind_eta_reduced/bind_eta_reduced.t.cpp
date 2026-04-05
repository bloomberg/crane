#include <bind_eta_reduced.h>
#include <cassert>
#include <sstream>
#include <iostream>

int main() {
    std::istringstream input("hello\nworld\n");
    std::cin.rdbuf(input.rdbuf());

    // Bug: with_line should call f on the read line
    auto r1 = BindEtaReduced::with_line([](const std::string& s) -> std::string {
        return s + "!";
    });
    assert(r1 == "hello!");

    // transform should work because (fun line => Ret (f line)) is not eta-reduced
    auto r2 = BindEtaReduced::transform([](const std::string& s) -> std::string {
        return s + "?";
    });
    assert(r2 == "world?");

    return 0;
}
