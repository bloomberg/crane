#ifndef INCLUDED_MAIN_TOPLEVEL
#define INCLUDED_MAIN_TOPLEVEL

#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <variant>

using namespace std::string_literals;

struct Greeter {
  static void greet();
};

int main();

#endif // INCLUDED_MAIN_TOPLEVEL
