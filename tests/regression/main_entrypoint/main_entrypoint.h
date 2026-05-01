#ifndef INCLUDED_MAIN_ENTRYPOINT
#define INCLUDED_MAIN_ENTRYPOINT

#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <variant>

using namespace std::string_literals;

struct MainEntrypoint {
  static void main();
};

#endif // INCLUDED_MAIN_ENTRYPOINT
