#ifndef INCLUDED_MAIN_ENTRYPOINT
#define INCLUDED_MAIN_ENTRYPOINT

#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <system_error>
#include <variant>

using namespace std::string_literals;

struct MainEntrypoint {
  static void main();
};

#endif // INCLUDED_MAIN_ENTRYPOINT
