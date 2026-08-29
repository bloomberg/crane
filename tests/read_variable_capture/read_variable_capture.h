#ifndef INCLUDED_READ_VARIABLE_CAPTURE
#define INCLUDED_READ_VARIABLE_CAPTURE

#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <system_error>

using namespace std::string_literals;

struct ReadVariableCapture {
  static std::string read_literal();
  static std::string read_variable(std::string path);
  static std::string read_and_check(std::string path);
};

#endif // INCLUDED_READ_VARIABLE_CAPTURE
