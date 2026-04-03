// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Regression test for pathE effects.

#include <path.h>

#include <cassert>
#include <filesystem>
#include <fstream>
#include <iostream>

namespace {

int testStatus = 0;

void aSsErT(bool condition, const char *message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;
    if (0 <= testStatus && testStatus <= 100) {
      ++testStatus;
    }
  }
}

} // namespace

#define ASSERT(X) aSsErT(!(X), #X, __LINE__)

void test_absolute() {
  auto p = Path::abs_path(".");
  ASSERT(!p.empty());
  ASSERT(p[0] == '/');
  std::cout << "PASS: absolute(\".\") = " << p << "\n";
}

void test_canonical() {
  // "." always exists, canonical should resolve to an absolute path
  auto p = Path::canon_path(".");
  ASSERT(!p.empty());
  ASSERT(p[0] == '/');
  std::cout << "PASS: canonical(\".\") = " << p << "\n";
}

void test_relative() {
  auto p = Path::rel_path(".");
  ASSERT(!p.empty());
  std::cout << "PASS: relative(\".\") = " << p << "\n";
}

void test_is_dir() {
  ASSERT(Path::check_is_dir("."));
  ASSERT(!Path::check_is_dir("/nonexistent_crane_test_path_xyz_999"));
  std::cout << "PASS: is_directory\n";
}

void test_is_file() {
  std::string f = "/tmp/crane_test_is_file.txt";
  std::ofstream(f) << "test";

  ASSERT(Path::check_is_file(f));
  ASSERT(!Path::check_is_file("."));

  std::filesystem::remove(f);
  std::cout << "PASS: is_regular_file\n";
}

int main() {
  test_absolute();
  test_canonical();
  test_relative();
  test_is_dir();
  test_is_file();

  std::cout << (testStatus ? "FAIL" : "PASS") << ": path\n";
  return testStatus;
}
