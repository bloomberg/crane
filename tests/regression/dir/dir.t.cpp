// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Regression test for dirE effects.

#include <dir.h>

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

void test_make_and_remove() {
  std::string dir = "/tmp/crane_test_dir_make_remove";
  std::filesystem::remove_all(dir);

  auto ok = Dir::make_dir(dir);
  ASSERT(ok);
  ASSERT(std::filesystem::is_directory(dir));

  auto ok2 = Dir::remove_dir(dir);
  ASSERT(ok2);
  ASSERT(!std::filesystem::exists(dir));

  std::cout << "PASS: make_dir / remove_dir\n";
}

void test_cwd() {
  auto cwd = Dir::get_cwd();
  ASSERT(!cwd.empty());
  ASSERT(cwd[0] == '/');
  std::cout << "PASS: current_path = " << cwd << "\n";
}

void test_list_dir() {
  std::string dir = "/tmp/crane_test_dir_list";
  std::filesystem::remove_all(dir);
  std::filesystem::create_directory(dir);
  std::ofstream(dir + "/a.txt") << "a";
  std::ofstream(dir + "/b.txt") << "b";

  auto entries = Dir::list_dir(dir);
  // Should be non-empty (Cons variant)
  ASSERT(std::holds_alternative<List<std::string>::Cons>(entries.v()));

  // Count entries
  int count = 0;
  const List<std::string> *cur = &entries;
  while (std::holds_alternative<List<std::string>::Cons>(cur->v())) {
    ++count;
    cur = std::get<List<std::string>::Cons>(cur->v()).d_a1.get();
  }
  ASSERT(count == 2);

  std::filesystem::remove_all(dir);
  std::cout << "PASS: list_dir (" << count << " entries)\n";
}

int main() {
  test_make_and_remove();
  test_cwd();
  test_list_dir();

  std::cout << (testStatus ? "FAIL" : "PASS") << ": dir\n";
  return testStatus;
}
