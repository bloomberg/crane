// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Regression test for tempFileE effects.

#include <temp_file.h>

#include <cassert>
#include <filesystem>
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

void test_create_temp_file() {
  auto path = TempFile::make_temp_file("crane_test_");
  ASSERT(!path.empty());
  ASSERT(std::filesystem::exists(path));
  ASSERT(std::filesystem::is_regular_file(path));

  std::filesystem::remove(path);
  std::cout << "PASS: create_temp_file = " << path << "\n";
}

void test_create_temp_dir() {
  auto path = TempFile::make_temp_dir("crane_test_dir_");
  ASSERT(!path.empty());
  ASSERT(std::filesystem::exists(path));
  ASSERT(std::filesystem::is_directory(path));

  std::filesystem::remove(path);
  std::cout << "PASS: create_temp_dir = " << path << "\n";
}

// A prefix containing directory separators, "..", or an absolute path must not
// escape the system temporary directory: the created entry's parent directory
// is always the temp directory itself.
void test_prefix_traversal() {
  namespace fs = std::filesystem;
  const fs::path tmp = fs::weakly_canonical(fs::temp_directory_path());

  for (const char *prefix :
       {"../crane_escape_", "/etc/crane_escape_", "a/b/crane_escape_", "..",
        "/"}) {
    auto path = TempFile::make_temp_file(prefix);
    ASSERT(!path.empty());
    ASSERT(fs::exists(path));
    // Resolve symlinks/./.. then confirm the parent is the temp directory.
    ASSERT(fs::weakly_canonical(fs::path(path)).parent_path() == tmp);

    fs::remove(path);
    std::cout << "PASS: traversal-safe temp file for prefix '" << prefix
              << "'\n";
  }
}

int main() {
  test_create_temp_file();
  test_create_temp_dir();
  test_prefix_traversal();

  std::cout << (testStatus ? "FAIL" : "PASS") << ": temp_file\n";
  return testStatus;
}
