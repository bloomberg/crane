// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <doc_comments.h>

#include <fstream>
#include <iostream>
#include <string>

// ============================================================================
//                     STANDARD BDE ASSERT TEST FUNCTION
// ----------------------------------------------------------------------------

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

#define ASSERT(X)                                                              \
  {                                                                            \
    aSsErT(!(X), #X, __LINE__);                                                \
  }

// ============================================================================
//                              MAIN PROGRAM
// ----------------------------------------------------------------------------

// Check that a file contains a given substring
bool file_contains(const std::string &path, const std::string &needle) {
  std::ifstream f(path);
  if (!f.is_open())
    return false;
  std::string contents((std::istreambuf_iterator<char>(f)),
                       std::istreambuf_iterator<char>());
  return contents.find(needle) != std::string::npos;
}

int main() {
  // Verify the generated header contains doc comments
  std::string header = "doc_comments.h";

  // Check that doc comments appear as /// comments
  ASSERT(file_contains(
      header, "/// add computes the sum of two natural numbers n and m."));
  ASSERT(file_contains(header, "/// It works by structural recursion on n."));
  ASSERT(file_contains(
      header,
      "/// A simple pair holding two values of possibly different types."));
  ASSERT(file_contains(header, "/// mylist is a polymorphic list type."));
  ASSERT(file_contains(
      header, "/// The identity function: returns its argument unchanged."));
  ASSERT(file_contains(header, "/// double n returns 2 * n."));

  // Basic functional test: the extracted code works
  ASSERT(DocComments::add(3, 4) == 7);
  ASSERT(DocComments::add(0, 5) == 5);
  ASSERT(DocComments::identity(42) == 42);
  ASSERT(DocComments::double_(3) == 6);

  return testStatus;
}
