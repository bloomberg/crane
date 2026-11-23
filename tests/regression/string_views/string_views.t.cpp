// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "string_views.h"

#include <iostream>
#include <string>
#include <string_view>
#include <type_traits>

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

// A read takes the view; a canonical read (c_str, cat) the string by const
// reference; a string kept or returned is the string; a string result is
// always an owning std::string.
static_assert(std::is_same_v<decltype(&StringViews::size_of),
                             int64_t (*)(std::string_view)>);
static_assert(
    std::is_same_v<decltype(&StringViews::describe),
                   std::string (*)(const std::string &, std::string)>);
static_assert(std::is_same_v<decltype(&StringViews::initial),
                             int64_t (*)(std::string_view)>);
static_assert(std::is_same_v<decltype(&StringViews::c_size),
                             int64_t (*)(const std::string &)>);
static_assert(std::is_same_v<decltype(&StringViews::nonempty_or),
                             std::string (*)(std::string, std::string)>);
static_assert(std::is_same_v<decltype(&StringViews::first_two),
                             std::string (*)(std::string_view)>);
static_assert(std::is_same_v<decltype(&StringViews::prefix_size),
                             int64_t (*)(std::string_view)>);
static_assert(std::is_same_v<decltype(&StringViews::joined_prefix_size),
                             int64_t (*)(const std::string &,
                                         const std::string &)>);
static_assert(std::is_same_v<decltype(&StringViews::outer),
                             int64_t (*)(const std::string &)>);

} // namespace

#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

int main() {
  const std::string hello = "hello";
  ASSERT(StringViews::size_of(hello) == 5);
  ASSERT(StringViews::describe("Ada", "Hi") == "Hi, AdaA");
  ASSERT(StringViews::describe("", "Hi") == "Hi");
  ASSERT(StringViews::initial(hello) == 'h');
  ASSERT(StringViews::initial("") == '\0');
  ASSERT(StringViews::c_size(hello) == 5);
  ASSERT(StringViews::nonempty_or("", "x") == "x");
  ASSERT(StringViews::nonempty_or("y", "x") == "y");
  {
    // The materialised result owns its characters: it outlives the
    // argument it was a view of.
    std::string two;
    {
      std::string temp = "abcdef";
      two = StringViews::first_two(temp);
    }
    ASSERT(two == "ab");
  }
  ASSERT(StringViews::first_two("a") == "a");
  ASSERT(StringViews::prefix_size(hello) == 2);
  ASSERT(StringViews::outer(hello) == 15);
  ASSERT(StringViews::joined_prefix_size("a", "bcdefghijklmnopqrstuvwxyz") ==
         3);
  ASSERT(StringViews::literal_size == 5);
  ASSERT(StringViews::literal_length == 3);
  ASSERT(StringViews::literal_prefix_size == 3);
  ASSERT(StringViews::with_nul.size() == 3);
  ASSERT(StringViews::with_nul == std::string("a\0b", 3));
  ASSERT(StringViews::nul_size == 3);
  ASSERT(StringViews::nul_length == 3);
  if (testStatus == 0) {
    std::cout << "All string_views tests passed!" << std::endl;
  }
  return testStatus;
}
