#include "string_views.h"

int64_t StringViews::size_of(std::string_view x0_) {
  return static_cast<int64_t>(x0_.size());
}

std::string StringViews::describe(const std::string &name,
                                  std::string greeting) {
  std::string whole = greeting + std::string(", ") + name;
  if (static_cast<int64_t>((std::string_view{name}).size()) < INT64_C(1)) {
    return greeting;
  } else {
    return whole +
           crane::string_sub(std::string_view{name}, INT64_C(0), INT64_C(1));
  }
}

int64_t StringViews::initial(std::string_view s) {
  return crane::string_get(s, INT64_C(0));
}

int64_t StringViews::c_size(const std::string &x0_) {
  return static_cast<int64_t>(std::strlen(x0_.c_str()));
}

std::string StringViews::nonempty_or(std::string s, std::string fallback) {
  if (static_cast<int64_t>((std::string_view{s}).size()) == INT64_C(0)) {
    return fallback;
  } else {
    return s;
  }
}

std::string StringViews::first_two(std::string_view s) {
  return std::string{s.substr(0, INT64_C(2))};
}

int64_t StringViews::prefix_size(std::string_view s) {
  return static_cast<int64_t>((s.substr(0, INT64_C(2))).size());
}

/// A view borrowed from a temporary, read within the full expression
/// that holds the temporary.
int64_t StringViews::joined_prefix_size(const std::string &a,
                                        const std::string &b) {
  return static_cast<int64_t>(
      ((std::string_view{a + b}).substr(0, INT64_C(3))).size());
}

int64_t StringViews::outer(const std::string &s) {
  return static_cast<int64_t>(
      (static_cast<uint64_t>(size_of(std::string_view{s})) +
       static_cast<uint64_t>(size_of(std::string_view{s + s}))) &
      0x7FFFFFFFFFFFFFFFULL);
}
