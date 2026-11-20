#include "string_views.h"

int64_t StringViews::size_of(std::string_view x0_) {
  return static_cast<int64_t>(x0_.size());
}

std::string StringViews::describe(std::string_view name, std::string greeting) {
  std::string whole = crane::string_cat(
      std::string_view{greeting},
      std::string_view{
          crane::string_cat(std::string_view{std::string(", ")}, name)});
  if (static_cast<int64_t>(name.size()) < INT64_C(1)) {
    return greeting;
  } else {
    return crane::string_cat(
        std::string_view{whole},
        std::string_view{crane::string_sub(name, INT64_C(0), INT64_C(1))});
  }
}

char StringViews::initial(std::string_view s) {
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
int64_t StringViews::joined_prefix_size(std::string_view a,
                                        std::string_view b) {
  return static_cast<int64_t>((
      (std::string_view{crane::string_cat(a, b)}).substr(0,
                                                         INT64_C(3)))
                                  .size());
}

int64_t StringViews::outer(std::string_view s) {
  return static_cast<int64_t>(
      (static_cast<uint64_t>(size_of(s)) +
       static_cast<uint64_t>(size_of(std::string_view{crane::string_cat(s,
                                                                        s)}))) &
      0x7FFFFFFFFFFFFFFFULL);
}
