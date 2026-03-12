// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <axiom_types.h>

#include <functional>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>
#include <variant>

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

#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

int main() {
  // Test that axiom values throw std::logic_error when called
  {
    bool caught = false;
    try {
      AxiomTypes::mystery_value();
    } catch (const std::logic_error &e) {
      caught = true;
    }
    ASSERT(caught);
  }

  // Test that axiom functions throw std::logic_error when called
  {
    bool caught = false;
    try {
      AxiomTypes::mystery_function(std::any{});
    } catch (const std::logic_error &e) {
      caught = true;
    }
    ASSERT(caught);
  }

  // Test that use_axiom (which calls mystery_function(mystery_value))
  // throws a catchable exception
  {
    bool caught = false;
    try {
      AxiomTypes::use_axiom(unit::tt);
    } catch (const std::logic_error &e) {
      caught = true;
    }
    ASSERT(caught);
  }

  // Test axiom_identity with a valid value (non-axiom) succeeds
  {
    std::any val = 42;
    auto result = AxiomTypes::axiom_identity(val);
    ASSERT(std::any_cast<int>(result) == 42);
  }

  // Test that nested_axiom throws
  {
    bool caught = false;
    try {
      AxiomTypes::nested_axiom(unit::tt);
    } catch (const std::logic_error &e) {
      caught = true;
    }
    ASSERT(caught);
  }

  // Test that axiom_list throws
  {
    bool caught = false;
    try {
      AxiomTypes::axiom_list(unit::tt);
    } catch (const std::logic_error &e) {
      caught = true;
    }
    ASSERT(caught);
  }

  // Test that AxiomInductive works with non-axiom values
  {
    auto ind = AxiomTypes::AxiomInductive::ctor::AxConstr1_(42u);
    auto result = AxiomTypes::AxiomInductive_rect<unsigned int>(
        [](unsigned int n) { return n; },
        [](std::any) -> unsigned int { return 0u; }, ind);
    ASSERT(result == 42u);
  }

  std::cout << "Axiom types test completed" << std::endl;
  return testStatus;
}
