// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Unit tests for the C++-side formula parser.  Built by the
// bin/spreadsheet/ CMakeLists; not currently part of `dune runtest`
// because it depends on the front-end build.

#include "formula.h"
#include "Spreadsheet.h"

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <string_view>

namespace {

int failures = 0;

void want_ok(const char* tag, std::string_view src) {
  if (!formula::parse(src).has_value()) {
    std::printf("FAIL parse(%s) [%s]\n", std::string(src).c_str(), tag);
    ++failures;
  }
}
void want_fail(const char* tag, std::string_view src) {
  if (formula::parse(src).has_value()) {
    std::printf("FAIL reject(%s) [%s]\n", std::string(src).c_str(), tag);
    ++failures;
  }
}
void want_int(const char* tag, std::string_view src, int64_t expected) {
  int64_t got;
  if (!formula::parse_int_literal(src, got) || got != expected) {
    std::printf("FAIL int(%s) [%s] got %lld want %lld\n",
                std::string(src).c_str(), tag, (long long)got,
                (long long)expected);
    ++failures;
  }
}
void want_int_fail(const char* tag, std::string_view src) {
  int64_t got;
  if (formula::parse_int_literal(src, got)) {
    std::printf("FAIL int_reject(%s) [%s] got %lld\n",
                std::string(src).c_str(), tag, (long long)got);
    ++failures;
  }
}

}  // namespace

int main() {
  // Single-letter refs.
  want_ok("single", "A1");
  want_ok("single", "Z100");
  want_ok("lower", "a1");

  // Multi-letter refs in range.
  want_ok("multi", "AA1");
  want_ok("multi", "BA1");
  want_ok("multi", "CZ1");
  want_ok("multi-lower", "cz100");
  want_ok("multi-mixed", "aA1");

  // Arithmetic / parens / precedence.
  want_ok("add", "1+2");
  want_ok("prec", "1+2*3");
  want_ok("paren", "(1+2)*3");
  want_ok("deep-paren", "((((1))))");
  want_ok("unary", "-1");
  want_ok("unary-deep", "---5");
  want_ok("unary-mid", "1+-1");
  want_ok("ws", "  A1  +  B2  ");

  // Out-of-range refs (NUM_COLS=104, NUM_ROWS=100).
  want_fail("row-oob", "A101");
  want_fail("col-oob", "DA1");
  want_fail("col-far-oob", "ZZ1");
  want_fail("row-zero", "A0");

  // Garbage.
  want_fail("empty", "");
  want_fail("3-letter", "AAA1");
  want_fail("trailing-op", "1+");
  want_fail("double-op", "1++1");
  want_fail("bare-letter", "A");
  want_fail("decimal", "1.5");
  want_fail("hex", "0x10");
  want_fail("paren-only", "(");
  want_fail("close-only", ")");
  want_fail("unbalanced", "(1+2");
  want_fail("extra-close", "1+2)");
  want_fail("ws-only", " ");

  // Integer-literal overflow handling.
  want_ok("just-under-max", "9223372036854775807");
  want_fail("over-max", "9223372036854775808");
  want_fail("way-over-max", "9999999999999999999");

  // parse_int_literal helper.
  want_int("zero", "0", 0);
  want_int("neg", "-42", -42);
  want_int("ws", "  17  ", 17);
  want_int_fail("mixed", "12 abc");
  want_int_fail("over", "9999999999999999999");

  if (failures == 0) std::printf("OK (all parser cases pass)\n");
  else std::printf("FAILED (%d)\n", failures);
  return failures;
}
