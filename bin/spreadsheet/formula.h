// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Tiny recursive-descent parser for spreadsheet formulas.  Produces an
// Expr value from the Crane-extracted [Spreadsheet] module.  Lives on the
// C++ side of the demo: the verified Rocq kernel is the evaluator, not
// the parser.

#pragma once

#include "Spreadsheet.h"

#include <cstdint>
#include <optional>
#include <string>
#include <string_view>

namespace formula {

// Parse a formula source string.  Accepts:
//   * decimal integer literals (overflow into int64 is rejected)
//   * cell references: <letter(s)><1-based row>, bounds-checked
//     against the kernel grid
//   * binary operators + - * / with usual precedence
//   * parentheses, unary minus
//
// Returns std::nullopt on any malformed input or out-of-range literal.
std::optional<Spreadsheet::Expr> parse(std::string_view src);

// Parse a plain (possibly negative) integer literal with optional
// surrounding whitespace.  Rejects overflow into int64.  Returns true
// on success.
bool parse_int_literal(std::string_view src, int64_t& out);

// "<col><row+1>", e.g. (0, 0) -> "A1", (701, 99) -> "ZZ100".
std::string label_of(int64_t col, int64_t row);

// Just the column letter(s), e.g. 0 -> "A", 26 -> "AA".
std::string col_label(int64_t col);

}  // namespace formula
