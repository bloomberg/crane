// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Tiny recursive-descent parser for spreadsheet formulas.  Produces an
// Expr value from the Crane-extracted [Spreadsheet] module.  Lives on the
// C++ side of the demo: the verified Rocq kernel is the evaluator, not
// the parser.

#pragma once

#include "Spreadsheet.h"

#include <optional>
#include <string>
#include <string_view>

namespace formula {

// Parse a formula source string.  Accepts:
//   * decimal integer literals, optionally signed (e.g. -42)
//   * cell references in the form A1, Z99, etc. (column A..Z, row 1..)
//   * binary operators + - * / with usual precedence
//   * parentheses
//
// Returns std::nullopt if the string is not a valid formula.  Whitespace
// is ignored.
std::optional<Spreadsheet::Expr> parse(std::string_view src);

// Convert a (col, row) reference back to a label like "A1".  Used for
// rendering the cell-name column of the grid.
std::string label_of(int64_t col, int64_t row);

}  // namespace formula
