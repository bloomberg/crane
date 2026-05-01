// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.

#include "formula.h"

#include <cctype>
#include <cstdint>
#include <limits>

namespace formula {
namespace {

bool is_alpha(char c) {
  return (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z');
}

char upper(char c) {
  return (c >= 'a' && c <= 'z') ? static_cast<char>(c - 'a' + 'A') : c;
}

// Add a digit to a positive int64 accumulator; return false on overflow.
bool accumulate_digit(int64_t& v, int digit) {
  constexpr int64_t MAX = std::numeric_limits<int64_t>::max();
  if (v > (MAX - digit) / 10) return false;
  v = v * 10 + digit;
  return true;
}

struct Parser {
  std::string_view src;
  size_t pos = 0;

  void skip_ws() {
    while (pos < src.size() && std::isspace(static_cast<unsigned char>(src[pos]))) ++pos;
  }
  bool eof() {
    skip_ws();
    return pos >= src.size();
  }
  char peek() {
    skip_ws();
    return pos < src.size() ? src[pos] : '\0';
  }
  bool consume(char c) {
    if (peek() == c) { ++pos; return true; }
    return false;
  }

  // expr   = term (('+'|'-') term)*
  // term   = factor (('*'|'/') factor)*
  // factor = '-' factor | '(' expr ')' | INT | REF
  std::optional<Spreadsheet::Expr> expr() {
    auto lhs = term();
    if (!lhs) return std::nullopt;
    while (true) {
      char c = peek();
      if (c == '+') {
        ++pos;
        auto rhs = term();
        if (!rhs) return std::nullopt;
        lhs = Spreadsheet::Expr::eadd(std::move(*lhs), std::move(*rhs));
      } else if (c == '-') {
        ++pos;
        auto rhs = term();
        if (!rhs) return std::nullopt;
        lhs = Spreadsheet::Expr::esub(std::move(*lhs), std::move(*rhs));
      } else {
        break;
      }
    }
    return lhs;
  }

  std::optional<Spreadsheet::Expr> term() {
    auto lhs = factor();
    if (!lhs) return std::nullopt;
    while (true) {
      char c = peek();
      if (c == '*') {
        ++pos;
        auto rhs = factor();
        if (!rhs) return std::nullopt;
        lhs = Spreadsheet::Expr::emul(std::move(*lhs), std::move(*rhs));
      } else if (c == '/') {
        ++pos;
        auto rhs = factor();
        if (!rhs) return std::nullopt;
        lhs = Spreadsheet::Expr::ediv(std::move(*lhs), std::move(*rhs));
      } else {
        break;
      }
    }
    return lhs;
  }

  std::optional<Spreadsheet::Expr> factor() {
    char c = peek();
    if (c == '-') {
      ++pos;
      auto e = factor();
      if (!e) return std::nullopt;
      return Spreadsheet::Expr::esub(
        Spreadsheet::Expr::eint(int64_t(0)), std::move(*e));
    }
    if (c == '(') {
      ++pos;
      auto e = expr();
      if (!e || !consume(')')) return std::nullopt;
      return e;
    }
    if (std::isdigit(static_cast<unsigned char>(c))) {
      return parse_int();
    }
    if (is_alpha(c)) {
      return parse_ref();
    }
    return std::nullopt;
  }

  std::optional<Spreadsheet::Expr> parse_int() {
    skip_ws();
    int64_t v = 0;
    bool any = false;
    while (pos < src.size() && std::isdigit(static_cast<unsigned char>(src[pos]))) {
      if (!accumulate_digit(v, src[pos] - '0')) return std::nullopt;
      ++pos;
      any = true;
    }
    if (!any) return std::nullopt;
    return Spreadsheet::Expr::eint(v);
  }

  // Cell references: one or two letters followed by a 1-based row.
  // Two-letter columns map A..Z (single) then AA, AB, ..., ZZ.
  // Bounds-checked against Spreadsheet::NUM_COLS / NUM_ROWS so that
  // out-of-grid references are rejected at parse time.
  std::optional<Spreadsheet::Expr> parse_ref() {
    skip_ws();
    if (pos >= src.size() || !is_alpha(src[pos])) return std::nullopt;
    char c1 = upper(src[pos++]);
    int64_t col;
    if (pos < src.size() && is_alpha(src[pos])) {
      char c2 = upper(src[pos++]);
      col = 26 + int64_t(c1 - 'A') * 26 + int64_t(c2 - 'A');
    } else {
      col = int64_t(c1 - 'A');
    }
    int64_t row1 = 0;
    bool any = false;
    while (pos < src.size() && std::isdigit(static_cast<unsigned char>(src[pos]))) {
      if (!accumulate_digit(row1, src[pos] - '0')) return std::nullopt;
      ++pos;
      any = true;
    }
    if (!any || row1 < 1) return std::nullopt;
    int64_t row = row1 - 1;
    if (col < 0 || col >= Spreadsheet::NUM_COLS ||
        row < 0 || row >= Spreadsheet::NUM_ROWS) {
      return std::nullopt;
    }
    Spreadsheet::CellRef r{col, row};
    return Spreadsheet::Expr::eref(r);
  }
};

}  // namespace

std::optional<Spreadsheet::Expr> parse(std::string_view src) {
  Parser p{src};
  auto e = p.expr();
  if (!e) return std::nullopt;
  if (!p.eof()) return std::nullopt;
  return e;
}

bool parse_int_literal(std::string_view src, int64_t& out) {
  size_t i = 0;
  while (i < src.size() && std::isspace(static_cast<unsigned char>(src[i]))) ++i;
  bool neg = false;
  if (i < src.size() && src[i] == '-') { neg = true; ++i; }
  int64_t v = 0;
  bool any = false;
  while (i < src.size() && std::isdigit(static_cast<unsigned char>(src[i]))) {
    if (!accumulate_digit(v, src[i] - '0')) return false;
    ++i;
    any = true;
  }
  while (i < src.size() && std::isspace(static_cast<unsigned char>(src[i]))) ++i;
  if (!any || i != src.size()) return false;
  out = neg ? -v : v;
  return true;
}

std::string label_of(int64_t col, int64_t row) {
  std::string s;
  if (col < 26) {
    s += static_cast<char>('A' + col);
  } else {
    int64_t adj = col - 26;
    s += static_cast<char>('A' + adj / 26);
    s += static_cast<char>('A' + adj % 26);
  }
  s += std::to_string(row + 1);
  return s;
}

std::string col_label(int64_t col) {
  std::string s;
  if (col < 26) {
    s += static_cast<char>('A' + col);
  } else {
    int64_t adj = col - 26;
    s += static_cast<char>('A' + adj / 26);
    s += static_cast<char>('A' + adj % 26);
  }
  return s;
}

}  // namespace formula
