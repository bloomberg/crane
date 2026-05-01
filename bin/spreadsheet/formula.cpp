// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.

#include "formula.h"

#include <cctype>
#include <cstdint>

namespace formula {
namespace {

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
      // Unary minus: sugar for (0 - factor).
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
    if (c >= 'A' && c <= 'Z') {
      return parse_ref();
    }
    if (c >= 'a' && c <= 'z') {
      // Lowercase cell letter, fold to upper.
      return parse_ref();
    }
    return std::nullopt;
  }

  std::optional<Spreadsheet::Expr> parse_int() {
    skip_ws();
    int64_t v = 0;
    bool any = false;
    while (pos < src.size() && std::isdigit(static_cast<unsigned char>(src[pos]))) {
      v = v * 10 + (src[pos] - '0');
      ++pos;
      any = true;
    }
    if (!any) return std::nullopt;
    return Spreadsheet::Expr::eint(v);
  }

  std::optional<Spreadsheet::Expr> parse_ref() {
    skip_ws();
    if (pos >= src.size()) return std::nullopt;
    char letter = src[pos];
    if (letter >= 'a' && letter <= 'z') letter = static_cast<char>(letter - 'a' + 'A');
    if (letter < 'A' || letter > 'Z') return std::nullopt;
    ++pos;
    int64_t row1 = 0;
    bool any = false;
    while (pos < src.size() && std::isdigit(static_cast<unsigned char>(src[pos]))) {
      row1 = row1 * 10 + (src[pos] - '0');
      ++pos;
      any = true;
    }
    if (!any || row1 < 1) return std::nullopt;
    int64_t col = letter - 'A';
    int64_t row = row1 - 1;  // 1-based to 0-based
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

std::string label_of(int64_t col, int64_t row) {
  if (col < 0 || col > 25) return "?";
  std::string s;
  s += static_cast<char>('A' + col);
  s += std::to_string(row + 1);
  return s;
}

}  // namespace formula
