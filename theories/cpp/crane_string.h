// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// The string operations of the typed string mapping
// (theories/Mapping/Std.v): a Rocq PrimString.string is a
// std::string, read through a std::string_view.  Each operation reads its
// strings through views and returns an owning std::string or a value, with
// Rocq's total semantics.

#pragma once

#include <cstdint>
#include <string>
#include <string_view>

namespace crane {

// PrimString.cat.
inline std::string string_cat(std::string_view left, std::string_view right) {
  std::string result;
  result.reserve(left.size() + right.size());
  result.append(left);
  result.append(right);
  return result;
}

// PrimString.get: total, an index out of range reads the null character.
inline char string_get(std::string_view text, std::int64_t i) {
  return (i >= 0 && static_cast<std::uint64_t>(i) < text.size())
             ? text[static_cast<std::size_t>(i)]
             : static_cast<char>(0);
}

// PrimString.sub: total, an offset at or past the end gives the empty
// string and the length is clamped to what remains.  An owner, not a view.
inline std::string string_sub(std::string_view text, std::int64_t off,
                              std::int64_t len) {
  if (off < 0 || static_cast<std::uint64_t>(off) > text.size() || len <= 0) {
    return std::string();
  }
  return std::string(text.substr(static_cast<std::size_t>(off),
                                 static_cast<std::size_t>(len)));
}

} // namespace crane
