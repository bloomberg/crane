#pragma once

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

struct StringGetBounds {
  static inline const std::string s = "abc";
  /// In-bounds access returns the expected character.
  static inline const int64_t first =
      static_cast<std::int64_t>(static_cast<std::size_t>(INT64_C(0)) <
                                s.size() ? static_cast<unsigned char>(
                                               s[static_cast<std::size_t>(
                                                   INT64_C(0))])
                                         : 0);
  /// Out-of-range access returns the null char (Rocq semantics), not an
  /// out-of-bounds read.
  static inline const int64_t oob =
      static_cast<std::int64_t>(static_cast<std::size_t>(INT64_C(100)) <
                                s.size() ? static_cast<unsigned char>(
                                               s[static_cast<std::size_t>(
                                                   INT64_C(100))])
                                         : 0);
  static inline const std::basic_string_view<char> sv = {s.data(), s.size()};
  /// Same contract for string views.
  static inline const int64_t sv_first = ((INT64_C(0) >= 0 &&
                                           INT64_C(0) <
                                           static_cast<int64_t>(sv.length()))
                                              ? static_cast<int64_t>(
                                                    static_cast<unsigned char>(
                                                        sv[INT64_C(0)]))
                                              : INT64_C(0));
  static inline const int64_t sv_oob = ((INT64_C(100) >= 0 &&
                                         INT64_C(100) <
                                         static_cast<int64_t>(sv.length()))
                                            ? static_cast<int64_t>(
                                                  static_cast<unsigned char>(
                                                      sv[INT64_C(100)]))
                                            : INT64_C(0));
};
