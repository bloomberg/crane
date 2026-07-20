#ifndef INCLUDED_STRING_GET_BOUNDS
#define INCLUDED_STRING_GET_BOUNDS

#include <cstdint>
#include <string>
#include <string_view>

struct StringGetBounds {
  static inline const std::string s = "abc";
  /// In-bounds access returns the expected character.
  static inline const char first =
      ((INT64_C(0) >= 0 && INT64_C(0) < static_cast<int64_t>(s.length()))
           ? s[INT64_C(0)]
           : static_cast<char>(0));
  /// Out-of-range access returns the null char (Rocq semantics), not an
  /// out-of-bounds read.
  static inline const char oob =
      ((INT64_C(100) >= 0 && INT64_C(100) < static_cast<int64_t>(s.length()))
           ? s[INT64_C(100)]
           : static_cast<char>(0));
  static inline const std::basic_string_view<char> sv = {s.data(), s.size()};
  /// Same contract for string views.
  static inline const char sv_first =
      ((INT64_C(0) >= 0 && INT64_C(0) < static_cast<int64_t>(sv.length()))
           ? sv[INT64_C(0)]
           : static_cast<char>(0));

  static inline const char sv_oob =
      ((INT64_C(100) >= 0 && INT64_C(100) < static_cast<int64_t>(sv.length()))
           ? sv[INT64_C(100)]
           : static_cast<char>(0));
};

#endif // INCLUDED_STRING_GET_BOUNDS
