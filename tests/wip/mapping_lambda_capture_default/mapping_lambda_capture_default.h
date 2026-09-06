#ifndef INCLUDED_MAPPING_LAMBDA_CAPTURE_DEFAULT
#define INCLUDED_MAPPING_LAMBDA_CAPTURE_DEFAULT

#include <cstdint>
#include <utility>

/// ZInt expands Z.div and Z.modulo into an immediately-invoked lambda
/// that adjusts C++ truncation to Rocq's flooring.  That lambda is written
/// [&], which C++ forbids for a lambda at class or namespace scope -- and a
/// top-level Definition is initialised exactly there.  Mapping.DequeList's
/// List.rev has the same shape and the same failure.
struct MappingLambdaCaptureDefault {
  static inline const int64_t d = [](int64_t _a, int64_t _b) -> int64_t {
    if (_b == 0)
      return INT64_C(0);
    if (_b == -1)
      return static_cast<int64_t>(-static_cast<uint64_t>(_a));
    int64_t _q = _a / _b;
    int64_t _r = _a % _b;
    if (_r != 0 && ((_r < 0) != (_b < 0)))
      return _q - 1;
    return _q;
  }(INT64_C(-7), INT64_C(2));
  static inline const int64_t m = [](int64_t _a, int64_t _b) -> int64_t {
    if (_b == 0)
      return _a;
    if (_b == -1)
      return INT64_C(0);
    int64_t _r = _a % _b;
    if (_r != 0 && ((_r < 0) != (_b < 0)))
      return _r + _b;
    return _r;
  }(INT64_C(-7), INT64_C(2));
  static inline const int64_t run = static_cast<int64_t>(
      static_cast<uint64_t>(static_cast<int64_t>(
          static_cast<uint64_t>(d) * static_cast<uint64_t>(INT64_C(10)))) +
      static_cast<uint64_t>(m));
};

#endif // INCLUDED_MAPPING_LAMBDA_CAPTURE_DEFAULT
