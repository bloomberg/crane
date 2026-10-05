#ifndef INCLUDED_RECORD_PROJ
#define INCLUDED_RECORD_PROJ

#include <cstdint>
#include <type_traits>

struct RecordProj {
  struct Point {
    uint64_t x;
    uint64_t y;
  };

  struct ComplexRecord {
    uint64_t field1;
    uint64_t field2;
    uint64_t field3;
  };

  static uint64_t weird_access(const Point &p);
  static uint64_t complex_access(const ComplexRecord &c);
  static uint64_t nested_record_match(const Point &p1, const Point &p2);

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static uint64_t apply_to_field(F0 &&f, const Point &p) {
    uint64_t a = p.x;
    uint64_t b = p.y;
    return (f(a) + f(b));
  }

  static constexpr uint64_t test1 = UINT64_C(40);
  static constexpr uint64_t test2 = UINT64_C(30);
};

#endif // INCLUDED_RECORD_PROJ
