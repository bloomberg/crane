#ifndef INCLUDED_RECORD_PROJ
#define INCLUDED_RECORD_PROJ

#include <type_traits>

struct RecordProj {
  struct Point {
    uint64_t x;
    uint64_t y;

    // ACCESSORS
    Point clone() const { return Point{(*this).x, (*this).y}; }
  };

  struct ComplexRecord {
    uint64_t field1;
    uint64_t field2;
    uint64_t field3;

    // ACCESSORS
    ComplexRecord clone() const {
      return ComplexRecord{(*this).field1, (*this).field2, (*this).field3};
    }
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

  static inline const uint64_t test1 =
      weird_access(Point{UINT64_C(10), UINT64_C(20)});
  static inline const uint64_t test2 =
      complex_access(ComplexRecord{UINT64_C(5), UINT64_C(10), UINT64_C(15)});
};

#endif // INCLUDED_RECORD_PROJ
