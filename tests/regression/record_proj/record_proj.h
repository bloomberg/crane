#ifndef INCLUDED_RECORD_PROJ
#define INCLUDED_RECORD_PROJ

#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct RecordProj {
  struct Point {
    unsigned int x;
    unsigned int y;

    // ACCESSORS
    Point clone() const { return Point{(*(this)).x, (*(this)).y}; }
  };

  struct ComplexRecord {
    unsigned int field1;
    unsigned int field2;
    unsigned int field3;

    // ACCESSORS
    ComplexRecord clone() const {
      return ComplexRecord{(*(this)).field1, (*(this)).field2,
                           (*(this)).field3};
    }
  };

  static unsigned int weird_access(const Point &p);
  static unsigned int complex_access(const ComplexRecord &c);
  static unsigned int nested_record_match(const Point &p1, const Point &p2);

  template <MapsTo<unsigned int, unsigned int> F0>
  static unsigned int apply_to_field(F0 &&f, const Point &p) {
    unsigned int a = p.x;
    unsigned int b = p.y;
    return (f(a) + f(b));
  }

  static inline const unsigned int test1 = weird_access(Point{10u, 20u});
  static inline const unsigned int test2 =
      complex_access(ComplexRecord{5u, 10u, 15u});
};

#endif // INCLUDED_RECORD_PROJ
