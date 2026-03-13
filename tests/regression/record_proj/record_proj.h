#ifndef INCLUDED_RECORD_PROJ
#define INCLUDED_RECORD_PROJ

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct RecordProj {
  struct Point {
    unsigned int x;
    unsigned int y;
  };

  struct ComplexRecord {
    unsigned int field1;
    unsigned int field2;
    unsigned int field3;
  };

  __attribute__((pure)) static unsigned int
  weird_access(const std::shared_ptr<Point> &p);
  __attribute__((pure)) static unsigned int
  complex_access(const std::shared_ptr<ComplexRecord> &c);
  __attribute__((pure)) static unsigned int
  nested_record_match(const std::shared_ptr<Point> &p1,
                      const std::shared_ptr<Point> &p2);

  template <MapsTo<unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  apply_to_field(F0 &&f, const std::shared_ptr<Point> &p) {
    return [&](void) {
      unsigned int a = p->x;
      unsigned int b = p->y;
      return (f(a) + f(b));
    }();
  }

  static inline const unsigned int test1 =
      weird_access(std::make_shared<Point>(Point{10u, 20u}));
  static inline const unsigned int test2 = complex_access(
      std::make_shared<ComplexRecord>(ComplexRecord{5u, 10u, 15u}));
};

#endif // INCLUDED_RECORD_PROJ
