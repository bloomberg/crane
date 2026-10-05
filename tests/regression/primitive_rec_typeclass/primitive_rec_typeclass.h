#ifndef INCLUDED_PRIMITIVE_REC_TYPECLASS
#define INCLUDED_PRIMITIVE_REC_TYPECLASS

#include <concepts>
#include <cstdint>
#include <utility>

template <typename I, typename A>
concept HasNorm = requires {
  { I::norm(std::declval<A>()) } -> std::convertible_to<uint64_t>;
};

struct PrimitiveRecTypeclass {
  struct point {
    uint64_t px;
    uint64_t py;
  };

  struct pointNorm {
    static uint64_t norm(point p) { return (p.px + p.py); }
  };

  static_assert(HasNorm<pointNorm, point>);

  struct vec3 {
    uint64_t vx;
    uint64_t vy;
    uint64_t vz;
  };

  struct vec3Norm {
    static uint64_t norm(vec3 v) { return ((v.vx + v.vy) + v.vz); }
  };

  static_assert(HasNorm<vec3Norm, vec3>);

  template <typename _tcI0, typename T1>
    requires HasNorm<_tcI0, T1>
  static uint64_t double_norm(const T1 &x) {
    return (_tcI0::norm(x) + _tcI0::norm(x));
  }

  struct rect {
    point top_left;
    point bot_right;
  };

  static uint64_t rect_width(const rect &r);
  static uint64_t rect_height(const rect &r);
  static uint64_t rect_perimeter(const rect &r);
  static inline const point p1 = point{UINT64_C(3), UINT64_C(4)};
  static inline const point p2 = point{UINT64_C(10), UINT64_C(20)};
  static constexpr uint64_t test_px = UINT64_C(3);
  static constexpr uint64_t test_py = UINT64_C(4);
  static constexpr uint64_t test_norm_point = UINT64_C(7);
  static constexpr uint64_t test_double_norm = UINT64_C(14);
  static inline const vec3 v1 = vec3{UINT64_C(1), UINT64_C(2), UINT64_C(3)};
  static constexpr uint64_t test_norm_vec3 = UINT64_C(6);
  static inline const rect r1 =
      rect{point{UINT64_C(2), UINT64_C(3)}, point{UINT64_C(12), UINT64_C(8)}};
  static constexpr uint64_t test_width = UINT64_C(10);
  static constexpr uint64_t test_height = UINT64_C(5);
  static constexpr uint64_t test_perimeter = UINT64_C(30);
};

#endif // INCLUDED_PRIMITIVE_REC_TYPECLASS
