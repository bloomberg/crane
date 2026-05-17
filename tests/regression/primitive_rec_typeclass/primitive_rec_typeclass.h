#ifndef INCLUDED_PRIMITIVE_REC_TYPECLASS
#define INCLUDED_PRIMITIVE_REC_TYPECLASS

#include <concepts>

template <typename I, typename A>
concept HasNorm = requires(A a0) {
  { I::norm(a0) } -> std::convertible_to<uint64_t>;
};

struct PrimitiveRecTypeclass {
  struct point {
    uint64_t px;
    uint64_t py;

    // ACCESSORS
    point clone() const { return point{(*this).px, (*this).py}; }
  };

  struct pointNorm {
    static uint64_t norm(point p) { return (p.px + p.py); }
  };

  static_assert(HasNorm<pointNorm, point>);

  struct vec3 {
    uint64_t vx;
    uint64_t vy;
    uint64_t vz;

    // ACCESSORS
    vec3 clone() const { return vec3{(*this).vx, (*this).vy, (*this).vz}; }
  };

  struct vec3Norm {
    static uint64_t norm(vec3 v) { return ((v.vx + v.vy) + v.vz); }
  };

  static_assert(HasNorm<vec3Norm, vec3>);

  template <typename _tcI0, typename T1>
  static uint64_t double_norm(const T1 &x) {
    return (_tcI0::norm(x) + _tcI0::norm(x));
  }

  struct rect {
    point top_left;
    point bot_right;

    // ACCESSORS
    rect clone() const {
      return rect{(*this).top_left.clone(), (*this).bot_right.clone()};
    }
  };

  static uint64_t rect_width(const rect &r);
  static uint64_t rect_height(const rect &r);
  static uint64_t rect_perimeter(const rect &r);
  static inline const point p1 = point{UINT64_C(3), UINT64_C(4)};
  static inline const point p2 = point{UINT64_C(10), UINT64_C(20)};
  static inline const uint64_t test_px = p1.px;
  static inline const uint64_t test_py = p1.py;
  static inline const uint64_t test_norm_point = pointNorm::norm(p1);
  static inline const uint64_t test_double_norm =
      double_norm<pointNorm, point>(p1);
  static inline const vec3 v1 = vec3{UINT64_C(1), UINT64_C(2), UINT64_C(3)};
  static inline const uint64_t test_norm_vec3 = vec3Norm::norm(v1);
  static inline const rect r1 =
      rect{point{UINT64_C(2), UINT64_C(3)}, point{UINT64_C(12), UINT64_C(8)}};
  static inline const uint64_t test_width = rect_width(r1);
  static inline const uint64_t test_height = rect_height(r1);
  static inline const uint64_t test_perimeter = rect_perimeter(r1);
};

#endif // INCLUDED_PRIMITIVE_REC_TYPECLASS
