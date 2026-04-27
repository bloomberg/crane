#ifndef INCLUDED_PRIMITIVE_REC_TYPECLASS
#define INCLUDED_PRIMITIVE_REC_TYPECLASS

#include <concepts>
#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename I, typename t_A>
concept HasNorm = requires(t_A a0) {
  { I::norm(a0) } -> std::convertible_to<unsigned int>;
};

struct PrimitiveRecTypeclass {
  struct point {
    unsigned int px;
    unsigned int py;

    // ACCESSORS
    __attribute__((pure)) point clone() const {
      return point{(*(this)).px, (*(this)).py};
    }
  };

  struct pointNorm {
    __attribute__((pure)) static unsigned int norm(point p) {
      return (p.px + p.py);
    }
  };

  static_assert(HasNorm<pointNorm, point>);

  struct vec3 {
    unsigned int vx;
    unsigned int vy;
    unsigned int vz;

    // ACCESSORS
    __attribute__((pure)) vec3 clone() const {
      return vec3{(*(this)).vx, (*(this)).vy, (*(this)).vz};
    }
  };

  struct vec3Norm {
    __attribute__((pure)) static unsigned int norm(vec3 v) {
      return ((v.vx + v.vy) + v.vz);
    }
  };

  static_assert(HasNorm<vec3Norm, vec3>);

  template <typename _tcI0, typename T1>
  __attribute__((pure)) static unsigned int double_norm(const T1 x) {
    return (_tcI0::norm(x) + _tcI0::norm(x));
  }

  struct rect {
    point top_left;
    point bot_right;

    // ACCESSORS
    __attribute__((pure)) rect clone() const {
      return rect{(*(this)).top_left.clone(), (*(this)).bot_right.clone()};
    }
  };

  __attribute__((pure)) static unsigned int rect_width(const rect &r);
  __attribute__((pure)) static unsigned int rect_height(const rect &r);
  __attribute__((pure)) static unsigned int rect_perimeter(const rect &r);
  static inline const point p1 = point{3u, 4u};
  static inline const point p2 = point{10u, 20u};
  static inline const unsigned int test_px = p1.px;
  static inline const unsigned int test_py = p1.py;
  static inline const unsigned int test_norm_point = pointNorm::norm(p1);
  static inline const unsigned int test_double_norm =
      double_norm<pointNorm, point>(p1);
  static inline const vec3 v1 = vec3{1u, 2u, 3u};
  static inline const unsigned int test_norm_vec3 = vec3Norm::norm(v1);
  static inline const rect r1 = rect{point{2u, 3u}, point{12u, 8u}};
  static inline const unsigned int test_width = rect_width(r1);
  static inline const unsigned int test_height = rect_height(r1);
  static inline const unsigned int test_perimeter = rect_perimeter(r1);
};

#endif // INCLUDED_PRIMITIVE_REC_TYPECLASS
