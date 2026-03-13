#ifndef INCLUDED_PRIMITIVE_REC_TYPECLASS
#define INCLUDED_PRIMITIVE_REC_TYPECLASS

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

template <typename I, typename t_A>
concept HasNorm = requires(t_A a0) {
  { I::norm(a0) } -> std::convertible_to<unsigned int>;
};

struct PrimitiveRecTypeclass {
  struct point {
    unsigned int px;
    unsigned int py;
  };

  struct pointNorm {
    __attribute__((pure)) static unsigned int norm(std::shared_ptr<point> p) {
      return (p->px + p->py);
    }
  };

  static_assert(HasNorm<pointNorm, std::shared_ptr<point>>);

  struct vec3 {
    unsigned int vx;
    unsigned int vy;
    unsigned int vz;
  };

  struct vec3Norm {
    __attribute__((pure)) static unsigned int norm(std::shared_ptr<vec3> v) {
      return ((v->vx + v->vy) + v->vz);
    }
  };

  static_assert(HasNorm<vec3Norm, std::shared_ptr<vec3>>);

  template <typename _tcI0, typename T1>
  __attribute__((pure)) static unsigned int double_norm(const T1 x) {
    return (_tcI0::norm(x) + _tcI0::norm(x));
  }

  struct rect {
    std::shared_ptr<point> top_left;
    std::shared_ptr<point> bot_right;
  };

  __attribute__((pure)) static unsigned int
  rect_width(const std::shared_ptr<rect> &r);
  __attribute__((pure)) static unsigned int
  rect_height(const std::shared_ptr<rect> &r);
  __attribute__((pure)) static unsigned int
  rect_perimeter(const std::shared_ptr<rect> &r);
  static inline const std::shared_ptr<point> p1 =
      std::make_shared<point>(point{3u, 4u});
  static inline const std::shared_ptr<point> p2 =
      std::make_shared<point>(point{10u, 20u});
  static inline const unsigned int test_px = p1->px;
  static inline const unsigned int test_py = p1->py;
  static inline const unsigned int test_norm_point = pointNorm::norm(p1);
  static inline const unsigned int test_double_norm =
      double_norm<pointNorm, std::shared_ptr<point>>(p1);
  static inline const std::shared_ptr<vec3> v1 =
      std::make_shared<vec3>(vec3{1u, 2u, 3u});
  static inline const unsigned int test_norm_vec3 = vec3Norm::norm(v1);
  static inline const std::shared_ptr<rect> r1 =
      std::make_shared<rect>(rect{std::make_shared<point>(point{2u, 3u}),
                                  std::make_shared<point>(point{12u, 8u})});
  static inline const unsigned int test_width = rect_width(r1);
  static inline const unsigned int test_height = rect_height(r1);
  static inline const unsigned int test_perimeter = rect_perimeter(r1);
};

#endif // INCLUDED_PRIMITIVE_REC_TYPECLASS
