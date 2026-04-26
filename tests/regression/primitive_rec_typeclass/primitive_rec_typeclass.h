#ifndef INCLUDED_PRIMITIVE_REC_TYPECLASS
#define INCLUDED_PRIMITIVE_REC_TYPECLASS

#include <concepts>
#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> struct is_shared_ptr : std::false_type {};

template <typename T>
struct is_shared_ptr<std::shared_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> struct is_optional : std::false_type {};

template <typename T> struct is_optional<std::optional<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_shared<T>(x->clone()) : nullptr;
  } else {
    return x;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using TargetBare = std::remove_cvref_t<Target>;
  using SourceBare = std::remove_cvref_t<Source>;
  if constexpr (is_unique_ptr<TargetBare>::value) {
    using Inner = typename is_unique_ptr<TargetBare>::element_type;
    if constexpr (is_unique_ptr<SourceBare>::value) {
      using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires {
                             typename Inner::crane_element_type;
                             x->template clone_as<
                                 typename Inner::crane_element_type>();
                           }) {
        return std::make_unique<Inner>(
            x->template clone_as<typename Inner::crane_element_type>());
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x->clone());
      }
    } else {
      if constexpr (requires { x.clone(); }) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (std::is_same_v<Inner, SourceBare>) {
        if constexpr (requires { x.clone(); }) {
          return std::make_unique<Inner>(x.clone());
        } else {
          return std::make_unique<Inner>(x);
        }
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        if constexpr (requires { x.clone(); }) {
          return std::make_unique<Inner>(x.clone());
        } else {
          return std::make_unique<Inner>(x);
        }
      }
    }
  } else if constexpr (is_optional<TargetBare>::value) {
    using Inner = typename is_optional<TargetBare>::element_type;
    if constexpr (is_optional<SourceBare>::value) {
      if (!x)
        return std::nullopt;
      return Target{clone_as_value<Inner>(*x)};
    } else {
      return Target{clone_as_value<Inner>(x)};
    }
  } else if constexpr (is_shared_ptr<TargetBare>::value) {
    using Inner = typename is_shared_ptr<TargetBare>::element_type;
    if constexpr (is_shared_ptr<SourceBare>::value) {
      using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else if constexpr (is_unique_ptr<SourceBare>::value) {
      if (!x)
        return nullptr;
      if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_shared<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x.clone());
      }
    }
  } else if constexpr (std::is_same_v<TargetBare, SourceBare>) {
    return clone_value(x);
  } else if constexpr (is_unique_ptr<SourceBare>::value) {
    using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      if (!x)
        return Target{};
      if constexpr (requires { x->clone(); }) {
        return x->clone();
      } else {
        return *x;
      }
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else if constexpr (requires { x->clone(); }) {
      return x->clone();
    } else {
      return Target(*x);
    }
  } else if constexpr (is_shared_ptr<SourceBare>::value) {
    using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (requires {
                         typename TargetBare::crane_element_type;
                         x.template clone_as<
                             typename TargetBare::crane_element_type>();
                       }) {
    return x.template clone_as<typename TargetBare::crane_element_type>();
  } else if constexpr (requires { x.template clone_as<TargetBare>(); }) {
    return x.template clone_as<TargetBare>();
  } else {
    return Target(x);
  }
}

template <typename I, typename t_A>
concept HasNorm = requires(t_A a0) {
  { I::norm(a0) } -> std::convertible_to<unsigned int>;
};

struct PrimitiveRecTypeclass {
  struct point {
    unsigned int px;
    unsigned int py;

    __attribute__((pure)) point *operator->() { return this; }

    __attribute__((pure)) const point *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) point clone() const {
      return point{clone_as_value<unsigned int>((*(this)).px),
                   clone_as_value<unsigned int>((*(this)).py)};
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

    __attribute__((pure)) vec3 *operator->() { return this; }

    __attribute__((pure)) const vec3 *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) vec3 clone() const {
      return vec3{clone_as_value<unsigned int>((*(this)).vx),
                  clone_as_value<unsigned int>((*(this)).vy),
                  clone_as_value<unsigned int>((*(this)).vz)};
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

    __attribute__((pure)) rect *operator->() { return this; }

    __attribute__((pure)) const rect *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) rect clone() const {
      return rect{clone_as_value<point>((*(this)).top_left),
                  clone_as_value<point>((*(this)).bot_right)};
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
