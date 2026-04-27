#ifndef INCLUDED_PRIM_PROJ
#define INCLUDED_PRIM_PROJ

#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct PrimProj {
  struct point {
    unsigned int px;
    unsigned int py;

    __attribute__((pure)) point *operator->() { return this; }

    __attribute__((pure)) const point *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) point clone() const {
      return point{
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).px),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).py)};
    }
  };

  __attribute__((pure)) static point add_points(const point &p1,
                                                const point &p2);
  static inline const point origin = point{0u, 0u};
  __attribute__((pure)) static point
  translate(const unsigned int &dx, const unsigned int &dy, const point &p);
};

#endif // INCLUDED_PRIM_PROJ
