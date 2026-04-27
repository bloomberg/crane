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
      return point{(*(this)).px, (*(this)).py};
    }
  };

  __attribute__((pure)) static point add_points(const point &p1,
                                                const point &p2);
  static inline const point origin = point{0u, 0u};
  __attribute__((pure)) static point
  translate(const unsigned int &dx, const unsigned int &dy, const point &p);
};

#endif // INCLUDED_PRIM_PROJ
