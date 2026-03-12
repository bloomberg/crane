#ifndef INCLUDED_PRIM_PROJ
#define INCLUDED_PRIM_PROJ

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

struct PrimProj {
  struct point {
    unsigned int px;
    unsigned int py;
  };

  static std::shared_ptr<point> add_points(std::shared_ptr<point> p1,
                                           std::shared_ptr<point> p2);
  static inline const std::shared_ptr<point> origin =
      std::make_shared<point>(point{0u, 0u});
  static std::shared_ptr<point> translate(const unsigned int dx,
                                          const unsigned int dy,
                                          std::shared_ptr<point> p);
};

#endif // INCLUDED_PRIM_PROJ
