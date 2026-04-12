#ifndef INCLUDED_PRIM_PROJ
#define INCLUDED_PRIM_PROJ

#include <memory>
#include <type_traits>

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

  static std::shared_ptr<point> add_points(const std::shared_ptr<point> &p1,
                                           const std::shared_ptr<point> &p2);
  static inline const std::shared_ptr<point> origin =
      std::make_shared<point>(point{0u, 0u});
  static std::shared_ptr<point> translate(const unsigned int dx,
                                          const unsigned int dy,
                                          const std::shared_ptr<point> &p);
};

#endif // INCLUDED_PRIM_PROJ
