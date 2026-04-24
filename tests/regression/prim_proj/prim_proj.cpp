#include <prim_proj.h>

#include <type_traits>

__attribute__((pure)) PrimProj::point
PrimProj::add_points(const PrimProj::point &p1, const PrimProj::point &p2) {
  return point{(p1.px + p2.px), (p1.py + p2.py)};
}

__attribute__((pure)) PrimProj::point
PrimProj::translate(const unsigned int &dx, const unsigned int &dy,
                    const PrimProj::point &p) {
  return point{(p.px + dx), (p.py + dy)};
}
