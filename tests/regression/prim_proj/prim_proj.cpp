#include <prim_proj.h>

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

std::shared_ptr<PrimProj::point>
PrimProj::add_points(std::shared_ptr<PrimProj::point> p1,
                     std::shared_ptr<PrimProj::point> p2) {
  return std::make_shared<PrimProj::point>(
      point{(p1->px + p2->px), (p1->py + p2->py)});
}

std::shared_ptr<PrimProj::point>
PrimProj::translate(const unsigned int dx, const unsigned int dy,
                    std::shared_ptr<PrimProj::point> p) {
  return std::make_shared<PrimProj::point>(
      point{(p->px + std::move(dx)), (p->py + std::move(dy))});
}
