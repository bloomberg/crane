#include <primitive_rec_typeclass.h>

#include <concepts>
#include <memory>
#include <optional>
#include <type_traits>

__attribute__((pure)) unsigned int
PrimitiveRecTypeclass::rect_width(const PrimitiveRecTypeclass::rect &r) {
  return (((r.bot_right.px - r.top_left.px) > r.bot_right.px
               ? 0
               : (r.bot_right.px - r.top_left.px)));
}

__attribute__((pure)) unsigned int
PrimitiveRecTypeclass::rect_height(const PrimitiveRecTypeclass::rect &r) {
  return (((r.bot_right.py - r.top_left.py) > r.bot_right.py
               ? 0
               : (r.bot_right.py - r.top_left.py)));
}

__attribute__((pure)) unsigned int
PrimitiveRecTypeclass::rect_perimeter(const PrimitiveRecTypeclass::rect &r) {
  return (2u * (rect_width(r) + rect_height(r)));
}
