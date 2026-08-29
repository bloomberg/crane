#include "primitive_rec_typeclass.h"

uint64_t
PrimitiveRecTypeclass::rect_width(const PrimitiveRecTypeclass::rect &r) {
  return (((r.bot_right.px - r.top_left.px) > r.bot_right.px
               ? 0
               : (r.bot_right.px - r.top_left.px)));
}

uint64_t
PrimitiveRecTypeclass::rect_height(const PrimitiveRecTypeclass::rect &r) {
  return (((r.bot_right.py - r.top_left.py) > r.bot_right.py
               ? 0
               : (r.bot_right.py - r.top_left.py)));
}

uint64_t
PrimitiveRecTypeclass::rect_perimeter(const PrimitiveRecTypeclass::rect &r) {
  return (UINT64_C(2) * (rect_width(r) + rect_height(r)));
}
