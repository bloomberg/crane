#include <primitive_rec_typeclass.h>

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

__attribute__((pure)) unsigned int PrimitiveRecTypeclass::rect_width(
    const std::shared_ptr<PrimitiveRecTypeclass::rect> &r) {
  return (((r->bot_right->px - r->top_left->px) > r->bot_right->px
               ? 0
               : (r->bot_right->px - r->top_left->px)));
}

__attribute__((pure)) unsigned int PrimitiveRecTypeclass::rect_height(
    const std::shared_ptr<PrimitiveRecTypeclass::rect> &r) {
  return (((r->bot_right->py - r->top_left->py) > r->bot_right->py
               ? 0
               : (r->bot_right->py - r->top_left->py)));
}

__attribute__((pure)) unsigned int PrimitiveRecTypeclass::rect_perimeter(
    const std::shared_ptr<PrimitiveRecTypeclass::rect> &r) {
  return (2u * (rect_width(r) + rect_height(r)));
}
