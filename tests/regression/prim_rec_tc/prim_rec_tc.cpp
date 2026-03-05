#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <prim_rec_tc.h>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int PrimRecTc::rect_width(const std::shared_ptr<PrimRecTc::rect> &r) {
  return (((r->bot_right->px - r->top_left->px) > r->bot_right->px
               ? 0
               : (r->bot_right->px - r->top_left->px)));
}

unsigned int PrimRecTc::rect_height(const std::shared_ptr<PrimRecTc::rect> &r) {
  return (((r->bot_right->py - r->top_left->py) > r->bot_right->py
               ? 0
               : (r->bot_right->py - r->top_left->py)));
}

unsigned int
PrimRecTc::rect_perimeter(const std::shared_ptr<PrimRecTc::rect> &r) {
  return (((0 + 1) + 1) * (rect_width(r) + rect_height(r)));
}
