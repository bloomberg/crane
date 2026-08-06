#include "object_model.h"

std::pair<std::pair<int64_t, int64_t>, int64_t> testtoST1_ext() {
  Point<std::monostate> p = []() {
    int64_t ref;
    ref = INT64_C(1);
    return Point<std::monostate>{
        ref,
        [=](int64_t move_amt) mutable {
          int64_t i = ref;
          ref = static_cast<int64_t>(static_cast<uint64_t>(i) +
                                     static_cast<uint64_t>(move_amt));
          return std::monostate{};
        },
        [&]() {
          int64_t i = ref;
          return static_cast<int64_t>(static_cast<uint64_t>(i) -
                                      static_cast<uint64_t>(INT64_C(1)));
        }()};
  }();
  int64_t a = p.getX;
  p.moveD(INT64_C(2));
  int64_t b = p.getX;
  int64_t c = p.offsetX;
  return std::make_pair(std::make_pair(a, b), c);
}

std::pair<std::pair<std::pair<int64_t, int64_t>, int64_t>, int64_t>
testtoST2_ext() {
  Point<std::monostate> p1 = []() {
    int64_t ref;
    ref = INT64_C(1);
    return Point<std::monostate>{
        ref,
        [=](int64_t move_amt) mutable {
          int64_t i = ref;
          ref = static_cast<int64_t>(static_cast<uint64_t>(i) +
                                     static_cast<uint64_t>(move_amt));
          return std::monostate{};
        },
        [&]() {
          int64_t i = ref;
          return static_cast<int64_t>(static_cast<uint64_t>(i) -
                                      static_cast<uint64_t>(INT64_C(1)));
        }()};
  }();
  Point<std::monostate> p2 = []() {
    int64_t ref;
    ref = INT64_C(10);
    return Point<std::monostate>{
        ref,
        [=](int64_t move_amt) mutable {
          int64_t i = ref;
          ref = static_cast<int64_t>(static_cast<uint64_t>(i) +
                                     static_cast<uint64_t>(move_amt));
          return std::monostate{};
        },
        [&]() {
          int64_t i = ref;
          return static_cast<int64_t>(static_cast<uint64_t>(i) -
                                      static_cast<uint64_t>(INT64_C(10)));
        }()};
  }();
  int64_t a = p1.getX;
  int64_t b = p2.getX;
  int64_t v1 = p1.getX;
  p2.moveD(v1);
  int64_t c = p1.getX;
  int64_t d = p2.getX;
  return std::make_pair(std::make_pair(std::make_pair(a, b), c), d);
}
