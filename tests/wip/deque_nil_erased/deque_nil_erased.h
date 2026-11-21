#pragma once

#include "fn.h"
#include "obj.h"
#include <cstdint>
#include <deque>
#include <string>
#include <string_view>
#include <utility>

struct Ascii;

struct Ascii {
  // DATA
  bool a0;
  bool a1;
  bool a2;
  bool a3;
  bool a4;
  bool a5;
  bool a6;
  bool a7;

  // ACCESSORS
  Ascii clone() const { return {a0, a1, a2, a3, a4, a5, a6, a7}; }

  // CREATORS
  static Ascii ascii0(bool a0, bool a1, bool a2, bool a3, bool a4, bool a5,
                      bool a6, bool a7) {
    return {a0, a1, a2, a3, a4, a5, a6, a7};
  }
};

struct DequeNilErased {
  static inline const uint64_t t_1 =
      static_cast<uint64_t>([]() -> std::deque<Ascii> {
        auto [_x, _x0] = []() {
          crane::fn<std::pair<uint64_t, std::deque<uint64_t>>(
              std::deque<std::string>,
              std::pair<uint64_t, std::deque<uint64_t>>)> go =
              [](const std::deque<std::string> &l,
                 std::pair<uint64_t, std::deque<uint64_t>> acc) {
                if (l.empty()) {
                  return acc;
                } else {
                  const std::string &_x = l.front();
                  std::deque<std::string> _x0 =
                      std::deque<std::string>(l.begin() + 1, l.end());
                  return std::make_pair(UINT64_C(0), std::deque<uint64_t>{});
                }
              };
          return go(
              [](auto _a0, auto _a1) {
                _a1.push_front(_a0);
                return _a1;
              }(std::string(""), std::deque<std::string>{}),
              std::make_pair(UINT64_C(0), std::deque<crane::obj>{}));
        }();
        return std::deque<Ascii>{};
      }().size());
};
