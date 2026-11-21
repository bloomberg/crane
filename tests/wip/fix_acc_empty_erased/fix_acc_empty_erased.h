#pragma once

#include "fn.h"
#include "obj.h"
#include <cstdint>
#include <deque>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <utility>

struct FixAccEmptyErased {
  static inline const uint64_t t_opt =
      static_cast<uint64_t>([]() -> std::deque<bool> {
        auto [_x, _x0] = []() {
          crane::fn<std::pair<std::optional<uint64_t>, uint64_t>(
              std::deque<std::string>,
              std::pair<std::optional<uint64_t>, uint64_t>)> go =
              [](const std::deque<std::string> &l,
                 std::pair<std::optional<uint64_t>, uint64_t> acc) {
                if (l.empty()) {
                  return acc;
                } else {
                  const std::string &_x = l.front();
                  std::deque<std::string> _x0 =
                      std::deque<std::string>(l.begin() + 1, l.end());
                  return std::make_pair(std::optional<uint64_t>(), UINT64_C(0));
                }
              };
          return go(
              [](auto _a0, auto _a1) {
                _a1.push_front(_a0);
                return _a1;
              }(std::string(""), std::deque<std::string>{}),
              std::make_pair(std::optional<crane::obj>(), UINT64_C(0)));
        }();
        return std::deque<bool>{};
      }().size());
  static inline const uint64_t t_deque =
      static_cast<uint64_t>([]() -> std::deque<bool> {
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
        return std::deque<bool>{};
      }().size());
};
