#pragma once

#include "fn.h"
#include <cstdint>
#include <deque>
#include <optional>
#include <type_traits>
#include <utility>

struct MappedOpCurriedElement {
  static uint64_t
  deque_map(const std::deque<crane::fn<uint64_t(uint64_t, uint64_t)>> &l);
  static uint64_t
  maybe_get(const std::optional<crane::fn<uint64_t(uint64_t, uint64_t)>> &m);
  static inline const uint64_t result =
      (((deque_map([](auto _a0, auto _a1) {
        _a1.push_front(_a0);
        return _a1;
      }(crane::fn<uint64_t(uint64_t, uint64_t)>(
             [](uint64_t _x0,
                uint64_t _x1)
                  -> uint64_t { return (_x0 + _x1); }),
        [](auto _a0, auto _a1) {
          _a1.push_front(_a0);
          return _a1;
        }(crane::fn<uint64_t(uint64_t, uint64_t)>([](uint64_t _x0,
                                                     uint64_t _x1)
                                                       -> uint64_t {
          return (((_x0 - _x1) > _x0 ? 0 : (_x0 - _x1)));
        }),
          std::deque<crane::fn<uint64_t(uint64_t, uint64_t)>>{}))) *
         UINT64_C(100)) +
        (maybe_get(std::optional<crane::fn<uint64_t(uint64_t, uint64_t)>>{
             crane::fn<uint64_t(uint64_t, uint64_t)>(
                 [](uint64_t _x0,
                    uint64_t _x1)
                      -> uint64_t { return (_x0 + _x1); })}) *
         UINT64_C(10))) +
       maybe_get(std::optional<crane::fn<uint64_t(uint64_t, uint64_t)>>{}));
};
