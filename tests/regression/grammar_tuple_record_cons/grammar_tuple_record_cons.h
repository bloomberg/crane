#ifndef INCLUDED_GRAMMAR_TUPLE_RECORD_CONS
#define INCLUDED_GRAMMAR_TUPLE_RECORD_CONS

#include "crane_fn.h"
#include <any>
#include <cstdint>
#include <deque>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A, typename P> struct SigT;
struct rgb;
enum class Symbol;

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  template <typename _U0, typename _U1> operator SigT<_U0, _U1>() const {
    return {[&]() -> _U0 {
              if constexpr (std::is_same_v<A, std::any>) {
                return crane_any_cast<_U0>(x);
              } else {
                if constexpr (std::is_constructible_v<_U0, const A &>) {
                  return _U0(x);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }
            }(),
            [&]() -> _U1 {
              if constexpr (std::is_same_v<P, std::any>) {
                return crane_any_cast<_U1>(a1);
              } else {
                if constexpr (std::is_constructible_v<_U1, const P &>) {
                  return _U1(a1);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }
            }()};
  }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }
};

struct rgb {
  uint64_t red;
  uint64_t green;
  uint64_t blue;
};

bool triples_le_max(const std::deque<rgb> &ts, uint64_t m);
enum class Symbol { T, NT };
using symbol_semty = std::any;
using production = std::pair<std::any, std::deque<Symbol>>;
using predicate_semty = std::any;
using action_semty = std::any;
using production_semty = std::pair<predicate_semty, action_semty>;
using grammar_entry = SigT<production, production_semty>;
const std::deque<grammar_entry> entries =
    [](auto _a0, auto _a1) {
      _a1.push_front(_a0);
      return _a1;
    }(SigT<std::pair<std::any, std::deque<Symbol>>,
           std::pair<std::any, std::any>>::
          existt(std::make_pair(std::any(),
                                [](auto _a0, auto _a1) {
                                  _a1.push_front(_a0);
                                  return _a1;
                                }(Symbol::T,
                                  [](auto _a0, auto _a1) {
                                    _a1.push_front(_a0);
                                    return _a1;
                                  }(Symbol::T,
                                    [](auto _a0, auto _a1) {
                                      _a1.push_front(_a0);
                                      return _a1;
                                    }(Symbol::T,
                                      [](auto _a0, auto _a1) {
                                        _a1.push_front(_a0);
                                        return _a1;
                                      }(Symbol::NT, std::deque<Symbol>{}))))),
                 std::make_pair(
                     std::any(crane_erase_fn([](const auto &tup) {
                       const auto &[x, y0] =
                           std::any_cast<std::pair<std::any, std::any>>(tup);
                       const auto &[_x, y1] =
                           std::any_cast<std::pair<std::any, std::any>>(y0);
                       const auto &[_x0, y2] =
                           std::any_cast<std::pair<std::any, std::any>>(y1);
                       const auto &[tpls, _x1] =
                           std::any_cast<std::pair<std::any, std::any>>(y2);
                       return triples_le_max(
                           crane_container_cast<std::deque<rgb>>(
                               std::any_cast<std::deque<std::any>>(tpls)),
                           std::any_cast<uint64_t>(x));
                     })),
                     std::any(crane_erase_fn([](const auto &tup) {
                       const auto &[x, y0] =
                           std::any_cast<std::pair<std::any, std::any>>(tup);
                       const auto &[y, y1] =
                           std::any_cast<std::pair<std::any, std::any>>(y0);
                       const auto &[z, y2] =
                           std::any_cast<std::pair<std::any, std::any>>(y1);
                       const auto &[tpls, _x] =
                           std::any_cast<std::pair<std::any, std::any>>(y2);
                       return [](auto _a0, auto _a1) {
                         _a1.push_front(_a0);
                         return _a1;
                       }(rgb{std::any_cast<uint64_t>(x),
                              std::any_cast<uint64_t>(y),
                              std::any_cast<uint64_t>(z)},
                              std::any_cast<std::deque<std::any>>(tpls));
                     })))),
      [](auto _a0, auto _a1) {
        _a1.push_front(_a0);
        return _a1;
      }(SigT<std::pair<std::any, std::deque<Symbol>>,
             std::pair<std::any, std::any>>::
            existt(std::make_pair(std::any(), std::deque<Symbol>{}),
                   std::make_pair(std::any(crane_erase_fn(
                                      [](const auto &) { return true; })),
                                  std::any(crane_erase_fn([](const auto &) {
                                    return std::deque<std::any>{};
                                  })))),
        std::deque<SigT<std::pair<std::any, std::deque<Symbol>>,
                        std::pair<std::any, std::any>>>{}));
uint64_t num_entries(std::monostate _x);

#endif // INCLUDED_GRAMMAR_TUPLE_RECORD_CONS
