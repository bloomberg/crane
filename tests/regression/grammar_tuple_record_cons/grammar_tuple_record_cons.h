#ifndef INCLUDED_GRAMMAR_TUPLE_RECORD_CONS
#define INCLUDED_GRAMMAR_TUPLE_RECORD_CONS

#include "crane_fn.h"
#include <any>
#include <cstdint>
#include <deque>
#include <stdexcept>
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
              if constexpr (crane_convertible<_U0, const A &>) {
                return crane_convert<_U0>(x);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }(),
            [&]() -> _U1 {
              if constexpr (crane_convertible<_U1, const P &>) {
                return crane_convert<_U1>(a1);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
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
          existt(
              std::make_pair(std::any(),
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
                  std::any(crane_erase_fn(
                      [](const std::pair<
                          uint64_t,
                          std::pair<symbol_semty,
                                    std::pair<symbol_semty,
                                              std::pair<std::deque<rgb>,
                                                        std::monostate>>>>
                             &tup) {
                        const auto &[x, y0] = tup;
                        const auto &[_x, y1] = y0;
                        const auto &[_x0, y2] = y1;
                        const auto &[tpls, _x1] = y2;
                        return triples_le_max(tpls, x);
                      })),
                  std::any(crane_erase_fn(
                      [](std::pair<
                          uint64_t,
                          std::pair<
                              uint64_t,
                              std::pair<uint64_t, std::pair<std::deque<rgb>,
                                                            std::monostate>>>>
                             tup) {
                        const auto &[x, y0] = tup;
                        const auto &[y, y1] = y0;
                        const auto &[z, y2] = y1;
                        const auto &[tpls, _x] = y2;
                        return [](auto _a0, auto _a1) {
                          _a1.push_front(_a0);
                          return _a1;
                        }(rgb{x, y, z}, tpls);
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
