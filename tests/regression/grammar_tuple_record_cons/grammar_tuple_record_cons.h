#ifndef INCLUDED_GRAMMAR_TUPLE_RECORD_CONS
#define INCLUDED_GRAMMAR_TUPLE_RECORD_CONS

#include "crane_fn.h"
#include <any>
#include <cstdint>
#include <deque>
#include <utility>
#include <variant>

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

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
                     crane_erase_fn([](const auto &tup) {
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
                               std::any_cast<std::deque<std::any>>(
                                   std::any_cast<std::deque<std::any>>(tpls))),
                           std::any_cast<uint64_t>(x));
                     }),
                     crane_erase_fn([](const auto &tup) {
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
                     }))),
      [](auto _a0, auto _a1) {
        _a1.push_front(_a0);
        return _a1;
      }(SigT<std::pair<std::any, std::deque<Symbol>>,
             std::pair<std::any, std::any>>::
            existt(std::make_pair(std::any(), std::deque<Symbol>{}),
                   std::make_pair(
                       crane_erase_fn([](const auto &) { return true; }),
                       crane_erase_fn([](const auto &) {
                         return std::deque<std::any>{};
                       }))),
        std::deque<SigT<std::pair<std::any, std::deque<Symbol>>,
                        std::pair<std::any, std::any>>>{}));
uint64_t num_entries(std::monostate _x);

#endif // INCLUDED_GRAMMAR_TUPLE_RECORD_CONS
