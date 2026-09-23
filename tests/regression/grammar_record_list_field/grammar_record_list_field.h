#ifndef INCLUDED_GRAMMAR_RECORD_LIST_FIELD
#define INCLUDED_GRAMMAR_RECORD_LIST_FIELD

#include "crane_fn.h"
#include <any>
#include <cstdint>
#include <deque>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A, typename P> struct SigT;
struct elt;
struct rec;
enum class Nonterminal;
struct Symbol;

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

/// Concrete element type, like rgb_triple.
struct elt {
  uint64_t a;
  uint64_t b;
};

/// Record with a concrete-element list field, like ppm_value's triples.
struct rec {
  std::deque<elt> items;
};
enum class Nonterminal { DOC, ITEMS };

struct Symbol {
  // TYPES
  struct T {};

  struct NT {
    Nonterminal a0;
  };

  using variant_t = std::variant<T, NT>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Symbol() {}

  explicit Symbol(T _v) : v_(_v) {}

  explicit Symbol(NT _v) : v_(std::move(_v)) {}

  static Symbol t() { return Symbol(T{}); }

  static Symbol nt(Nonterminal a0) { return Symbol(NT{a0}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

using symbol_semty = std::any;
using production = std::pair<Nonterminal, std::deque<Symbol>>;
using predicate_semty = std::any;
using action_semty = std::any;
using production_semty = std::pair<predicate_semty, action_semty>;
using grammar_entry = SigT<production, production_semty>;
const std::deque<grammar_entry> entries =
    [](auto _a0, auto _a1) {
      _a1.push_front(_a0);
      return _a1;
    }(SigT<std::pair<Nonterminal, std::deque<Symbol>>,
           std::pair<std::any, std::any>>::
          existt(
              std::make_pair(
                  Nonterminal::DOC,
                  [](auto _a0, auto _a1) {
                    _a1.push_front(_a0);
                    return _a1;
                  }(Symbol::nt(Nonterminal::ITEMS), std::deque<Symbol>{})),
              std::make_pair(
                  std::any(crane_erase_fn(
                      [](const std::pair<symbol_semty, std::monostate> &tup) {
                        const auto &[_x, _x0] = tup;
                        return true;
                      })),
                  std::any(crane_erase_fn(
                      [](std::pair<std::deque<elt>, std::monostate> tup) {
                        const auto &[ts, _x] = tup;
                        return rec{ts};
                      })))),
      [](auto _a0, auto _a1) {
        _a1.push_front(_a0);
        return _a1;
      }(SigT<std::pair<Nonterminal, std::deque<Symbol>>,
             std::pair<std::any, std::any>>::
            existt(std::make_pair(Nonterminal::ITEMS, std::deque<Symbol>{}),
                   std::make_pair(std::any(crane_erase_fn(
                                      [](const auto &) { return true; })),
                                  std::any(crane_erase_fn([](const auto &) {
                                    return std::deque<std::any>{};
                                  })))),
        [](auto _a0, auto _a1) {
          _a1.push_front(_a0);
          return _a1;
        }(SigT<std::pair<Nonterminal, std::deque<Symbol>>,
               std::pair<std::any, std::any>>::
              existt(
                  std::
                      make_pair(Nonterminal::ITEMS,
                                [](auto _a0, auto _a1) {
                                  _a1.push_front(_a0);
                                  return _a1;
                                }(Symbol::
                                      t(),
                                  [](auto _a0, auto _a1) {
                                    _a1.push_front(_a0);
                                    return _a1;
                                  }(Symbol::nt(Nonterminal::ITEMS),
                                    std::deque<Symbol>{}))),
                  std::make_pair(
                      std::any(
                          crane_erase_fn([](const auto &) { return true; })),
                      std::any(crane_erase_fn(
                          [](std::pair<uint64_t, std::pair<std::deque<elt>,
                                                           std::monostate>>
                                 tup) {
                            const auto &[n, y] = tup;
                            const auto &[ts, _x] = y;
                            return [](auto _a0, auto _a1) {
                              _a1.push_front(_a0);
                              return _a1;
                            }(elt{n, n}, ts);
                          })))),
          std::deque<SigT<std::pair<Nonterminal, std::deque<Symbol>>,
                          std::pair<std::any, std::any>>>{})));
uint64_t num_entries(std::monostate _x);

#endif // INCLUDED_GRAMMAR_RECORD_LIST_FIELD
