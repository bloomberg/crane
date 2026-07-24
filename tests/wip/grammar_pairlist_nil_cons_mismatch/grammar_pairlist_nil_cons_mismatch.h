#ifndef INCLUDED_GRAMMAR_PAIRLIST_NIL_CONS_MISMATCH
#define INCLUDED_GRAMMAR_PAIRLIST_NIL_CONS_MISMATCH

#include "crane_fn.h"
#include <any>
#include <cstdint>
#include <deque>
#include <memory>
#include <utility>
#include <variant>
#include <vector>

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }
};

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

struct String {
  // TYPES
  struct EmptyString {};

  struct String0 {
    Ascii a0;
    std::shared_ptr<String> a1;
  };

  using variant_t = std::variant<EmptyString, String0>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  String() {}

  explicit String(EmptyString _v) : v_(_v) {}

  explicit String(String0 _v) : v_(std::move(_v)) {}

  static String emptystring() { return String(EmptyString{}); }

  static String string0(Ascii a0, String a1) {
    return String(
        String0{std::move(a0), std::make_shared<String>(std::move(a1))});
  }

  // MANIPULATORS
  ~String() {
    std::vector<std::shared_ptr<String>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<String0>(&_v)) {
        if (_alt->a1) {
          _stack.push_back(std::move(_alt->a1));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        _drain(_cur->v_mut());
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct val {
  std::deque<std::pair<String, uint64_t>> pairs;
};
enum class Terminal { LBRACE, RBRACE, COMMA, COLON, STR, NAT };
enum class Nonterminal { DOC, OBJ, PAIR, PAIRS };

struct Symbol {
  // TYPES
  struct T {
    Terminal a0;
  };

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

  explicit Symbol(T _v) : v_(std::move(_v)) {}

  explicit Symbol(NT _v) : v_(std::move(_v)) {}

  static Symbol t(Terminal a0) { return Symbol(T{a0}); }

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
    }(
        SigT<std::pair<Nonterminal, std::deque<Symbol>>,
             std::pair<std::any, std::any>>::
            existt(std::make_pair(
                       Nonterminal::DOC,
                       [](auto _a0, auto _a1) {
                         _a1.push_front(_a0);
                         return _a1;
                       }(Symbol::nt(Nonterminal::OBJ), std::deque<Symbol>{})),
                   std::make_pair(
                       crane_erase_fn([](const auto &) { return true; }),
                       crane_erase_fn([](const auto &tup) {
                         const auto &[prs, _x] =
                             std::any_cast<std::pair<std::any, std::any>>(tup);
                         return val{crane_container_cast<
                             std::deque<std::pair<String, uint64_t>>>(
                             std::any_cast<
                                 std::deque<std::pair<std::any, std::any>>>(
                                 std::any_cast<
                                     std::deque<std::pair<std::any, std::any>>>(
                                     prs)))};
                       }))),
        [](auto _a0, auto _a1) {
          _a1.push_front(_a0);
          return _a1;
        }(SigT<std::pair<Nonterminal, std::deque<Symbol>>,
               std::pair<std::any, std::any>>::
              existt(std::make_pair(Nonterminal::OBJ,
                                    [](auto _a0, auto _a1) {
                                      _a1.push_front(_a0);
                                      return _a1;
                                    }(Symbol::t(Terminal::LBRACE),
                                      [](auto _a0, auto _a1) {
                                        _a1.push_front(_a0);
                                        return _a1;
                                      }(Symbol::nt(Nonterminal::PAIR),
                                        [](auto _a0, auto _a1) {
                                          _a1.push_front(_a0);
                                          return _a1;
                                        }(Symbol::nt(Nonterminal::PAIRS),
                                          [](auto _a0, auto _a1) {
                                            _a1.push_front(_a0);
                                            return _a1;
                                          }(Symbol::t(Terminal::RBRACE),
                                            std::deque<Symbol>{}))))),
                     std::make_pair(
                         crane_erase_fn([](const auto &) { return true; }),
                         crane_erase_fn([](const auto &tup) {
                           const auto &[_x, y0] =
                               std::any_cast<std::pair<std::any, std::any>>(
                                   tup);
                           const auto &[pr, y1] =
                               std::any_cast<std::pair<std::any, std::any>>(y0);
                           const auto &[prs, y2] =
                               std::any_cast<std::pair<std::any, std::any>>(y1);
                           const auto &[_x0, _x1] =
                               std::any_cast<std::pair<std::any, std::any>>(y2);
                           return [](auto _a0, auto _a1) {
                             _a1.push_front(_a0);
                             return _a1;
                           }(pr, std::any_cast<std::deque<std::any>>(prs));
                         }))),
          [](auto _a0, auto _a1) {
            _a1.push_front(_a0);
            return _a1;
          }(
              SigT<std::pair<Nonterminal, std::deque<Symbol>>,
                   std::pair<std::any, std::any>>::
                  existt(
                      std::make_pair(Nonterminal::OBJ,
                                     [](auto _a0, auto _a1) {
                                       _a1.push_front(_a0);
                                       return _a1;
                                     }(Symbol::t(Terminal::LBRACE),
                                       [](auto _a0, auto _a1) {
                                         _a1.push_front(_a0);
                                         return _a1;
                                       }(Symbol::t(Terminal::RBRACE),
                                         std::deque<Symbol>{}))),
                      std::make_pair(
                          crane_erase_fn([](const auto &) { return true; }),
                          crane_erase_fn([](const auto &) {
                            return std::deque<std::pair<std::any, std::any>>{};
                          }))),
              [](auto _a0, auto _a1) {
                _a1.push_front(_a0);
                return _a1;
              }(SigT<std::pair<Nonterminal, std::deque<Symbol>>,
                     std::pair<std::any, std::any>>::
                    existt(std::make_pair(Nonterminal::PAIRS,
                                          [](auto _a0, auto _a1) {
                                            _a1.push_front(_a0);
                                            return _a1;
                                          }(Symbol::t(Terminal::COMMA),
                                            [](auto _a0, auto _a1) {
                                              _a1.push_front(_a0);
                                              return _a1;
                                            }(Symbol::nt(Nonterminal::PAIR),
                                              [](auto _a0, auto _a1) {
                                                _a1.push_front(_a0);
                                                return _a1;
                                              }(Symbol::nt(Nonterminal::PAIRS),
                                                std::deque<Symbol>{})))),
                           std::make_pair(
                               crane_erase_fn(
                                   [](const auto &) { return true; }),
                               crane_erase_fn([](const auto &tup) {
                                 const auto &[_x, y0] = std::any_cast<
                                     std::pair<std::any, std::any>>(tup);
                                 const auto &[pr, y1] = std::any_cast<
                                     std::pair<std::any, std::any>>(y0);
                                 const auto &[prs, _x0] = std::any_cast<
                                     std::pair<std::any, std::any>>(y1);
                                 return [](auto _a0, auto _a1) {
                                   _a1.push_front(_a0);
                                   return _a1;
                                 }(pr, std::any_cast<std::deque<std::any>>(
                                           prs));
                               }))),
                [](auto _a0, auto _a1) {
                  _a1.push_front(_a0);
                  return _a1;
                }(SigT<std::pair<Nonterminal, std::deque<Symbol>>,
                       std::pair<std::any, std::any>>::
                      existt(
                          std::make_pair(Nonterminal::PAIRS,
                                         std::deque<Symbol>{}),
                          std::make_pair(
                              crane_erase_fn([](const auto &) { return true; }),
                              crane_erase_fn([](const auto &) {
                                return std::deque<
                                    std::pair<std::any, std::any>>{};
                              }))),
                  [](auto _a0, auto _a1) {
                    _a1.push_front(_a0);
                    return _a1;
                  }(SigT<std::pair<Nonterminal, std::deque<Symbol>>,
                         std::pair<std::any, std::any>>::
                        existt(std::make_pair(Nonterminal::PAIR,
                                              [](auto _a0, auto _a1) {
                                                _a1.push_front(_a0);
                                                return _a1;
                                              }(Symbol::t(Terminal::STR),
                                                [](auto _a0, auto _a1) {
                                                  _a1.push_front(_a0);
                                                  return _a1;
                                                }(Symbol::t(Terminal::COLON),
                                                  [](auto _a0, auto _a1) {
                                                    _a1.push_front(_a0);
                                                    return _a1;
                                                  }(Symbol::t(Terminal::NAT),
                                                    std::deque<Symbol>{})))),
                               std::make_pair(
                                   crane_erase_fn(
                                       [](const auto &) { return true; }),
                                   crane_erase_fn([](const auto &tup) {
                                     const auto &[s, y] = std::any_cast<
                                         std::pair<std::any, std::any>>(tup);
                                     const auto &[_x, y1] = std::any_cast<
                                         std::pair<std::any, std::any>>(y);
                                     const auto &[n, _x0] = std::any_cast<
                                         std::pair<std::any, std::any>>(y1);
                                     return std::make_pair(s, n);
                                   }))),
                    std::deque<SigT<std::pair<Nonterminal, std::deque<Symbol>>,
                                    std::pair<std::any, std::any>>>{}))))));
uint64_t num_entries(std::monostate _x);

#endif // INCLUDED_GRAMMAR_PAIRLIST_NIL_CONS_MISMATCH
