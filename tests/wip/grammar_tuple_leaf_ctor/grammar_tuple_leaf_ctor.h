#ifndef INCLUDED_GRAMMAR_TUPLE_LEAF_CTOR
#define INCLUDED_GRAMMAR_TUPLE_LEAF_CTOR

#include "crane_fn.h"
#include <any>
#include <memory>
#include <string>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
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

  uint64_t length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (a1->length() + 1);
    }
  }
};

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }
};
enum class Terminal { TSTRING, TINT };

struct Val {
  // TYPES
  struct VStr {
    std::string a0;
  };

  struct VInt {
    uint64_t a0;
  };

  using variant_t = std::variant<VStr, VInt>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Val() {}

  explicit Val(VStr _v) : v_(std::move(_v)) {}

  explicit Val(VInt _v) : v_(std::move(_v)) {}

  static Val vstr(std::string a0) { return Val(VStr{std::move(a0)}); }

  static Val vint(uint64_t a0) { return Val(VInt{a0}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Symbol {
  // TYPES
  struct T {
    Terminal a0;
  };

  struct NT {};

  using variant_t = std::variant<T, NT>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Symbol() {}

  explicit Symbol(T _v) : v_(std::move(_v)) {}

  explicit Symbol(NT _v) : v_(_v) {}

  static Symbol t(Terminal a0) { return Symbol(T{a0}); }

  static Symbol nt() { return Symbol(NT{}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

using production = std::pair<std::any, List<Symbol>>;
using predicate_semty = std::any;
using action_semty = std::any;
using production_semty = std::pair<predicate_semty, action_semty>;
using grammar_entry = SigT<production, production_semty>;
const List<grammar_entry> entries = List<
    SigT<std::pair<std::any, List<Symbol>>, std::pair<std::any, std::any>>>::
    cons(
        SigT<std::pair<std::any, List<Symbol>>, std::pair<std::any, std::any>>::
            existt(std::make_pair(std::any(), List<Symbol>::cons(
                                                  Symbol::t(Terminal::TSTRING),
                                                  List<Symbol>::nil())),
                   std::make_pair(
                       crane_erase_fn([](const auto &) { return true; }),
                       crane_erase_fn([](const auto &tup) {
                         const auto &[s, _x] =
                             std::any_cast<std::pair<std::any, std::any>>(tup);
                         return Val::vstr(s);
                       }))),
        List<SigT<std::pair<std::any, List<Symbol>>,
                  std::pair<std::any, std::any>>>::
            cons(SigT<std::pair<std::any, List<Symbol>>,
                      std::pair<std::any, std::any>>::
                     existt(
                         std::make_pair(std::any(),
                                        List<Symbol>::cons(
                                            Symbol::t(Terminal::TINT),
                                            List<Symbol>::nil())),
                         std::make_pair(
                             crane_erase_fn([](const auto &) { return true; }),
                             crane_erase_fn([](const auto &tup) {
                               const auto &[i, _x] =
                                   std::any_cast<std::pair<std::any, std::any>>(
                                       tup);
                               return Val::vint(i);
                             }))),
                 List<SigT<std::pair<std::any, List<Symbol>>,
                           std::pair<std::any, std::any>>>::nil()));
uint64_t num_entries(std::monostate _x);

#endif // INCLUDED_GRAMMAR_TUPLE_LEAF_CTOR
