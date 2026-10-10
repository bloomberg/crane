#ifndef INCLUDED_GRAMMAR_ACTION_PAIRLIST_CRASH
#define INCLUDED_GRAMMAR_ACTION_PAIRLIST_CRASH

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <deque>
#include <memory>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

template <typename A, typename P> struct SigT;
struct Val;
enum class Nonterminal;
struct Symbol;
using predicate_semty = crane::obj;
using action_semty = crane::obj;

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  template <typename CraneU0, typename CraneU1>
  operator SigT<CraneU0, CraneU1>() const {
    return {[&]() -> CraneU0 {
              if constexpr (crane_convertible<CraneU0, const A &>) {
                return crane_convert<CraneU0>(x);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }(),
            [&]() -> CraneU1 {
              if constexpr (crane_convertible<CraneU1, const P &>) {
                return crane_convert<CraneU1>(a1);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
  }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }
};

struct Val {
  // TYPES
  struct VAssoc {
    std::shared_ptr<std::deque<std::pair<std::string, Val>>> a0;
  };

  struct VBool {
    bool a0;
  };

  struct VFloat {
    uint64_t a0;
  };

  struct VInt {
    uint64_t a0;
  };

  struct VList {
    std::shared_ptr<std::deque<Val>> a0;
  };

  struct VNull {};

  struct VStr {
    std::string a0;
  };

  using variant_t =
      std::variant<VAssoc, VBool, VFloat, VInt, VList, VNull, VStr>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Val() {}

  explicit Val(VAssoc _v) : v_(std::move(_v)) {}

  explicit Val(VBool _v) : v_(std::move(_v)) {}

  explicit Val(VFloat _v) : v_(std::move(_v)) {}

  explicit Val(VInt _v) : v_(std::move(_v)) {}

  explicit Val(VList _v) : v_(std::move(_v)) {}

  explicit Val(VNull _v) : v_(_v) {}

  explicit Val(VStr _v) : v_(std::move(_v)) {}

  static Val vassoc(std::deque<std::pair<std::string, Val>> a0);

  static Val vbool(bool a0) { return Val(VBool{a0}); }

  static Val vfloat(uint64_t a0) { return Val(VFloat{a0}); }

  static Val vint(uint64_t a0) { return Val(VInt{a0}); }

  static Val vlist(std::deque<Val> a0);

  static Val vnull() { return Val(VNull{}); }

  static Val vstr(std::string a0) { return Val(VStr{std::move(a0)}); }

  // MANIPULATORS
  ~Val() {
    if (std::holds_alternative<VBool>(v_mut())) {
      return;
    }
    if (std::holds_alternative<VFloat>(v_mut())) {
      return;
    }
    if (std::holds_alternative<VInt>(v_mut())) {
      return;
    }
    if (std::holds_alternative<VNull>(v_mut())) {
      return;
    }
    if (std::holds_alternative<VStr>(v_mut())) {
      return;
    }
    crane::small_vector<std::shared_ptr<Val>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<VList>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          for (auto &_elem : *_alt->a0) {
            _stack.push_back(std::make_shared<Val>(std::move(_elem)));
          }
          _alt->a0.reset();
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        std::atomic_thread_fence(std::memory_order_acquire);
        _drain(_cur->v_mut());
      }
    }
  }

  Val(const Val &) = default;
  Val &operator=(const Val &) = default;
  Val(Val &&) = default;
  Val &operator=(Val &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename T1>
bool nodupKeys(const std::deque<std::pair<std::string, T1>> &prs) {
  if (prs.empty()) {
    return true;
  } else {
    const auto &_x = prs.front();
    std::deque<std::pair<std::string, T1>> _x0(prs.begin() + 1, prs.end());
    return false;
  }
}
enum class Nonterminal { VALUE, OBJ };

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

using production = std::pair<Nonterminal, std::deque<Symbol>>;
using production_semty = std::pair<predicate_semty, action_semty>;
using grammar_entry = SigT<production, production_semty>;
const std::deque<grammar_entry> entries =
    [](auto _a0, auto _a1) {
      _a1.push_front(_a0);
      return _a1;
    }(SigT<std::pair<Nonterminal, std::deque<Symbol>>,
           std::pair<crane::obj, crane::obj>>::
          existt(
              std::make_pair(
                  Nonterminal::VALUE,
                  [](auto _a0, auto _a1) {
                    _a1.push_front(_a0);
                    return _a1;
                  }(Symbol::nt(Nonterminal::OBJ), std::deque<Symbol>{})),
              std::make_pair(
                  crane::obj(crane_erase_fn([](const auto &tup) {
                    const auto &[prs, _x] =
                        crane::any_cast<std::pair<crane::obj, crane::obj>>(tup);
                    return nodupKeys<Val>(
                        crane_container_cast<
                            std::deque<std::pair<std::string, Val>>>(
                            crane::any_cast<std::deque<crane::obj>>(prs)));
                  })),
                  crane::obj(crane_erase_fn([](const auto &tup) {
                    const auto &[prs, _x] =
                        crane::any_cast<std::pair<crane::obj, crane::obj>>(tup);
                    return Val::vassoc(crane_container_cast<
                                       std::deque<std::pair<std::string, Val>>>(
                        crane::any_cast<std::deque<crane::obj>>(prs)));
                  })))),
      [](auto _a0, auto _a1) {
        _a1.push_front(_a0);
        return _a1;
      }(SigT<std::pair<Nonterminal, std::deque<Symbol>>,
             std::pair<crane::obj, crane::obj>>::
            existt(std::make_pair(Nonterminal::VALUE,
                                  [](auto _a0, auto _a1) {
                                    _a1.push_front(_a0);
                                    return _a1;
                                  }(Symbol::t(), std::deque<Symbol>{})),
                   std::make_pair(
                       crane::obj(
                           crane_erase_fn([](const auto &) { return true; })),
                       crane::obj(crane_erase_fn([](const auto &tup) {
                         const auto &[s, _x] =
                             crane::any_cast<std::pair<crane::obj, crane::obj>>(
                                 tup);
                         return Val::vstr(crane::any_cast<std::string>(s));
                       })))),
        std::deque<SigT<std::pair<Nonterminal, std::deque<Symbol>>,
                        std::pair<crane::obj, crane::obj>>>{}));
uint64_t num_entries(std::monostate _x);

inline Val Val::vassoc(std::deque<std::pair<std::string, Val>> a0) {
  return Val(VAssoc{std::make_shared<std::deque<std::pair<std::string, Val>>>(
      std::move(a0))});
}

inline Val Val::vlist(std::deque<Val> a0) {
  return Val(VList{std::make_shared<std::deque<Val>>(std::move(a0))});
}

#endif // INCLUDED_GRAMMAR_ACTION_PAIRLIST_CRASH
