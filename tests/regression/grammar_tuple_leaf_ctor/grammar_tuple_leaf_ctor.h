#ifndef INCLUDED_GRAMMAR_TUPLE_LEAF_CTOR
#define INCLUDED_GRAMMAR_TUPLE_LEAF_CTOR

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

template <typename A> struct List;
template <typename A, typename P> struct SigT;
enum class Terminal;
struct Val;
struct Symbol;
using predicate_semty = crane::obj;
using action_semty = crane::obj;

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

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_(crane_convert_spine(
            _other, std::shared_ptr<List<A>>(nullptr),
            [](const List<CraneU> &_cell) -> const List<CraneU> * {
              if (std::holds_alternative<typename List<CraneU>::Cons>(
                      _cell.v())) {
                return std::get<typename List<CraneU>::Cons>(_cell.v()).l.get();
              } else {
                return nullptr;
              }
            },
            [&](const List<CraneU> &_other,
                std::shared_ptr<List<A>> _below) -> variant_t {
              if (std::holds_alternative<typename List<CraneU>::Nil>(
                      _other.v())) {
                return Nil{};
              } else {
                const auto &[a, l] =
                    std::get<typename List<CraneU>::Cons>(_other.v());
                return Cons{
                    [&]() -> A {
                      if constexpr (crane_convertible<A, const CraneU &>) {
                        return crane_convert<A>(a);
                      } else {
                        throw std::logic_error(
                            "unreachable: inactive constructor field at this "
                            "instantiation");
                      }
                    }(),
                    std::move(_below)};
              }
            },
            [](auto &&_alt) {
              return std::make_shared<List<A>>(std::move(_alt));
            })) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  uint64_t length() const {
    const List<A> *_self = this;

    /// CraneEnter: captures varying parameters for each recursive call.
    struct CraneEnter {
      const List<A> *_self;
    };

    /// CraneCont_Cons: resumes after recursive call, then processes rest.
    struct CraneCont_Cons {};

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    uint64_t _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{_self});
    /// Loopified length: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(CraneCont_Cons{});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }
};

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  template <typename CraneU0, typename CraneU1>
    requires crane_convertible<CraneU0, const A &> &&
             crane_convertible<CraneU1, const P &>
  operator SigT<CraneU0, CraneU1>() const {
    return {crane_convert<CraneU0>(x), crane_convert<CraneU1>(a1)};
  }

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

using production = std::pair<crane::obj, List<Symbol>>;
using production_semty = std::pair<predicate_semty, action_semty>;
using grammar_entry = SigT<production, production_semty>;
const List<grammar_entry> entries = List<grammar_entry>::cons(
    SigT<production, production_semty>::existt(
        std::make_pair(crane::obj(crane::obj()),
                       List<Symbol>::cons(Symbol::t(Terminal::TSTRING),
                                          List<Symbol>::nil())),
        std::make_pair(
            crane::obj(crane_erase_fn([](const auto &) { return true; })),
            crane::obj(crane_erase_fn([](const auto &tup) {
              const auto &[s, _x] =
                  crane::any_cast<std::pair<crane::obj, crane::obj>>(tup);
              return Val::vstr(crane::any_cast<std::string>(s));
            })))),
    List<grammar_entry>::cons(
        SigT<production, production_semty>::existt(
            std::make_pair(crane::obj(crane::obj()),
                           List<Symbol>::cons(Symbol::t(Terminal::TINT),
                                              List<Symbol>::nil())),
            std::make_pair(
                crane::obj(crane_erase_fn([](const auto &) { return true; })),
                crane::obj(crane_erase_fn([](const auto &tup) {
                  const auto &[i, _x] =
                      crane::any_cast<std::pair<crane::obj, crane::obj>>(tup);
                  return Val::vint(crane::any_cast<uint64_t>(i));
                })))),
        List<grammar_entry>::nil()));
uint64_t num_entries(std::monostate _x);

#endif // INCLUDED_GRAMMAR_TUPLE_LEAF_CTOR
