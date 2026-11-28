#pragma once

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <concepts>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;
template <typename A, typename P> struct SigT;
struct Val;

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
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, crane::shared_child_slot<List<A>> l) {
    return List<A>(Cons{std::move(a), l.take()});
  }

  // MANIPULATORS
  ~List() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
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
};

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

  A projT1() const {
    const auto &[x0, _] = *this;
    return x0;
  }
};

template <typename M>
concept SYM = requires {
  typename M::terminal;
  typename M::nonterminal;
  {
    M::t_eq_dec(std::declval<typename M::terminal>(),
                std::declval<typename M::terminal>())
  } -> std::same_as<bool>;
  {
    M::nt_eq_dec(std::declval<typename M::nonterminal>(),
                 std::declval<typename M::nonterminal>())
  } -> std::same_as<bool>;
  typename M::t_semty;
  typename M::nt_semty;
};

template <SYM Ty> struct DefsFn {
  struct symbol {
    // TYPES
    struct T {
      typename Ty::terminal a0;
    };

    struct NT {
      typename Ty::nonterminal a0;
    };

    using variant_t = std::variant<T, NT>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    symbol() {}

    explicit symbol(T _v) : v_(std::move(_v)) {}

    explicit symbol(NT _v) : v_(std::move(_v)) {}

    static symbol t(typename Ty::terminal a0) {
      return symbol(T{std::move(a0)});
    }

    static symbol nt(typename Ty::nonterminal a0) {
      return symbol(NT{std::move(a0)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, const typename Ty::terminal &> &&
             std::is_invocable_r_v<T1, F1 &, const typename Ty::nonterminal &>
  static T1 symbol_rect(F0 &&f, F1 &&f0, const symbol &s) {
    if (std::holds_alternative<typename symbol::T>(s.v())) {
      const auto &[a0] = std::get<typename symbol::T>(s.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename symbol::NT>(s.v());
      return f0(a0);
    }
  }

  template <typename T1, typename F0, typename F1>
  static T1 symbol_rec(F0 &&f, F1 &&f0, const symbol &s) {
    return symbol_rect<T1>(f, f0, s);
  }

  static bool symbol_eq_dec(const symbol &s1, const symbol &s2) {
    if (std::holds_alternative<typename symbol::T>(s1.v())) {
      const auto &[a0] = std::get<typename symbol::T>(s1.v());
      if (std::holds_alternative<typename symbol::T>(s2.v())) {
        const auto &[a00] = std::get<typename symbol::T>(s2.v());
        if (Ty::t_eq_dec(a0, a00)) {
          return true;
        } else {
          return false;
        }
      } else {
        return false;
      }
    } else {
      const auto &[a0] = std::get<typename symbol::NT>(s1.v());
      if (std::holds_alternative<typename symbol::T>(s2.v())) {
        return false;
      } else {
        const auto &[a00] = std::get<typename symbol::NT>(s2.v());
        if (Ty::nt_eq_dec(a0, a00)) {
          return true;
        } else {
          return false;
        }
      }
    }
  }

  using symbol_semty = crane::obj;
  using tuple = crane::obj;
  using production = std::pair<typename Ty::nonterminal, List<symbol>>;
  using symbols_semty = tuple;
  using predicate_semty = crane::obj;
  using action_semty = crane::obj;
  using production_semty = std::pair<predicate_semty, action_semty>;
  using grammar_entry = SigT<production, production_semty>;
  using grammar = List<grammar_entry>;
  using sem_val = SigT<symbol, symbol_semty>;

  static std::optional<symbols_semty>
  assemble(const List<symbol> &ys, const List<SigT<symbol, crane::obj>> &stk) {
    if (std::holds_alternative<typename List<symbol>::Nil>(ys.v())) {
      return std::make_optional<symbols_semty>(std::monostate{});
    } else {
      const auto &[a0, a1] = std::get<typename List<symbol>::Cons>(ys.v());
      if (std::holds_alternative<typename List<SigT<symbol, crane::obj>>::Nil>(
              stk.v())) {
        return std::optional<symbols_semty>();
      } else {
        const auto &[a00, a10] =
            std::get<typename List<SigT<symbol, crane::obj>>::Cons>(stk.v());
        const auto &[x1, a11] = a00;
        if (symbol_eq_dec(crane::any_cast<symbol>(x1), a0)) {
          auto _cs = assemble(*a1, *a10);
          if (_cs.has_value()) {
            const auto &rest = *_cs;
            return std::make_optional<symbols_semty>(
                std::make_pair(crane::obj(a11), crane::obj(rest)));
          } else {
            return std::optional<symbols_semty>();
          }
        } else {
          return std::optional<symbols_semty>();
        }
      }
    }
  }

  static crane::obj
  action_of(const SigT<std::pair<typename Ty::nonterminal, List<symbol>>,
                       std::pair<crane::obj, crane::obj>> &e,
            symbols_semty x0_) {
    const auto &[x0, a1] = e;
    auto [_, _] = x0;
    const auto &[_, a] = a1;
    auto act = crane_any_cast<crane::fn<crane::obj(symbols_semty)>>(a);
    return crane_call_erased(act, std::move(x0_));
  }

  static std::optional<crane::obj>
  run_entry(const SigT<std::pair<typename Ty::nonterminal, List<symbol>>,
                       std::pair<crane::obj, crane::obj>> &e,
            const List<SigT<symbol, crane::obj>> &stk) {
    auto _cs = assemble(e.projT1().second, stk);
    if (_cs.has_value()) {
      const auto &vs = *_cs;
      return std::make_optional<crane::obj>(crane::obj(action_of(e, vs)));
    } else {
      return std::optional<crane::obj>();
    }
  }
};

struct Val {
  // TYPES
  struct VN {
    uint64_t a0;
  };

  struct VL {
    std::shared_ptr<List<Val>> a0;
  };

  using variant_t = std::variant<VN, VL>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Val() {}

  explicit Val(VN _v) : v_(std::move(_v)) {}

  explicit Val(VL _v) : v_(std::move(_v)) {}

  static Val vn(uint64_t a0) { return Val(VN{a0}); }

  static Val vl(List<Val> a0);
  // MANIPULATORS
  ~Val();
  Val(const Val &) = default;
  Val &operator=(const Val &) = default;
  Val(Val &&) = default;
  Val &operator=(Val &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct MySym {
  enum class Term { LBRACE, RBRACE };

  template <typename T1> static T1 term_rect(T1 f, T1 f0, Term t) {
    switch (t) {
    case Term::LBRACE: {
      return f;
    }
    case Term::RBRACE: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 term_rec(T1 f, T1 f0, Term t) {
    return term_rect<T1>(std::move(f), std::move(f0), t);
  }

  enum class Nt { ELEM, LST };

  template <typename T1> static T1 nt_rect(T1 f, T1 f0, Nt n) {
    switch (n) {
    case Nt::ELEM: {
      return f;
    }
    case Nt::LST: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 nt_rec(T1 f, T1 f0, Nt n) {
    return nt_rect<T1>(std::move(f), std::move(f0), n);
  }

  using terminal = Term;
  using nonterminal = Nt;
  static bool t_eq_dec(Term x, Term y);
  static bool nt_eq_dec(Nt x, Nt y);
  using t_semty = std::monostate;
  using nt_semty = crane::obj;
};

using MyDefs = DefsFn<MySym>;
const MyDefs::grammar entries =
    List<SigT<std::pair<MySym::Nt, List<MyDefs::symbol>>,
              std::pair<crane::obj, crane::obj>>>::cons(
        SigT<std::pair<MySym::Nt, List<MyDefs::symbol>>,
             std::pair<crane::obj, crane::obj>>::existt(
            std::make_pair(
                MySym::Nt::LST, List<MyDefs::symbol>::cons(
                                    MyDefs::symbol::t(MySym::Term::LBRACE),
                                    List<MyDefs::symbol>::cons(
                                        MyDefs::symbol::nt(MySym::Nt::ELEM),
                                        List<MyDefs::symbol>::cons(
                                            MyDefs::symbol::nt(MySym::Nt::LST),
                                            List<MyDefs::symbol>::cons(
                                                MyDefs::symbol::t(
                                                    MySym::Term::RBRACE),
                                                List<MyDefs::symbol>::nil()))))),
            std::make_pair(
                crane::obj(crane_erase_fn([](const auto &) { return true; })),
                crane::obj(crane_erase_fn([](const auto &tup) {
                  const auto &[_, y0] =
                      crane::any_cast<std::pair<crane::obj, crane::obj>>(tup);
                  const auto &[pr, y1] =
                      crane::any_cast<std::pair<crane::obj, crane::obj>>(y0);
                  const auto &[prs, y2] =
                      crane::any_cast<std::pair<crane::obj, crane::obj>>(y1);
                  const auto &[_, _] =
                      crane::any_cast<std::pair<crane::obj, crane::obj>>(y2);
                  return List<std::pair<uint64_t, Val>>::cons(
                      crane_any_cast<std::pair<uint64_t, Val>>(pr),
                      crane::any_cast<List<crane::obj>>(prs));
                })))),
        List<SigT<std::pair<MySym::Nt, List<MyDefs::symbol>>,
                  std::pair<crane::obj, crane::obj>>>::nil());

inline Val Val::vl(List<Val> a0) {
  return Val(VL{std::make_shared<List<Val>>(std::move(a0))});
}

inline Val::~Val() {
  // Release the children this node alone owns in a loop, not recursively, so a
  // deep value cannot overflow the stack.
  if (std::holds_alternative<VN>(v_mut())) {
    return;
  }
  crane::small_vector<std::shared_ptr<Val>> _stack = {};
  auto _drain = [&](variant_t &_v) {
    if (auto *_alt = std::get_if<VL>(&_v)) {
      if (_alt->a0 && _alt->a0.use_count() == 1) {
        std::atomic_thread_fence(std::memory_order_acquire);
        auto _lp = _alt->a0.get();
        while (std::holds_alternative<typename List<Val>::Cons>(_lp->v())) {
          auto &_lc = std::get<typename List<Val>::Cons>(_lp->v_mut());
          _stack.push_back(std::make_shared<Val>(std::move(_lc.a)));
          if (_lc.l && _lc.l.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            _lp = _lc.l.get();
          } else {
            break;
          }
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
