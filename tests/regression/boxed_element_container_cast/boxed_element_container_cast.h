#ifndef INCLUDED_BOXED_ELEMENT_CONTAINER_CAST
#define INCLUDED_BOXED_ELEMENT_CONTAINER_CAST

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <conslist.h>
#include <cstdint>
#include <functional>
#include <stdexcept>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A, typename P> struct SigT;

struct Datatypes {
  template <typename T1> static uint64_t length(const crane::list<T1> &l);
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
};

struct ListDef {
  template <typename T1, typename T2, typename F0>
  static crane::list<T2> map(F0 &&f, const crane::list<T1> &l);
};

/// A container cast into a callee generic over the element, over a list
/// mapped with a Boxed Element wrapper.
///
/// val recurses through list, so list (string * val) is
/// crane::list<crane::box<std::pair<std::string, Val>>> wherever it is
/// written.  The predicate below hands an erased list (string * val) to
/// nodupKeys, a function template over list (string * A) whose own
/// declaration never boxes its element (a bare type variable never recurses).
/// The cast that recovers the argument must therefore name the element
/// unboxed, as the declaration does, or template argument deduction fails;
/// the action hands the same leaf to VAssoc's concrete factory, whose cast
/// keeps the box.  run_entry and action_size run both.
struct BoxedElementContainerCast {
  using tuple = crane::obj;

  struct val {
    // TYPES
    struct VAssoc {
      crane::list<crane::box<std::pair<std::string, val>>> a0;
    };

    struct VList {
      crane::list<crane::box<val>> a0;
    };

    struct VNull {};

    struct VStr {
      std::string a0;
    };

    using variant_t = std::variant<VAssoc, VList, VNull, VStr>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    val() {}

    explicit val(VAssoc _v) : v_(std::move(_v)) {}

    explicit val(VList _v) : v_(std::move(_v)) {}

    explicit val(VNull _v) : v_(_v) {}

    explicit val(VStr _v) : v_(std::move(_v)) {}

    static val vassoc(crane::list<crane::box<std::pair<std::string, val>>> a0) {
      return val(VAssoc{std::move(a0)});
    }

    static val vlist(crane::list<crane::box<val>> a0) {
      return val(VList{std::move(a0)});
    }

    static val vnull() { return val(VNull{}); }

    static val vstr(std::string a0) { return val(VStr{std::move(a0)}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F0, typename F1, typename F3>
    T1 val_rec(F0 &&f, F1 &&f0, T1 f1, F3 &&f2) const {
      return this->template val_rect<T1>(f, f0, std::move(f1), f2);
    }

    template <typename T1, typename F0, typename F1, typename F3>
      requires std::is_invocable_r_v<
                   T1, F0 &,
                   const crane::list<crane::box<std::pair<std::string, val>>>
                       &> &&
               std::is_invocable_r_v<T1, F1 &,
                                     const crane::list<crane::box<val>> &> &&
               std::is_invocable_r_v<T1, F3 &, const std::string &>
    T1 val_rect(F0 &&f, F1 &&f0, T1 f1, F3 &&f2) const {
      if (std::holds_alternative<typename val::VAssoc>(this->v())) {
        const auto &[a0] = std::get<typename val::VAssoc>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename val::VList>(this->v())) {
        const auto &[a0] = std::get<typename val::VList>(this->v());
        return f0(a0);
      } else if (std::holds_alternative<typename val::VNull>(this->v())) {
        return f1;
      } else {
        const auto &[a0] = std::get<typename val::VStr>(this->v());
        return f2(a0);
      }
    }
  };

  template <typename T1>
  static bool nodupKeys(const crane::list<std::pair<std::string, T1>> &prs) {
    if (prs.empty()) {
      return true;
    } else {
      const std::pair<std::string, T1> &_x = prs.front();
      auto _x0 = prs.tail();
      return false;
    }
  }

  template <typename T1> static T1 terminal_rect(T1 f) { return f; }

  template <typename T1> static T1 terminal_rec(T1 f) {
    return terminal_rect<T1>(std::move(f));
  }
  enum class Nonterminal { VALUE, OBJ };

  template <typename T1>
  static T1 nonterminal_rect(T1 f, T1 f0, Nonterminal n) {
    switch (n) {
    case Nonterminal::VALUE: {
      return f;
    }
    case Nonterminal::OBJ: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 nonterminal_rec(T1 f, T1 f0, Nonterminal n) {
    return nonterminal_rect<T1>(std::move(f), std::move(f0), n);
  }

  using t_semty = crane::obj;
  using nt_semty = crane::obj;

  struct symbol {
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
    symbol() {}

    explicit symbol(T _v) : v_(_v) {}

    explicit symbol(NT _v) : v_(std::move(_v)) {}

    static symbol t() { return symbol(T{}); }

    static symbol nt(Nonterminal a0) { return symbol(NT{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F1>
    T1 symbol_rec(const T1 &f, F1 &&f0) const {
      return this->template symbol_rect<T1>(f, f0);
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, const Nonterminal &>
    T1 symbol_rect(const T1 &f, F1 &&f0) const {
      if (std::holds_alternative<typename symbol::T>(this->v())) {
        return f;
      } else {
        const auto &[a0] = std::get<typename symbol::NT>(this->v());
        return f0(a0);
      }
    }
  };

  using symbol_semty = crane::obj;
  using symbols_semty = tuple;
  using production = std::pair<Nonterminal, crane::list<symbol>>;
  using predicate_semty = crane::obj;
  using action_semty = crane::obj;
  using production_semty = std::pair<predicate_semty, action_semty>;
  using grammar_entry = SigT<production, production_semty>;
  static inline const crane::list<grammar_entry> entries = crane::cons(
      SigT<std::pair<Nonterminal, crane::list<symbol>>,
           std::pair<crane::obj, crane::obj>>::
          existt(
              std::make_pair(Nonterminal::VALUE,
                             crane::cons(symbol::nt(Nonterminal::OBJ),
                                         crane::list<symbol>{})),
              std::make_pair(
                  crane::obj(crane_erase_fn([](const auto &tup) {
                    const auto &[prs, _x] =
                        crane::any_cast<std::pair<crane::obj, crane::obj>>(tup);
                    return nodupKeys<val>(
                        crane_container_cast<
                            crane::list<std::pair<std::string, val>>>(
                            crane::any_cast<crane::list<crane::obj>>(prs)));
                  })),
                  crane::obj(crane_erase_fn([](const auto &tup) {
                    const auto &[prs, _x] =
                        crane::any_cast<std::pair<crane::obj, crane::obj>>(tup);
                    return val::vassoc(
                        crane_container_cast<crane::list<
                            crane::box<std::pair<std::string, val>>>>(
                            crane::any_cast<crane::list<crane::obj>>(prs)));
                  })))),
      crane::cons(
          SigT<std::pair<Nonterminal, crane::list<symbol>>,
               std::pair<crane::obj, crane::obj>>::
              existt(
                  std::make_pair(
                      Nonterminal::VALUE,
                      crane::cons(symbol::t(), crane::list<symbol>{})),
                  std::make_pair(
                      crane::obj(
                          crane_erase_fn([](const auto &) { return true; })),
                      crane::obj(crane_erase_fn([](const auto &tup) {
                        const auto &[s, _x] =
                            crane::any_cast<std::pair<crane::obj, crane::obj>>(
                                tup);
                        return val::vstr(crane::any_cast<std::string>(s));
                      })))),
          crane::list<SigT<std::pair<Nonterminal, crane::list<symbol>>,
                           std::pair<crane::obj, crane::obj>>>{}));
  static inline const t_semty sample_t = []() {
    return std::string(
               1, (static_cast<char>((true ? 1 : 0) | (true ? 2 : 0) |
                                     (false ? 4 : 0) | (false ? 8 : 0) |
                                     (true ? 16 : 0) | (true ? 32 : 0) |
                                     (true ? 64 : 0) | (false ? 128 : 0)))) +
           std::string();
  }();
  static nt_semty sample_nt(Nonterminal x);
  static symbol_semty sample_symbol(const symbol &s);
  static symbols_semty sample_symbols(const crane::list<symbol> &ys);
  static bool run_entry(const SigT<std::pair<Nonterminal, crane::list<symbol>>,
                                   std::pair<crane::obj, crane::obj>> &e);
  static uint64_t size_of(Nonterminal x, nt_semty v);
  static uint64_t
  action_size(const SigT<std::pair<Nonterminal, crane::list<symbol>>,
                         std::pair<crane::obj, crane::obj>> &e);
  static inline const crane::list<bool> predicates =
      ListDef::template map<grammar_entry, bool>(run_entry, entries);
  static inline const crane::list<uint64_t> action_sizes =
      ListDef::template map<grammar_entry, uint64_t>(action_size, entries);
};

template <typename T1> uint64_t Datatypes::length(const crane::list<T1> &l) {
  if (l.empty()) {
    return UINT64_C(0);
  } else {
    const T1 &_x = l.front();
    auto l_ = l.tail();
    return (Datatypes::template length<T1>(l_) + 1);
  }
}

template <typename T1, typename T2, typename F0>
crane::list<T2> ListDef::map(F0 &&f, const crane::list<T1> &l) {
  if (l.empty()) {
    return crane::list<T2>{};
  } else {
    const T1 &a = l.front();
    auto l0 = l.tail();
    return crane::cons(f(a), ListDef::template map<T1, T2>(f, l0));
  }
}

#endif // INCLUDED_BOXED_ELEMENT_CONTAINER_CAST
