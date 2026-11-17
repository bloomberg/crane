#pragma once

#include "crane_fn.h"
#include "crane_variant.h"
#include "obj.h"
#include "shared_block.h"
#include "shared_variant.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>

template <typename A> struct List;
struct Ascii;
struct String;

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    crane::shared_box<List<A>> l;
  };

  using variant_t = crane::shared_variant<Nil, Cons>;

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
          if (crane::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                crane::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? crane::shared_box<List<A>>::make(
                         crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(
        Cons{std::move(a), crane::shared_box<List<A>>::make(std::move(l))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  uint64_t length() const {
    const List<A> *_self = this;

    // Explicit stack replaces the non-tail recursion of length: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const List<A> *_self;
    };

    struct _after_length_in_Cons {};

    using _frame = std::variant<_call, _after_length_in_Cons>;
    uint64_t _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{_self});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (crane::holds_alternative<_call>(_popped)) {
        auto _f = std::move(crane::get<_call>(_popped));
        _stack.pop_back();
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (crane::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[_, a1] = crane::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_after_length_in_Cons{});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(crane::get<_after_length_in_Cons>(_popped));
        _stack.pop_back();
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }
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
    crane::shared_box<String> a1;
  };

  using variant_t = crane::shared_variant<EmptyString, String0>;

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
        String0{std::move(a0), crane::shared_box<String>::make(std::move(a1))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct AliasSlot {
  using parts = List<String>;

  struct expr {
    // TYPES
    struct ELit {
      String s;
    };

    struct EAdd {
      crane::shared_box<expr> a;
      crane::shared_box<expr> b;
    };

    using variant_t = crane::shared_variant<ELit, EAdd>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    expr() {}

    explicit expr(ELit _v) : v_(std::move(_v)) {}

    explicit expr(EAdd _v) : v_(std::move(_v)) {}

    static expr elit(String s) { return expr(ELit{std::move(s)}); }

    static expr eadd(expr a, expr b) {
      return expr(EAdd{crane::shared_box<expr>::make(std::move(a)),
                       crane::shared_box<expr>::make(std::move(b))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, const String &>
  static T1 expr_rect(F0 &&f, F1 &&f0, const expr &e) {
    // Explicit stack replaces the non-tail recursion of expr_rect: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const expr *e;
    };

    struct _after_expr_rect_in_EAdd {
      crane::shared_box<expr> a0;
      const expr *b0;
    };

    struct _after_expr_rect_in_EAdd_2 {
      crane::shared_box<expr> a0;
      const expr *b0;
      T1 _tmp2;
    };

    using _frame = std::variant<_call, _after_expr_rect_in_EAdd,
                                _after_expr_rect_in_EAdd_2>;
    T1 _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&e});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (crane::holds_alternative<_call>(_popped)) {
        auto _f = std::move(crane::get<_call>(_popped));
        _stack.pop_back();
        const expr &e = *_f.e;
        if (crane::holds_alternative<typename expr::ELit>(e.v())) {
          const auto &[s0] = crane::get<typename expr::ELit>(e.v());
          _result = f(s0);
        } else {
          const auto &[a0, b0] = crane::get<typename expr::EAdd>(e.v());
          _stack.emplace_back(_after_expr_rect_in_EAdd{a0, crane_raw(b0)});
          _stack.emplace_back(_call{crane_raw(a0)});
        }
      } else if (crane::holds_alternative<_after_expr_rect_in_EAdd>(_popped)) {
        auto _f = std::move(crane::get<_after_expr_rect_in_EAdd>(_popped));
        _stack.pop_back();
        crane::shared_box<expr> a0 = std::move(_f.a0);
        const expr &b0 = *_f.b0;
        _stack.emplace_back(
            _after_expr_rect_in_EAdd_2{std::move(a0), &b0, std::move(_result)});
        _stack.emplace_back(_call{&b0});
      } else {
        auto _f = std::move(crane::get<_after_expr_rect_in_EAdd_2>(_popped));
        _stack.pop_back();
        crane::shared_box<expr> a0 = std::move(_f.a0);
        const expr &b0 = *_f.b0;
        _result = f0(*a0, std::move(_f._tmp2), b0, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F0, typename F1>
  static T1 expr_rec(F0 &&f, F1 &&f0, const expr &e) {
    return expr_rect<T1>(f, f0, e);
  }

  static parts expr_parts(const expr &e, const List<String> &k);
  /// Each of xs with a comma after it, then k: a loop that fills the
  /// tail of the cell before, a cell whose type is the alias.
  static parts comma_parts(const List<String> &xs, List<String> k);

  struct line {
    uint64_t l_indent;
    parts l_text;
  };

  static line line_of(const expr &e);
  static uint64_t count(const expr &e);
  static inline const uint64_t sample = count(expr::eadd(
      expr::eadd(
          expr::elit(String::string0(Ascii::ascii0(true, false, false, false,
                                                   false, true, true, false),
                                     String::emptystring())),
          expr::elit(String::string0(Ascii::ascii0(false, true, false, false,
                                                   false, true, true, false),
                                     String::emptystring()))),
      expr::elit(String::string0(
          Ascii::ascii0(true, true, false, false, false, true, true, false),
          String::emptystring()))));
  static inline const uint64_t commas =
      comma_parts(
          List<String>::cons(
              String::string0(Ascii::ascii0(true, false, false, false, false,
                                            true, true, false),
                              String::emptystring()),
              List<String>::cons(
                  String::string0(Ascii::ascii0(false, true, false, false,
                                                false, true, true, false),
                                  String::emptystring()),
                  List<String>::cons(
                      String::string0(Ascii::ascii0(true, true, false, false,
                                                    false, true, true, false),
                                      String::emptystring()),
                      List<String>::nil()))),
          List<String>::cons(String::string0(
              Ascii::ascii0(true, false, true, false, false, true, true, false),
              String::string0(
                  Ascii::ascii0(false, true, true, true, false, true, true,
                                false),
                  String::string0(Ascii::ascii0(false, false, true, false,
                                                false, true, true, false),
                                  String::emptystring()))),
                             List<String>::nil()))
          .length();
};
