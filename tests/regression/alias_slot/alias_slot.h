#ifndef INCLUDED_ALIAS_SLOT
#define INCLUDED_ALIAS_SLOT

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
          if (crane::holds_alternative<typename List<CraneU>::Nil>(
                  _other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                crane::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{[&]() -> A {
                          if constexpr (crane_convertible<A, const CraneU &>) {
                            return crane_convert<A>(a);
                          } else {
                            throw std::logic_error(
                                "unreachable: inactive constructor field at "
                                "this instantiation");
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
      if (crane::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(crane::get<CraneEnter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (crane::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = crane::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(CraneCont_Cons{});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(crane::get<CraneCont_Cons>(_frame));
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
  static T1 expr_rect(F0 &&f, F1 &&f0,
                      const expr &e) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

    struct CraneEnter {
      const expr *e;
    };

    /// CraneCont_EAdd: saves [a0, b0], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_EAdd {
      crane::shared_box<expr> a0;
      const expr *b0;
    };

    /// CraneCont_EAdd_1: saves [a0, b0, _tmp2], resumes after recursive call,
    /// then processes rest.
    struct CraneCont_EAdd_1 {
      crane::shared_box<expr> a0;
      const expr *b0;
      T1 _tmp2;
    };

    using CraneFrame =
        std::variant<CraneEnter, CraneCont_EAdd, CraneCont_EAdd_1>;
    T1 _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&e});
    /// Loopified expr_rect: CraneEnter -> CraneCont_EAdd -> CraneCont_EAdd_1.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (crane::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(crane::get<CraneEnter>(_frame));
        const expr &e = *_f.e;
        if (crane::holds_alternative<typename expr::ELit>(e.v())) {
          const auto &[s0] = crane::get<typename expr::ELit>(e.v());
          _result = f(s0);
        } else {
          const auto &[a0, b0] = crane::get<typename expr::EAdd>(e.v());
          _stack.emplace_back(CraneCont_EAdd{a0, crane_raw(b0)});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        }
      } else if (crane::holds_alternative<CraneCont_EAdd>(_frame)) {
        auto _f = std::move(crane::get<CraneCont_EAdd>(_frame));
        crane::shared_box<expr> a0 = std::move(_f.a0);
        const expr &b0 = *_f.b0;
        _stack.emplace_back(
            CraneCont_EAdd_1{std::move(a0), &b0, std::move(_result)});
        _stack.emplace_back(CraneEnter{&b0});
      } else {
        auto _f = std::move(crane::get<CraneCont_EAdd_1>(_frame));
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
          List<String>::cons(
              String::string0(
                  Ascii::ascii0(true, false, true, false, false, true, true,
                                false),
                  String::string0(
                      Ascii::ascii0(false, true, true, true, false, true, true,
                                    false),
                      String::string0(Ascii::ascii0(false, false, true, false,
                                                    false, true, true, false),
                                      String::emptystring()))),
              List<String>::nil()))
          .length();
};

#endif // INCLUDED_ALIAS_SLOT
