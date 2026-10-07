#ifndef INCLUDED_SHARED_VARIANT_NESTED
#define INCLUDED_SHARED_VARIANT_NESTED

#include "crane_fn.h"
#include "crane_variant.h"
#include "obj.h"
#include "shared_variant.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>

template <typename A> struct List;

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

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &&, const A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    const List<A> *_loop_self = this;
    T1 _loop_a0 = std::move(a0);
    while (true) {
      auto &&_sv = *_loop_self;
      if (crane::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        return _loop_a0;
      } else {
        const auto &[a1, a2] = crane::get<typename List<A>::Cons>(_sv.v());
        _loop_self = crane_raw(a2);
        _loop_a0 = f(std::move(_loop_a0), a1);
      }
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const A &>
  List<T1> map(F0 &&f) const {
    std::optional<List<T1>> _root{};
    crane::shared_box<List<T1>> *_write = nullptr;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (crane::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = List<T1>::nil();
        (_write
             ? *(*_write = crane::shared_box<List<T1>>::make(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = crane::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<T1>::Cons(f(a0), nullptr);
        List<T1> &_node =
            (_write ? *(*_write =
                            crane::shared_box<List<T1>>::make(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &crane::get<typename List<T1>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

struct SharedVariantNested {
  struct rose {
    // TYPES
    struct RNode {
      uint64_t a0;
      crane::shared_box<List<rose>> a1;
    };

    using variant_t = crane::shared_variant<RNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    rose() {}

    explicit rose(RNode _v) : v_(std::move(_v)) {}

    static rose rnode(uint64_t a0, List<rose> a1) {
      return rose(
          RNode{a0, crane::shared_box<List<rose>>::make(std::move(a1))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    rose rbump() const {
      const auto &[a0, a1] = crane::get<typename rose::RNode>(this->v());
      return rose::rnode((a0 + 1), a1->template map<rose>([](const rose &_x) {
        return _x.rbump();
      }));
    }

    uint64_t rsum() const {
      const rose *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const rose *_self;
      };

      using CraneFrame = std::variant<CraneEnter>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified rsum: CraneEnter.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        auto _f = std::move(crane::get<CraneEnter>(_frame));
        const rose *_self = _f._self;
        auto &&_sv = *_self;
        const auto &[a0, a1] = crane::get<typename rose::RNode>(_sv.v());
        const List<rose> &a1_value = *a1;
        _result = (a0 + a1_value.template fold_left<uint64_t>(
                            [](uint64_t acc, const rose &t0) {
                              return (acc + t0.rsum());
                            },
                            UINT64_C(0)));
      }
      return _result;
    }

    template <typename T1, typename F0> T1 rose_rec(F0 &&f) const {
      return this->template rose_rect<T1>(f);
    }

    template <typename T1, typename F0> T1 rose_rect(F0 &&f) const {
      const auto &[a0, a1] = crane::get<typename rose::RNode>(this->v());
      return f(a0, *a1);
    }
  };

  static inline const rose r0 = rose::rnode(
      UINT64_C(1),
      List<rose>::cons(
          rose::rnode(UINT64_C(2), List<rose>::nil()),
          List<rose>::cons(
              rose::rnode(
                  UINT64_C(3),
                  List<rose>::cons(rose::rnode(UINT64_C(4), List<rose>::nil()),
                                   List<rose>::nil())),
              List<rose>::nil())));
  static inline const rose r1 = r0.rbump();

  struct chain {
    // TYPES
    struct Link {
      uint64_t a0;
      std::shared_ptr<std::optional<chain>> a1;
    };

    using variant_t = crane::shared_variant<Link>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    chain() {}

    explicit chain(Link _v) : v_(std::move(_v)) {}

    static chain link(uint64_t a0, std::optional<chain> a1) {
      return chain(
          Link{a0, std::make_shared<std::optional<chain>>(std::move(a1))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t clen() const {
      const chain *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const chain *_self;
      };

      /// CraneCont_c_: resumes after recursive call, then processes rest.
      struct CraneCont_c_ {};

      using CraneFrame = std::variant<CraneEnter, CraneCont_c_>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified clen: CraneEnter -> CraneCont_c_.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (crane::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(crane::get<CraneEnter>(_frame));
          const chain *_self = _f._self;
          auto &&_sv = *_self;
          const auto &[a0, a1] = crane::get<typename chain::Link>(_sv.v());
          if ((*a1).has_value()) {
            const chain &c_ = *(*a1);
            _stack.emplace_back(CraneCont_c_{});
            _stack.emplace_back(CraneEnter{&c_});
          } else {
            _result = UINT64_C(1);
          }
        } else {
          auto _f = std::move(crane::get<CraneCont_c_>(_frame));
          _result = (std::move(_result) + 1);
        }
      }
      return _result;
    }

    template <typename T1, typename F0> T1 chain_rec(F0 &&f) const {
      return this->template chain_rect<T1>(f);
    }

    template <typename T1, typename F0> T1 chain_rect(F0 &&f) const {
      const auto &[a0, a1] = crane::get<typename chain::Link>(this->v());
      return f(a0, *a1);
    }
  };

  static inline const chain c0 =
      chain::link(UINT64_C(1),
                  std::make_optional<chain>(chain::link(
                      UINT64_C(2), std::make_optional<chain>(chain::link(
                                       UINT64_C(3), std::optional<chain>())))));
  struct stmt;
  struct expr;

  struct stmt {
    // TYPES
    struct Assign {
      uint64_t a0;
      crane::shared_box<expr> a1;
    };

    struct Seq {
      crane::shared_box<stmt> a0;
      crane::shared_box<stmt> a1;
    };

    struct Skip {};

    using variant_t = crane::shared_variant<Assign, Seq, Skip>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    stmt() {}

    explicit stmt(Assign _v) : v_(std::move(_v)) {}

    explicit stmt(Seq _v) : v_(std::move(_v)) {}

    explicit stmt(Skip _v) : v_(_v) {}

    static stmt assign(uint64_t a0, expr a1) {
      return stmt(Assign{a0, crane::shared_box<expr>::make(std::move(a1))});
    }

    static stmt seq(stmt a0, stmt a1) {
      return stmt(Seq{crane::shared_box<stmt>::make(std::move(a0)),
                      crane::shared_box<stmt>::make(std::move(a1))});
    }

    static stmt skip() { return stmt(Skip{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  struct expr {
    // TYPES
    struct Num {
      uint64_t a0;
    };

    struct Add {
      crane::shared_box<expr> a0;
      crane::shared_box<expr> a1;
    };

    struct Block {
      crane::shared_box<stmt> a0;
      crane::shared_box<expr> a1;
    };

    using variant_t = crane::shared_variant<Num, Add, Block>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    expr() {}

    explicit expr(Num _v) : v_(std::move(_v)) {}

    explicit expr(Add _v) : v_(std::move(_v)) {}

    explicit expr(Block _v) : v_(std::move(_v)) {}

    static expr num(uint64_t a0) { return expr(Num{a0}); }

    static expr add(expr a0, expr a1) {
      return expr(Add{crane::shared_box<expr>::make(std::move(a0)),
                      crane::shared_box<expr>::make(std::move(a1))});
    }

    static expr block(stmt a0, expr a1) {
      return expr(Block{crane::shared_box<stmt>::make(std::move(a0)),
                        crane::shared_box<expr>::make(std::move(a1))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
  static T1 stmt_rect(F0 &&f, F1 &&f0, T1 f1, const stmt &s) {
    if (crane::holds_alternative<typename stmt::Assign>(s.v())) {
      const auto &[a0, a1] = crane::get<typename stmt::Assign>(s.v());
      return f(a0, *a1);
    } else if (crane::holds_alternative<typename stmt::Seq>(s.v())) {
      const auto &[a0, a1] = crane::get<typename stmt::Seq>(s.v());
      return f0(*a0, stmt_rect<T1>(f, f0, f1, *a0), *a1,
                stmt_rect<T1>(f, f0, f1, *a1));
    } else {
      return f1;
    }
  }

  template <typename T1, typename F0, typename F1>
  static T1 stmt_rec(F0 &&f, F1 &&f0, T1 f1, const stmt &s) {
    return stmt_rect<T1>(f, f0, std::move(f1), s);
  }

  template <typename T1, typename F0, typename F1, typename F2>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
  static T1 expr_rect(F0 &&f, F1 &&f0, F2 &&f1, const expr &e) {
    if (crane::holds_alternative<typename expr::Num>(e.v())) {
      const auto &[a0] = crane::get<typename expr::Num>(e.v());
      return f(a0);
    } else if (crane::holds_alternative<typename expr::Add>(e.v())) {
      const auto &[a0, a1] = crane::get<typename expr::Add>(e.v());
      return f0(*a0, expr_rect<T1>(f, f0, f1, *a0), *a1,
                expr_rect<T1>(f, f0, f1, *a1));
    } else {
      const auto &[a0, a1] = crane::get<typename expr::Block>(e.v());
      return f1(*a0, *a1, expr_rect<T1>(f, f0, f1, *a1));
    }
  }

  template <typename T1, typename F0, typename F1, typename F2>
  static T1 expr_rec(F0 &&f, F1 &&f0, F2 &&f1, const expr &e) {
    return expr_rect<T1>(f, f0, f1, e);
  }

  static uint64_t ssize(const stmt &s);
  static uint64_t esize(const expr &e);
  static inline const stmt s0 = stmt::seq(
      stmt::assign(UINT64_C(1), expr::add(expr::num(UINT64_C(2)),
                                          expr::block(stmt::skip(),
                                                      expr::num(UINT64_C(3))))),
      stmt::skip());

  /// Not recursive, but large: a value is one word all the same.
  struct shape {
    // TYPES
    struct Point {};

    struct Box3 {
      uint64_t a0;
      uint64_t a1;
      uint64_t a2;
    };

    using variant_t = crane::shared_variant<Point, Box3>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    shape() {}

    explicit shape(Point _v) : v_(_v) {}

    explicit shape(Box3 _v) : v_(std::move(_v)) {}

    static shape point() { return shape(Point{}); }

    static shape box3(uint64_t a0, uint64_t a1, uint64_t a2) {
      return shape(Box3{a0, a1, a2});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t volume() const {
      if (crane::holds_alternative<typename shape::Point>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] = crane::get<typename shape::Box3>(this->v());
        return ((a0 * a1) * a2);
      }
    }

    template <typename T1, typename F1> T1 shape_rec(T1 f, F1 &&f0) const {
      return this->template shape_rect<T1>(std::move(f), f0);
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, const uint64_t &,
                                     const uint64_t &, const uint64_t &>
    T1 shape_rect(T1 f, F1 &&f0) const {
      if (crane::holds_alternative<typename shape::Point>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2] = crane::get<typename shape::Box3>(this->v());
        return f0(a0, a1, a2);
      }
    }
  };

  static inline const List<shape> shapes = List<shape>::cons(
      shape::box3(UINT64_C(2), UINT64_C(3), UINT64_C(4)),
      List<shape>::cons(
          shape::point(),
          List<shape>::cons(shape::box3(UINT64_C(1), UINT64_C(1), UINT64_C(1)),
                            List<shape>::nil())));

  static inline const uint64_t result =
      ((((r0.rsum() + r1.rsum()) + c0.clen()) + ssize(s0)) +
       shapes.template fold_left<uint64_t>(
           [](uint64_t n, const shape &s) { return (n + s.volume()); },
           UINT64_C(0)));
};

#endif // INCLUDED_SHARED_VARIANT_NESTED
