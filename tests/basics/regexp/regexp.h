#ifndef INCLUDED_REGEXP
#define INCLUDED_REGEXP

#include <cstdint>
#include <memory>
#include <type_traits>
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

  List(const List<A> &_other) : v_(std::move(_other.clone().v_)) {}

  List(List<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  List<A> clone() const {
    List<A> _out{};

    struct _CloneFrame {
      const List<A> *_src;
      List<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<A> *_src = _frame._src;
      List<A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->v_ = Cons{_alt.a, _alt.l ? std::make_shared<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.l) {
          _stack.push_back({_alt.l.get(), _dst_alt.l.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a), l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.l) {
          _stack.push_back(std::move(_alt.l));
        }
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node) {
        _drain(*_node);
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Matcher {
  static bool char_eq(int64_t x, int64_t y);

  /// Regular expression abstract syntax
  struct regexp {
    // TYPES
    struct Any {};

    struct Char {
      int64_t c;
    };

    struct Eps {};

    struct Cat {
      std::shared_ptr<regexp> r1;
      std::shared_ptr<regexp> r2;
    };

    struct Alt {
      std::shared_ptr<regexp> r1;
      std::shared_ptr<regexp> r2;
    };

    struct Zero {};

    struct Star {
      std::shared_ptr<regexp> r;
    };

    using variant_t = std::variant<Any, Char, Eps, Cat, Alt, Zero, Star>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    regexp() {}

    explicit regexp(Any _v) : v_(_v) {}

    explicit regexp(Char _v) : v_(std::move(_v)) {}

    explicit regexp(Eps _v) : v_(_v) {}

    explicit regexp(Cat _v) : v_(std::move(_v)) {}

    explicit regexp(Alt _v) : v_(std::move(_v)) {}

    explicit regexp(Zero _v) : v_(_v) {}

    explicit regexp(Star _v) : v_(std::move(_v)) {}

    regexp(const regexp &_other) : v_(std::move(_other.clone().v_)) {}

    regexp(regexp &&_other) noexcept : v_(std::move(_other.v_)) {}

    regexp &operator=(const regexp &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    regexp &operator=(regexp &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    regexp clone() const {
      regexp _out{};

      struct _CloneFrame {
        const regexp *_src;
        regexp *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const regexp *_src = _frame._src;
        regexp *_dst = _frame._dst;
        if (std::holds_alternative<Any>(_src->v())) {
          _dst->v_ = Any{};
        } else if (std::holds_alternative<Char>(_src->v())) {
          const auto &_alt = std::get<Char>(_src->v());
          _dst->v_ = Char{_alt.c};
        } else if (std::holds_alternative<Eps>(_src->v())) {
          _dst->v_ = Eps{};
        } else if (std::holds_alternative<Cat>(_src->v())) {
          const auto &_alt = std::get<Cat>(_src->v());
          _dst->v_ = Cat{_alt.r1 ? std::make_shared<regexp>() : nullptr,
                         _alt.r2 ? std::make_shared<regexp>() : nullptr};
          auto &_dst_alt = std::get<Cat>(_dst->v_);
          if (_alt.r1) {
            _stack.push_back({_alt.r1.get(), _dst_alt.r1.get()});
          }
          if (_alt.r2) {
            _stack.push_back({_alt.r2.get(), _dst_alt.r2.get()});
          }
        } else if (std::holds_alternative<Alt>(_src->v())) {
          const auto &_alt = std::get<Alt>(_src->v());
          _dst->v_ = Alt{_alt.r1 ? std::make_shared<regexp>() : nullptr,
                         _alt.r2 ? std::make_shared<regexp>() : nullptr};
          auto &_dst_alt = std::get<Alt>(_dst->v_);
          if (_alt.r1) {
            _stack.push_back({_alt.r1.get(), _dst_alt.r1.get()});
          }
          if (_alt.r2) {
            _stack.push_back({_alt.r2.get(), _dst_alt.r2.get()});
          }
        } else if (std::holds_alternative<Zero>(_src->v())) {
          _dst->v_ = Zero{};
        } else {
          const auto &_alt = std::get<Star>(_src->v());
          _dst->v_ = Star{_alt.r ? std::make_shared<regexp>() : nullptr};
          auto &_dst_alt = std::get<Star>(_dst->v_);
          if (_alt.r) {
            _stack.push_back({_alt.r.get(), _dst_alt.r.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static regexp any() { return regexp(Any{}); }

    static regexp Char_(int64_t c) { return regexp(Char{c}); }

    static regexp eps() { return regexp(Eps{}); }

    static regexp cat(regexp r1, regexp r2) {
      return regexp(Cat{std::make_shared<regexp>(std::move(r1)),
                        std::make_shared<regexp>(std::move(r2))});
    }

    static regexp alt(regexp r1, regexp r2) {
      return regexp(Alt{std::make_shared<regexp>(std::move(r1)),
                        std::make_shared<regexp>(std::move(r2))});
    }

    static regexp zero() { return regexp(Zero{}); }

    static regexp star(regexp r) {
      return regexp(Star{std::make_shared<regexp>(std::move(r))});
    }

    // MANIPULATORS
    ~regexp() {
      std::vector<std::shared_ptr<regexp>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](regexp &_node) {
        if (std::holds_alternative<Cat>(_node.v_)) {
          auto &_alt = std::get<Cat>(_node.v_);
          if (_alt.r1) {
            _stack.push_back(std::move(_alt.r1));
          }
          if (_alt.r2) {
            _stack.push_back(std::move(_alt.r2));
          }
        }
        if (std::holds_alternative<Alt>(_node.v_)) {
          auto &_alt = std::get<Alt>(_node.v_);
          if (_alt.r1) {
            _stack.push_back(std::move(_alt.r1));
          }
          if (_alt.r2) {
            _stack.push_back(std::move(_alt.r2));
          }
        }
        if (std::holds_alternative<Star>(_node.v_)) {
          auto &_alt = std::get<Star>(_node.v_);
          if (_alt.r) {
            _stack.push_back(std::move(_alt.r));
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1, typename F3, typename F4, typename F6>
    requires std::is_invocable_r_v<T1, F1 &, int64_t &> &&
             std::is_invocable_r_v<T1, F3 &, regexp &, T1 &, regexp &, T1 &> &&
             std::is_invocable_r_v<T1, F4 &, regexp &, T1 &, regexp &, T1 &> &&
             std::is_invocable_r_v<T1, F6 &, regexp &, T1 &>
  static T1 regexp_rect(T1 f, F1 &&f0, T1 f1, F3 &&f2, F4 &&f3, T1 f4, F6 &&f5,
                        const regexp &r) {
    if (std::holds_alternative<typename regexp::Any>(r.v())) {
      return f;
    } else if (std::holds_alternative<typename regexp::Char>(r.v())) {
      const auto &[c0] = std::get<typename regexp::Char>(r.v());
      return f0(c0);
    } else if (std::holds_alternative<typename regexp::Eps>(r.v())) {
      return f1;
    } else if (std::holds_alternative<typename regexp::Cat>(r.v())) {
      const auto &[r4, r5] = std::get<typename regexp::Cat>(r.v());
      return f2(*r4, regexp_rect<T1>(f, f0, f1, f2, f3, f4, f5, *r4), *r5,
                regexp_rect<T1>(f, f0, f1, f2, f3, f4, f5, *r5));
    } else if (std::holds_alternative<typename regexp::Alt>(r.v())) {
      const auto &[r4, r5] = std::get<typename regexp::Alt>(r.v());
      return f3(*r4, regexp_rect<T1>(f, f0, f1, f2, f3, f4, f5, *r4), *r5,
                regexp_rect<T1>(f, f0, f1, f2, f3, f4, f5, *r5));
    } else if (std::holds_alternative<typename regexp::Zero>(r.v())) {
      return f4;
    } else {
      const auto &[r2] = std::get<typename regexp::Star>(r.v());
      return f5(*r2, regexp_rect<T1>(f, f0, f1, f2, f3, f4, f5, *r2));
    }
  }

  template <typename T1, typename F1, typename F3, typename F4, typename F6>
    requires std::is_invocable_r_v<T1, F1 &, int64_t &> &&
             std::is_invocable_r_v<T1, F3 &, regexp &, T1 &, regexp &, T1 &> &&
             std::is_invocable_r_v<T1, F4 &, regexp &, T1 &, regexp &, T1 &> &&
             std::is_invocable_r_v<T1, F6 &, regexp &, T1 &>
  static T1 regexp_rec(T1 f, F1 &&f0, T1 f1, F3 &&f2, F4 &&f3, T1 f4, F6 &&f5,
                       const regexp &r) {
    if (std::holds_alternative<typename regexp::Any>(r.v())) {
      return f;
    } else if (std::holds_alternative<typename regexp::Char>(r.v())) {
      const auto &[c0] = std::get<typename regexp::Char>(r.v());
      return f0(c0);
    } else if (std::holds_alternative<typename regexp::Eps>(r.v())) {
      return f1;
    } else if (std::holds_alternative<typename regexp::Cat>(r.v())) {
      const auto &[r4, r5] = std::get<typename regexp::Cat>(r.v());
      return f2(*r4, regexp_rec<T1>(f, f0, f1, f2, f3, f4, f5, *r4), *r5,
                regexp_rec<T1>(f, f0, f1, f2, f3, f4, f5, *r5));
    } else if (std::holds_alternative<typename regexp::Alt>(r.v())) {
      const auto &[r4, r5] = std::get<typename regexp::Alt>(r.v());
      return f3(*r4, regexp_rec<T1>(f, f0, f1, f2, f3, f4, f5, *r4), *r5,
                regexp_rec<T1>(f, f0, f1, f2, f3, f4, f5, *r5));
    } else if (std::holds_alternative<typename regexp::Zero>(r.v())) {
      return f4;
    } else {
      const auto &[r2] = std::get<typename regexp::Star>(r.v());
      return f5(*r2, regexp_rec<T1>(f, f0, f1, f2, f3, f4, f5, *r2));
    }
  }

  static bool regexp_eq(const regexp &r, const regexp &x);
  /// An optimized constructor for Cat.
  static regexp OptCat(regexp r2, regexp r3);
  /// Optimized version of Alt.
  static regexp OptAlt(regexp r2, regexp r3);
  /// If r accepts the empty string, return Eps, else return Zero.
  static regexp null(const regexp &r);
  static bool accepts_null(const regexp &r);
  /// This is the heart of the algorithm.  It returns a regexp denoting
  /// { cs | (c::cs) in r }.
  static regexp deriv(const regexp &r, int64_t c);
  /// This calculates the derivative of a regular expression with respect to a
  /// string.
  static regexp derivs(regexp r, const List<int64_t> &cs);
  /// To see if cs matches r, calculate the derivative of r with respect
  /// to s, and see if the resulting regexp accepts the empty string.
  static bool deriv_parse(const regexp &r, const List<int64_t> &cs);
  /// null r returns Eps or Zero
  static bool NullEpsOrZero(const regexp &r);
  /// From this, we can build a decidable regexp matcher by running
  /// the derivative-based parser.
  static bool parse(const regexp &r, const List<int64_t> &cs);
  static bool parse_bool(const regexp &r, const List<int64_t> &cs);
  static inline const regexp r1 = regexp::cat(
      regexp::star(regexp::Char_(INT64_C(0))), regexp::Char_(INT64_C(1)));
  static inline const List<int64_t> s1 = List<int64_t>::cons(
      INT64_C(0), List<int64_t>::cons(INT64_C(1), List<int64_t>::nil()));
  static inline const List<int64_t> s2 =
      List<int64_t>::cons(INT64_C(1), List<int64_t>::nil());
  static inline const List<int64_t> s3 = List<int64_t>::cons(
      INT64_C(0),
      List<int64_t>::cons(
          INT64_C(0), List<int64_t>::cons(INT64_C(1), List<int64_t>::nil())));
  static inline const List<int64_t> s4 =
      List<int64_t>::cons(INT64_C(0), List<int64_t>::nil());
};

#endif // INCLUDED_REGEXP
