#ifndef INCLUDED_LOOPIFY_EXPR_VARIANTS
#define INCLUDED_LOOPIFY_EXPR_VARIANTS

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_unique<T>(x->clone()) : nullptr;
  } else {
    return x ? std::make_unique<T>(*x) : nullptr;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using T = std::remove_cvref_t<Target>;
  using S = std::remove_cvref_t<Source>;
  if constexpr (requires(const S &s) {
                  s.has_value();
                  *s;
                }) {
    if (!x.has_value())
      return T{};
    using TInner = std::remove_cvref_t<decltype(*std::declval<const T &>())>;
    return T{clone_as_value<TInner>(*x)};
  } else if constexpr (std::is_same_v<T, S>) {
    if constexpr (is_unique_ptr<T>::value) {
      return clone_value(x);
    } else if constexpr (requires { x.clone(); }) {
      return x.clone();
    } else {
      return x;
    }
  } else if constexpr (is_unique_ptr<S>::value) {
    if (!x)
      return T{};
    return clone_as_value<T>(*x);
  } else if constexpr (is_unique_ptr<T>::value) {
    using Inner = typename is_unique_ptr<T>::element_type;
    return std::make_unique<Inner>(clone_as_value<Inner>(x));
  } else {
    return T(x);
  }
}

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;
  using crane_element_type = t_A;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  __attribute__((pure)) List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{clone_value(d_a0), clone_value(d_a1)});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ = Cons{clone_as_value<t_A>(d_a0),
                  d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) List<t_A> app(List<t_A> m) const {
    std::unique_ptr<List<t_A>> _head{};
    std::unique_ptr<List<t_A>> *_write = &_head;
    const List *_loop_self = this;
    while (true) {
      auto &&_sv = *(_loop_self);
      if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
        *(_write) = std::make_unique<List<t_A>>(m);
        break;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
        auto _cell = std::make_unique<List<t_A>>(
            typename List<t_A>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename List<t_A>::Cons>((*_write)->v_mut()).d_a1;
        _loop_self = d_a1.get();
        continue;
      }
    }
    return std::move(*(_head));
  }
};

struct ListDef {
  template <typename T1>
  __attribute__((pure)) static List<T1> repeat(const T1 x,
                                               const unsigned int &n);
};

struct LoopifyExprVariants {
  struct cond_expr {
    // TYPES
    struct Lit {
      unsigned int d_a0;
    };

    struct Add {
      std::unique_ptr<cond_expr> d_a0;
      std::unique_ptr<cond_expr> d_a1;
    };

    struct Cond {
      std::unique_ptr<cond_expr> d_a0;
      std::unique_ptr<cond_expr> d_a1;
      std::unique_ptr<cond_expr> d_a2;
    };

    using variant_t = std::variant<Lit, Add, Cond>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    cond_expr() {}

    explicit cond_expr(Lit _v) : d_v_(std::move(_v)) {}

    explicit cond_expr(Add _v) : d_v_(std::move(_v)) {}

    explicit cond_expr(Cond _v) : d_v_(std::move(_v)) {}

    cond_expr(const cond_expr &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    cond_expr(cond_expr &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) cond_expr &operator=(const cond_expr &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) cond_expr &operator=(cond_expr &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) cond_expr clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Lit>(_sv.v())) {
        const auto &[d_a0] = std::get<Lit>(_sv.v());
        return cond_expr(Lit{d_a0});
      } else if (std::holds_alternative<Add>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<Add>(_sv.v());
        return cond_expr(Add{clone_value(d_a0), clone_value(d_a1)});
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<Cond>(_sv.v());
        return cond_expr(
            Cond{clone_value(d_a0), clone_value(d_a1), clone_value(d_a2)});
      }
    }

    // CREATORS
    __attribute__((pure)) static cond_expr lit(unsigned int a0) {
      return cond_expr(Lit{std::move(a0)});
    }

    __attribute__((pure)) static cond_expr add(const cond_expr &a0,
                                               const cond_expr &a1) {
      return cond_expr(Add{std::make_unique<cond_expr>(a0),
                           std::make_unique<cond_expr>(a1)});
    }

    __attribute__((pure)) static cond_expr
    cond(const cond_expr &a0, const cond_expr &a1, const cond_expr &a2) {
      return cond_expr(Cond{std::make_unique<cond_expr>(a0),
                            std::make_unique<cond_expr>(a1),
                            std::make_unique<cond_expr>(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) cond_expr *operator->() { return this; }

    __attribute__((pure)) const cond_expr *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = cond_expr(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int size_cond() const {
      const cond_expr *_self = this;

      struct _Enter {
        const cond_expr *_self;
      };

      struct _Call1 {
        cond_expr *_s0;
        decltype(1u) _s1;
      };

      struct _Call2 {
        unsigned int _s0;
        decltype(1u) _s1;
      };

      struct _Call3 {
        const cond_expr *_s0;
        const cond_expr *_s1;
        decltype(1u) _s2;
      };

      struct _Call4 {
        unsigned int _s0;
        const cond_expr *_s1;
        decltype(1u) _s2;
      };

      struct _Call5 {
        unsigned int _s0;
        unsigned int _s1;
        decltype(1u) _s2;
      };

      using _Frame =
          std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const cond_expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename cond_expr::Lit>(_sv.v())) {
            _result = 1u;
          } else if (std::holds_alternative<typename cond_expr::Add>(_sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename cond_expr::Add>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get(), 1u});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename cond_expr::Cond>(_sv.v());
            _stack.emplace_back(_Call3{d_a1.get(), d_a0.get(), 1u});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = ((_f._s1 + _result) + _f._s0);
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          _stack.emplace_back(_Call4{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call4>(_frame)) {
          auto _f = std::move(std::get<_Call4>(_frame));
          _stack.emplace_back(_Call5{_f._s0, _result, _f._s2});
          _stack.emplace_back(_Enter{_f._s1});
        } else {
          auto _f = std::move(std::get<_Call5>(_frame));
          _result = (((_f._s2 + _result) + _f._s1) + _f._s0);
        }
      }
      return _result;
    }

    __attribute__((pure)) unsigned int eval_cond() const {
      const cond_expr *_self = this;
      auto &&_sv = *(_self);
      if (std::holds_alternative<typename cond_expr::Lit>(_sv.v())) {
        const auto &[d_a0] = std::get<typename cond_expr::Lit>(_sv.v());
        return d_a0;
      } else if (std::holds_alternative<typename cond_expr::Add>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename cond_expr::Add>(_sv.v());
        return ((*(d_a0)).eval_cond() + (*(d_a1)).eval_cond());
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename cond_expr::Cond>(_sv.v());
        if (0u < (*(d_a0)).eval_cond()) {
          return (*(d_a1)).eval_cond();
        } else {
          return (*(d_a2)).eval_cond();
        }
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, cond_expr, T1, cond_expr, T1> F1,
              MapsTo<T1, cond_expr, T1, cond_expr, T1, cond_expr, T1> F2>
    T1 cond_expr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      const cond_expr *_self = this;

      struct _Enter {
        const cond_expr *_self;
      };

      struct _Call1 {
        cond_expr *_s0;
        cond_expr _s1;
        cond_expr _s2;
      };

      struct _Call2 {
        T1 _s0;
        cond_expr _s1;
        cond_expr _s2;
      };

      struct _Call3 {
        const cond_expr *_s0;
        const cond_expr *_s1;
        cond_expr _s2;
        cond_expr _s3;
        cond_expr _s4;
      };

      struct _Call4 {
        T1 _s0;
        const cond_expr *_s1;
        cond_expr _s2;
        cond_expr _s3;
        cond_expr _s4;
      };

      struct _Call5 {
        T1 _s0;
        T1 _s1;
        cond_expr _s2;
        cond_expr _s3;
        cond_expr _s4;
      };

      using _Frame =
          std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const cond_expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename cond_expr::Lit>(_sv.v())) {
            const auto &[d_a0] = std::get<typename cond_expr::Lit>(_sv.v());
            _result = f(d_a0);
          } else if (std::holds_alternative<typename cond_expr::Add>(_sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename cond_expr::Add>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename cond_expr::Cond>(_sv.v());
            _stack.emplace_back(
                _Call3{d_a1.get(), d_a0.get(), *(d_a2), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = f0(_f._s2, _result, _f._s1, _f._s0);
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          _stack.emplace_back(_Call4{_result, _f._s1, _f._s2, _f._s3, _f._s4});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call4>(_frame)) {
          auto _f = std::move(std::get<_Call4>(_frame));
          _stack.emplace_back(_Call5{_f._s0, _result, _f._s2, _f._s3, _f._s4});
          _stack.emplace_back(_Enter{_f._s1});
        } else {
          auto _f = std::move(std::get<_Call5>(_frame));
          _result = f1(_f._s4, _result, _f._s3, _f._s1, _f._s2, _f._s0);
        }
      }
      return _result;
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, cond_expr, T1, cond_expr, T1> F1,
              MapsTo<T1, cond_expr, T1, cond_expr, T1, cond_expr, T1> F2>
    T1 cond_expr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      const cond_expr *_self = this;

      struct _Enter {
        const cond_expr *_self;
      };

      struct _Call1 {
        cond_expr *_s0;
        cond_expr _s1;
        cond_expr _s2;
      };

      struct _Call2 {
        T1 _s0;
        cond_expr _s1;
        cond_expr _s2;
      };

      struct _Call3 {
        const cond_expr *_s0;
        const cond_expr *_s1;
        cond_expr _s2;
        cond_expr _s3;
        cond_expr _s4;
      };

      struct _Call4 {
        T1 _s0;
        const cond_expr *_s1;
        cond_expr _s2;
        cond_expr _s3;
        cond_expr _s4;
      };

      struct _Call5 {
        T1 _s0;
        T1 _s1;
        cond_expr _s2;
        cond_expr _s3;
        cond_expr _s4;
      };

      using _Frame =
          std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const cond_expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename cond_expr::Lit>(_sv.v())) {
            const auto &[d_a0] = std::get<typename cond_expr::Lit>(_sv.v());
            _result = f(d_a0);
          } else if (std::holds_alternative<typename cond_expr::Add>(_sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename cond_expr::Add>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename cond_expr::Cond>(_sv.v());
            _stack.emplace_back(
                _Call3{d_a1.get(), d_a0.get(), *(d_a2), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = f0(_f._s2, _result, _f._s1, _f._s0);
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          _stack.emplace_back(_Call4{_result, _f._s1, _f._s2, _f._s3, _f._s4});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call4>(_frame)) {
          auto _f = std::move(std::get<_Call4>(_frame));
          _stack.emplace_back(_Call5{_f._s0, _result, _f._s2, _f._s3, _f._s4});
          _stack.emplace_back(_Enter{_f._s1});
        } else {
          auto _f = std::move(std::get<_Call5>(_frame));
          _result = f1(_f._s4, _result, _f._s3, _f._s1, _f._s2, _f._s0);
        }
      }
      return _result;
    }
  };

  struct arith_expr {
    // TYPES
    struct ANum {
      unsigned int d_a0;
    };

    struct AAdd {
      std::unique_ptr<arith_expr> d_a0;
      std::unique_ptr<arith_expr> d_a1;
    };

    struct AMul {
      std::unique_ptr<arith_expr> d_a0;
      std::unique_ptr<arith_expr> d_a1;
    };

    struct ADiv {
      std::unique_ptr<arith_expr> d_a0;
      std::unique_ptr<arith_expr> d_a1;
    };

    using variant_t = std::variant<ANum, AAdd, AMul, ADiv>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    arith_expr() {}

    explicit arith_expr(ANum _v) : d_v_(std::move(_v)) {}

    explicit arith_expr(AAdd _v) : d_v_(std::move(_v)) {}

    explicit arith_expr(AMul _v) : d_v_(std::move(_v)) {}

    explicit arith_expr(ADiv _v) : d_v_(std::move(_v)) {}

    arith_expr(const arith_expr &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    arith_expr(arith_expr &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) arith_expr &operator=(const arith_expr &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) arith_expr &operator=(arith_expr &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) arith_expr clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<ANum>(_sv.v())) {
        const auto &[d_a0] = std::get<ANum>(_sv.v());
        return arith_expr(ANum{d_a0});
      } else if (std::holds_alternative<AAdd>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<AAdd>(_sv.v());
        return arith_expr(AAdd{clone_value(d_a0), clone_value(d_a1)});
      } else if (std::holds_alternative<AMul>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<AMul>(_sv.v());
        return arith_expr(AMul{clone_value(d_a0), clone_value(d_a1)});
      } else {
        const auto &[d_a0, d_a1] = std::get<ADiv>(_sv.v());
        return arith_expr(ADiv{clone_value(d_a0), clone_value(d_a1)});
      }
    }

    // CREATORS
    __attribute__((pure)) static arith_expr anum(unsigned int a0) {
      return arith_expr(ANum{std::move(a0)});
    }

    __attribute__((pure)) static arith_expr aadd(const arith_expr &a0,
                                                 const arith_expr &a1) {
      return arith_expr(AAdd{std::make_unique<arith_expr>(a0),
                             std::make_unique<arith_expr>(a1)});
    }

    __attribute__((pure)) static arith_expr amul(const arith_expr &a0,
                                                 const arith_expr &a1) {
      return arith_expr(AMul{std::make_unique<arith_expr>(a0),
                             std::make_unique<arith_expr>(a1)});
    }

    __attribute__((pure)) static arith_expr adiv(const arith_expr &a0,
                                                 const arith_expr &a1) {
      return arith_expr(ADiv{std::make_unique<arith_expr>(a0),
                             std::make_unique<arith_expr>(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) arith_expr *operator->() { return this; }

    __attribute__((pure)) const arith_expr *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = arith_expr(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int count_ops() const {
      const arith_expr *_self = this;

      struct _Enter {
        const arith_expr *_self;
      };

      struct _Call1 {
        arith_expr *_s0;
        decltype(1u) _s1;
      };

      struct _Call2 {
        unsigned int _s0;
        decltype(1u) _s1;
      };

      struct _Call3 {
        arith_expr *_s0;
        decltype(1u) _s1;
      };

      struct _Call4 {
        unsigned int _s0;
        decltype(1u) _s1;
      };

      struct _Call5 {
        arith_expr *_s0;
        decltype(1u) _s1;
      };

      struct _Call6 {
        unsigned int _s0;
        decltype(1u) _s1;
      };

      using _Frame =
          std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5, _Call6>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const arith_expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename arith_expr::ANum>(_sv.v())) {
            _result = 0u;
          } else if (std::holds_alternative<typename arith_expr::AAdd>(
                         _sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename arith_expr::AAdd>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get(), 1u});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else if (std::holds_alternative<typename arith_expr::AMul>(
                         _sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename arith_expr::AMul>(_sv.v());
            _stack.emplace_back(_Call3{d_a0.get(), 1u});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename arith_expr::ADiv>(_sv.v());
            _stack.emplace_back(_Call5{d_a0.get(), 1u});
            _stack.emplace_back(_Enter{d_a1.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = ((_f._s1 + _result) + _f._s0);
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          _stack.emplace_back(_Call4{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call4>(_frame)) {
          auto _f = std::move(std::get<_Call4>(_frame));
          _result = ((_f._s1 + _result) + _f._s0);
        } else if (std::holds_alternative<_Call5>(_frame)) {
          auto _f = std::move(std::get<_Call5>(_frame));
          _stack.emplace_back(_Call6{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Call6>(_frame));
          _result = ((_f._s1 + _result) + _f._s0);
        }
      }
      return _result;
    }

    __attribute__((pure)) unsigned int eval_arith() const {
      const arith_expr *_self = this;
      auto &&_sv = *(_self);
      if (std::holds_alternative<typename arith_expr::ANum>(_sv.v())) {
        const auto &[d_a0] = std::get<typename arith_expr::ANum>(_sv.v());
        return d_a0;
      } else if (std::holds_alternative<typename arith_expr::AAdd>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename arith_expr::AAdd>(_sv.v());
        return ((*(d_a0)).eval_arith() + (*(d_a1)).eval_arith());
      } else if (std::holds_alternative<typename arith_expr::AMul>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename arith_expr::AMul>(_sv.v());
        return ((*(d_a0)).eval_arith() * (*(d_a1)).eval_arith());
      } else {
        const auto &[d_a0, d_a1] = std::get<typename arith_expr::ADiv>(_sv.v());
        auto _cs = (*(d_a1)).eval_arith();
        if (_cs <= 0) {
          return 0u;
        } else {
          unsigned int n = _cs - 1;
          return ((n + 1) ? (*(d_a0)).eval_arith() / (n + 1) : 0);
        }
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, arith_expr, T1, arith_expr, T1> F1,
              MapsTo<T1, arith_expr, T1, arith_expr, T1> F2,
              MapsTo<T1, arith_expr, T1, arith_expr, T1> F3>
    T1 arith_expr_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2) const {
      const arith_expr *_self = this;

      struct _Enter {
        const arith_expr *_self;
      };

      struct _Call1 {
        arith_expr *_s0;
        arith_expr _s1;
        arith_expr _s2;
      };

      struct _Call2 {
        T1 _s0;
        arith_expr _s1;
        arith_expr _s2;
      };

      struct _Call3 {
        arith_expr *_s0;
        arith_expr _s1;
        arith_expr _s2;
      };

      struct _Call4 {
        T1 _s0;
        arith_expr _s1;
        arith_expr _s2;
      };

      struct _Call5 {
        arith_expr *_s0;
        arith_expr _s1;
        arith_expr _s2;
      };

      struct _Call6 {
        T1 _s0;
        arith_expr _s1;
        arith_expr _s2;
      };

      using _Frame =
          std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5, _Call6>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const arith_expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename arith_expr::ANum>(_sv.v())) {
            const auto &[d_a0] = std::get<typename arith_expr::ANum>(_sv.v());
            _result = f(d_a0);
          } else if (std::holds_alternative<typename arith_expr::AAdd>(
                         _sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename arith_expr::AAdd>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else if (std::holds_alternative<typename arith_expr::AMul>(
                         _sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename arith_expr::AMul>(_sv.v());
            _stack.emplace_back(_Call3{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename arith_expr::ADiv>(_sv.v());
            _stack.emplace_back(_Call5{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = f0(_f._s2, _result, _f._s1, _f._s0);
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          _stack.emplace_back(_Call4{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call4>(_frame)) {
          auto _f = std::move(std::get<_Call4>(_frame));
          _result = f1(_f._s2, _result, _f._s1, _f._s0);
        } else if (std::holds_alternative<_Call5>(_frame)) {
          auto _f = std::move(std::get<_Call5>(_frame));
          _stack.emplace_back(_Call6{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Call6>(_frame));
          _result = f2(_f._s2, _result, _f._s1, _f._s0);
        }
      }
      return _result;
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, arith_expr, T1, arith_expr, T1> F1,
              MapsTo<T1, arith_expr, T1, arith_expr, T1> F2,
              MapsTo<T1, arith_expr, T1, arith_expr, T1> F3>
    T1 arith_expr_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2) const {
      const arith_expr *_self = this;

      struct _Enter {
        const arith_expr *_self;
      };

      struct _Call1 {
        arith_expr *_s0;
        arith_expr _s1;
        arith_expr _s2;
      };

      struct _Call2 {
        T1 _s0;
        arith_expr _s1;
        arith_expr _s2;
      };

      struct _Call3 {
        arith_expr *_s0;
        arith_expr _s1;
        arith_expr _s2;
      };

      struct _Call4 {
        T1 _s0;
        arith_expr _s1;
        arith_expr _s2;
      };

      struct _Call5 {
        arith_expr *_s0;
        arith_expr _s1;
        arith_expr _s2;
      };

      struct _Call6 {
        T1 _s0;
        arith_expr _s1;
        arith_expr _s2;
      };

      using _Frame =
          std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5, _Call6>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const arith_expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename arith_expr::ANum>(_sv.v())) {
            const auto &[d_a0] = std::get<typename arith_expr::ANum>(_sv.v());
            _result = f(d_a0);
          } else if (std::holds_alternative<typename arith_expr::AAdd>(
                         _sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename arith_expr::AAdd>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else if (std::holds_alternative<typename arith_expr::AMul>(
                         _sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename arith_expr::AMul>(_sv.v());
            _stack.emplace_back(_Call3{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename arith_expr::ADiv>(_sv.v());
            _stack.emplace_back(_Call5{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = f0(_f._s2, _result, _f._s1, _f._s0);
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          _stack.emplace_back(_Call4{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call4>(_frame)) {
          auto _f = std::move(std::get<_Call4>(_frame));
          _result = f1(_f._s2, _result, _f._s1, _f._s0);
        } else if (std::holds_alternative<_Call5>(_frame)) {
          auto _f = std::move(std::get<_Call5>(_frame));
          _stack.emplace_back(_Call6{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Call6>(_frame));
          _result = f2(_f._s2, _result, _f._s1, _f._s0);
        }
      }
      return _result;
    }
  };

  struct bool_expr {
    // TYPES
    struct BTrue {};

    struct BFalse {};

    struct BAnd {
      std::unique_ptr<bool_expr> d_a0;
      std::unique_ptr<bool_expr> d_a1;
    };

    struct BOr {
      std::unique_ptr<bool_expr> d_a0;
      std::unique_ptr<bool_expr> d_a1;
    };

    struct BNot {
      std::unique_ptr<bool_expr> d_a0;
    };

    using variant_t = std::variant<BTrue, BFalse, BAnd, BOr, BNot>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    bool_expr() {}

    explicit bool_expr(BTrue _v) : d_v_(_v) {}

    explicit bool_expr(BFalse _v) : d_v_(_v) {}

    explicit bool_expr(BAnd _v) : d_v_(std::move(_v)) {}

    explicit bool_expr(BOr _v) : d_v_(std::move(_v)) {}

    explicit bool_expr(BNot _v) : d_v_(std::move(_v)) {}

    bool_expr(const bool_expr &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    bool_expr(bool_expr &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) bool_expr &operator=(const bool_expr &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) bool_expr &operator=(bool_expr &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) bool_expr clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<BTrue>(_sv.v())) {
        return bool_expr(BTrue{});
      } else if (std::holds_alternative<BFalse>(_sv.v())) {
        return bool_expr(BFalse{});
      } else if (std::holds_alternative<BAnd>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<BAnd>(_sv.v());
        return bool_expr(BAnd{clone_value(d_a0), clone_value(d_a1)});
      } else if (std::holds_alternative<BOr>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<BOr>(_sv.v());
        return bool_expr(BOr{clone_value(d_a0), clone_value(d_a1)});
      } else {
        const auto &[d_a0] = std::get<BNot>(_sv.v());
        return bool_expr(BNot{clone_value(d_a0)});
      }
    }

    // CREATORS
    __attribute__((pure)) static bool_expr btrue() {
      return bool_expr(BTrue{});
    }

    __attribute__((pure)) static bool_expr bfalse() {
      return bool_expr(BFalse{});
    }

    __attribute__((pure)) static bool_expr band(const bool_expr &a0,
                                                const bool_expr &a1) {
      return bool_expr(BAnd{std::make_unique<bool_expr>(a0),
                            std::make_unique<bool_expr>(a1)});
    }

    __attribute__((pure)) static bool_expr bor(const bool_expr &a0,
                                               const bool_expr &a1) {
      return bool_expr(BOr{std::make_unique<bool_expr>(a0),
                           std::make_unique<bool_expr>(a1)});
    }

    __attribute__((pure)) static bool_expr bnot(const bool_expr &a0) {
      return bool_expr(BNot{std::make_unique<bool_expr>(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) bool_expr *operator->() { return this; }

    __attribute__((pure)) const bool_expr *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = bool_expr(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) bool_expr simplify_bool() const {
      const bool_expr *_self = this;
      auto &&_sv = *(_self);
      if (std::holds_alternative<typename bool_expr::BTrue>(_sv.v())) {
        return bool_expr::btrue();
      } else if (std::holds_alternative<typename bool_expr::BFalse>(_sv.v())) {
        return bool_expr::bfalse();
      } else if (std::holds_alternative<typename bool_expr::BAnd>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename bool_expr::BAnd>(_sv.v());
        auto &&_sv0 = (*(d_a0)).simplify_bool();
        if (std::holds_alternative<typename bool_expr::BTrue>(_sv0.v())) {
          auto &&_sv1 = (*(d_a1)).simplify_bool();
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv1.v())) {
            return bool_expr::btrue();
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv1.v())) {
            return bool_expr::bfalse();
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv1.v())) {
            const auto &[d_a01, d_a11] =
                std::get<typename bool_expr::BAnd>(_sv1.v());
            return bool_expr::band(*(d_a01), *(d_a11));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _sv1.v())) {
            const auto &[d_a01, d_a11] =
                std::get<typename bool_expr::BOr>(_sv1.v());
            return bool_expr::bor(*(d_a01), *(d_a11));
          } else {
            const auto &[d_a01] = std::get<typename bool_expr::BNot>(_sv1.v());
            return bool_expr::bnot(*(d_a01));
          }
        } else if (std::holds_alternative<typename bool_expr::BFalse>(
                       _sv0.v())) {
          return bool_expr::bfalse();
        } else if (std::holds_alternative<typename bool_expr::BAnd>(_sv0.v())) {
          const auto &[d_a00, d_a10] =
              std::get<typename bool_expr::BAnd>(_sv0.v());
          bool_expr a_ = bool_expr::band(*(d_a00), *(d_a10));
          auto &&_sv1 = (*(d_a1)).simplify_bool();
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv1.v())) {
            return a_;
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv1.v())) {
            return bool_expr::bfalse();
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv1.v())) {
            const auto &[d_a01, d_a11] =
                std::get<typename bool_expr::BAnd>(_sv1.v());
            return bool_expr::band(a_, bool_expr::band(*(d_a01), *(d_a11)));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _sv1.v())) {
            const auto &[d_a01, d_a11] =
                std::get<typename bool_expr::BOr>(_sv1.v());
            return bool_expr::band(a_, bool_expr::bor(*(d_a01), *(d_a11)));
          } else {
            const auto &[d_a01] = std::get<typename bool_expr::BNot>(_sv1.v());
            return bool_expr::band(a_, bool_expr::bnot(*(d_a01)));
          }
        } else if (std::holds_alternative<typename bool_expr::BOr>(_sv0.v())) {
          const auto &[d_a00, d_a10] =
              std::get<typename bool_expr::BOr>(_sv0.v());
          bool_expr a_ = bool_expr::bor(*(d_a00), *(d_a10));
          auto &&_sv1 = (*(d_a1)).simplify_bool();
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv1.v())) {
            return a_;
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv1.v())) {
            return bool_expr::bfalse();
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv1.v())) {
            const auto &[d_a01, d_a11] =
                std::get<typename bool_expr::BAnd>(_sv1.v());
            return bool_expr::band(a_, bool_expr::band(*(d_a01), *(d_a11)));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _sv1.v())) {
            const auto &[d_a01, d_a11] =
                std::get<typename bool_expr::BOr>(_sv1.v());
            return bool_expr::band(a_, bool_expr::bor(*(d_a01), *(d_a11)));
          } else {
            const auto &[d_a01] = std::get<typename bool_expr::BNot>(_sv1.v());
            return bool_expr::band(a_, bool_expr::bnot(*(d_a01)));
          }
        } else {
          const auto &[d_a00] = std::get<typename bool_expr::BNot>(_sv0.v());
          bool_expr a_ = bool_expr::bnot(*(d_a00));
          auto &&_sv1 = (*(d_a1)).simplify_bool();
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv1.v())) {
            return a_;
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv1.v())) {
            return bool_expr::bfalse();
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv1.v())) {
            const auto &[d_a01, d_a11] =
                std::get<typename bool_expr::BAnd>(_sv1.v());
            return bool_expr::band(a_, bool_expr::band(*(d_a01), *(d_a11)));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _sv1.v())) {
            const auto &[d_a01, d_a11] =
                std::get<typename bool_expr::BOr>(_sv1.v());
            return bool_expr::band(a_, bool_expr::bor(*(d_a01), *(d_a11)));
          } else {
            const auto &[d_a01] = std::get<typename bool_expr::BNot>(_sv1.v());
            return bool_expr::band(a_, bool_expr::bnot(*(d_a01)));
          }
        }
      } else if (std::holds_alternative<typename bool_expr::BOr>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename bool_expr::BOr>(_sv.v());
        auto &&_sv0 = (*(d_a0)).simplify_bool();
        if (std::holds_alternative<typename bool_expr::BTrue>(_sv0.v())) {
          return bool_expr::btrue();
        } else if (std::holds_alternative<typename bool_expr::BFalse>(
                       _sv0.v())) {
          auto &&_sv1 = (*(d_a1)).simplify_bool();
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv1.v())) {
            return bool_expr::btrue();
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv1.v())) {
            return bool_expr::bfalse();
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv1.v())) {
            const auto &[d_a01, d_a11] =
                std::get<typename bool_expr::BAnd>(_sv1.v());
            return bool_expr::band(*(d_a01), *(d_a11));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _sv1.v())) {
            const auto &[d_a01, d_a11] =
                std::get<typename bool_expr::BOr>(_sv1.v());
            return bool_expr::bor(*(d_a01), *(d_a11));
          } else {
            const auto &[d_a01] = std::get<typename bool_expr::BNot>(_sv1.v());
            return bool_expr::bnot(*(d_a01));
          }
        } else if (std::holds_alternative<typename bool_expr::BAnd>(_sv0.v())) {
          const auto &[d_a00, d_a10] =
              std::get<typename bool_expr::BAnd>(_sv0.v());
          bool_expr a_ = bool_expr::band(*(d_a00), *(d_a10));
          auto &&_sv1 = (*(d_a1)).simplify_bool();
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv1.v())) {
            return bool_expr::btrue();
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv1.v())) {
            return a_;
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv1.v())) {
            const auto &[d_a01, d_a11] =
                std::get<typename bool_expr::BAnd>(_sv1.v());
            return bool_expr::bor(a_, bool_expr::band(*(d_a01), *(d_a11)));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _sv1.v())) {
            const auto &[d_a01, d_a11] =
                std::get<typename bool_expr::BOr>(_sv1.v());
            return bool_expr::bor(a_, bool_expr::bor(*(d_a01), *(d_a11)));
          } else {
            const auto &[d_a01] = std::get<typename bool_expr::BNot>(_sv1.v());
            return bool_expr::bor(a_, bool_expr::bnot(*(d_a01)));
          }
        } else if (std::holds_alternative<typename bool_expr::BOr>(_sv0.v())) {
          const auto &[d_a00, d_a10] =
              std::get<typename bool_expr::BOr>(_sv0.v());
          bool_expr a_ = bool_expr::bor(*(d_a00), *(d_a10));
          auto &&_sv1 = (*(d_a1)).simplify_bool();
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv1.v())) {
            return bool_expr::btrue();
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv1.v())) {
            return a_;
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv1.v())) {
            const auto &[d_a01, d_a11] =
                std::get<typename bool_expr::BAnd>(_sv1.v());
            return bool_expr::bor(a_, bool_expr::band(*(d_a01), *(d_a11)));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _sv1.v())) {
            const auto &[d_a01, d_a11] =
                std::get<typename bool_expr::BOr>(_sv1.v());
            return bool_expr::bor(a_, bool_expr::bor(*(d_a01), *(d_a11)));
          } else {
            const auto &[d_a01] = std::get<typename bool_expr::BNot>(_sv1.v());
            return bool_expr::bor(a_, bool_expr::bnot(*(d_a01)));
          }
        } else {
          const auto &[d_a00] = std::get<typename bool_expr::BNot>(_sv0.v());
          bool_expr a_ = bool_expr::bnot(*(d_a00));
          auto &&_sv1 = (*(d_a1)).simplify_bool();
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv1.v())) {
            return bool_expr::btrue();
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv1.v())) {
            return a_;
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv1.v())) {
            const auto &[d_a01, d_a11] =
                std::get<typename bool_expr::BAnd>(_sv1.v());
            return bool_expr::bor(a_, bool_expr::band(*(d_a01), *(d_a11)));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _sv1.v())) {
            const auto &[d_a01, d_a11] =
                std::get<typename bool_expr::BOr>(_sv1.v());
            return bool_expr::bor(a_, bool_expr::bor(*(d_a01), *(d_a11)));
          } else {
            const auto &[d_a01] = std::get<typename bool_expr::BNot>(_sv1.v());
            return bool_expr::bor(a_, bool_expr::bnot(*(d_a01)));
          }
        }
      } else {
        const auto &[d_a0] = std::get<typename bool_expr::BNot>(_sv.v());
        auto &&_sv0 = (*(d_a0)).simplify_bool();
        if (std::holds_alternative<typename bool_expr::BTrue>(_sv0.v())) {
          return bool_expr::bfalse();
        } else if (std::holds_alternative<typename bool_expr::BFalse>(
                       _sv0.v())) {
          return bool_expr::btrue();
        } else if (std::holds_alternative<typename bool_expr::BAnd>(_sv0.v())) {
          const auto &[d_a00, d_a10] =
              std::get<typename bool_expr::BAnd>(_sv0.v());
          return bool_expr::bnot(bool_expr::band(*(d_a00), *(d_a10)));
        } else if (std::holds_alternative<typename bool_expr::BOr>(_sv0.v())) {
          const auto &[d_a00, d_a10] =
              std::get<typename bool_expr::BOr>(_sv0.v());
          return bool_expr::bnot(bool_expr::bor(*(d_a00), *(d_a10)));
        } else {
          const auto &[d_a00] = std::get<typename bool_expr::BNot>(_sv0.v());
          return bool_expr::bnot(bool_expr::bnot(*(d_a00)));
        }
      }
    }

    __attribute__((pure)) bool eval_bool() const {
      const bool_expr *_self = this;

      struct _Enter {
        const bool_expr *_self;
      };

      struct _Call1 {
        bool_expr *_s0;
      };

      struct _Call2 {
        bool _s0;
      };

      struct _Call3 {
        bool_expr *_s0;
      };

      struct _Call4 {
        bool _s0;
      };

      struct _Call5 {};

      using _Frame =
          std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5>;
      bool _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const bool_expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv.v())) {
            _result = true;
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv.v())) {
            _result = false;
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename bool_expr::BAnd>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get()});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else if (std::holds_alternative<typename bool_expr::BOr>(_sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename bool_expr::BOr>(_sv.v());
            _stack.emplace_back(_Call3{d_a0.get()});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0] = std::get<typename bool_expr::BNot>(_sv.v());
            _stack.emplace_back(_Call5{});
            _stack.emplace_back(_Enter{d_a0.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = (_result && _f._s0);
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          _stack.emplace_back(_Call4{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call4>(_frame)) {
          auto _f = std::move(std::get<_Call4>(_frame));
          _result = (_result || _f._s0);
        } else {
          auto _f = std::move(std::get<_Call5>(_frame));
          _result = !(_result);
        }
      }
      return _result;
    }

    template <typename T1, MapsTo<T1, bool_expr, T1, bool_expr, T1> F2,
              MapsTo<T1, bool_expr, T1, bool_expr, T1> F3,
              MapsTo<T1, bool_expr, T1> F4>
    T1 bool_expr_rec(const T1 f, const T1 f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      const bool_expr *_self = this;

      struct _Enter {
        const bool_expr *_self;
      };

      struct _Call1 {
        bool_expr *_s0;
        bool_expr _s1;
        bool_expr _s2;
      };

      struct _Call2 {
        T1 _s0;
        bool_expr _s1;
        bool_expr _s2;
      };

      struct _Call3 {
        bool_expr *_s0;
        bool_expr _s1;
        bool_expr _s2;
      };

      struct _Call4 {
        T1 _s0;
        bool_expr _s1;
        bool_expr _s2;
      };

      struct _Call5 {
        bool_expr _s0;
      };

      using _Frame =
          std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const bool_expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv.v())) {
            _result = f;
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv.v())) {
            _result = f0;
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename bool_expr::BAnd>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else if (std::holds_alternative<typename bool_expr::BOr>(_sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename bool_expr::BOr>(_sv.v());
            _stack.emplace_back(_Call3{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0] = std::get<typename bool_expr::BNot>(_sv.v());
            _stack.emplace_back(_Call5{*(d_a0)});
            _stack.emplace_back(_Enter{d_a0.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = f1(_f._s2, _result, _f._s1, _f._s0);
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          _stack.emplace_back(_Call4{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call4>(_frame)) {
          auto _f = std::move(std::get<_Call4>(_frame));
          _result = f2(_f._s2, _result, _f._s1, _f._s0);
        } else {
          auto _f = std::move(std::get<_Call5>(_frame));
          _result = f3(_f._s0, _result);
        }
      }
      return _result;
    }

    template <typename T1, MapsTo<T1, bool_expr, T1, bool_expr, T1> F2,
              MapsTo<T1, bool_expr, T1, bool_expr, T1> F3,
              MapsTo<T1, bool_expr, T1> F4>
    T1 bool_expr_rect(const T1 f, const T1 f0, F2 &&f1, F3 &&f2,
                      F4 &&f3) const {
      const bool_expr *_self = this;

      struct _Enter {
        const bool_expr *_self;
      };

      struct _Call1 {
        bool_expr *_s0;
        bool_expr _s1;
        bool_expr _s2;
      };

      struct _Call2 {
        T1 _s0;
        bool_expr _s1;
        bool_expr _s2;
      };

      struct _Call3 {
        bool_expr *_s0;
        bool_expr _s1;
        bool_expr _s2;
      };

      struct _Call4 {
        T1 _s0;
        bool_expr _s1;
        bool_expr _s2;
      };

      struct _Call5 {
        bool_expr _s0;
      };

      using _Frame =
          std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const bool_expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv.v())) {
            _result = f;
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv.v())) {
            _result = f0;
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename bool_expr::BAnd>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else if (std::holds_alternative<typename bool_expr::BOr>(_sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename bool_expr::BOr>(_sv.v());
            _stack.emplace_back(_Call3{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0] = std::get<typename bool_expr::BNot>(_sv.v());
            _stack.emplace_back(_Call5{*(d_a0)});
            _stack.emplace_back(_Enter{d_a0.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = f1(_f._s2, _result, _f._s1, _f._s0);
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          _stack.emplace_back(_Call4{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call4>(_frame)) {
          auto _f = std::move(std::get<_Call4>(_frame));
          _result = f2(_f._s2, _result, _f._s1, _f._s0);
        } else {
          auto _f = std::move(std::get<_Call5>(_frame));
          _result = f3(_f._s0, _result);
        }
      }
      return _result;
    }
  };

  struct list_expr {
    // TYPES
    struct LNil {};

    struct LCons {
      unsigned int d_a0;
      std::unique_ptr<list_expr> d_a1;
    };

    struct LAppend {
      std::unique_ptr<list_expr> d_a0;
      std::unique_ptr<list_expr> d_a1;
    };

    struct LReplicate {
      unsigned int d_a0;
      unsigned int d_a1;
    };

    using variant_t = std::variant<LNil, LCons, LAppend, LReplicate>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    list_expr() {}

    explicit list_expr(LNil _v) : d_v_(_v) {}

    explicit list_expr(LCons _v) : d_v_(std::move(_v)) {}

    explicit list_expr(LAppend _v) : d_v_(std::move(_v)) {}

    explicit list_expr(LReplicate _v) : d_v_(std::move(_v)) {}

    list_expr(const list_expr &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    list_expr(list_expr &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) list_expr &operator=(const list_expr &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) list_expr &operator=(list_expr &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) list_expr clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<LNil>(_sv.v())) {
        return list_expr(LNil{});
      } else if (std::holds_alternative<LCons>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<LCons>(_sv.v());
        return list_expr(LCons{d_a0, clone_value(d_a1)});
      } else if (std::holds_alternative<LAppend>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<LAppend>(_sv.v());
        return list_expr(LAppend{clone_value(d_a0), clone_value(d_a1)});
      } else {
        const auto &[d_a0, d_a1] = std::get<LReplicate>(_sv.v());
        return list_expr(LReplicate{d_a0, d_a1});
      }
    }

    // CREATORS
    __attribute__((pure)) static list_expr lnil() { return list_expr(LNil{}); }

    __attribute__((pure)) static list_expr lcons(unsigned int a0,
                                                 const list_expr &a1) {
      return list_expr(LCons{std::move(a0), std::make_unique<list_expr>(a1)});
    }

    __attribute__((pure)) static list_expr lappend(const list_expr &a0,
                                                   const list_expr &a1) {
      return list_expr(LAppend{std::make_unique<list_expr>(a0),
                               std::make_unique<list_expr>(a1)});
    }

    __attribute__((pure)) static list_expr lreplicate(unsigned int a0,
                                                      unsigned int a1) {
      return list_expr(LReplicate{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) list_expr *operator->() { return this; }

    __attribute__((pure)) const list_expr *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = list_expr(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int list_expr_size() const {
      const list_expr *_self = this;

      struct _Enter {
        const list_expr *_self;
      };

      struct _Call1 {
        decltype(1u) _s0;
      };

      struct _Call2 {
        list_expr *_s0;
        decltype(1u) _s1;
      };

      struct _Call3 {
        unsigned int _s0;
        decltype(1u) _s1;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const list_expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename list_expr::LCons>(_sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename list_expr::LCons>(_sv.v());
            _stack.emplace_back(_Call1{1u});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else if (std::holds_alternative<typename list_expr::LAppend>(
                         _sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename list_expr::LAppend>(_sv.v());
            _stack.emplace_back(_Call2{d_a0.get(), 1u});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            _result = 1u;
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _result = (_f._s0 + _result);
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _stack.emplace_back(_Call3{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Call3>(_frame));
          _result = ((_f._s1 + _result) + _f._s0);
        }
      }
      return _result;
    }

    __attribute__((pure)) List<unsigned int> eval_list() const {
      const list_expr *_self = this;

      struct _Enter {
        const list_expr *_self;
      };

      struct _Call1 {
        unsigned int _s0;
      };

      struct _Call2 {
        list_expr *_s0;
      };

      struct _Call3 {
        List<unsigned int> _s0;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
      List<unsigned int> _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const list_expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename list_expr::LNil>(_sv.v())) {
            _result = List<unsigned int>::nil();
          } else if (std::holds_alternative<typename list_expr::LCons>(
                         _sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename list_expr::LCons>(_sv.v());
            _stack.emplace_back(_Call1{d_a0});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else if (std::holds_alternative<typename list_expr::LAppend>(
                         _sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename list_expr::LAppend>(_sv.v());
            _stack.emplace_back(_Call2{d_a0.get()});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename list_expr::LReplicate>(_sv.v());
            _result = ListDef::template repeat<unsigned int>(d_a1, d_a0);
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _result = List<unsigned int>::cons(_f._s0, _result);
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _stack.emplace_back(_Call3{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Call3>(_frame));
          _result = _result.app(_f._s0);
        }
      }
      return _result;
    }

    template <typename T1, MapsTo<T1, unsigned int, list_expr, T1> F1,
              MapsTo<T1, list_expr, T1, list_expr, T1> F2,
              MapsTo<T1, unsigned int, unsigned int> F3>
    T1 list_expr_rec(const T1 f, F1 &&f0, F2 &&f1, F3 &&f2) const {
      const list_expr *_self = this;

      struct _Enter {
        const list_expr *_self;
      };

      struct _Call1 {
        list_expr _s0;
        unsigned int _s1;
      };

      struct _Call2 {
        list_expr *_s0;
        list_expr _s1;
        list_expr _s2;
      };

      struct _Call3 {
        T1 _s0;
        list_expr _s1;
        list_expr _s2;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const list_expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename list_expr::LNil>(_sv.v())) {
            _result = f;
          } else if (std::holds_alternative<typename list_expr::LCons>(
                         _sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename list_expr::LCons>(_sv.v());
            _stack.emplace_back(_Call1{*(d_a1), d_a0});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else if (std::holds_alternative<typename list_expr::LAppend>(
                         _sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename list_expr::LAppend>(_sv.v());
            _stack.emplace_back(_Call2{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename list_expr::LReplicate>(_sv.v());
            _result = f2(d_a0, d_a1);
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _result = f0(_f._s1, _f._s0, _result);
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _stack.emplace_back(_Call3{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Call3>(_frame));
          _result = f1(_f._s2, _result, _f._s1, _f._s0);
        }
      }
      return _result;
    }

    template <typename T1, MapsTo<T1, unsigned int, list_expr, T1> F1,
              MapsTo<T1, list_expr, T1, list_expr, T1> F2,
              MapsTo<T1, unsigned int, unsigned int> F3>
    T1 list_expr_rect(const T1 f, F1 &&f0, F2 &&f1, F3 &&f2) const {
      const list_expr *_self = this;

      struct _Enter {
        const list_expr *_self;
      };

      struct _Call1 {
        list_expr _s0;
        unsigned int _s1;
      };

      struct _Call2 {
        list_expr *_s0;
        list_expr _s1;
        list_expr _s2;
      };

      struct _Call3 {
        T1 _s0;
        list_expr _s1;
        list_expr _s2;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const list_expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename list_expr::LNil>(_sv.v())) {
            _result = f;
          } else if (std::holds_alternative<typename list_expr::LCons>(
                         _sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename list_expr::LCons>(_sv.v());
            _stack.emplace_back(_Call1{*(d_a1), d_a0});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else if (std::holds_alternative<typename list_expr::LAppend>(
                         _sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename list_expr::LAppend>(_sv.v());
            _stack.emplace_back(_Call2{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename list_expr::LReplicate>(_sv.v());
            _result = f2(d_a0, d_a1);
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _result = f0(_f._s1, _f._s0, _result);
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _stack.emplace_back(_Call3{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Call3>(_frame));
          _result = f1(_f._s2, _result, _f._s1, _f._s0);
        }
      }
      return _result;
    }
  };
};

template <typename T1>
__attribute__((pure)) List<T1> ListDef::repeat(const T1 x,
                                               const unsigned int &n) {
  std::unique_ptr<List<T1>> _head{};
  std::unique_ptr<List<T1>> *_write = &_head;
  unsigned int _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      *(_write) = std::make_unique<List<T1>>(List<T1>::nil());
      break;
    } else {
      unsigned int k = _loop_n - 1;
      auto _cell =
          std::make_unique<List<T1>>(typename List<T1>::Cons(x, nullptr));
      *(_write) = std::move(_cell);
      _write = &std::get<typename List<T1>::Cons>((*_write)->v_mut()).d_a1;
      _loop_n = k;
      continue;
    }
  }
  return std::move(*(_head));
}

#endif // INCLUDED_LOOPIFY_EXPR_VARIANTS
