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

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

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

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  List clone() const {
    List _out{};

    struct _CloneFrame {
      const List *_src;
      List *_dst;
    };

    std::vector<_CloneFrame> _stack;
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List *_src = _frame._src;
      List *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        const auto &_alt = std::get<Nil>(_src->v());
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ =
            Cons{_alt.d_a0, _alt.d_a1 ? std::make_unique<List>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1)
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  static List<t_A> nil() { return List(Nil{}); }

  static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List>> _stack;
    auto _drain = [&](List &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
        if (_alt.d_a1)
          _stack.push_back(std::move(_alt.d_a1));
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node)
        _drain(*_node);
    }
  }

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }

  List<t_A> app(List<t_A> m) const {
    std::unique_ptr<List<t_A>> _head{};
    std::unique_ptr<List<t_A>> *_write = &_head;
    const List *_loop_self = this;
    List<t_A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *(_loop_self);
      if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
        *(_write) = std::make_unique<List<t_A>>(std::move(_loop_m));
        break;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
        auto _cell = std::make_unique<List<t_A>>(
            typename List<t_A>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename List<t_A>::Cons>((*_write)->v_mut()).d_a1;
        const List *_next_self = d_a1.get();
        List<t_A> _next_m = std::move(_loop_m);
        _loop_self = _next_self;
        _loop_m = std::move(_next_m);
        continue;
      }
    }
    return std::move(*(_head));
  }
};

struct ListDef {
  template <typename T1>
  static List<T1> repeat(const T1 x, const unsigned int &n);
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

    cond_expr &operator=(const cond_expr &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    cond_expr &operator=(cond_expr &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    cond_expr clone() const {
      cond_expr _out{};

      struct _CloneFrame {
        const cond_expr *_src;
        cond_expr *_dst;
      };

      std::vector<_CloneFrame> _stack;
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const cond_expr *_src = _frame._src;
        cond_expr *_dst = _frame._dst;
        if (std::holds_alternative<Lit>(_src->v())) {
          const auto &_alt = std::get<Lit>(_src->v());
          _dst->d_v_ = Lit{_alt.d_a0};
        } else if (std::holds_alternative<Add>(_src->v())) {
          const auto &_alt = std::get<Add>(_src->v());
          _dst->d_v_ = Add{_alt.d_a0 ? std::make_unique<cond_expr>() : nullptr,
                           _alt.d_a1 ? std::make_unique<cond_expr>() : nullptr};
          auto &_dst_alt = std::get<Add>(_dst->d_v_);
          if (_alt.d_a0)
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          if (_alt.d_a1)
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        } else {
          const auto &_alt = std::get<Cond>(_src->v());
          _dst->d_v_ =
              Cond{_alt.d_a0 ? std::make_unique<cond_expr>() : nullptr,
                   _alt.d_a1 ? std::make_unique<cond_expr>() : nullptr,
                   _alt.d_a2 ? std::make_unique<cond_expr>() : nullptr};
          auto &_dst_alt = std::get<Cond>(_dst->d_v_);
          if (_alt.d_a0)
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          if (_alt.d_a1)
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          if (_alt.d_a2)
            _stack.push_back({_alt.d_a2.get(), _dst_alt.d_a2.get()});
        }
      }
      return _out;
    }

    // CREATORS
    static cond_expr lit(unsigned int a0) {
      return cond_expr(Lit{std::move(a0)});
    }

    static cond_expr add(cond_expr a0, cond_expr a1) {
      return cond_expr(Add{std::make_unique<cond_expr>(std::move(a0)),
                           std::make_unique<cond_expr>(std::move(a1))});
    }

    static cond_expr cond(cond_expr a0, cond_expr a1, cond_expr a2) {
      return cond_expr(Cond{std::make_unique<cond_expr>(std::move(a0)),
                            std::make_unique<cond_expr>(std::move(a1)),
                            std::make_unique<cond_expr>(std::move(a2))});
    }

    // MANIPULATORS
    ~cond_expr() {
      std::vector<std::unique_ptr<cond_expr>> _stack;
      auto _drain = [&](cond_expr &_node) {
        if (std::holds_alternative<Add>(_node.d_v_)) {
          auto &_alt = std::get<Add>(_node.d_v_);
          if (_alt.d_a0)
            _stack.push_back(std::move(_alt.d_a0));
          if (_alt.d_a1)
            _stack.push_back(std::move(_alt.d_a1));
        }
        if (std::holds_alternative<Cond>(_node.d_v_)) {
          auto &_alt = std::get<Cond>(_node.d_v_);
          if (_alt.d_a0)
            _stack.push_back(std::move(_alt.d_a0));
          if (_alt.d_a1)
            _stack.push_back(std::move(_alt.d_a1));
          if (_alt.d_a2)
            _stack.push_back(std::move(_alt.d_a2));
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node)
          _drain(*_node);
      }
    }

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

    unsigned int size_cond() const {
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

    unsigned int eval_cond() const {
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
          _stack.emplace_back(
              _Call2{_result, std::move(_f._s1), std::move(_f._s2)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = f0(_f._s2, _result, _f._s1, _f._s0);
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          _stack.emplace_back(_Call4{_result, _f._s1, std::move(_f._s2),
                                     std::move(_f._s3), std::move(_f._s4)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call4>(_frame)) {
          auto _f = std::move(std::get<_Call4>(_frame));
          _stack.emplace_back(_Call5{_f._s0, _result, std::move(_f._s2),
                                     std::move(_f._s3), std::move(_f._s4)});
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
          _stack.emplace_back(
              _Call2{_result, std::move(_f._s1), std::move(_f._s2)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = f0(_f._s2, _result, _f._s1, _f._s0);
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          _stack.emplace_back(_Call4{_result, _f._s1, std::move(_f._s2),
                                     std::move(_f._s3), std::move(_f._s4)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call4>(_frame)) {
          auto _f = std::move(std::get<_Call4>(_frame));
          _stack.emplace_back(_Call5{_f._s0, _result, std::move(_f._s2),
                                     std::move(_f._s3), std::move(_f._s4)});
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

    arith_expr &operator=(const arith_expr &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    arith_expr &operator=(arith_expr &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    arith_expr clone() const {
      arith_expr _out{};

      struct _CloneFrame {
        const arith_expr *_src;
        arith_expr *_dst;
      };

      std::vector<_CloneFrame> _stack;
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const arith_expr *_src = _frame._src;
        arith_expr *_dst = _frame._dst;
        if (std::holds_alternative<ANum>(_src->v())) {
          const auto &_alt = std::get<ANum>(_src->v());
          _dst->d_v_ = ANum{_alt.d_a0};
        } else if (std::holds_alternative<AAdd>(_src->v())) {
          const auto &_alt = std::get<AAdd>(_src->v());
          _dst->d_v_ =
              AAdd{_alt.d_a0 ? std::make_unique<arith_expr>() : nullptr,
                   _alt.d_a1 ? std::make_unique<arith_expr>() : nullptr};
          auto &_dst_alt = std::get<AAdd>(_dst->d_v_);
          if (_alt.d_a0)
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          if (_alt.d_a1)
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        } else if (std::holds_alternative<AMul>(_src->v())) {
          const auto &_alt = std::get<AMul>(_src->v());
          _dst->d_v_ =
              AMul{_alt.d_a0 ? std::make_unique<arith_expr>() : nullptr,
                   _alt.d_a1 ? std::make_unique<arith_expr>() : nullptr};
          auto &_dst_alt = std::get<AMul>(_dst->d_v_);
          if (_alt.d_a0)
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          if (_alt.d_a1)
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        } else {
          const auto &_alt = std::get<ADiv>(_src->v());
          _dst->d_v_ =
              ADiv{_alt.d_a0 ? std::make_unique<arith_expr>() : nullptr,
                   _alt.d_a1 ? std::make_unique<arith_expr>() : nullptr};
          auto &_dst_alt = std::get<ADiv>(_dst->d_v_);
          if (_alt.d_a0)
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          if (_alt.d_a1)
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
      }
      return _out;
    }

    // CREATORS
    static arith_expr anum(unsigned int a0) {
      return arith_expr(ANum{std::move(a0)});
    }

    static arith_expr aadd(arith_expr a0, arith_expr a1) {
      return arith_expr(AAdd{std::make_unique<arith_expr>(std::move(a0)),
                             std::make_unique<arith_expr>(std::move(a1))});
    }

    static arith_expr amul(arith_expr a0, arith_expr a1) {
      return arith_expr(AMul{std::make_unique<arith_expr>(std::move(a0)),
                             std::make_unique<arith_expr>(std::move(a1))});
    }

    static arith_expr adiv(arith_expr a0, arith_expr a1) {
      return arith_expr(ADiv{std::make_unique<arith_expr>(std::move(a0)),
                             std::make_unique<arith_expr>(std::move(a1))});
    }

    // MANIPULATORS
    ~arith_expr() {
      std::vector<std::unique_ptr<arith_expr>> _stack;
      auto _drain = [&](arith_expr &_node) {
        if (std::holds_alternative<AAdd>(_node.d_v_)) {
          auto &_alt = std::get<AAdd>(_node.d_v_);
          if (_alt.d_a0)
            _stack.push_back(std::move(_alt.d_a0));
          if (_alt.d_a1)
            _stack.push_back(std::move(_alt.d_a1));
        }
        if (std::holds_alternative<AMul>(_node.d_v_)) {
          auto &_alt = std::get<AMul>(_node.d_v_);
          if (_alt.d_a0)
            _stack.push_back(std::move(_alt.d_a0));
          if (_alt.d_a1)
            _stack.push_back(std::move(_alt.d_a1));
        }
        if (std::holds_alternative<ADiv>(_node.d_v_)) {
          auto &_alt = std::get<ADiv>(_node.d_v_);
          if (_alt.d_a0)
            _stack.push_back(std::move(_alt.d_a0));
          if (_alt.d_a1)
            _stack.push_back(std::move(_alt.d_a1));
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node)
          _drain(*_node);
      }
    }

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

    unsigned int count_ops() const {
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

    unsigned int eval_arith() const {
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
          _stack.emplace_back(
              _Call2{_result, std::move(_f._s1), std::move(_f._s2)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = f0(_f._s2, _result, _f._s1, _f._s0);
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          _stack.emplace_back(
              _Call4{_result, std::move(_f._s1), std::move(_f._s2)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call4>(_frame)) {
          auto _f = std::move(std::get<_Call4>(_frame));
          _result = f1(_f._s2, _result, _f._s1, _f._s0);
        } else if (std::holds_alternative<_Call5>(_frame)) {
          auto _f = std::move(std::get<_Call5>(_frame));
          _stack.emplace_back(
              _Call6{_result, std::move(_f._s1), std::move(_f._s2)});
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
          _stack.emplace_back(
              _Call2{_result, std::move(_f._s1), std::move(_f._s2)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = f0(_f._s2, _result, _f._s1, _f._s0);
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          _stack.emplace_back(
              _Call4{_result, std::move(_f._s1), std::move(_f._s2)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call4>(_frame)) {
          auto _f = std::move(std::get<_Call4>(_frame));
          _result = f1(_f._s2, _result, _f._s1, _f._s0);
        } else if (std::holds_alternative<_Call5>(_frame)) {
          auto _f = std::move(std::get<_Call5>(_frame));
          _stack.emplace_back(
              _Call6{_result, std::move(_f._s1), std::move(_f._s2)});
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

    bool_expr &operator=(const bool_expr &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    bool_expr &operator=(bool_expr &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    bool_expr clone() const {
      bool_expr _out{};

      struct _CloneFrame {
        const bool_expr *_src;
        bool_expr *_dst;
      };

      std::vector<_CloneFrame> _stack;
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const bool_expr *_src = _frame._src;
        bool_expr *_dst = _frame._dst;
        if (std::holds_alternative<BTrue>(_src->v())) {
          const auto &_alt = std::get<BTrue>(_src->v());
          _dst->d_v_ = BTrue{};
        } else if (std::holds_alternative<BFalse>(_src->v())) {
          const auto &_alt = std::get<BFalse>(_src->v());
          _dst->d_v_ = BFalse{};
        } else if (std::holds_alternative<BAnd>(_src->v())) {
          const auto &_alt = std::get<BAnd>(_src->v());
          _dst->d_v_ =
              BAnd{_alt.d_a0 ? std::make_unique<bool_expr>() : nullptr,
                   _alt.d_a1 ? std::make_unique<bool_expr>() : nullptr};
          auto &_dst_alt = std::get<BAnd>(_dst->d_v_);
          if (_alt.d_a0)
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          if (_alt.d_a1)
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        } else if (std::holds_alternative<BOr>(_src->v())) {
          const auto &_alt = std::get<BOr>(_src->v());
          _dst->d_v_ = BOr{_alt.d_a0 ? std::make_unique<bool_expr>() : nullptr,
                           _alt.d_a1 ? std::make_unique<bool_expr>() : nullptr};
          auto &_dst_alt = std::get<BOr>(_dst->d_v_);
          if (_alt.d_a0)
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          if (_alt.d_a1)
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        } else {
          const auto &_alt = std::get<BNot>(_src->v());
          _dst->d_v_ =
              BNot{_alt.d_a0 ? std::make_unique<bool_expr>() : nullptr};
          auto &_dst_alt = std::get<BNot>(_dst->d_v_);
          if (_alt.d_a0)
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
        }
      }
      return _out;
    }

    // CREATORS
    static bool_expr btrue() { return bool_expr(BTrue{}); }

    static bool_expr bfalse() { return bool_expr(BFalse{}); }

    static bool_expr band(bool_expr a0, bool_expr a1) {
      return bool_expr(BAnd{std::make_unique<bool_expr>(std::move(a0)),
                            std::make_unique<bool_expr>(std::move(a1))});
    }

    static bool_expr bor(bool_expr a0, bool_expr a1) {
      return bool_expr(BOr{std::make_unique<bool_expr>(std::move(a0)),
                           std::make_unique<bool_expr>(std::move(a1))});
    }

    static bool_expr bnot(bool_expr a0) {
      return bool_expr(BNot{std::make_unique<bool_expr>(std::move(a0))});
    }

    // MANIPULATORS
    ~bool_expr() {
      std::vector<std::unique_ptr<bool_expr>> _stack;
      auto _drain = [&](bool_expr &_node) {
        if (std::holds_alternative<BAnd>(_node.d_v_)) {
          auto &_alt = std::get<BAnd>(_node.d_v_);
          if (_alt.d_a0)
            _stack.push_back(std::move(_alt.d_a0));
          if (_alt.d_a1)
            _stack.push_back(std::move(_alt.d_a1));
        }
        if (std::holds_alternative<BOr>(_node.d_v_)) {
          auto &_alt = std::get<BOr>(_node.d_v_);
          if (_alt.d_a0)
            _stack.push_back(std::move(_alt.d_a0));
          if (_alt.d_a1)
            _stack.push_back(std::move(_alt.d_a1));
        }
        if (std::holds_alternative<BNot>(_node.d_v_)) {
          auto &_alt = std::get<BNot>(_node.d_v_);
          if (_alt.d_a0)
            _stack.push_back(std::move(_alt.d_a0));
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node)
          _drain(*_node);
      }
    }

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

    bool_expr simplify_bool() const {
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
            return bool_expr::band(std::move(a_),
                                   bool_expr::band(*(d_a01), *(d_a11)));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _sv1.v())) {
            const auto &[d_a01, d_a11] =
                std::get<typename bool_expr::BOr>(_sv1.v());
            return bool_expr::band(std::move(a_),
                                   bool_expr::bor(*(d_a01), *(d_a11)));
          } else {
            const auto &[d_a01] = std::get<typename bool_expr::BNot>(_sv1.v());
            return bool_expr::band(std::move(a_), bool_expr::bnot(*(d_a01)));
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
            return bool_expr::band(std::move(a_),
                                   bool_expr::band(*(d_a01), *(d_a11)));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _sv1.v())) {
            const auto &[d_a01, d_a11] =
                std::get<typename bool_expr::BOr>(_sv1.v());
            return bool_expr::band(std::move(a_),
                                   bool_expr::bor(*(d_a01), *(d_a11)));
          } else {
            const auto &[d_a01] = std::get<typename bool_expr::BNot>(_sv1.v());
            return bool_expr::band(std::move(a_), bool_expr::bnot(*(d_a01)));
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
            return bool_expr::band(std::move(a_),
                                   bool_expr::band(*(d_a01), *(d_a11)));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _sv1.v())) {
            const auto &[d_a01, d_a11] =
                std::get<typename bool_expr::BOr>(_sv1.v());
            return bool_expr::band(std::move(a_),
                                   bool_expr::bor(*(d_a01), *(d_a11)));
          } else {
            const auto &[d_a01] = std::get<typename bool_expr::BNot>(_sv1.v());
            return bool_expr::band(std::move(a_), bool_expr::bnot(*(d_a01)));
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
            return bool_expr::bor(std::move(a_),
                                  bool_expr::band(*(d_a01), *(d_a11)));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _sv1.v())) {
            const auto &[d_a01, d_a11] =
                std::get<typename bool_expr::BOr>(_sv1.v());
            return bool_expr::bor(std::move(a_),
                                  bool_expr::bor(*(d_a01), *(d_a11)));
          } else {
            const auto &[d_a01] = std::get<typename bool_expr::BNot>(_sv1.v());
            return bool_expr::bor(std::move(a_), bool_expr::bnot(*(d_a01)));
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
            return bool_expr::bor(std::move(a_),
                                  bool_expr::band(*(d_a01), *(d_a11)));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _sv1.v())) {
            const auto &[d_a01, d_a11] =
                std::get<typename bool_expr::BOr>(_sv1.v());
            return bool_expr::bor(std::move(a_),
                                  bool_expr::bor(*(d_a01), *(d_a11)));
          } else {
            const auto &[d_a01] = std::get<typename bool_expr::BNot>(_sv1.v());
            return bool_expr::bor(std::move(a_), bool_expr::bnot(*(d_a01)));
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
            return bool_expr::bor(std::move(a_),
                                  bool_expr::band(*(d_a01), *(d_a11)));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _sv1.v())) {
            const auto &[d_a01, d_a11] =
                std::get<typename bool_expr::BOr>(_sv1.v());
            return bool_expr::bor(std::move(a_),
                                  bool_expr::bor(*(d_a01), *(d_a11)));
          } else {
            const auto &[d_a01] = std::get<typename bool_expr::BNot>(_sv1.v());
            return bool_expr::bor(std::move(a_), bool_expr::bnot(*(d_a01)));
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

    bool eval_bool() const {
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
          _stack.emplace_back(
              _Call2{_result, std::move(_f._s1), std::move(_f._s2)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = f1(_f._s2, _result, _f._s1, _f._s0);
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          _stack.emplace_back(
              _Call4{_result, std::move(_f._s1), std::move(_f._s2)});
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
          _stack.emplace_back(
              _Call2{_result, std::move(_f._s1), std::move(_f._s2)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = f1(_f._s2, _result, _f._s1, _f._s0);
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          _stack.emplace_back(
              _Call4{_result, std::move(_f._s1), std::move(_f._s2)});
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

    list_expr &operator=(const list_expr &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    list_expr &operator=(list_expr &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    list_expr clone() const {
      list_expr _out{};

      struct _CloneFrame {
        const list_expr *_src;
        list_expr *_dst;
      };

      std::vector<_CloneFrame> _stack;
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const list_expr *_src = _frame._src;
        list_expr *_dst = _frame._dst;
        if (std::holds_alternative<LNil>(_src->v())) {
          const auto &_alt = std::get<LNil>(_src->v());
          _dst->d_v_ = LNil{};
        } else if (std::holds_alternative<LCons>(_src->v())) {
          const auto &_alt = std::get<LCons>(_src->v());
          _dst->d_v_ = LCons{
              _alt.d_a0, _alt.d_a1 ? std::make_unique<list_expr>() : nullptr};
          auto &_dst_alt = std::get<LCons>(_dst->d_v_);
          if (_alt.d_a1)
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        } else if (std::holds_alternative<LAppend>(_src->v())) {
          const auto &_alt = std::get<LAppend>(_src->v());
          _dst->d_v_ =
              LAppend{_alt.d_a0 ? std::make_unique<list_expr>() : nullptr,
                      _alt.d_a1 ? std::make_unique<list_expr>() : nullptr};
          auto &_dst_alt = std::get<LAppend>(_dst->d_v_);
          if (_alt.d_a0)
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          if (_alt.d_a1)
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        } else {
          const auto &_alt = std::get<LReplicate>(_src->v());
          _dst->d_v_ = LReplicate{_alt.d_a0, _alt.d_a1};
        }
      }
      return _out;
    }

    // CREATORS
    static list_expr lnil() { return list_expr(LNil{}); }

    static list_expr lcons(unsigned int a0, list_expr a1) {
      return list_expr(
          LCons{std::move(a0), std::make_unique<list_expr>(std::move(a1))});
    }

    static list_expr lappend(list_expr a0, list_expr a1) {
      return list_expr(LAppend{std::make_unique<list_expr>(std::move(a0)),
                               std::make_unique<list_expr>(std::move(a1))});
    }

    static list_expr lreplicate(unsigned int a0, unsigned int a1) {
      return list_expr(LReplicate{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    ~list_expr() {
      std::vector<std::unique_ptr<list_expr>> _stack;
      auto _drain = [&](list_expr &_node) {
        if (std::holds_alternative<LCons>(_node.d_v_)) {
          auto &_alt = std::get<LCons>(_node.d_v_);
          if (_alt.d_a1)
            _stack.push_back(std::move(_alt.d_a1));
        }
        if (std::holds_alternative<LAppend>(_node.d_v_)) {
          auto &_alt = std::get<LAppend>(_node.d_v_);
          if (_alt.d_a0)
            _stack.push_back(std::move(_alt.d_a0));
          if (_alt.d_a1)
            _stack.push_back(std::move(_alt.d_a1));
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node)
          _drain(*_node);
      }
    }

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

    unsigned int list_expr_size() const {
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

    List<unsigned int> eval_list() const {
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
          _stack.emplace_back(_Call3{std::move(_result)});
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
          _stack.emplace_back(
              _Call3{_result, std::move(_f._s1), std::move(_f._s2)});
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
          _stack.emplace_back(
              _Call3{_result, std::move(_f._s1), std::move(_f._s2)});
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
List<T1> ListDef::repeat(const T1 x, const unsigned int &n) {
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
