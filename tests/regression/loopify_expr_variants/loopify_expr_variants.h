#ifndef INCLUDED_LOOPIFY_EXPR_VARIANTS
#define INCLUDED_LOOPIFY_EXPR_VARIANTS

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
    std::unique_ptr<List<A>> l;
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
        _dst->v_ = Cons{_alt.a, _alt.l ? std::make_unique<List<A>>() : nullptr};
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
      this->v_ = Cons{A(a), l ? std::make_unique<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_unique<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
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

  List<A> app(List<A> m) const {
    std::unique_ptr<List<A>> _head{};
    std::unique_ptr<List<A>> *_write = &_head;
    const List *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = std::make_unique<List<A>>(std::move(_loop_m));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell =
            std::make_unique<List<A>>(typename List<A>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<A>::Cons>((*_write)->v_mut()).l;
        _loop_self = a1.get();
        continue;
      }
    }
    return std::move(*_head);
  }
};

struct ListDef {
  template <typename T1> static List<T1> repeat(T1 x, uint64_t n);
};

struct LoopifyExprVariants {
  struct cond_expr {
    // TYPES
    struct Lit {
      uint64_t a0;
    };

    struct Add {
      std::unique_ptr<cond_expr> a0;
      std::unique_ptr<cond_expr> a1;
    };

    struct Cond {
      std::unique_ptr<cond_expr> a0;
      std::unique_ptr<cond_expr> a1;
      std::unique_ptr<cond_expr> a2;
    };

    using variant_t = std::variant<Lit, Add, Cond>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    cond_expr() {}

    explicit cond_expr(Lit _v) : v_(std::move(_v)) {}

    explicit cond_expr(Add _v) : v_(std::move(_v)) {}

    explicit cond_expr(Cond _v) : v_(std::move(_v)) {}

    cond_expr(const cond_expr &_other) : v_(std::move(_other.clone().v_)) {}

    cond_expr(cond_expr &&_other) noexcept : v_(std::move(_other.v_)) {}

    cond_expr &operator=(const cond_expr &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    cond_expr &operator=(cond_expr &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    cond_expr clone() const {
      cond_expr _out{};

      struct _CloneFrame {
        const cond_expr *_src;
        cond_expr *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const cond_expr *_src = _frame._src;
        cond_expr *_dst = _frame._dst;
        if (std::holds_alternative<Lit>(_src->v())) {
          const auto &_alt = std::get<Lit>(_src->v());
          _dst->v_ = Lit{_alt.a0};
        } else if (std::holds_alternative<Add>(_src->v())) {
          const auto &_alt = std::get<Add>(_src->v());
          _dst->v_ = Add{_alt.a0 ? std::make_unique<cond_expr>() : nullptr,
                         _alt.a1 ? std::make_unique<cond_expr>() : nullptr};
          auto &_dst_alt = std::get<Add>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        } else {
          const auto &_alt = std::get<Cond>(_src->v());
          _dst->v_ = Cond{_alt.a0 ? std::make_unique<cond_expr>() : nullptr,
                          _alt.a1 ? std::make_unique<cond_expr>() : nullptr,
                          _alt.a2 ? std::make_unique<cond_expr>() : nullptr};
          auto &_dst_alt = std::get<Cond>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
          if (_alt.a2) {
            _stack.push_back({_alt.a2.get(), _dst_alt.a2.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static cond_expr lit(uint64_t a0) { return cond_expr(Lit{a0}); }

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
      std::vector<std::unique_ptr<cond_expr>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](cond_expr &_node) {
        if (std::holds_alternative<Add>(_node.v_)) {
          auto &_alt = std::get<Add>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
        }
        if (std::holds_alternative<Cond>(_node.v_)) {
          auto &_alt = std::get<Cond>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
          if (_alt.a2) {
            _stack.push_back(std::move(_alt.a2));
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

    uint64_t size_cond() const {
      const cond_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const cond_expr *_self;
      };

      /// _After_Add: saves [_s0, _s1], dispatches next recursive call.
      struct _After_Add {
        cond_expr *_s0;
        decltype(UINT64_C(1)) _s1;
      };

      /// _After_Cond: saves [_s0, _s1, _s2], dispatches next recursive call.
      struct _After_Cond {
        const cond_expr *_s0;
        const cond_expr *_s1;
        decltype(UINT64_C(1)) _s2;
      };

      /// _After_Cond_1: saves [_result, _s1, _s2], dispatches next recursive
      /// call.
      struct _After_Cond_1 {
        uint64_t _result;
        const cond_expr *_s1;
        decltype(UINT64_C(1)) _s2;
      };

      /// _Combine_Add: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Add {
        uint64_t _result;
        decltype(UINT64_C(1)) _s1;
      };

      /// _Combine_Cond: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Cond {
        uint64_t _result_0;
        uint64_t _result_1;
        decltype(UINT64_C(1)) _s2;
      };

      using _Frame = std::variant<_Enter, _After_Add, _After_Cond,
                                  _After_Cond_1, _Combine_Add, _Combine_Cond>;
      uint64_t _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified size_cond: _Enter -> _After_Add -> _After_Cond ->
      /// _After_Cond_1 -> _Combine_Add -> _Combine_Cond.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const cond_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename cond_expr::Lit>(_sv.v())) {
            _result = UINT64_C(1);
          } else if (std::holds_alternative<typename cond_expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename cond_expr::Add>(_sv.v());
            _stack.emplace_back(_After_Add{a0.get(), UINT64_C(1)});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename cond_expr::Cond>(_sv.v());
            _stack.emplace_back(_After_Cond{a1.get(), a0.get(), UINT64_C(1)});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_Add>(_frame)) {
          auto _f = std::move(std::get<_After_Add>(_frame));
          _stack.emplace_back(_Combine_Add{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_Cond>(_frame)) {
          auto _f = std::move(std::get<_After_Cond>(_frame));
          _stack.emplace_back(_After_Cond_1{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_Cond_1>(_frame)) {
          auto _f = std::move(std::get<_After_Cond_1>(_frame));
          _stack.emplace_back(_Combine_Cond{_f._result, _result, _f._s2});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_Combine_Add>(_frame)) {
          auto _f = std::move(std::get<_Combine_Add>(_frame));
          _result = ((_f._s1 + std::move(_result)) + std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Combine_Cond>(_frame));
          _result = (((_f._s2 + _result) + _f._result_1) + _f._result_0);
        }
      }
      return _result;
    }

    uint64_t eval_cond() const {
      const cond_expr *_self = this;
      auto &&_sv = *_self;
      if (std::holds_alternative<typename cond_expr::Lit>(_sv.v())) {
        const auto &[a0] = std::get<typename cond_expr::Lit>(_sv.v());
        return a0;
      } else if (std::holds_alternative<typename cond_expr::Add>(_sv.v())) {
        const auto &[a0, a1] = std::get<typename cond_expr::Add>(_sv.v());
        return (a0->eval_cond() + a1->eval_cond());
      } else {
        const auto &[a0, a1, a2] = std::get<typename cond_expr::Cond>(_sv.v());
        if (UINT64_C(0) < a0->eval_cond()) {
          return a1->eval_cond();
        } else {
          return a2->eval_cond();
        }
      }
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, cond_expr &, T1 &, cond_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F2 &, cond_expr &, T1 &, cond_expr &,
                                     T1 &, cond_expr &, T1 &>
    T1 cond_expr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      const cond_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const cond_expr *_self;
      };

      /// _After_Add: saves [_s0, a1, a0], dispatches next recursive call.
      struct _After_Add {
        cond_expr *_s0;
        cond_expr a1;
        cond_expr a0;
      };

      /// _After_Cond: saves [_s0, _s1, a2, a1, a0], dispatches next recursive
      /// call.
      struct _After_Cond {
        const cond_expr *_s0;
        const cond_expr *_s1;
        cond_expr a2;
        cond_expr a1;
        cond_expr a0;
      };

      /// _After_Cond_1: saves [_result, _s1, a2, a1, a0], dispatches next
      /// recursive call.
      struct _After_Cond_1 {
        T1 _result;
        const cond_expr *_s1;
        cond_expr a2;
        cond_expr a1;
        cond_expr a0;
      };

      /// _Combine_Add: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Add {
        T1 _result;
        cond_expr a1;
        cond_expr a0;
      };

      /// _Combine_Cond: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Cond {
        T1 _result_0;
        T1 _result_1;
        cond_expr a2;
        cond_expr a1;
        cond_expr a0;
      };

      using _Frame = std::variant<_Enter, _After_Add, _After_Cond,
                                  _After_Cond_1, _Combine_Add, _Combine_Cond>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified cond_expr_rec: _Enter -> _After_Add -> _After_Cond ->
      /// _After_Cond_1 -> _Combine_Add -> _Combine_Cond.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const cond_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename cond_expr::Lit>(_sv.v())) {
            const auto &[a0] = std::get<typename cond_expr::Lit>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename cond_expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename cond_expr::Add>(_sv.v());
            _stack.emplace_back(_After_Add{a0.get(), *a1, *a0});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename cond_expr::Cond>(_sv.v());
            _stack.emplace_back(_After_Cond{a1.get(), a0.get(), *a2, *a1, *a0});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_Add>(_frame)) {
          auto _f = std::move(std::get<_After_Add>(_frame));
          _stack.emplace_back(
              _Combine_Add{_result, std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_Cond>(_frame)) {
          auto _f = std::move(std::get<_After_Cond>(_frame));
          _stack.emplace_back(_After_Cond_1{_result, _f._s1, std::move(_f.a2),
                                            std::move(_f.a1),
                                            std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_Cond_1>(_frame)) {
          auto _f = std::move(std::get<_After_Cond_1>(_frame));
          _stack.emplace_back(_Combine_Cond{_f._result, _result,
                                            std::move(_f.a2), std::move(_f.a1),
                                            std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_Combine_Add>(_frame)) {
          auto _f = std::move(std::get<_Combine_Add>(_frame));
          _result = f0(_f.a0, std::move(_result), _f.a1, std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Combine_Cond>(_frame));
          _result =
              f1(_f.a0, _result, _f.a1, _f._result_1, _f.a2, _f._result_0);
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, cond_expr &, T1 &, cond_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F2 &, cond_expr &, T1 &, cond_expr &,
                                     T1 &, cond_expr &, T1 &>
    T1 cond_expr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      const cond_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const cond_expr *_self;
      };

      /// _After_Add: saves [_s0, a1, a0], dispatches next recursive call.
      struct _After_Add {
        cond_expr *_s0;
        cond_expr a1;
        cond_expr a0;
      };

      /// _After_Cond: saves [_s0, _s1, a2, a1, a0], dispatches next recursive
      /// call.
      struct _After_Cond {
        const cond_expr *_s0;
        const cond_expr *_s1;
        cond_expr a2;
        cond_expr a1;
        cond_expr a0;
      };

      /// _After_Cond_1: saves [_result, _s1, a2, a1, a0], dispatches next
      /// recursive call.
      struct _After_Cond_1 {
        T1 _result;
        const cond_expr *_s1;
        cond_expr a2;
        cond_expr a1;
        cond_expr a0;
      };

      /// _Combine_Add: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Add {
        T1 _result;
        cond_expr a1;
        cond_expr a0;
      };

      /// _Combine_Cond: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Cond {
        T1 _result_0;
        T1 _result_1;
        cond_expr a2;
        cond_expr a1;
        cond_expr a0;
      };

      using _Frame = std::variant<_Enter, _After_Add, _After_Cond,
                                  _After_Cond_1, _Combine_Add, _Combine_Cond>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified cond_expr_rect: _Enter -> _After_Add -> _After_Cond ->
      /// _After_Cond_1 -> _Combine_Add -> _Combine_Cond.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const cond_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename cond_expr::Lit>(_sv.v())) {
            const auto &[a0] = std::get<typename cond_expr::Lit>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename cond_expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename cond_expr::Add>(_sv.v());
            _stack.emplace_back(_After_Add{a0.get(), *a1, *a0});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename cond_expr::Cond>(_sv.v());
            _stack.emplace_back(_After_Cond{a1.get(), a0.get(), *a2, *a1, *a0});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_Add>(_frame)) {
          auto _f = std::move(std::get<_After_Add>(_frame));
          _stack.emplace_back(
              _Combine_Add{_result, std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_Cond>(_frame)) {
          auto _f = std::move(std::get<_After_Cond>(_frame));
          _stack.emplace_back(_After_Cond_1{_result, _f._s1, std::move(_f.a2),
                                            std::move(_f.a1),
                                            std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_Cond_1>(_frame)) {
          auto _f = std::move(std::get<_After_Cond_1>(_frame));
          _stack.emplace_back(_Combine_Cond{_f._result, _result,
                                            std::move(_f.a2), std::move(_f.a1),
                                            std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_Combine_Add>(_frame)) {
          auto _f = std::move(std::get<_Combine_Add>(_frame));
          _result = f0(_f.a0, std::move(_result), _f.a1, std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Combine_Cond>(_frame));
          _result =
              f1(_f.a0, _result, _f.a1, _f._result_1, _f.a2, _f._result_0);
        }
      }
      return _result;
    }
  };

  struct arith_expr {
    // TYPES
    struct ANum {
      uint64_t a0;
    };

    struct AAdd {
      std::unique_ptr<arith_expr> a0;
      std::unique_ptr<arith_expr> a1;
    };

    struct AMul {
      std::unique_ptr<arith_expr> a0;
      std::unique_ptr<arith_expr> a1;
    };

    struct ADiv {
      std::unique_ptr<arith_expr> a0;
      std::unique_ptr<arith_expr> a1;
    };

    using variant_t = std::variant<ANum, AAdd, AMul, ADiv>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    arith_expr() {}

    explicit arith_expr(ANum _v) : v_(std::move(_v)) {}

    explicit arith_expr(AAdd _v) : v_(std::move(_v)) {}

    explicit arith_expr(AMul _v) : v_(std::move(_v)) {}

    explicit arith_expr(ADiv _v) : v_(std::move(_v)) {}

    arith_expr(const arith_expr &_other) : v_(std::move(_other.clone().v_)) {}

    arith_expr(arith_expr &&_other) noexcept : v_(std::move(_other.v_)) {}

    arith_expr &operator=(const arith_expr &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    arith_expr &operator=(arith_expr &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    arith_expr clone() const {
      arith_expr _out{};

      struct _CloneFrame {
        const arith_expr *_src;
        arith_expr *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const arith_expr *_src = _frame._src;
        arith_expr *_dst = _frame._dst;
        if (std::holds_alternative<ANum>(_src->v())) {
          const auto &_alt = std::get<ANum>(_src->v());
          _dst->v_ = ANum{_alt.a0};
        } else if (std::holds_alternative<AAdd>(_src->v())) {
          const auto &_alt = std::get<AAdd>(_src->v());
          _dst->v_ = AAdd{_alt.a0 ? std::make_unique<arith_expr>() : nullptr,
                          _alt.a1 ? std::make_unique<arith_expr>() : nullptr};
          auto &_dst_alt = std::get<AAdd>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        } else if (std::holds_alternative<AMul>(_src->v())) {
          const auto &_alt = std::get<AMul>(_src->v());
          _dst->v_ = AMul{_alt.a0 ? std::make_unique<arith_expr>() : nullptr,
                          _alt.a1 ? std::make_unique<arith_expr>() : nullptr};
          auto &_dst_alt = std::get<AMul>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        } else {
          const auto &_alt = std::get<ADiv>(_src->v());
          _dst->v_ = ADiv{_alt.a0 ? std::make_unique<arith_expr>() : nullptr,
                          _alt.a1 ? std::make_unique<arith_expr>() : nullptr};
          auto &_dst_alt = std::get<ADiv>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static arith_expr anum(uint64_t a0) { return arith_expr(ANum{a0}); }

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
      std::vector<std::unique_ptr<arith_expr>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](arith_expr &_node) {
        if (std::holds_alternative<AAdd>(_node.v_)) {
          auto &_alt = std::get<AAdd>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
        }
        if (std::holds_alternative<AMul>(_node.v_)) {
          auto &_alt = std::get<AMul>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
        }
        if (std::holds_alternative<ADiv>(_node.v_)) {
          auto &_alt = std::get<ADiv>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
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

    uint64_t count_ops() const {
      const arith_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const arith_expr *_self;
      };

      /// _After_AAdd: saves [_s0, _s1], dispatches next recursive call.
      struct _After_AAdd {
        arith_expr *_s0;
        decltype(UINT64_C(1)) _s1;
      };

      /// _After_ADiv: saves [_s0, _s1], dispatches next recursive call.
      struct _After_ADiv {
        arith_expr *_s0;
        decltype(UINT64_C(1)) _s1;
      };

      /// _After_AMul: saves [_s0, _s1], dispatches next recursive call.
      struct _After_AMul {
        arith_expr *_s0;
        decltype(UINT64_C(1)) _s1;
      };

      /// _Combine_AAdd: receives partial results, combines with _result from
      /// final call.
      struct _Combine_AAdd {
        uint64_t _result;
        decltype(UINT64_C(1)) _s1;
      };

      /// _Combine_ADiv: receives partial results, combines with _result from
      /// final call.
      struct _Combine_ADiv {
        uint64_t _result;
        decltype(UINT64_C(1)) _s1;
      };

      /// _Combine_AMul: receives partial results, combines with _result from
      /// final call.
      struct _Combine_AMul {
        uint64_t _result;
        decltype(UINT64_C(1)) _s1;
      };

      using _Frame = std::variant<_Enter, _After_AAdd, _After_ADiv, _After_AMul,
                                  _Combine_AAdd, _Combine_ADiv, _Combine_AMul>;
      uint64_t _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified count_ops: _Enter -> _After_AAdd -> _After_ADiv ->
      /// _After_AMul -> _Combine_AAdd -> _Combine_ADiv -> _Combine_AMul.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const arith_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename arith_expr::ANum>(_sv.v())) {
            _result = UINT64_C(0);
          } else if (std::holds_alternative<typename arith_expr::AAdd>(
                         _sv.v())) {
            const auto &[a0, a1] = std::get<typename arith_expr::AAdd>(_sv.v());
            _stack.emplace_back(_After_AAdd{a0.get(), UINT64_C(1)});
            _stack.emplace_back(_Enter{a1.get()});
          } else if (std::holds_alternative<typename arith_expr::AMul>(
                         _sv.v())) {
            const auto &[a0, a1] = std::get<typename arith_expr::AMul>(_sv.v());
            _stack.emplace_back(_After_AMul{a0.get(), UINT64_C(1)});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            const auto &[a0, a1] = std::get<typename arith_expr::ADiv>(_sv.v());
            _stack.emplace_back(_After_ADiv{a0.get(), UINT64_C(1)});
            _stack.emplace_back(_Enter{a1.get()});
          }
        } else if (std::holds_alternative<_After_AAdd>(_frame)) {
          auto _f = std::move(std::get<_After_AAdd>(_frame));
          _stack.emplace_back(_Combine_AAdd{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_ADiv>(_frame)) {
          auto _f = std::move(std::get<_After_ADiv>(_frame));
          _stack.emplace_back(_Combine_ADiv{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_AMul>(_frame)) {
          auto _f = std::move(std::get<_After_AMul>(_frame));
          _stack.emplace_back(_Combine_AMul{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Combine_AAdd>(_frame)) {
          auto _f = std::move(std::get<_Combine_AAdd>(_frame));
          _result = ((_f._s1 + std::move(_result)) + std::move(_f._result));
        } else if (std::holds_alternative<_Combine_ADiv>(_frame)) {
          auto _f = std::move(std::get<_Combine_ADiv>(_frame));
          _result = ((_f._s1 + std::move(_result)) + std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Combine_AMul>(_frame));
          _result = ((_f._s1 + std::move(_result)) + std::move(_f._result));
        }
      }
      return _result;
    }

    uint64_t eval_arith() const {
      const arith_expr *_self = this;
      auto &&_sv = *_self;
      if (std::holds_alternative<typename arith_expr::ANum>(_sv.v())) {
        const auto &[a0] = std::get<typename arith_expr::ANum>(_sv.v());
        return a0;
      } else if (std::holds_alternative<typename arith_expr::AAdd>(_sv.v())) {
        const auto &[a0, a1] = std::get<typename arith_expr::AAdd>(_sv.v());
        return (a0->eval_arith() + a1->eval_arith());
      } else if (std::holds_alternative<typename arith_expr::AMul>(_sv.v())) {
        const auto &[a0, a1] = std::get<typename arith_expr::AMul>(_sv.v());
        return (a0->eval_arith() * a1->eval_arith());
      } else {
        const auto &[a0, a1] = std::get<typename arith_expr::ADiv>(_sv.v());
        auto _cs = a1->eval_arith();
        if (_cs <= 0) {
          return UINT64_C(0);
        } else {
          uint64_t n = _cs - 1;
          return ((n + 1) ? a0->eval_arith() / (n + 1) : 0);
        }
      }
    }

    template <typename T1, typename F0, typename F1, typename F2, typename F3>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, arith_expr &, T1 &, arith_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F2 &, arith_expr &, T1 &, arith_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F3 &, arith_expr &, T1 &, arith_expr &,
                                     T1 &>
    T1 arith_expr_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2) const {
      const arith_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const arith_expr *_self;
      };

      /// _After_AAdd: saves [_s0, a3, a2], dispatches next recursive call.
      struct _After_AAdd {
        arith_expr *_s0;
        arith_expr a3;
        arith_expr a2;
      };

      /// _After_ADiv: saves [_s0, a3, a2], dispatches next recursive call.
      struct _After_ADiv {
        arith_expr *_s0;
        arith_expr a3;
        arith_expr a2;
      };

      /// _After_AMul: saves [_s0, a3, a2], dispatches next recursive call.
      struct _After_AMul {
        arith_expr *_s0;
        arith_expr a3;
        arith_expr a2;
      };

      /// _Combine_AAdd: receives partial results, combines with _result from
      /// final call.
      struct _Combine_AAdd {
        T1 _result;
        arith_expr a3;
        arith_expr a2;
      };

      /// _Combine_ADiv: receives partial results, combines with _result from
      /// final call.
      struct _Combine_ADiv {
        T1 _result;
        arith_expr a3;
        arith_expr a2;
      };

      /// _Combine_AMul: receives partial results, combines with _result from
      /// final call.
      struct _Combine_AMul {
        T1 _result;
        arith_expr a3;
        arith_expr a2;
      };

      using _Frame = std::variant<_Enter, _After_AAdd, _After_ADiv, _After_AMul,
                                  _Combine_AAdd, _Combine_ADiv, _Combine_AMul>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified arith_expr_rec: _Enter -> _After_AAdd -> _After_ADiv ->
      /// _After_AMul -> _Combine_AAdd -> _Combine_ADiv -> _Combine_AMul.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const arith_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename arith_expr::ANum>(_sv.v())) {
            const auto &[a0] = std::get<typename arith_expr::ANum>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename arith_expr::AAdd>(
                         _sv.v())) {
            const auto &[a2, a3] = std::get<typename arith_expr::AAdd>(_sv.v());
            _stack.emplace_back(_After_AAdd{a2.get(), *a3, *a2});
            _stack.emplace_back(_Enter{a3.get()});
          } else if (std::holds_alternative<typename arith_expr::AMul>(
                         _sv.v())) {
            const auto &[a2, a3] = std::get<typename arith_expr::AMul>(_sv.v());
            _stack.emplace_back(_After_AMul{a2.get(), *a3, *a2});
            _stack.emplace_back(_Enter{a3.get()});
          } else {
            const auto &[a2, a3] = std::get<typename arith_expr::ADiv>(_sv.v());
            _stack.emplace_back(_After_ADiv{a2.get(), *a3, *a2});
            _stack.emplace_back(_Enter{a3.get()});
          }
        } else if (std::holds_alternative<_After_AAdd>(_frame)) {
          auto _f = std::move(std::get<_After_AAdd>(_frame));
          _stack.emplace_back(
              _Combine_AAdd{_result, std::move(_f.a3), std::move(_f.a2)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_ADiv>(_frame)) {
          auto _f = std::move(std::get<_After_ADiv>(_frame));
          _stack.emplace_back(
              _Combine_ADiv{_result, std::move(_f.a3), std::move(_f.a2)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_AMul>(_frame)) {
          auto _f = std::move(std::get<_After_AMul>(_frame));
          _stack.emplace_back(
              _Combine_AMul{_result, std::move(_f.a3), std::move(_f.a2)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Combine_AAdd>(_frame)) {
          auto _f = std::move(std::get<_Combine_AAdd>(_frame));
          _result = f0(_f.a2, std::move(_result), _f.a3, std::move(_f._result));
        } else if (std::holds_alternative<_Combine_ADiv>(_frame)) {
          auto _f = std::move(std::get<_Combine_ADiv>(_frame));
          _result = f2(_f.a2, std::move(_result), _f.a3, std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Combine_AMul>(_frame));
          _result = f1(_f.a2, std::move(_result), _f.a3, std::move(_f._result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2, typename F3>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, arith_expr &, T1 &, arith_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F2 &, arith_expr &, T1 &, arith_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F3 &, arith_expr &, T1 &, arith_expr &,
                                     T1 &>
    T1 arith_expr_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2) const {
      const arith_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const arith_expr *_self;
      };

      /// _After_AAdd: saves [_s0, a3, a2], dispatches next recursive call.
      struct _After_AAdd {
        arith_expr *_s0;
        arith_expr a3;
        arith_expr a2;
      };

      /// _After_ADiv: saves [_s0, a3, a2], dispatches next recursive call.
      struct _After_ADiv {
        arith_expr *_s0;
        arith_expr a3;
        arith_expr a2;
      };

      /// _After_AMul: saves [_s0, a3, a2], dispatches next recursive call.
      struct _After_AMul {
        arith_expr *_s0;
        arith_expr a3;
        arith_expr a2;
      };

      /// _Combine_AAdd: receives partial results, combines with _result from
      /// final call.
      struct _Combine_AAdd {
        T1 _result;
        arith_expr a3;
        arith_expr a2;
      };

      /// _Combine_ADiv: receives partial results, combines with _result from
      /// final call.
      struct _Combine_ADiv {
        T1 _result;
        arith_expr a3;
        arith_expr a2;
      };

      /// _Combine_AMul: receives partial results, combines with _result from
      /// final call.
      struct _Combine_AMul {
        T1 _result;
        arith_expr a3;
        arith_expr a2;
      };

      using _Frame = std::variant<_Enter, _After_AAdd, _After_ADiv, _After_AMul,
                                  _Combine_AAdd, _Combine_ADiv, _Combine_AMul>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified arith_expr_rect: _Enter -> _After_AAdd -> _After_ADiv ->
      /// _After_AMul -> _Combine_AAdd -> _Combine_ADiv -> _Combine_AMul.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const arith_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename arith_expr::ANum>(_sv.v())) {
            const auto &[a0] = std::get<typename arith_expr::ANum>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename arith_expr::AAdd>(
                         _sv.v())) {
            const auto &[a2, a3] = std::get<typename arith_expr::AAdd>(_sv.v());
            _stack.emplace_back(_After_AAdd{a2.get(), *a3, *a2});
            _stack.emplace_back(_Enter{a3.get()});
          } else if (std::holds_alternative<typename arith_expr::AMul>(
                         _sv.v())) {
            const auto &[a2, a3] = std::get<typename arith_expr::AMul>(_sv.v());
            _stack.emplace_back(_After_AMul{a2.get(), *a3, *a2});
            _stack.emplace_back(_Enter{a3.get()});
          } else {
            const auto &[a2, a3] = std::get<typename arith_expr::ADiv>(_sv.v());
            _stack.emplace_back(_After_ADiv{a2.get(), *a3, *a2});
            _stack.emplace_back(_Enter{a3.get()});
          }
        } else if (std::holds_alternative<_After_AAdd>(_frame)) {
          auto _f = std::move(std::get<_After_AAdd>(_frame));
          _stack.emplace_back(
              _Combine_AAdd{_result, std::move(_f.a3), std::move(_f.a2)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_ADiv>(_frame)) {
          auto _f = std::move(std::get<_After_ADiv>(_frame));
          _stack.emplace_back(
              _Combine_ADiv{_result, std::move(_f.a3), std::move(_f.a2)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_AMul>(_frame)) {
          auto _f = std::move(std::get<_After_AMul>(_frame));
          _stack.emplace_back(
              _Combine_AMul{_result, std::move(_f.a3), std::move(_f.a2)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Combine_AAdd>(_frame)) {
          auto _f = std::move(std::get<_Combine_AAdd>(_frame));
          _result = f0(_f.a2, std::move(_result), _f.a3, std::move(_f._result));
        } else if (std::holds_alternative<_Combine_ADiv>(_frame)) {
          auto _f = std::move(std::get<_Combine_ADiv>(_frame));
          _result = f2(_f.a2, std::move(_result), _f.a3, std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Combine_AMul>(_frame));
          _result = f1(_f.a2, std::move(_result), _f.a3, std::move(_f._result));
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
      std::unique_ptr<bool_expr> a0;
      std::unique_ptr<bool_expr> a1;
    };

    struct BOr {
      std::unique_ptr<bool_expr> a0;
      std::unique_ptr<bool_expr> a1;
    };

    struct BNot {
      std::unique_ptr<bool_expr> a0;
    };

    using variant_t = std::variant<BTrue, BFalse, BAnd, BOr, BNot>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    bool_expr() {}

    explicit bool_expr(BTrue _v) : v_(_v) {}

    explicit bool_expr(BFalse _v) : v_(_v) {}

    explicit bool_expr(BAnd _v) : v_(std::move(_v)) {}

    explicit bool_expr(BOr _v) : v_(std::move(_v)) {}

    explicit bool_expr(BNot _v) : v_(std::move(_v)) {}

    bool_expr(const bool_expr &_other) : v_(std::move(_other.clone().v_)) {}

    bool_expr(bool_expr &&_other) noexcept : v_(std::move(_other.v_)) {}

    bool_expr &operator=(const bool_expr &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    bool_expr &operator=(bool_expr &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    bool_expr clone() const {
      bool_expr _out{};

      struct _CloneFrame {
        const bool_expr *_src;
        bool_expr *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const bool_expr *_src = _frame._src;
        bool_expr *_dst = _frame._dst;
        if (std::holds_alternative<BTrue>(_src->v())) {
          _dst->v_ = BTrue{};
        } else if (std::holds_alternative<BFalse>(_src->v())) {
          _dst->v_ = BFalse{};
        } else if (std::holds_alternative<BAnd>(_src->v())) {
          const auto &_alt = std::get<BAnd>(_src->v());
          _dst->v_ = BAnd{_alt.a0 ? std::make_unique<bool_expr>() : nullptr,
                          _alt.a1 ? std::make_unique<bool_expr>() : nullptr};
          auto &_dst_alt = std::get<BAnd>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        } else if (std::holds_alternative<BOr>(_src->v())) {
          const auto &_alt = std::get<BOr>(_src->v());
          _dst->v_ = BOr{_alt.a0 ? std::make_unique<bool_expr>() : nullptr,
                         _alt.a1 ? std::make_unique<bool_expr>() : nullptr};
          auto &_dst_alt = std::get<BOr>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        } else {
          const auto &_alt = std::get<BNot>(_src->v());
          _dst->v_ = BNot{_alt.a0 ? std::make_unique<bool_expr>() : nullptr};
          auto &_dst_alt = std::get<BNot>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
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
      std::vector<std::unique_ptr<bool_expr>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](bool_expr &_node) {
        if (std::holds_alternative<BAnd>(_node.v_)) {
          auto &_alt = std::get<BAnd>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
        }
        if (std::holds_alternative<BOr>(_node.v_)) {
          auto &_alt = std::get<BOr>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
        }
        if (std::holds_alternative<BNot>(_node.v_)) {
          auto &_alt = std::get<BNot>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
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

    bool_expr simplify_bool() const {
      const bool_expr *_self = this;
      auto &&_sv = *_self;
      if (std::holds_alternative<typename bool_expr::BTrue>(_sv.v())) {
        return bool_expr::btrue();
      } else if (std::holds_alternative<typename bool_expr::BFalse>(_sv.v())) {
        return bool_expr::bfalse();
      } else if (std::holds_alternative<typename bool_expr::BAnd>(_sv.v())) {
        const auto &[a0, a1] = std::get<typename bool_expr::BAnd>(_sv.v());
        auto &&_sv0 = a0->simplify_bool();
        if (std::holds_alternative<typename bool_expr::BTrue>(_sv0.v())) {
          auto &&_sv1 = a1->simplify_bool();
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv1.v())) {
            return bool_expr::btrue();
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv1.v())) {
            return bool_expr::bfalse();
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv1.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_sv1.v());
            return bool_expr::band(*a01, *a11);
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _sv1.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BOr>(_sv1.v());
            return bool_expr::bor(*a01, *a11);
          } else {
            const auto &[a01] = std::get<typename bool_expr::BNot>(_sv1.v());
            return bool_expr::bnot(*a01);
          }
        } else if (std::holds_alternative<typename bool_expr::BFalse>(
                       _sv0.v())) {
          return bool_expr::bfalse();
        } else if (std::holds_alternative<typename bool_expr::BAnd>(_sv0.v())) {
          const auto &[a00, a10] = std::get<typename bool_expr::BAnd>(_sv0.v());
          bool_expr a_ = bool_expr::band(*a00, *a10);
          auto &&_sv1 = a1->simplify_bool();
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv1.v())) {
            return a_;
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv1.v())) {
            return bool_expr::bfalse();
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv1.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_sv1.v());
            return bool_expr::band(std::move(a_), bool_expr::band(*a01, *a11));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _sv1.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BOr>(_sv1.v());
            return bool_expr::band(std::move(a_), bool_expr::bor(*a01, *a11));
          } else {
            const auto &[a01] = std::get<typename bool_expr::BNot>(_sv1.v());
            return bool_expr::band(std::move(a_), bool_expr::bnot(*a01));
          }
        } else if (std::holds_alternative<typename bool_expr::BOr>(_sv0.v())) {
          const auto &[a00, a10] = std::get<typename bool_expr::BOr>(_sv0.v());
          bool_expr a_ = bool_expr::bor(*a00, *a10);
          auto &&_sv1 = a1->simplify_bool();
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv1.v())) {
            return a_;
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv1.v())) {
            return bool_expr::bfalse();
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv1.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_sv1.v());
            return bool_expr::band(std::move(a_), bool_expr::band(*a01, *a11));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _sv1.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BOr>(_sv1.v());
            return bool_expr::band(std::move(a_), bool_expr::bor(*a01, *a11));
          } else {
            const auto &[a01] = std::get<typename bool_expr::BNot>(_sv1.v());
            return bool_expr::band(std::move(a_), bool_expr::bnot(*a01));
          }
        } else {
          const auto &[a00] = std::get<typename bool_expr::BNot>(_sv0.v());
          bool_expr a_ = bool_expr::bnot(*a00);
          auto &&_sv1 = a1->simplify_bool();
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv1.v())) {
            return a_;
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv1.v())) {
            return bool_expr::bfalse();
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv1.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_sv1.v());
            return bool_expr::band(std::move(a_), bool_expr::band(*a01, *a11));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _sv1.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BOr>(_sv1.v());
            return bool_expr::band(std::move(a_), bool_expr::bor(*a01, *a11));
          } else {
            const auto &[a01] = std::get<typename bool_expr::BNot>(_sv1.v());
            return bool_expr::band(std::move(a_), bool_expr::bnot(*a01));
          }
        }
      } else if (std::holds_alternative<typename bool_expr::BOr>(_sv.v())) {
        const auto &[a0, a1] = std::get<typename bool_expr::BOr>(_sv.v());
        auto &&_sv0 = a0->simplify_bool();
        if (std::holds_alternative<typename bool_expr::BTrue>(_sv0.v())) {
          return bool_expr::btrue();
        } else if (std::holds_alternative<typename bool_expr::BFalse>(
                       _sv0.v())) {
          auto &&_sv1 = a1->simplify_bool();
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv1.v())) {
            return bool_expr::btrue();
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv1.v())) {
            return bool_expr::bfalse();
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv1.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_sv1.v());
            return bool_expr::band(*a01, *a11);
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _sv1.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BOr>(_sv1.v());
            return bool_expr::bor(*a01, *a11);
          } else {
            const auto &[a01] = std::get<typename bool_expr::BNot>(_sv1.v());
            return bool_expr::bnot(*a01);
          }
        } else if (std::holds_alternative<typename bool_expr::BAnd>(_sv0.v())) {
          const auto &[a00, a10] = std::get<typename bool_expr::BAnd>(_sv0.v());
          bool_expr a_ = bool_expr::band(*a00, *a10);
          auto &&_sv1 = a1->simplify_bool();
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv1.v())) {
            return bool_expr::btrue();
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv1.v())) {
            return a_;
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv1.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_sv1.v());
            return bool_expr::bor(std::move(a_), bool_expr::band(*a01, *a11));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _sv1.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BOr>(_sv1.v());
            return bool_expr::bor(std::move(a_), bool_expr::bor(*a01, *a11));
          } else {
            const auto &[a01] = std::get<typename bool_expr::BNot>(_sv1.v());
            return bool_expr::bor(std::move(a_), bool_expr::bnot(*a01));
          }
        } else if (std::holds_alternative<typename bool_expr::BOr>(_sv0.v())) {
          const auto &[a00, a10] = std::get<typename bool_expr::BOr>(_sv0.v());
          bool_expr a_ = bool_expr::bor(*a00, *a10);
          auto &&_sv1 = a1->simplify_bool();
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv1.v())) {
            return bool_expr::btrue();
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv1.v())) {
            return a_;
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv1.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_sv1.v());
            return bool_expr::bor(std::move(a_), bool_expr::band(*a01, *a11));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _sv1.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BOr>(_sv1.v());
            return bool_expr::bor(std::move(a_), bool_expr::bor(*a01, *a11));
          } else {
            const auto &[a01] = std::get<typename bool_expr::BNot>(_sv1.v());
            return bool_expr::bor(std::move(a_), bool_expr::bnot(*a01));
          }
        } else {
          const auto &[a00] = std::get<typename bool_expr::BNot>(_sv0.v());
          bool_expr a_ = bool_expr::bnot(*a00);
          auto &&_sv1 = a1->simplify_bool();
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv1.v())) {
            return bool_expr::btrue();
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv1.v())) {
            return a_;
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv1.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_sv1.v());
            return bool_expr::bor(std::move(a_), bool_expr::band(*a01, *a11));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _sv1.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BOr>(_sv1.v());
            return bool_expr::bor(std::move(a_), bool_expr::bor(*a01, *a11));
          } else {
            const auto &[a01] = std::get<typename bool_expr::BNot>(_sv1.v());
            return bool_expr::bor(std::move(a_), bool_expr::bnot(*a01));
          }
        }
      } else {
        const auto &[a0] = std::get<typename bool_expr::BNot>(_sv.v());
        auto &&_sv0 = a0->simplify_bool();
        if (std::holds_alternative<typename bool_expr::BTrue>(_sv0.v())) {
          return bool_expr::bfalse();
        } else if (std::holds_alternative<typename bool_expr::BFalse>(
                       _sv0.v())) {
          return bool_expr::btrue();
        } else if (std::holds_alternative<typename bool_expr::BAnd>(_sv0.v())) {
          const auto &[a00, a10] = std::get<typename bool_expr::BAnd>(_sv0.v());
          return bool_expr::bnot(bool_expr::band(*a00, *a10));
        } else if (std::holds_alternative<typename bool_expr::BOr>(_sv0.v())) {
          const auto &[a00, a10] = std::get<typename bool_expr::BOr>(_sv0.v());
          return bool_expr::bnot(bool_expr::bor(*a00, *a10));
        } else {
          const auto &[a00] = std::get<typename bool_expr::BNot>(_sv0.v());
          return bool_expr::bnot(bool_expr::bnot(*a00));
        }
      }
    }

    bool eval_bool() const {
      const bool_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const bool_expr *_self;
      };

      /// _After_BAnd: saves [_s0], dispatches next recursive call.
      struct _After_BAnd {
        bool_expr *_s0;
      };

      /// _After_BOr: saves [_s0], dispatches next recursive call.
      struct _After_BOr {
        bool_expr *_s0;
      };

      /// _Combine_BAnd: receives partial results, combines with _result from
      /// final call.
      struct _Combine_BAnd {
        bool _result;
      };

      /// _Combine_BOr: receives partial results, combines with _result from
      /// final call.
      struct _Combine_BOr {
        bool _result;
      };

      /// _Resume_BNot: resumes after recursive call with _result.
      struct _Resume_BNot {};

      using _Frame = std::variant<_Enter, _After_BAnd, _After_BOr,
                                  _Combine_BAnd, _Combine_BOr, _Resume_BNot>;
      bool _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified eval_bool: _Enter -> _After_BAnd -> _After_BOr ->
      /// _Combine_BAnd -> _Combine_BOr -> _Resume_BNot.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const bool_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv.v())) {
            _result = true;
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv.v())) {
            _result = false;
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv.v())) {
            const auto &[a0, a1] = std::get<typename bool_expr::BAnd>(_sv.v());
            _stack.emplace_back(_After_BAnd{a0.get()});
            _stack.emplace_back(_Enter{a1.get()});
          } else if (std::holds_alternative<typename bool_expr::BOr>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename bool_expr::BOr>(_sv.v());
            _stack.emplace_back(_After_BOr{a0.get()});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            const auto &[a0] = std::get<typename bool_expr::BNot>(_sv.v());
            _stack.emplace_back(_Resume_BNot{});
            _stack.emplace_back(_Enter{a0.get()});
          }
        } else if (std::holds_alternative<_After_BAnd>(_frame)) {
          auto _f = std::move(std::get<_After_BAnd>(_frame));
          _stack.emplace_back(_Combine_BAnd{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_BOr>(_frame)) {
          auto _f = std::move(std::get<_After_BOr>(_frame));
          _stack.emplace_back(_Combine_BOr{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Combine_BAnd>(_frame)) {
          auto _f = std::move(std::get<_Combine_BAnd>(_frame));
          _result = (std::move(_result) && std::move(_f._result));
        } else if (std::holds_alternative<_Combine_BOr>(_frame)) {
          auto _f = std::move(std::get<_Combine_BOr>(_frame));
          _result = (std::move(_result) || std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Resume_BNot>(_frame));
          _result = !(_result);
        }
      }
      return _result;
    }

    template <typename T1, typename F2, typename F3, typename F4>
      requires std::is_invocable_r_v<T1, F2 &, bool_expr &, T1 &, bool_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F3 &, bool_expr &, T1 &, bool_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F4 &, bool_expr &, T1 &>
    T1 bool_expr_rec(T1 f, T1 f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      const bool_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const bool_expr *_self;
      };

      /// _After_BAnd: saves [_s0, a1, a0], dispatches next recursive call.
      struct _After_BAnd {
        bool_expr *_s0;
        bool_expr a1;
        bool_expr a0;
      };

      /// _After_BOr: saves [_s0, a1, a0], dispatches next recursive call.
      struct _After_BOr {
        bool_expr *_s0;
        bool_expr a1;
        bool_expr a0;
      };

      /// _Combine_BAnd: receives partial results, combines with _result from
      /// final call.
      struct _Combine_BAnd {
        T1 _result;
        bool_expr a1;
        bool_expr a0;
      };

      /// _Combine_BOr: receives partial results, combines with _result from
      /// final call.
      struct _Combine_BOr {
        T1 _result;
        bool_expr a1;
        bool_expr a0;
      };

      /// _Resume_BNot: saves [f3, a0], resumes after recursive call with
      /// _result.
      struct _Resume_BNot {
        F4 f3;
        bool_expr a0;
      };

      using _Frame = std::variant<_Enter, _After_BAnd, _After_BOr,
                                  _Combine_BAnd, _Combine_BOr, _Resume_BNot>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified bool_expr_rec: _Enter -> _After_BAnd -> _After_BOr ->
      /// _Combine_BAnd -> _Combine_BOr -> _Resume_BNot.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const bool_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv.v())) {
            _result = std::move(f);
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv.v())) {
            _result = std::move(f0);
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv.v())) {
            const auto &[a0, a1] = std::get<typename bool_expr::BAnd>(_sv.v());
            _stack.emplace_back(_After_BAnd{a0.get(), *a1, *a0});
            _stack.emplace_back(_Enter{a1.get()});
          } else if (std::holds_alternative<typename bool_expr::BOr>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename bool_expr::BOr>(_sv.v());
            _stack.emplace_back(_After_BOr{a0.get(), *a1, *a0});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            const auto &[a0] = std::get<typename bool_expr::BNot>(_sv.v());
            _stack.emplace_back(_Resume_BNot{f3, *a0});
            _stack.emplace_back(_Enter{a0.get()});
          }
        } else if (std::holds_alternative<_After_BAnd>(_frame)) {
          auto _f = std::move(std::get<_After_BAnd>(_frame));
          _stack.emplace_back(
              _Combine_BAnd{_result, std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_BOr>(_frame)) {
          auto _f = std::move(std::get<_After_BOr>(_frame));
          _stack.emplace_back(
              _Combine_BOr{_result, std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Combine_BAnd>(_frame)) {
          auto _f = std::move(std::get<_Combine_BAnd>(_frame));
          _result = f1(_f.a0, std::move(_result), _f.a1, std::move(_f._result));
        } else if (std::holds_alternative<_Combine_BOr>(_frame)) {
          auto _f = std::move(std::get<_Combine_BOr>(_frame));
          _result = f2(_f.a0, std::move(_result), _f.a1, std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Resume_BNot>(_frame));
          _result = _f.f3(_f.a0, _result);
        }
      }
      return _result;
    }

    template <typename T1, typename F2, typename F3, typename F4>
      requires std::is_invocable_r_v<T1, F2 &, bool_expr &, T1 &, bool_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F3 &, bool_expr &, T1 &, bool_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F4 &, bool_expr &, T1 &>
    T1 bool_expr_rect(T1 f, T1 f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      const bool_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const bool_expr *_self;
      };

      /// _After_BAnd: saves [_s0, a1, a0], dispatches next recursive call.
      struct _After_BAnd {
        bool_expr *_s0;
        bool_expr a1;
        bool_expr a0;
      };

      /// _After_BOr: saves [_s0, a1, a0], dispatches next recursive call.
      struct _After_BOr {
        bool_expr *_s0;
        bool_expr a1;
        bool_expr a0;
      };

      /// _Combine_BAnd: receives partial results, combines with _result from
      /// final call.
      struct _Combine_BAnd {
        T1 _result;
        bool_expr a1;
        bool_expr a0;
      };

      /// _Combine_BOr: receives partial results, combines with _result from
      /// final call.
      struct _Combine_BOr {
        T1 _result;
        bool_expr a1;
        bool_expr a0;
      };

      /// _Resume_BNot: saves [f3, a0], resumes after recursive call with
      /// _result.
      struct _Resume_BNot {
        F4 f3;
        bool_expr a0;
      };

      using _Frame = std::variant<_Enter, _After_BAnd, _After_BOr,
                                  _Combine_BAnd, _Combine_BOr, _Resume_BNot>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified bool_expr_rect: _Enter -> _After_BAnd -> _After_BOr ->
      /// _Combine_BAnd -> _Combine_BOr -> _Resume_BNot.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const bool_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv.v())) {
            _result = std::move(f);
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv.v())) {
            _result = std::move(f0);
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv.v())) {
            const auto &[a0, a1] = std::get<typename bool_expr::BAnd>(_sv.v());
            _stack.emplace_back(_After_BAnd{a0.get(), *a1, *a0});
            _stack.emplace_back(_Enter{a1.get()});
          } else if (std::holds_alternative<typename bool_expr::BOr>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename bool_expr::BOr>(_sv.v());
            _stack.emplace_back(_After_BOr{a0.get(), *a1, *a0});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            const auto &[a0] = std::get<typename bool_expr::BNot>(_sv.v());
            _stack.emplace_back(_Resume_BNot{f3, *a0});
            _stack.emplace_back(_Enter{a0.get()});
          }
        } else if (std::holds_alternative<_After_BAnd>(_frame)) {
          auto _f = std::move(std::get<_After_BAnd>(_frame));
          _stack.emplace_back(
              _Combine_BAnd{_result, std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_BOr>(_frame)) {
          auto _f = std::move(std::get<_After_BOr>(_frame));
          _stack.emplace_back(
              _Combine_BOr{_result, std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Combine_BAnd>(_frame)) {
          auto _f = std::move(std::get<_Combine_BAnd>(_frame));
          _result = f1(_f.a0, std::move(_result), _f.a1, std::move(_f._result));
        } else if (std::holds_alternative<_Combine_BOr>(_frame)) {
          auto _f = std::move(std::get<_Combine_BOr>(_frame));
          _result = f2(_f.a0, std::move(_result), _f.a1, std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Resume_BNot>(_frame));
          _result = _f.f3(_f.a0, _result);
        }
      }
      return _result;
    }
  };

  struct list_expr {
    // TYPES
    struct LNil {};

    struct LCons {
      uint64_t a0;
      std::unique_ptr<list_expr> a1;
    };

    struct LAppend {
      std::unique_ptr<list_expr> a0;
      std::unique_ptr<list_expr> a1;
    };

    struct LReplicate {
      uint64_t a0;
      uint64_t a1;
    };

    using variant_t = std::variant<LNil, LCons, LAppend, LReplicate>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    list_expr() {}

    explicit list_expr(LNil _v) : v_(_v) {}

    explicit list_expr(LCons _v) : v_(std::move(_v)) {}

    explicit list_expr(LAppend _v) : v_(std::move(_v)) {}

    explicit list_expr(LReplicate _v) : v_(std::move(_v)) {}

    list_expr(const list_expr &_other) : v_(std::move(_other.clone().v_)) {}

    list_expr(list_expr &&_other) noexcept : v_(std::move(_other.v_)) {}

    list_expr &operator=(const list_expr &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    list_expr &operator=(list_expr &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    list_expr clone() const {
      list_expr _out{};

      struct _CloneFrame {
        const list_expr *_src;
        list_expr *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const list_expr *_src = _frame._src;
        list_expr *_dst = _frame._dst;
        if (std::holds_alternative<LNil>(_src->v())) {
          _dst->v_ = LNil{};
        } else if (std::holds_alternative<LCons>(_src->v())) {
          const auto &_alt = std::get<LCons>(_src->v());
          _dst->v_ =
              LCons{_alt.a0, _alt.a1 ? std::make_unique<list_expr>() : nullptr};
          auto &_dst_alt = std::get<LCons>(_dst->v_);
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        } else if (std::holds_alternative<LAppend>(_src->v())) {
          const auto &_alt = std::get<LAppend>(_src->v());
          _dst->v_ = LAppend{_alt.a0 ? std::make_unique<list_expr>() : nullptr,
                             _alt.a1 ? std::make_unique<list_expr>() : nullptr};
          auto &_dst_alt = std::get<LAppend>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        } else {
          const auto &_alt = std::get<LReplicate>(_src->v());
          _dst->v_ = LReplicate{_alt.a0, _alt.a1};
        }
      }
      return _out;
    }

    // CREATORS
    static list_expr lnil() { return list_expr(LNil{}); }

    static list_expr lcons(uint64_t a0, list_expr a1) {
      return list_expr(LCons{a0, std::make_unique<list_expr>(std::move(a1))});
    }

    static list_expr lappend(list_expr a0, list_expr a1) {
      return list_expr(LAppend{std::make_unique<list_expr>(std::move(a0)),
                               std::make_unique<list_expr>(std::move(a1))});
    }

    static list_expr lreplicate(uint64_t a0, uint64_t a1) {
      return list_expr(LReplicate{a0, a1});
    }

    // MANIPULATORS
    ~list_expr() {
      std::vector<std::unique_ptr<list_expr>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](list_expr &_node) {
        if (std::holds_alternative<LCons>(_node.v_)) {
          auto &_alt = std::get<LCons>(_node.v_);
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
        }
        if (std::holds_alternative<LAppend>(_node.v_)) {
          auto &_alt = std::get<LAppend>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
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

    uint64_t list_expr_size() const {
      const list_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const list_expr *_self;
      };

      /// _After_LAppend: saves [_s0, _s1], dispatches next recursive call.
      struct _After_LAppend {
        list_expr *_s0;
        decltype(UINT64_C(1)) _s1;
      };

      /// _Combine_LAppend: receives partial results, combines with _result from
      /// final call.
      struct _Combine_LAppend {
        uint64_t _result;
        decltype(UINT64_C(1)) _s1;
      };

      /// _Resume_LCons: saves [_s0], resumes after recursive call with _result.
      struct _Resume_LCons {
        decltype(UINT64_C(1)) _s0;
      };

      using _Frame =
          std::variant<_Enter, _After_LAppend, _Combine_LAppend, _Resume_LCons>;
      uint64_t _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified list_expr_size: _Enter -> _After_LAppend -> _Combine_LAppend
      /// -> _Resume_LCons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const list_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename list_expr::LCons>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename list_expr::LCons>(_sv.v());
            _stack.emplace_back(_Resume_LCons{UINT64_C(1)});
            _stack.emplace_back(_Enter{a1.get()});
          } else if (std::holds_alternative<typename list_expr::LAppend>(
                         _sv.v())) {
            const auto &[a0, a1] =
                std::get<typename list_expr::LAppend>(_sv.v());
            _stack.emplace_back(_After_LAppend{a0.get(), UINT64_C(1)});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            _result = UINT64_C(1);
          }
        } else if (std::holds_alternative<_After_LAppend>(_frame)) {
          auto _f = std::move(std::get<_After_LAppend>(_frame));
          _stack.emplace_back(_Combine_LAppend{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Combine_LAppend>(_frame)) {
          auto _f = std::move(std::get<_Combine_LAppend>(_frame));
          _result = ((_f._s1 + std::move(_result)) + std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Resume_LCons>(_frame));
          _result = (_f._s0 + _result);
        }
      }
      return _result;
    }

    List<uint64_t> eval_list() const {
      const list_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const list_expr *_self;
      };

      /// _After_LAppend: saves [_s0], dispatches next recursive call.
      struct _After_LAppend {
        list_expr *_s0;
      };

      /// _Combine_LAppend: receives partial results, combines with _result from
      /// final call.
      struct _Combine_LAppend {
        List<uint64_t> _result;
      };

      /// _Resume_LCons: saves [a0], resumes after recursive call with _result.
      struct _Resume_LCons {
        uint64_t a0;
      };

      using _Frame =
          std::variant<_Enter, _After_LAppend, _Combine_LAppend, _Resume_LCons>;
      List<uint64_t> _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified eval_list: _Enter -> _After_LAppend -> _Combine_LAppend ->
      /// _Resume_LCons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const list_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename list_expr::LNil>(_sv.v())) {
            _result = List<uint64_t>::nil();
          } else if (std::holds_alternative<typename list_expr::LCons>(
                         _sv.v())) {
            const auto &[a0, a1] = std::get<typename list_expr::LCons>(_sv.v());
            _stack.emplace_back(_Resume_LCons{a0});
            _stack.emplace_back(_Enter{a1.get()});
          } else if (std::holds_alternative<typename list_expr::LAppend>(
                         _sv.v())) {
            const auto &[a0, a1] =
                std::get<typename list_expr::LAppend>(_sv.v());
            _stack.emplace_back(_After_LAppend{a0.get()});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            const auto &[a0, a1] =
                std::get<typename list_expr::LReplicate>(_sv.v());
            _result = ListDef::template repeat<uint64_t>(a1, a0);
          }
        } else if (std::holds_alternative<_After_LAppend>(_frame)) {
          auto _f = std::move(std::get<_After_LAppend>(_frame));
          _stack.emplace_back(_Combine_LAppend{std::move(_result)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Combine_LAppend>(_frame)) {
          auto _f = std::move(std::get<_Combine_LAppend>(_frame));
          _result = std::move(_result).app(std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Resume_LCons>(_frame));
          _result = List<uint64_t>::cons(_f.a0, _result);
        }
      }
      return _result;
    }

    template <typename T1, typename F1, typename F2, typename F3>
      requires std::is_invocable_r_v<T1, F1 &, uint64_t &, list_expr &, T1 &> &&
               std::is_invocable_r_v<T1, F2 &, list_expr &, T1 &, list_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F3 &, uint64_t &, uint64_t &>
    T1 list_expr_rec(T1 f, F1 &&f0, F2 &&f1, F3 &&f2) const {
      const list_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const list_expr *_self;
      };

      /// _After_LAppend: saves [_s0, a1, a0], dispatches next recursive call.
      struct _After_LAppend {
        list_expr *_s0;
        list_expr a1;
        list_expr a0;
      };

      /// _Combine_LAppend: receives partial results, combines with _result from
      /// final call.
      struct _Combine_LAppend {
        T1 _result;
        list_expr a1;
        list_expr a0;
      };

      /// _Resume_LCons: saves [f0, a1, a0], resumes after recursive call with
      /// _result.
      struct _Resume_LCons {
        F1 f0;
        list_expr a1;
        uint64_t a0;
      };

      using _Frame =
          std::variant<_Enter, _After_LAppend, _Combine_LAppend, _Resume_LCons>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified list_expr_rec: _Enter -> _After_LAppend -> _Combine_LAppend
      /// -> _Resume_LCons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const list_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename list_expr::LNil>(_sv.v())) {
            _result = std::move(f);
          } else if (std::holds_alternative<typename list_expr::LCons>(
                         _sv.v())) {
            const auto &[a0, a1] = std::get<typename list_expr::LCons>(_sv.v());
            _stack.emplace_back(_Resume_LCons{f0, *a1, a0});
            _stack.emplace_back(_Enter{a1.get()});
          } else if (std::holds_alternative<typename list_expr::LAppend>(
                         _sv.v())) {
            const auto &[a0, a1] =
                std::get<typename list_expr::LAppend>(_sv.v());
            _stack.emplace_back(_After_LAppend{a0.get(), *a1, *a0});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            const auto &[a0, a1] =
                std::get<typename list_expr::LReplicate>(_sv.v());
            _result = f2(a0, a1);
          }
        } else if (std::holds_alternative<_After_LAppend>(_frame)) {
          auto _f = std::move(std::get<_After_LAppend>(_frame));
          _stack.emplace_back(
              _Combine_LAppend{_result, std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Combine_LAppend>(_frame)) {
          auto _f = std::move(std::get<_Combine_LAppend>(_frame));
          _result = f1(_f.a0, std::move(_result), _f.a1, std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Resume_LCons>(_frame));
          _result = _f.f0(_f.a0, _f.a1, _result);
        }
      }
      return _result;
    }

    template <typename T1, typename F1, typename F2, typename F3>
      requires std::is_invocable_r_v<T1, F1 &, uint64_t &, list_expr &, T1 &> &&
               std::is_invocable_r_v<T1, F2 &, list_expr &, T1 &, list_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F3 &, uint64_t &, uint64_t &>
    T1 list_expr_rect(T1 f, F1 &&f0, F2 &&f1, F3 &&f2) const {
      const list_expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const list_expr *_self;
      };

      /// _After_LAppend: saves [_s0, a1, a0], dispatches next recursive call.
      struct _After_LAppend {
        list_expr *_s0;
        list_expr a1;
        list_expr a0;
      };

      /// _Combine_LAppend: receives partial results, combines with _result from
      /// final call.
      struct _Combine_LAppend {
        T1 _result;
        list_expr a1;
        list_expr a0;
      };

      /// _Resume_LCons: saves [f0, a1, a0], resumes after recursive call with
      /// _result.
      struct _Resume_LCons {
        F1 f0;
        list_expr a1;
        uint64_t a0;
      };

      using _Frame =
          std::variant<_Enter, _After_LAppend, _Combine_LAppend, _Resume_LCons>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified list_expr_rect: _Enter -> _After_LAppend -> _Combine_LAppend
      /// -> _Resume_LCons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const list_expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename list_expr::LNil>(_sv.v())) {
            _result = std::move(f);
          } else if (std::holds_alternative<typename list_expr::LCons>(
                         _sv.v())) {
            const auto &[a0, a1] = std::get<typename list_expr::LCons>(_sv.v());
            _stack.emplace_back(_Resume_LCons{f0, *a1, a0});
            _stack.emplace_back(_Enter{a1.get()});
          } else if (std::holds_alternative<typename list_expr::LAppend>(
                         _sv.v())) {
            const auto &[a0, a1] =
                std::get<typename list_expr::LAppend>(_sv.v());
            _stack.emplace_back(_After_LAppend{a0.get(), *a1, *a0});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            const auto &[a0, a1] =
                std::get<typename list_expr::LReplicate>(_sv.v());
            _result = f2(a0, a1);
          }
        } else if (std::holds_alternative<_After_LAppend>(_frame)) {
          auto _f = std::move(std::get<_After_LAppend>(_frame));
          _stack.emplace_back(
              _Combine_LAppend{_result, std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Combine_LAppend>(_frame)) {
          auto _f = std::move(std::get<_Combine_LAppend>(_frame));
          _result = f1(_f.a0, std::move(_result), _f.a1, std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Resume_LCons>(_frame));
          _result = _f.f0(_f.a0, _f.a1, _result);
        }
      }
      return _result;
    }
  };
};

template <typename T1> List<T1> ListDef::repeat(T1 x, uint64_t n) {
  std::unique_ptr<List<T1>> _head{};
  std::unique_ptr<List<T1>> *_write = &_head;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write = std::make_unique<List<T1>>(List<T1>::nil());
      break;
    } else {
      uint64_t k = _loop_n - 1;
      auto _cell =
          std::make_unique<List<T1>>(typename List<T1>::Cons(x, nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename List<T1>::Cons>((*_write)->v_mut()).l;
      _loop_n = k;
      continue;
    }
  }
  return std::move(*_head);
}

#endif // INCLUDED_LOOPIFY_EXPR_VARIANTS
