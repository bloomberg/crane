#ifndef INCLUDED_LOOPIFY_EXPR_VARIANTS
#define INCLUDED_LOOPIFY_EXPR_VARIANTS

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  std::shared_ptr<List<t_A>> app(std::shared_ptr<List<t_A>> m) const {
    std::shared_ptr<List<t_A>> _head{};
    std::shared_ptr<List<t_A>> _last{};
    const List *_loop_self = this;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{
              [&](const typename List<t_A>::Nil &) {
                if (_last) {
                  std::get<typename List<t_A>::Cons>(_last->v_mut()).d_a1 = m;
                } else {
                  _head = m;
                }
                _continue = false;
              },
              [&](const typename List<t_A>::Cons &_args) {
                auto _cell = List<t_A>::cons(_args.d_a0, nullptr);
                if (_last) {
                  std::get<typename List<t_A>::Cons>(_last->v_mut()).d_a1 =
                      _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                _loop_self = _args.d_a1.get();
              }},
          _loop_self->v());
    }
    return _head;
  }
};

struct ListDef {
  template <typename T1>
  static std::shared_ptr<List<T1>> repeat(const T1 x, const unsigned int n);
};

struct LoopifyExprVariants {
  struct cond_expr {
    // TYPES
    struct Lit {
      unsigned int d_a0;
    };

    struct Add {
      std::shared_ptr<cond_expr> d_a0;
      std::shared_ptr<cond_expr> d_a1;
    };

    struct Cond {
      std::shared_ptr<cond_expr> d_a0;
      std::shared_ptr<cond_expr> d_a1;
      std::shared_ptr<cond_expr> d_a2;
    };

    using variant_t = std::variant<Lit, Add, Cond>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit cond_expr(Lit _v) : d_v_(std::move(_v)) {}

    explicit cond_expr(Add _v) : d_v_(std::move(_v)) {}

    explicit cond_expr(Cond _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<cond_expr> lit(unsigned int a0) {
      return std::make_shared<cond_expr>(Lit{std::move(a0)});
    }

    static std::shared_ptr<cond_expr>
    add(const std::shared_ptr<cond_expr> &a0,
        const std::shared_ptr<cond_expr> &a1) {
      return std::make_shared<cond_expr>(Add{a0, a1});
    }

    static std::shared_ptr<cond_expr> add(std::shared_ptr<cond_expr> &&a0,
                                          std::shared_ptr<cond_expr> &&a1) {
      return std::make_shared<cond_expr>(Add{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<cond_expr>
    cond(const std::shared_ptr<cond_expr> &a0,
         const std::shared_ptr<cond_expr> &a1,
         const std::shared_ptr<cond_expr> &a2) {
      return std::make_shared<cond_expr>(Cond{a0, a1, a2});
    }

    static std::shared_ptr<cond_expr> cond(std::shared_ptr<cond_expr> &&a0,
                                           std::shared_ptr<cond_expr> &&a1,
                                           std::shared_ptr<cond_expr> &&a2) {
      return std::make_shared<cond_expr>(
          Cond{std::move(a0), std::move(a1), std::move(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int size_cond() const {
      const cond_expr *_self = this;

      struct _Enter {
        const cond_expr *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename cond_expr::Add &>()
                     .d_a0.get()) _s0;
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
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const cond_expr *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename cond_expr::Lit &) -> void {
                            _result = 1u;
                          },
                          [&](const typename cond_expr::Add &_args) -> void {
                            _stack.push_back(_Call1{_args.d_a0.get(), 1u});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename cond_expr::Cond &_args) -> void {
                            _stack.push_back(
                                _Call3{_args.d_a1.get(), _args.d_a0.get(), 1u});
                            _stack.push_back(_Enter{_args.d_a2.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.push_back(_Call2{_result, _f._s1});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) { _result = ((_f._s1 + _result) + _f._s0); },
                [&](_Call3 _f) {
                  _stack.push_back(_Call4{_result, _f._s1, _f._s2});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call4 _f) {
                  _stack.push_back(_Call5{_f._s0, _result, _f._s2});
                  _stack.push_back(_Enter{_f._s1});
                },
                [&](_Call5 _f) {
                  _result = (((_f._s2 + _result) + _f._s1) + _f._s0);
                }},
            _frame);
      }
      return _result;
    }

    __attribute__((pure)) unsigned int eval_cond() const {
      const cond_expr *_self = this;

      struct _Enter {
        const cond_expr *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename cond_expr::Add &>()
                     .d_a0.get()) _s0;
      };

      struct _Call2 {
        unsigned int _s0;
      };

      struct _Call3 {
        const typename cond_expr::Cond _s0;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const cond_expr *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename cond_expr::Lit &_args) -> void {
                            _result = _args.d_a0;
                          },
                          [&](const typename cond_expr::Add &_args) -> void {
                            _stack.push_back(_Call1{_args.d_a0.get()});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename cond_expr::Cond &_args) -> void {
                            _stack.push_back(_Call3{_args});
                            _stack.push_back(_Enter{_args.d_a0.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.push_back(_Call2{_result});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) { _result = (_result + _f._s0); },
                [&](_Call3 _f) {
                  const typename cond_expr::Cond _args = _f._s0;
                  unsigned int _cond0 = _result;
                  if (0u < _cond0) {
                    _stack.push_back(_Enter{_args.d_a1.get()});
                  } else {
                    _stack.push_back(_Enter{_args.d_a2.get()});
                  }
                }},
            _frame);
      }
      return _result;
    }

    template <
        typename T1, MapsTo<T1, unsigned int> F0,
        MapsTo<T1, std::shared_ptr<cond_expr>, T1, std::shared_ptr<cond_expr>,
               T1>
            F1,
        MapsTo<T1, std::shared_ptr<cond_expr>, T1, std::shared_ptr<cond_expr>,
               T1, std::shared_ptr<cond_expr>, T1>
            F2>
    T1 cond_expr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      const cond_expr *_self = this;

      struct _Enter {
        const cond_expr *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename cond_expr::Add &>()
                     .d_a0.get()) _s0;
        decltype(std::declval<const typename cond_expr::Add &>().d_a1) _s1;
        decltype(std::declval<const typename cond_expr::Add &>().d_a0) _s2;
      };

      struct _Call2 {
        T1 _s0;
        decltype(std::declval<const typename cond_expr::Add &>().d_a1) _s1;
        decltype(std::declval<const typename cond_expr::Add &>().d_a0) _s2;
      };

      struct _Call3 {
        const cond_expr *_s0;
        const cond_expr *_s1;
        decltype(std::declval<const typename cond_expr::Cond &>().d_a2) _s2;
        decltype(std::declval<const typename cond_expr::Cond &>().d_a1) _s3;
        decltype(std::declval<const typename cond_expr::Cond &>().d_a0) _s4;
      };

      struct _Call4 {
        T1 _s0;
        const cond_expr *_s1;
        decltype(std::declval<const typename cond_expr::Cond &>().d_a2) _s2;
        decltype(std::declval<const typename cond_expr::Cond &>().d_a1) _s3;
        decltype(std::declval<const typename cond_expr::Cond &>().d_a0) _s4;
      };

      struct _Call5 {
        T1 _s0;
        T1 _s1;
        decltype(std::declval<const typename cond_expr::Cond &>().d_a2) _s2;
        decltype(std::declval<const typename cond_expr::Cond &>().d_a1) _s3;
        decltype(std::declval<const typename cond_expr::Cond &>().d_a0) _s4;
      };

      using _Frame =
          std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const cond_expr *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename cond_expr::Lit &_args) -> void {
                            _result = f(_args.d_a0);
                          },
                          [&](const typename cond_expr::Add &_args) -> void {
                            _stack.push_back(_Call1{_args.d_a0.get(),
                                                    _args.d_a1, _args.d_a0});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename cond_expr::Cond &_args) -> void {
                            _stack.push_back(
                                _Call3{_args.d_a1.get(), _args.d_a0.get(),
                                       _args.d_a2, _args.d_a1, _args.d_a0});
                            _stack.push_back(_Enter{_args.d_a2.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.push_back(_Call2{_result, _f._s1, _f._s2});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) {
                  _result = f0(_f._s2, _result, _f._s1, _f._s0);
                },
                [&](_Call3 _f) {
                  _stack.push_back(
                      _Call4{_result, _f._s1, _f._s2, _f._s3, _f._s4});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call4 _f) {
                  _stack.push_back(
                      _Call5{_f._s0, _result, _f._s2, _f._s3, _f._s4});
                  _stack.push_back(_Enter{_f._s1});
                },
                [&](_Call5 _f) {
                  _result = f1(_f._s4, _result, _f._s3, _f._s1, _f._s2, _f._s0);
                }},
            _frame);
      }
      return _result;
    }

    template <
        typename T1, MapsTo<T1, unsigned int> F0,
        MapsTo<T1, std::shared_ptr<cond_expr>, T1, std::shared_ptr<cond_expr>,
               T1>
            F1,
        MapsTo<T1, std::shared_ptr<cond_expr>, T1, std::shared_ptr<cond_expr>,
               T1, std::shared_ptr<cond_expr>, T1>
            F2>
    T1 cond_expr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      const cond_expr *_self = this;

      struct _Enter {
        const cond_expr *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename cond_expr::Add &>()
                     .d_a0.get()) _s0;
        decltype(std::declval<const typename cond_expr::Add &>().d_a1) _s1;
        decltype(std::declval<const typename cond_expr::Add &>().d_a0) _s2;
      };

      struct _Call2 {
        T1 _s0;
        decltype(std::declval<const typename cond_expr::Add &>().d_a1) _s1;
        decltype(std::declval<const typename cond_expr::Add &>().d_a0) _s2;
      };

      struct _Call3 {
        const cond_expr *_s0;
        const cond_expr *_s1;
        decltype(std::declval<const typename cond_expr::Cond &>().d_a2) _s2;
        decltype(std::declval<const typename cond_expr::Cond &>().d_a1) _s3;
        decltype(std::declval<const typename cond_expr::Cond &>().d_a0) _s4;
      };

      struct _Call4 {
        T1 _s0;
        const cond_expr *_s1;
        decltype(std::declval<const typename cond_expr::Cond &>().d_a2) _s2;
        decltype(std::declval<const typename cond_expr::Cond &>().d_a1) _s3;
        decltype(std::declval<const typename cond_expr::Cond &>().d_a0) _s4;
      };

      struct _Call5 {
        T1 _s0;
        T1 _s1;
        decltype(std::declval<const typename cond_expr::Cond &>().d_a2) _s2;
        decltype(std::declval<const typename cond_expr::Cond &>().d_a1) _s3;
        decltype(std::declval<const typename cond_expr::Cond &>().d_a0) _s4;
      };

      using _Frame =
          std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const cond_expr *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename cond_expr::Lit &_args) -> void {
                            _result = f(_args.d_a0);
                          },
                          [&](const typename cond_expr::Add &_args) -> void {
                            _stack.push_back(_Call1{_args.d_a0.get(),
                                                    _args.d_a1, _args.d_a0});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename cond_expr::Cond &_args) -> void {
                            _stack.push_back(
                                _Call3{_args.d_a1.get(), _args.d_a0.get(),
                                       _args.d_a2, _args.d_a1, _args.d_a0});
                            _stack.push_back(_Enter{_args.d_a2.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.push_back(_Call2{_result, _f._s1, _f._s2});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) {
                  _result = f0(_f._s2, _result, _f._s1, _f._s0);
                },
                [&](_Call3 _f) {
                  _stack.push_back(
                      _Call4{_result, _f._s1, _f._s2, _f._s3, _f._s4});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call4 _f) {
                  _stack.push_back(
                      _Call5{_f._s0, _result, _f._s2, _f._s3, _f._s4});
                  _stack.push_back(_Enter{_f._s1});
                },
                [&](_Call5 _f) {
                  _result = f1(_f._s4, _result, _f._s3, _f._s1, _f._s2, _f._s0);
                }},
            _frame);
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
      std::shared_ptr<arith_expr> d_a0;
      std::shared_ptr<arith_expr> d_a1;
    };

    struct AMul {
      std::shared_ptr<arith_expr> d_a0;
      std::shared_ptr<arith_expr> d_a1;
    };

    struct ADiv {
      std::shared_ptr<arith_expr> d_a0;
      std::shared_ptr<arith_expr> d_a1;
    };

    using variant_t = std::variant<ANum, AAdd, AMul, ADiv>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit arith_expr(ANum _v) : d_v_(std::move(_v)) {}

    explicit arith_expr(AAdd _v) : d_v_(std::move(_v)) {}

    explicit arith_expr(AMul _v) : d_v_(std::move(_v)) {}

    explicit arith_expr(ADiv _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<arith_expr> anum(unsigned int a0) {
      return std::make_shared<arith_expr>(ANum{std::move(a0)});
    }

    static std::shared_ptr<arith_expr>
    aadd(const std::shared_ptr<arith_expr> &a0,
         const std::shared_ptr<arith_expr> &a1) {
      return std::make_shared<arith_expr>(AAdd{a0, a1});
    }

    static std::shared_ptr<arith_expr> aadd(std::shared_ptr<arith_expr> &&a0,
                                            std::shared_ptr<arith_expr> &&a1) {
      return std::make_shared<arith_expr>(AAdd{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<arith_expr>
    amul(const std::shared_ptr<arith_expr> &a0,
         const std::shared_ptr<arith_expr> &a1) {
      return std::make_shared<arith_expr>(AMul{a0, a1});
    }

    static std::shared_ptr<arith_expr> amul(std::shared_ptr<arith_expr> &&a0,
                                            std::shared_ptr<arith_expr> &&a1) {
      return std::make_shared<arith_expr>(AMul{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<arith_expr>
    adiv(const std::shared_ptr<arith_expr> &a0,
         const std::shared_ptr<arith_expr> &a1) {
      return std::make_shared<arith_expr>(ADiv{a0, a1});
    }

    static std::shared_ptr<arith_expr> adiv(std::shared_ptr<arith_expr> &&a0,
                                            std::shared_ptr<arith_expr> &&a1) {
      return std::make_shared<arith_expr>(ADiv{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int count_ops() const {
      const arith_expr *_self = this;

      struct _Enter {
        const arith_expr *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename arith_expr::AAdd &>()
                     .d_a0.get()) _s0;
        decltype(1u) _s1;
      };

      struct _Call2 {
        unsigned int _s0;
        decltype(1u) _s1;
      };

      struct _Call3 {
        decltype(std::declval<const typename arith_expr::AMul &>()
                     .d_a0.get()) _s0;
        decltype(1u) _s1;
      };

      struct _Call4 {
        unsigned int _s0;
        decltype(1u) _s1;
      };

      struct _Call5 {
        decltype(std::declval<const typename arith_expr::ADiv &>()
                     .d_a0.get()) _s0;
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
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const arith_expr *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename arith_expr::ANum &) -> void {
                            _result = 0u;
                          },
                          [&](const typename arith_expr::AAdd &_args) -> void {
                            _stack.push_back(_Call1{_args.d_a0.get(), 1u});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename arith_expr::AMul &_args) -> void {
                            _stack.push_back(_Call3{_args.d_a0.get(), 1u});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename arith_expr::ADiv &_args) -> void {
                            _stack.push_back(_Call5{_args.d_a0.get(), 1u});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.push_back(_Call2{_result, _f._s1});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) { _result = ((_f._s1 + _result) + _f._s0); },
                [&](_Call3 _f) {
                  _stack.push_back(_Call4{_result, _f._s1});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call4 _f) { _result = ((_f._s1 + _result) + _f._s0); },
                [&](_Call5 _f) {
                  _stack.push_back(_Call6{_result, _f._s1});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call6 _f) { _result = ((_f._s1 + _result) + _f._s0); }},
            _frame);
      }
      return _result;
    }

    __attribute__((pure)) unsigned int eval_arith() const {
      const arith_expr *_self = this;

      struct _Enter {
        const arith_expr *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename arith_expr::AAdd &>()
                     .d_a0.get()) _s0;
      };

      struct _Call2 {
        unsigned int _s0;
      };

      struct _Call3 {
        decltype(std::declval<const typename arith_expr::AMul &>()
                     .d_a0.get()) _s0;
      };

      struct _Call4 {
        unsigned int _s0;
      };

      struct _Call5 {
        const typename arith_expr::ADiv _s0;
      };

      struct _Call6 {
        decltype((std::declval<unsigned int &>() + 1)) _s0;
      };

      using _Frame =
          std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5, _Call6>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const arith_expr *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename arith_expr::ANum &_args) -> void {
                            _result = _args.d_a0;
                          },
                          [&](const typename arith_expr::AAdd &_args) -> void {
                            _stack.push_back(_Call1{_args.d_a0.get()});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename arith_expr::AMul &_args) -> void {
                            _stack.push_back(_Call3{_args.d_a0.get()});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename arith_expr::ADiv &_args) -> void {
                            _stack.push_back(_Call5{_args});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.push_back(_Call2{_result});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) { _result = (_result + _f._s0); },
                [&](_Call3 _f) {
                  _stack.push_back(_Call4{_result});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call4 _f) { _result = (_result * _f._s0); },
                [&](_Call5 _f) {
                  const typename arith_expr::ADiv _args = _f._s0;
                  if (_result <= 0) {
                    _result = 0u;
                  } else {
                    unsigned int n = _result - 1;
                    _stack.push_back(_Call6{(n + 1)});
                    _stack.push_back(_Enter{_args.d_a0.get()});
                  }
                },
                [&](_Call6 _f) { _result = (_f._s0 ? _result / _f._s0 : 0); }},
            _frame);
      }
      return _result;
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, std::shared_ptr<arith_expr>, T1,
                     std::shared_ptr<arith_expr>, T1>
                  F1,
              MapsTo<T1, std::shared_ptr<arith_expr>, T1,
                     std::shared_ptr<arith_expr>, T1>
                  F2,
              MapsTo<T1, std::shared_ptr<arith_expr>, T1,
                     std::shared_ptr<arith_expr>, T1>
                  F3>
    T1 arith_expr_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2) const {
      const arith_expr *_self = this;

      struct _Enter {
        const arith_expr *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename arith_expr::AAdd &>()
                     .d_a0.get()) _s0;
        decltype(std::declval<const typename arith_expr::AAdd &>().d_a1) _s1;
        decltype(std::declval<const typename arith_expr::AAdd &>().d_a0) _s2;
      };

      struct _Call2 {
        T1 _s0;
        decltype(std::declval<const typename arith_expr::AAdd &>().d_a1) _s1;
        decltype(std::declval<const typename arith_expr::AAdd &>().d_a0) _s2;
      };

      struct _Call3 {
        decltype(std::declval<const typename arith_expr::AMul &>()
                     .d_a0.get()) _s0;
        decltype(std::declval<const typename arith_expr::AMul &>().d_a1) _s1;
        decltype(std::declval<const typename arith_expr::AMul &>().d_a0) _s2;
      };

      struct _Call4 {
        T1 _s0;
        decltype(std::declval<const typename arith_expr::AMul &>().d_a1) _s1;
        decltype(std::declval<const typename arith_expr::AMul &>().d_a0) _s2;
      };

      struct _Call5 {
        decltype(std::declval<const typename arith_expr::ADiv &>()
                     .d_a0.get()) _s0;
        decltype(std::declval<const typename arith_expr::ADiv &>().d_a1) _s1;
        decltype(std::declval<const typename arith_expr::ADiv &>().d_a0) _s2;
      };

      struct _Call6 {
        T1 _s0;
        decltype(std::declval<const typename arith_expr::ADiv &>().d_a1) _s1;
        decltype(std::declval<const typename arith_expr::ADiv &>().d_a0) _s2;
      };

      using _Frame =
          std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5, _Call6>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const arith_expr *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename arith_expr::ANum &_args) -> void {
                            _result = f(_args.d_a0);
                          },
                          [&](const typename arith_expr::AAdd &_args) -> void {
                            _stack.push_back(_Call1{_args.d_a0.get(),
                                                    _args.d_a1, _args.d_a0});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename arith_expr::AMul &_args) -> void {
                            _stack.push_back(_Call3{_args.d_a0.get(),
                                                    _args.d_a1, _args.d_a0});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename arith_expr::ADiv &_args) -> void {
                            _stack.push_back(_Call5{_args.d_a0.get(),
                                                    _args.d_a1, _args.d_a0});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.push_back(_Call2{_result, _f._s1, _f._s2});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) {
                  _result = f0(_f._s2, _result, _f._s1, _f._s0);
                },
                [&](_Call3 _f) {
                  _stack.push_back(_Call4{_result, _f._s1, _f._s2});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call4 _f) {
                  _result = f1(_f._s2, _result, _f._s1, _f._s0);
                },
                [&](_Call5 _f) {
                  _stack.push_back(_Call6{_result, _f._s1, _f._s2});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call6 _f) {
                  _result = f2(_f._s2, _result, _f._s1, _f._s0);
                }},
            _frame);
      }
      return _result;
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, std::shared_ptr<arith_expr>, T1,
                     std::shared_ptr<arith_expr>, T1>
                  F1,
              MapsTo<T1, std::shared_ptr<arith_expr>, T1,
                     std::shared_ptr<arith_expr>, T1>
                  F2,
              MapsTo<T1, std::shared_ptr<arith_expr>, T1,
                     std::shared_ptr<arith_expr>, T1>
                  F3>
    T1 arith_expr_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2) const {
      const arith_expr *_self = this;

      struct _Enter {
        const arith_expr *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename arith_expr::AAdd &>()
                     .d_a0.get()) _s0;
        decltype(std::declval<const typename arith_expr::AAdd &>().d_a1) _s1;
        decltype(std::declval<const typename arith_expr::AAdd &>().d_a0) _s2;
      };

      struct _Call2 {
        T1 _s0;
        decltype(std::declval<const typename arith_expr::AAdd &>().d_a1) _s1;
        decltype(std::declval<const typename arith_expr::AAdd &>().d_a0) _s2;
      };

      struct _Call3 {
        decltype(std::declval<const typename arith_expr::AMul &>()
                     .d_a0.get()) _s0;
        decltype(std::declval<const typename arith_expr::AMul &>().d_a1) _s1;
        decltype(std::declval<const typename arith_expr::AMul &>().d_a0) _s2;
      };

      struct _Call4 {
        T1 _s0;
        decltype(std::declval<const typename arith_expr::AMul &>().d_a1) _s1;
        decltype(std::declval<const typename arith_expr::AMul &>().d_a0) _s2;
      };

      struct _Call5 {
        decltype(std::declval<const typename arith_expr::ADiv &>()
                     .d_a0.get()) _s0;
        decltype(std::declval<const typename arith_expr::ADiv &>().d_a1) _s1;
        decltype(std::declval<const typename arith_expr::ADiv &>().d_a0) _s2;
      };

      struct _Call6 {
        T1 _s0;
        decltype(std::declval<const typename arith_expr::ADiv &>().d_a1) _s1;
        decltype(std::declval<const typename arith_expr::ADiv &>().d_a0) _s2;
      };

      using _Frame =
          std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5, _Call6>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const arith_expr *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename arith_expr::ANum &_args) -> void {
                            _result = f(_args.d_a0);
                          },
                          [&](const typename arith_expr::AAdd &_args) -> void {
                            _stack.push_back(_Call1{_args.d_a0.get(),
                                                    _args.d_a1, _args.d_a0});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename arith_expr::AMul &_args) -> void {
                            _stack.push_back(_Call3{_args.d_a0.get(),
                                                    _args.d_a1, _args.d_a0});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename arith_expr::ADiv &_args) -> void {
                            _stack.push_back(_Call5{_args.d_a0.get(),
                                                    _args.d_a1, _args.d_a0});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.push_back(_Call2{_result, _f._s1, _f._s2});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) {
                  _result = f0(_f._s2, _result, _f._s1, _f._s0);
                },
                [&](_Call3 _f) {
                  _stack.push_back(_Call4{_result, _f._s1, _f._s2});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call4 _f) {
                  _result = f1(_f._s2, _result, _f._s1, _f._s0);
                },
                [&](_Call5 _f) {
                  _stack.push_back(_Call6{_result, _f._s1, _f._s2});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call6 _f) {
                  _result = f2(_f._s2, _result, _f._s1, _f._s0);
                }},
            _frame);
      }
      return _result;
    }
  };

  struct bool_expr {
    // TYPES
    struct BTrue {};

    struct BFalse {};

    struct BAnd {
      std::shared_ptr<bool_expr> d_a0;
      std::shared_ptr<bool_expr> d_a1;
    };

    struct BOr {
      std::shared_ptr<bool_expr> d_a0;
      std::shared_ptr<bool_expr> d_a1;
    };

    struct BNot {
      std::shared_ptr<bool_expr> d_a0;
    };

    using variant_t = std::variant<BTrue, BFalse, BAnd, BOr, BNot>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit bool_expr(BTrue _v) : d_v_(std::move(_v)) {}

    explicit bool_expr(BFalse _v) : d_v_(std::move(_v)) {}

    explicit bool_expr(BAnd _v) : d_v_(std::move(_v)) {}

    explicit bool_expr(BOr _v) : d_v_(std::move(_v)) {}

    explicit bool_expr(BNot _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<bool_expr> btrue() {
      return std::make_shared<bool_expr>(BTrue{});
    }

    static std::shared_ptr<bool_expr> bfalse() {
      return std::make_shared<bool_expr>(BFalse{});
    }

    static std::shared_ptr<bool_expr>
    band(const std::shared_ptr<bool_expr> &a0,
         const std::shared_ptr<bool_expr> &a1) {
      return std::make_shared<bool_expr>(BAnd{a0, a1});
    }

    static std::shared_ptr<bool_expr> band(std::shared_ptr<bool_expr> &&a0,
                                           std::shared_ptr<bool_expr> &&a1) {
      return std::make_shared<bool_expr>(BAnd{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<bool_expr>
    bor(const std::shared_ptr<bool_expr> &a0,
        const std::shared_ptr<bool_expr> &a1) {
      return std::make_shared<bool_expr>(BOr{a0, a1});
    }

    static std::shared_ptr<bool_expr> bor(std::shared_ptr<bool_expr> &&a0,
                                          std::shared_ptr<bool_expr> &&a1) {
      return std::make_shared<bool_expr>(BOr{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<bool_expr>
    bnot(const std::shared_ptr<bool_expr> &a0) {
      return std::make_shared<bool_expr>(BNot{a0});
    }

    static std::shared_ptr<bool_expr> bnot(std::shared_ptr<bool_expr> &&a0) {
      return std::make_shared<bool_expr>(BNot{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    std::shared_ptr<bool_expr> simplify_bool() const {
      const bool_expr *_self = this;

      struct _Enter {
        const bool_expr *_self;
      };

      struct _Call1 {
        const typename bool_expr::BAnd _s0;
      };

      struct _Call10 {
        std::shared_ptr<bool_expr> _s0;
      };

      struct _Call11 {};

      struct _Call2 {};

      struct _Call3 {
        std::shared_ptr<bool_expr> _s0;
      };

      struct _Call4 {
        std::shared_ptr<bool_expr> _s0;
      };

      struct _Call5 {
        std::shared_ptr<bool_expr> _s0;
      };

      struct _Call6 {
        const typename bool_expr::BOr _s0;
      };

      struct _Call7 {};

      struct _Call8 {
        std::shared_ptr<bool_expr> _s0;
      };

      struct _Call9 {
        std::shared_ptr<bool_expr> _s0;
      };

      using _Frame =
          std::variant<_Enter, _Call1, _Call10, _Call11, _Call2, _Call3, _Call4,
                       _Call5, _Call6, _Call7, _Call8, _Call9>;
      std::shared_ptr<bool_expr> _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const bool_expr *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename bool_expr::BTrue &) -> void {
                            _result = bool_expr::btrue();
                          },
                          [&](const typename bool_expr::BFalse &) -> void {
                            _result = bool_expr::bfalse();
                          },
                          [&](const typename bool_expr::BAnd &_args) -> void {
                            _stack.push_back(_Call1{_args});
                            _stack.push_back(_Enter{_args.d_a0.get()});
                          },
                          [&](const typename bool_expr::BOr &_args) -> void {
                            _stack.push_back(_Call6{_args});
                            _stack.push_back(_Enter{_args.d_a0.get()});
                          },
                          [&](const typename bool_expr::BNot &_args) -> void {
                            _stack.push_back(_Call11{});
                            _stack.push_back(_Enter{_args.d_a0.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  const typename bool_expr::BAnd _args = _f._s0;
                  std::visit(
                      Overloaded{
                          [&](const typename bool_expr::BTrue &) -> void {
                            _stack.push_back(_Call2{});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename bool_expr::BFalse &) -> void {
                            _result = bool_expr::bfalse();
                          },
                          [&](const typename bool_expr::BAnd &_args0) -> void {
                            std::shared_ptr<bool_expr> a_ =
                                bool_expr::band(_args0.d_a0, _args0.d_a1);
                            _stack.push_back(_Call3{a_});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename bool_expr::BOr &_args0) -> void {
                            std::shared_ptr<bool_expr> a_ =
                                bool_expr::bor(_args0.d_a0, _args0.d_a1);
                            _stack.push_back(_Call4{a_});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename bool_expr::BNot &_args0) -> void {
                            std::shared_ptr<bool_expr> a_ =
                                bool_expr::bnot(_args0.d_a0);
                            _stack.push_back(_Call5{a_});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          }},
                      _result->v());
                },
                [&](_Call10 _f) {
                  std::shared_ptr<bool_expr> a_ = _f._s0;
                  std::visit(
                      Overloaded{
                          [&](const typename bool_expr::BTrue &) -> void {
                            _result = bool_expr::btrue();
                          },
                          [&](const typename bool_expr::BFalse &) -> void {
                            _result = std::move(a_);
                          },
                          [&](const typename bool_expr::BAnd &_args1) -> void {
                            _result = bool_expr::bor(
                                a_, bool_expr::band(_args1.d_a0, _args1.d_a1));
                          },
                          [&](const typename bool_expr::BOr &_args1) -> void {
                            _result = bool_expr::bor(
                                a_, bool_expr::bor(_args1.d_a0, _args1.d_a1));
                          },
                          [&](const typename bool_expr::BNot &_args1) -> void {
                            _result = bool_expr::bor(
                                a_, bool_expr::bnot(_args1.d_a0));
                          }},
                      _result->v());
                },
                [&](_Call11) {
                  std::visit(
                      Overloaded{
                          [&](const typename bool_expr::BTrue &) -> void {
                            _result = bool_expr::bfalse();
                          },
                          [&](const typename bool_expr::BFalse &) -> void {
                            _result = bool_expr::btrue();
                          },
                          [&](const typename bool_expr::BAnd &_args0) -> void {
                            _result = bool_expr::bnot(
                                bool_expr::band(_args0.d_a0, _args0.d_a1));
                          },
                          [&](const typename bool_expr::BOr &_args0) -> void {
                            _result = bool_expr::bnot(
                                bool_expr::bor(_args0.d_a0, _args0.d_a1));
                          },
                          [&](const typename bool_expr::BNot &_args0) -> void {
                            _result =
                                bool_expr::bnot(bool_expr::bnot(_args0.d_a0));
                          }},
                      _result->v());
                },
                [&](_Call2) {
                  std::visit(
                      Overloaded{
                          [&](const typename bool_expr::BTrue &) -> void {
                            _result = bool_expr::btrue();
                          },
                          [&](const typename bool_expr::BFalse &) -> void {
                            _result = bool_expr::bfalse();
                          },
                          [&](const typename bool_expr::BAnd &_args1) -> void {
                            _result = bool_expr::band(_args1.d_a0, _args1.d_a1);
                          },
                          [&](const typename bool_expr::BOr &_args1) -> void {
                            _result = bool_expr::bor(_args1.d_a0, _args1.d_a1);
                          },
                          [&](const typename bool_expr::BNot &_args1) -> void {
                            _result = bool_expr::bnot(_args1.d_a0);
                          }},
                      _result->v());
                },
                [&](_Call3 _f) {
                  std::shared_ptr<bool_expr> a_ = _f._s0;
                  std::visit(
                      Overloaded{
                          [&](const typename bool_expr::BTrue &) -> void {
                            _result = std::move(a_);
                          },
                          [&](const typename bool_expr::BFalse &) -> void {
                            _result = bool_expr::bfalse();
                          },
                          [&](const typename bool_expr::BAnd &_args1) -> void {
                            _result = bool_expr::band(
                                a_, bool_expr::band(_args1.d_a0, _args1.d_a1));
                          },
                          [&](const typename bool_expr::BOr &_args1) -> void {
                            _result = bool_expr::band(
                                a_, bool_expr::bor(_args1.d_a0, _args1.d_a1));
                          },
                          [&](const typename bool_expr::BNot &_args1) -> void {
                            _result = bool_expr::band(
                                a_, bool_expr::bnot(_args1.d_a0));
                          }},
                      _result->v());
                },
                [&](_Call4 _f) {
                  std::shared_ptr<bool_expr> a_ = _f._s0;
                  std::visit(
                      Overloaded{
                          [&](const typename bool_expr::BTrue &) -> void {
                            _result = std::move(a_);
                          },
                          [&](const typename bool_expr::BFalse &) -> void {
                            _result = bool_expr::bfalse();
                          },
                          [&](const typename bool_expr::BAnd &_args1) -> void {
                            _result = bool_expr::band(
                                a_, bool_expr::band(_args1.d_a0, _args1.d_a1));
                          },
                          [&](const typename bool_expr::BOr &_args1) -> void {
                            _result = bool_expr::band(
                                a_, bool_expr::bor(_args1.d_a0, _args1.d_a1));
                          },
                          [&](const typename bool_expr::BNot &_args1) -> void {
                            _result = bool_expr::band(
                                a_, bool_expr::bnot(_args1.d_a0));
                          }},
                      _result->v());
                },
                [&](_Call5 _f) {
                  std::shared_ptr<bool_expr> a_ = _f._s0;
                  std::visit(
                      Overloaded{
                          [&](const typename bool_expr::BTrue &) -> void {
                            _result = std::move(a_);
                          },
                          [&](const typename bool_expr::BFalse &) -> void {
                            _result = bool_expr::bfalse();
                          },
                          [&](const typename bool_expr::BAnd &_args1) -> void {
                            _result = bool_expr::band(
                                a_, bool_expr::band(_args1.d_a0, _args1.d_a1));
                          },
                          [&](const typename bool_expr::BOr &_args1) -> void {
                            _result = bool_expr::band(
                                a_, bool_expr::bor(_args1.d_a0, _args1.d_a1));
                          },
                          [&](const typename bool_expr::BNot &_args1) -> void {
                            _result = bool_expr::band(
                                a_, bool_expr::bnot(_args1.d_a0));
                          }},
                      _result->v());
                },
                [&](_Call6 _f) {
                  const typename bool_expr::BOr _args = _f._s0;
                  std::visit(
                      Overloaded{
                          [&](const typename bool_expr::BTrue &) -> void {
                            _result = bool_expr::btrue();
                          },
                          [&](const typename bool_expr::BFalse &) -> void {
                            _stack.push_back(_Call7{});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename bool_expr::BAnd &_args0) -> void {
                            std::shared_ptr<bool_expr> a_ =
                                bool_expr::band(_args0.d_a0, _args0.d_a1);
                            _stack.push_back(_Call8{a_});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename bool_expr::BOr &_args0) -> void {
                            std::shared_ptr<bool_expr> a_ =
                                bool_expr::bor(_args0.d_a0, _args0.d_a1);
                            _stack.push_back(_Call9{a_});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename bool_expr::BNot &_args0) -> void {
                            std::shared_ptr<bool_expr> a_ =
                                bool_expr::bnot(_args0.d_a0);
                            _stack.push_back(_Call10{a_});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          }},
                      _result->v());
                },
                [&](_Call7) {
                  std::visit(
                      Overloaded{
                          [&](const typename bool_expr::BTrue &) -> void {
                            _result = bool_expr::btrue();
                          },
                          [&](const typename bool_expr::BFalse &) -> void {
                            _result = bool_expr::bfalse();
                          },
                          [&](const typename bool_expr::BAnd &_args1) -> void {
                            _result = bool_expr::band(_args1.d_a0, _args1.d_a1);
                          },
                          [&](const typename bool_expr::BOr &_args1) -> void {
                            _result = bool_expr::bor(_args1.d_a0, _args1.d_a1);
                          },
                          [&](const typename bool_expr::BNot &_args1) -> void {
                            _result = bool_expr::bnot(_args1.d_a0);
                          }},
                      _result->v());
                },
                [&](_Call8 _f) {
                  std::shared_ptr<bool_expr> a_ = _f._s0;
                  std::visit(
                      Overloaded{
                          [&](const typename bool_expr::BTrue &) -> void {
                            _result = bool_expr::btrue();
                          },
                          [&](const typename bool_expr::BFalse &) -> void {
                            _result = std::move(a_);
                          },
                          [&](const typename bool_expr::BAnd &_args1) -> void {
                            _result = bool_expr::bor(
                                a_, bool_expr::band(_args1.d_a0, _args1.d_a1));
                          },
                          [&](const typename bool_expr::BOr &_args1) -> void {
                            _result = bool_expr::bor(
                                a_, bool_expr::bor(_args1.d_a0, _args1.d_a1));
                          },
                          [&](const typename bool_expr::BNot &_args1) -> void {
                            _result = bool_expr::bor(
                                a_, bool_expr::bnot(_args1.d_a0));
                          }},
                      _result->v());
                },
                [&](_Call9 _f) {
                  std::shared_ptr<bool_expr> a_ = _f._s0;
                  std::visit(
                      Overloaded{
                          [&](const typename bool_expr::BTrue &) -> void {
                            _result = bool_expr::btrue();
                          },
                          [&](const typename bool_expr::BFalse &) -> void {
                            _result = std::move(a_);
                          },
                          [&](const typename bool_expr::BAnd &_args1) -> void {
                            _result = bool_expr::bor(
                                a_, bool_expr::band(_args1.d_a0, _args1.d_a1));
                          },
                          [&](const typename bool_expr::BOr &_args1) -> void {
                            _result = bool_expr::bor(
                                a_, bool_expr::bor(_args1.d_a0, _args1.d_a1));
                          },
                          [&](const typename bool_expr::BNot &_args1) -> void {
                            _result = bool_expr::bor(
                                a_, bool_expr::bnot(_args1.d_a0));
                          }},
                      _result->v());
                }},
            _frame);
      }
      return _result;
    }

    __attribute__((pure)) bool eval_bool() const {
      const bool_expr *_self = this;

      struct _Enter {
        const bool_expr *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename bool_expr::BAnd &>()
                     .d_a0.get()) _s0;
      };

      struct _Call2 {
        bool _s0;
      };

      struct _Call3 {
        decltype(std::declval<const typename bool_expr::BOr &>()
                     .d_a0.get()) _s0;
      };

      struct _Call4 {
        bool _s0;
      };

      struct _Call5 {};

      using _Frame =
          std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5>;
      bool _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const bool_expr *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename bool_expr::BTrue &) -> void {
                            _result = true;
                          },
                          [&](const typename bool_expr::BFalse &) -> void {
                            _result = false;
                          },
                          [&](const typename bool_expr::BAnd &_args) -> void {
                            _stack.push_back(_Call1{_args.d_a0.get()});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename bool_expr::BOr &_args) -> void {
                            _stack.push_back(_Call3{_args.d_a0.get()});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename bool_expr::BNot &_args) -> void {
                            _stack.push_back(_Call5{});
                            _stack.push_back(_Enter{_args.d_a0.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.push_back(_Call2{_result});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) { _result = (_result && _f._s0); },
                [&](_Call3 _f) {
                  _stack.push_back(_Call4{_result});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call4 _f) { _result = (_result || _f._s0); },
                [&](_Call5) { _result = !(_result); }},
            _frame);
      }
      return _result;
    }
  };

  template <
      typename T1,
      MapsTo<T1, std::shared_ptr<bool_expr>, T1, std::shared_ptr<bool_expr>, T1>
          F2,
      MapsTo<T1, std::shared_ptr<bool_expr>, T1, std::shared_ptr<bool_expr>, T1>
          F3,
      MapsTo<T1, std::shared_ptr<bool_expr>, T1> F4>
  static T1 bool_expr_rect(const T1 f, const T1 f0, F2 &&f1, F3 &&f2, F4 &&f3,
                           const std::shared_ptr<bool_expr> &b) {
    struct _Enter {
      const std::shared_ptr<bool_expr> b;
    };

    struct _Call1 {
      decltype(std::declval<const typename bool_expr::BAnd &>().d_a0) _s0;
      decltype(std::declval<const typename bool_expr::BAnd &>().d_a1) _s1;
      decltype(std::declval<const typename bool_expr::BAnd &>().d_a0) _s2;
    };

    struct _Call2 {
      T1 _s0;
      decltype(std::declval<const typename bool_expr::BAnd &>().d_a1) _s1;
      decltype(std::declval<const typename bool_expr::BAnd &>().d_a0) _s2;
    };

    struct _Call3 {
      decltype(std::declval<const typename bool_expr::BOr &>().d_a0) _s0;
      decltype(std::declval<const typename bool_expr::BOr &>().d_a1) _s1;
      decltype(std::declval<const typename bool_expr::BOr &>().d_a0) _s2;
    };

    struct _Call4 {
      T1 _s0;
      decltype(std::declval<const typename bool_expr::BOr &>().d_a1) _s1;
      decltype(std::declval<const typename bool_expr::BOr &>().d_a0) _s2;
    };

    struct _Call5 {
      decltype(std::declval<const typename bool_expr::BNot &>().d_a0) _s0;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{b});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<bool_expr> b = _f.b;
                std::visit(
                    Overloaded{
                        [&](const typename bool_expr::BTrue &) -> void {
                          _result = f;
                        },
                        [&](const typename bool_expr::BFalse &) -> void {
                          _result = f0;
                        },
                        [&](const typename bool_expr::BAnd &_args) -> void {
                          _stack.push_back(
                              _Call1{_args.d_a0, _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        },
                        [&](const typename bool_expr::BOr &_args) -> void {
                          _stack.push_back(
                              _Call3{_args.d_a0, _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        },
                        [&](const typename bool_expr::BNot &_args) -> void {
                          _stack.push_back(_Call5{_args.d_a0});
                          _stack.push_back(_Enter{_args.d_a0});
                        }},
                    b->v());
              },
              [&](_Call1 _f) {
                _stack.push_back(_Call2{_result, _f._s1, _f._s2});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) { _result = f1(_f._s2, _result, _f._s1, _f._s0); },
              [&](_Call3 _f) {
                _stack.push_back(_Call4{_result, _f._s1, _f._s2});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call4 _f) { _result = f2(_f._s2, _result, _f._s1, _f._s0); },
              [&](_Call5 _f) { _result = f3(_f._s0, _result); }},
          _frame);
    }
    return _result;
  }

  template <
      typename T1,
      MapsTo<T1, std::shared_ptr<bool_expr>, T1, std::shared_ptr<bool_expr>, T1>
          F2,
      MapsTo<T1, std::shared_ptr<bool_expr>, T1, std::shared_ptr<bool_expr>, T1>
          F3,
      MapsTo<T1, std::shared_ptr<bool_expr>, T1> F4>
  static T1 bool_expr_rec(const T1 f, const T1 f0, F2 &&f1, F3 &&f2, F4 &&f3,
                          const std::shared_ptr<bool_expr> &b) {
    struct _Enter {
      const std::shared_ptr<bool_expr> b;
    };

    struct _Call1 {
      decltype(std::declval<const typename bool_expr::BAnd &>().d_a0) _s0;
      decltype(std::declval<const typename bool_expr::BAnd &>().d_a1) _s1;
      decltype(std::declval<const typename bool_expr::BAnd &>().d_a0) _s2;
    };

    struct _Call2 {
      T1 _s0;
      decltype(std::declval<const typename bool_expr::BAnd &>().d_a1) _s1;
      decltype(std::declval<const typename bool_expr::BAnd &>().d_a0) _s2;
    };

    struct _Call3 {
      decltype(std::declval<const typename bool_expr::BOr &>().d_a0) _s0;
      decltype(std::declval<const typename bool_expr::BOr &>().d_a1) _s1;
      decltype(std::declval<const typename bool_expr::BOr &>().d_a0) _s2;
    };

    struct _Call4 {
      T1 _s0;
      decltype(std::declval<const typename bool_expr::BOr &>().d_a1) _s1;
      decltype(std::declval<const typename bool_expr::BOr &>().d_a0) _s2;
    };

    struct _Call5 {
      decltype(std::declval<const typename bool_expr::BNot &>().d_a0) _s0;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{b});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<bool_expr> b = _f.b;
                std::visit(
                    Overloaded{
                        [&](const typename bool_expr::BTrue &) -> void {
                          _result = f;
                        },
                        [&](const typename bool_expr::BFalse &) -> void {
                          _result = f0;
                        },
                        [&](const typename bool_expr::BAnd &_args) -> void {
                          _stack.push_back(
                              _Call1{_args.d_a0, _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        },
                        [&](const typename bool_expr::BOr &_args) -> void {
                          _stack.push_back(
                              _Call3{_args.d_a0, _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        },
                        [&](const typename bool_expr::BNot &_args) -> void {
                          _stack.push_back(_Call5{_args.d_a0});
                          _stack.push_back(_Enter{_args.d_a0});
                        }},
                    b->v());
              },
              [&](_Call1 _f) {
                _stack.push_back(_Call2{_result, _f._s1, _f._s2});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) { _result = f1(_f._s2, _result, _f._s1, _f._s0); },
              [&](_Call3 _f) {
                _stack.push_back(_Call4{_result, _f._s1, _f._s2});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call4 _f) { _result = f2(_f._s2, _result, _f._s1, _f._s0); },
              [&](_Call5 _f) { _result = f3(_f._s0, _result); }},
          _frame);
    }
    return _result;
  }

  struct list_expr {
    // TYPES
    struct LNil {};

    struct LCons {
      unsigned int d_a0;
      std::shared_ptr<list_expr> d_a1;
    };

    struct LAppend {
      std::shared_ptr<list_expr> d_a0;
      std::shared_ptr<list_expr> d_a1;
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
    explicit list_expr(LNil _v) : d_v_(std::move(_v)) {}

    explicit list_expr(LCons _v) : d_v_(std::move(_v)) {}

    explicit list_expr(LAppend _v) : d_v_(std::move(_v)) {}

    explicit list_expr(LReplicate _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<list_expr> lnil() {
      return std::make_shared<list_expr>(LNil{});
    }

    static std::shared_ptr<list_expr>
    lcons(unsigned int a0, const std::shared_ptr<list_expr> &a1) {
      return std::make_shared<list_expr>(LCons{std::move(a0), a1});
    }

    static std::shared_ptr<list_expr> lcons(unsigned int a0,
                                            std::shared_ptr<list_expr> &&a1) {
      return std::make_shared<list_expr>(LCons{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<list_expr>
    lappend(const std::shared_ptr<list_expr> &a0,
            const std::shared_ptr<list_expr> &a1) {
      return std::make_shared<list_expr>(LAppend{a0, a1});
    }

    static std::shared_ptr<list_expr> lappend(std::shared_ptr<list_expr> &&a0,
                                              std::shared_ptr<list_expr> &&a1) {
      return std::make_shared<list_expr>(LAppend{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<list_expr> lreplicate(unsigned int a0,
                                                 unsigned int a1) {
      return std::make_shared<list_expr>(
          LReplicate{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

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
        decltype(std::declval<const typename list_expr::LAppend &>()
                     .d_a0.get()) _s0;
        decltype(1u) _s1;
      };

      struct _Call3 {
        unsigned int _s0;
        decltype(1u) _s1;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const list_expr *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename list_expr::LCons &_args) -> void {
                            _stack.push_back(_Call1{1u});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename list_expr::LAppend &_args)
                              -> void {
                            _stack.push_back(_Call2{_args.d_a0.get(), 1u});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const auto &) -> void { _result = 1u; }},
                      _self->v());
                },
                [&](_Call1 _f) { _result = (_f._s0 + _result); },
                [&](_Call2 _f) {
                  _stack.push_back(_Call3{_result, _f._s1});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call3 _f) { _result = ((_f._s1 + _result) + _f._s0); }},
            _frame);
      }
      return _result;
    }

    std::shared_ptr<List<unsigned int>> eval_list() const {
      const list_expr *_self = this;

      struct _Enter {
        const list_expr *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename list_expr::LCons &>().d_a0) _s0;
      };

      struct _Call2 {
        decltype(std::declval<const typename list_expr::LAppend &>()
                     .d_a0.get()) _s0;
      };

      struct _Call3 {
        std::shared_ptr<List<unsigned int>> _s0;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
      std::shared_ptr<List<unsigned int>> _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const list_expr *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename list_expr::LNil &) -> void {
                            _result = List<unsigned int>::nil();
                          },
                          [&](const typename list_expr::LCons &_args) -> void {
                            _stack.push_back(_Call1{_args.d_a0});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename list_expr::LAppend &_args)
                              -> void {
                            _stack.push_back(_Call2{_args.d_a0.get()});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename list_expr::LReplicate &_args)
                              -> void {
                            _result = ListDef::template repeat<unsigned int>(
                                _args.d_a1, _args.d_a0);
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _result = List<unsigned int>::cons(_f._s0, _result);
                },
                [&](_Call2 _f) {
                  _stack.push_back(_Call3{_result});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call3 _f) { _result = _result->app(_f._s0); }},
            _frame);
      }
      return _result;
    }
  };

  template <
      typename T1, MapsTo<T1, unsigned int, std::shared_ptr<list_expr>, T1> F1,
      MapsTo<T1, std::shared_ptr<list_expr>, T1, std::shared_ptr<list_expr>, T1>
          F2,
      MapsTo<T1, unsigned int, unsigned int> F3>
  static T1 list_expr_rect(const T1 f, F1 &&f0, F2 &&f1, F3 &&f2,
                           const std::shared_ptr<list_expr> &l) {
    struct _Enter {
      const std::shared_ptr<list_expr> l;
    };

    struct _Call1 {
      decltype(std::declval<const typename list_expr::LCons &>().d_a1) _s0;
      decltype(std::declval<const typename list_expr::LCons &>().d_a0) _s1;
    };

    struct _Call2 {
      decltype(std::declval<const typename list_expr::LAppend &>().d_a0) _s0;
      decltype(std::declval<const typename list_expr::LAppend &>().d_a1) _s1;
      decltype(std::declval<const typename list_expr::LAppend &>().d_a0) _s2;
    };

    struct _Call3 {
      T1 _s0;
      decltype(std::declval<const typename list_expr::LAppend &>().d_a1) _s1;
      decltype(std::declval<const typename list_expr::LAppend &>().d_a0) _s2;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<list_expr> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename list_expr::LNil &) -> void {
                          _result = f;
                        },
                        [&](const typename list_expr::LCons &_args) -> void {
                          _stack.push_back(_Call1{_args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        },
                        [&](const typename list_expr::LAppend &_args) -> void {
                          _stack.push_back(
                              _Call2{_args.d_a0, _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        },
                        [&](const typename list_expr::LReplicate &_args)
                            -> void { _result = f2(_args.d_a0, _args.d_a1); }},
                    l->v());
              },
              [&](_Call1 _f) { _result = f0(_f._s1, _f._s0, _result); },
              [&](_Call2 _f) {
                _stack.push_back(_Call3{_result, _f._s1, _f._s2});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call3 _f) {
                _result = f1(_f._s2, _result, _f._s1, _f._s0);
              }},
          _frame);
    }
    return _result;
  }

  template <
      typename T1, MapsTo<T1, unsigned int, std::shared_ptr<list_expr>, T1> F1,
      MapsTo<T1, std::shared_ptr<list_expr>, T1, std::shared_ptr<list_expr>, T1>
          F2,
      MapsTo<T1, unsigned int, unsigned int> F3>
  static T1 list_expr_rec(const T1 f, F1 &&f0, F2 &&f1, F3 &&f2,
                          const std::shared_ptr<list_expr> &l) {
    struct _Enter {
      const std::shared_ptr<list_expr> l;
    };

    struct _Call1 {
      decltype(std::declval<const typename list_expr::LCons &>().d_a1) _s0;
      decltype(std::declval<const typename list_expr::LCons &>().d_a0) _s1;
    };

    struct _Call2 {
      decltype(std::declval<const typename list_expr::LAppend &>().d_a0) _s0;
      decltype(std::declval<const typename list_expr::LAppend &>().d_a1) _s1;
      decltype(std::declval<const typename list_expr::LAppend &>().d_a0) _s2;
    };

    struct _Call3 {
      T1 _s0;
      decltype(std::declval<const typename list_expr::LAppend &>().d_a1) _s1;
      decltype(std::declval<const typename list_expr::LAppend &>().d_a0) _s2;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<list_expr> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename list_expr::LNil &) -> void {
                          _result = f;
                        },
                        [&](const typename list_expr::LCons &_args) -> void {
                          _stack.push_back(_Call1{_args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        },
                        [&](const typename list_expr::LAppend &_args) -> void {
                          _stack.push_back(
                              _Call2{_args.d_a0, _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        },
                        [&](const typename list_expr::LReplicate &_args)
                            -> void { _result = f2(_args.d_a0, _args.d_a1); }},
                    l->v());
              },
              [&](_Call1 _f) { _result = f0(_f._s1, _f._s0, _result); },
              [&](_Call2 _f) {
                _stack.push_back(_Call3{_result, _f._s1, _f._s2});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call3 _f) {
                _result = f1(_f._s2, _result, _f._s1, _f._s0);
              }},
          _frame);
    }
    return _result;
  }
};

template <typename T1>
std::shared_ptr<List<T1>> ListDef::repeat(const T1 x, const unsigned int n) {
  std::shared_ptr<List<T1>> _head{};
  std::shared_ptr<List<T1>> _last{};
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    if (_loop_n <= 0) {
      {
        if (_last) {
          std::get<typename List<T1>::Cons>(_last->v_mut()).d_a1 =
              List<T1>::nil();
        } else {
          _head = List<T1>::nil();
        }
        _continue = false;
      }
    } else {
      unsigned int k = _loop_n - 1;
      {
        auto _cell = List<T1>::cons(x, nullptr);
        if (_last) {
          std::get<typename List<T1>::Cons>(_last->v_mut()).d_a1 = _cell;
        } else {
          _head = _cell;
        }
        _last = _cell;
        _loop_n = k;
        continue;
      }
    }
  }
  return _head;
}

#endif // INCLUDED_LOOPIFY_EXPR_VARIANTS
