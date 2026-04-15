#ifndef INCLUDED_LOOPIFY_EXPR_VARIANTS
#define INCLUDED_LOOPIFY_EXPR_VARIANTS

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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
  explicit List(Nil _v) : d_v_(_v) {}

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
      if (std::holds_alternative<typename List<t_A>::Nil>(_loop_self->v())) {
        if (_last) {
          std::get<typename List<t_A>::Cons>(_last->v_mut()).d_a1 = m;
        } else {
          _head = m;
        }
        _continue = false;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<t_A>::Cons>(_loop_self->v());
        auto _cell = List<t_A>::cons(d_a0, nullptr);
        if (_last) {
          std::get<typename List<t_A>::Cons>(_last->v_mut()).d_a1 = _cell;
        } else {
          _head = _cell;
        }
        _last = _cell;
        _loop_self = d_a1.get();
        continue;
      }
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
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          const auto &_f = std::get<_Enter>(_frame);
          const cond_expr *_self = _f._self;
          if (std::holds_alternative<typename cond_expr::Lit>(_self->v())) {
            _result = 1u;
          } else if (std::holds_alternative<typename cond_expr::Add>(
                         _self->v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename cond_expr::Add>(_self->v());
            _stack.emplace_back(_Call1{d_a0.get(), 1u});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename cond_expr::Cond>(_self->v());
            _stack.emplace_back(_Call3{d_a1.get(), d_a0.get(), 1u});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          const auto &_f = std::get<_Call1>(_frame);
          _stack.emplace_back(_Call2{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          const auto &_f = std::get<_Call2>(_frame);
          _result = ((_f._s1 + _result) + _f._s0);
        } else if (std::holds_alternative<_Call3>(_frame)) {
          const auto &_f = std::get<_Call3>(_frame);
          _stack.emplace_back(_Call4{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call4>(_frame)) {
          const auto &_f = std::get<_Call4>(_frame);
          _stack.emplace_back(_Call5{_f._s0, _result, _f._s2});
          _stack.emplace_back(_Enter{_f._s1});
        } else {
          const auto &_f = std::get<_Call5>(_frame);
          _result = (((_f._s2 + _result) + _f._s1) + _f._s0);
        }
      }
      return _result;
    }

    __attribute__((pure)) unsigned int eval_cond() const {
      const cond_expr *_self = this;

      struct _Enter {
        const cond_expr *_self;
      };

      struct _Call1 {
        cond_expr *_s0;
      };

      struct _Call2 {
        unsigned int _s0;
      };

      struct _Call3 {
        std::shared_ptr<cond_expr> _s0;
        std::shared_ptr<cond_expr> _s1;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          const auto &_f = std::get<_Enter>(_frame);
          const cond_expr *_self = _f._self;
          if (std::holds_alternative<typename cond_expr::Lit>(_self->v())) {
            const auto &[d_a0] = std::get<typename cond_expr::Lit>(_self->v());
            _result = d_a0;
          } else if (std::holds_alternative<typename cond_expr::Add>(
                         _self->v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename cond_expr::Add>(_self->v());
            _stack.emplace_back(_Call1{d_a0.get()});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename cond_expr::Cond>(_self->v());
            _stack.emplace_back(_Call3{d_a1, d_a2});
            _stack.emplace_back(_Enter{d_a0.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          const auto &_f = std::get<_Call1>(_frame);
          _stack.emplace_back(_Call2{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          const auto &_f = std::get<_Call2>(_frame);
          _result = (_result + _f._s0);
        } else {
          const auto &_f = std::get<_Call3>(_frame);
          std::shared_ptr<cond_expr> d_a1 = _f._s0;
          std::shared_ptr<cond_expr> d_a2 = _f._s1;
          unsigned int _cond0 = _result;
          if (0u < _cond0) {
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        }
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
        cond_expr *_s0;
        std::shared_ptr<cond_expr> _s1;
        std::shared_ptr<cond_expr> _s2;
      };

      struct _Call2 {
        T1 _s0;
        std::shared_ptr<cond_expr> _s1;
        std::shared_ptr<cond_expr> _s2;
      };

      struct _Call3 {
        const cond_expr *_s0;
        const cond_expr *_s1;
        std::shared_ptr<cond_expr> _s2;
        std::shared_ptr<cond_expr> _s3;
        std::shared_ptr<cond_expr> _s4;
      };

      struct _Call4 {
        T1 _s0;
        const cond_expr *_s1;
        std::shared_ptr<cond_expr> _s2;
        std::shared_ptr<cond_expr> _s3;
        std::shared_ptr<cond_expr> _s4;
      };

      struct _Call5 {
        T1 _s0;
        T1 _s1;
        std::shared_ptr<cond_expr> _s2;
        std::shared_ptr<cond_expr> _s3;
        std::shared_ptr<cond_expr> _s4;
      };

      using _Frame =
          std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          const auto &_f = std::get<_Enter>(_frame);
          const cond_expr *_self = _f._self;
          if (std::holds_alternative<typename cond_expr::Lit>(_self->v())) {
            const auto &[d_a0] = std::get<typename cond_expr::Lit>(_self->v());
            _result = f(d_a0);
          } else if (std::holds_alternative<typename cond_expr::Add>(
                         _self->v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename cond_expr::Add>(_self->v());
            _stack.emplace_back(_Call1{d_a0.get(), d_a1, d_a0});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename cond_expr::Cond>(_self->v());
            _stack.emplace_back(
                _Call3{d_a1.get(), d_a0.get(), d_a2, d_a1, d_a0});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          const auto &_f = std::get<_Call1>(_frame);
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          const auto &_f = std::get<_Call2>(_frame);
          _result = f0(_f._s2, _result, _f._s1, _f._s0);
        } else if (std::holds_alternative<_Call3>(_frame)) {
          const auto &_f = std::get<_Call3>(_frame);
          _stack.emplace_back(_Call4{_result, _f._s1, _f._s2, _f._s3, _f._s4});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call4>(_frame)) {
          const auto &_f = std::get<_Call4>(_frame);
          _stack.emplace_back(_Call5{_f._s0, _result, _f._s2, _f._s3, _f._s4});
          _stack.emplace_back(_Enter{_f._s1});
        } else {
          const auto &_f = std::get<_Call5>(_frame);
          _result = f1(_f._s4, _result, _f._s3, _f._s1, _f._s2, _f._s0);
        }
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
        cond_expr *_s0;
        std::shared_ptr<cond_expr> _s1;
        std::shared_ptr<cond_expr> _s2;
      };

      struct _Call2 {
        T1 _s0;
        std::shared_ptr<cond_expr> _s1;
        std::shared_ptr<cond_expr> _s2;
      };

      struct _Call3 {
        const cond_expr *_s0;
        const cond_expr *_s1;
        std::shared_ptr<cond_expr> _s2;
        std::shared_ptr<cond_expr> _s3;
        std::shared_ptr<cond_expr> _s4;
      };

      struct _Call4 {
        T1 _s0;
        const cond_expr *_s1;
        std::shared_ptr<cond_expr> _s2;
        std::shared_ptr<cond_expr> _s3;
        std::shared_ptr<cond_expr> _s4;
      };

      struct _Call5 {
        T1 _s0;
        T1 _s1;
        std::shared_ptr<cond_expr> _s2;
        std::shared_ptr<cond_expr> _s3;
        std::shared_ptr<cond_expr> _s4;
      };

      using _Frame =
          std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          const auto &_f = std::get<_Enter>(_frame);
          const cond_expr *_self = _f._self;
          if (std::holds_alternative<typename cond_expr::Lit>(_self->v())) {
            const auto &[d_a0] = std::get<typename cond_expr::Lit>(_self->v());
            _result = f(d_a0);
          } else if (std::holds_alternative<typename cond_expr::Add>(
                         _self->v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename cond_expr::Add>(_self->v());
            _stack.emplace_back(_Call1{d_a0.get(), d_a1, d_a0});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename cond_expr::Cond>(_self->v());
            _stack.emplace_back(
                _Call3{d_a1.get(), d_a0.get(), d_a2, d_a1, d_a0});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          const auto &_f = std::get<_Call1>(_frame);
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          const auto &_f = std::get<_Call2>(_frame);
          _result = f0(_f._s2, _result, _f._s1, _f._s0);
        } else if (std::holds_alternative<_Call3>(_frame)) {
          const auto &_f = std::get<_Call3>(_frame);
          _stack.emplace_back(_Call4{_result, _f._s1, _f._s2, _f._s3, _f._s4});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call4>(_frame)) {
          const auto &_f = std::get<_Call4>(_frame);
          _stack.emplace_back(_Call5{_f._s0, _result, _f._s2, _f._s3, _f._s4});
          _stack.emplace_back(_Enter{_f._s1});
        } else {
          const auto &_f = std::get<_Call5>(_frame);
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
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          const auto &_f = std::get<_Enter>(_frame);
          const arith_expr *_self = _f._self;
          if (std::holds_alternative<typename arith_expr::ANum>(_self->v())) {
            _result = 0u;
          } else if (std::holds_alternative<typename arith_expr::AAdd>(
                         _self->v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename arith_expr::AAdd>(_self->v());
            _stack.emplace_back(_Call1{d_a0.get(), 1u});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else if (std::holds_alternative<typename arith_expr::AMul>(
                         _self->v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename arith_expr::AMul>(_self->v());
            _stack.emplace_back(_Call3{d_a0.get(), 1u});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename arith_expr::ADiv>(_self->v());
            _stack.emplace_back(_Call5{d_a0.get(), 1u});
            _stack.emplace_back(_Enter{d_a1.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          const auto &_f = std::get<_Call1>(_frame);
          _stack.emplace_back(_Call2{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          const auto &_f = std::get<_Call2>(_frame);
          _result = ((_f._s1 + _result) + _f._s0);
        } else if (std::holds_alternative<_Call3>(_frame)) {
          const auto &_f = std::get<_Call3>(_frame);
          _stack.emplace_back(_Call4{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call4>(_frame)) {
          const auto &_f = std::get<_Call4>(_frame);
          _result = ((_f._s1 + _result) + _f._s0);
        } else if (std::holds_alternative<_Call5>(_frame)) {
          const auto &_f = std::get<_Call5>(_frame);
          _stack.emplace_back(_Call6{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          const auto &_f = std::get<_Call6>(_frame);
          _result = ((_f._s1 + _result) + _f._s0);
        }
      }
      return _result;
    }

    __attribute__((pure)) unsigned int eval_arith() const {
      const arith_expr *_self = this;

      struct _Enter {
        const arith_expr *_self;
      };

      struct _Call1 {
        arith_expr *_s0;
      };

      struct _Call2 {
        unsigned int _s0;
      };

      struct _Call3 {
        arith_expr *_s0;
      };

      struct _Call4 {
        unsigned int _s0;
      };

      struct _Call5 {
        std::shared_ptr<arith_expr> _s0;
      };

      struct _Call6 {
        decltype((std::declval<unsigned int &>() + 1)) _s0;
      };

      using _Frame =
          std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5, _Call6>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          const auto &_f = std::get<_Enter>(_frame);
          const arith_expr *_self = _f._self;
          if (std::holds_alternative<typename arith_expr::ANum>(_self->v())) {
            const auto &[d_a0] =
                std::get<typename arith_expr::ANum>(_self->v());
            _result = d_a0;
          } else if (std::holds_alternative<typename arith_expr::AAdd>(
                         _self->v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename arith_expr::AAdd>(_self->v());
            _stack.emplace_back(_Call1{d_a0.get()});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else if (std::holds_alternative<typename arith_expr::AMul>(
                         _self->v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename arith_expr::AMul>(_self->v());
            _stack.emplace_back(_Call3{d_a0.get()});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename arith_expr::ADiv>(_self->v());
            _stack.emplace_back(_Call5{d_a0});
            _stack.emplace_back(_Enter{d_a1.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          const auto &_f = std::get<_Call1>(_frame);
          _stack.emplace_back(_Call2{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          const auto &_f = std::get<_Call2>(_frame);
          _result = (_result + _f._s0);
        } else if (std::holds_alternative<_Call3>(_frame)) {
          const auto &_f = std::get<_Call3>(_frame);
          _stack.emplace_back(_Call4{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call4>(_frame)) {
          const auto &_f = std::get<_Call4>(_frame);
          _result = (_result * _f._s0);
        } else if (std::holds_alternative<_Call5>(_frame)) {
          const auto &_f = std::get<_Call5>(_frame);
          std::shared_ptr<arith_expr> d_a0 = _f._s0;
          if (_result <= 0) {
            _result = 0u;
          } else {
            unsigned int n = _result - 1;
            _stack.emplace_back(_Call6{(n + 1)});
            _stack.emplace_back(_Enter{d_a0.get()});
          }
        } else {
          const auto &_f = std::get<_Call6>(_frame);
          _result = (_f._s0 ? _result / _f._s0 : 0);
        }
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
        arith_expr *_s0;
        std::shared_ptr<arith_expr> _s1;
        std::shared_ptr<arith_expr> _s2;
      };

      struct _Call2 {
        T1 _s0;
        std::shared_ptr<arith_expr> _s1;
        std::shared_ptr<arith_expr> _s2;
      };

      struct _Call3 {
        arith_expr *_s0;
        std::shared_ptr<arith_expr> _s1;
        std::shared_ptr<arith_expr> _s2;
      };

      struct _Call4 {
        T1 _s0;
        std::shared_ptr<arith_expr> _s1;
        std::shared_ptr<arith_expr> _s2;
      };

      struct _Call5 {
        arith_expr *_s0;
        std::shared_ptr<arith_expr> _s1;
        std::shared_ptr<arith_expr> _s2;
      };

      struct _Call6 {
        T1 _s0;
        std::shared_ptr<arith_expr> _s1;
        std::shared_ptr<arith_expr> _s2;
      };

      using _Frame =
          std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5, _Call6>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          const auto &_f = std::get<_Enter>(_frame);
          const arith_expr *_self = _f._self;
          if (std::holds_alternative<typename arith_expr::ANum>(_self->v())) {
            const auto &[d_a0] =
                std::get<typename arith_expr::ANum>(_self->v());
            _result = f(d_a0);
          } else if (std::holds_alternative<typename arith_expr::AAdd>(
                         _self->v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename arith_expr::AAdd>(_self->v());
            _stack.emplace_back(_Call1{d_a0.get(), d_a1, d_a0});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else if (std::holds_alternative<typename arith_expr::AMul>(
                         _self->v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename arith_expr::AMul>(_self->v());
            _stack.emplace_back(_Call3{d_a0.get(), d_a1, d_a0});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename arith_expr::ADiv>(_self->v());
            _stack.emplace_back(_Call5{d_a0.get(), d_a1, d_a0});
            _stack.emplace_back(_Enter{d_a1.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          const auto &_f = std::get<_Call1>(_frame);
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          const auto &_f = std::get<_Call2>(_frame);
          _result = f0(_f._s2, _result, _f._s1, _f._s0);
        } else if (std::holds_alternative<_Call3>(_frame)) {
          const auto &_f = std::get<_Call3>(_frame);
          _stack.emplace_back(_Call4{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call4>(_frame)) {
          const auto &_f = std::get<_Call4>(_frame);
          _result = f1(_f._s2, _result, _f._s1, _f._s0);
        } else if (std::holds_alternative<_Call5>(_frame)) {
          const auto &_f = std::get<_Call5>(_frame);
          _stack.emplace_back(_Call6{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          const auto &_f = std::get<_Call6>(_frame);
          _result = f2(_f._s2, _result, _f._s1, _f._s0);
        }
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
        arith_expr *_s0;
        std::shared_ptr<arith_expr> _s1;
        std::shared_ptr<arith_expr> _s2;
      };

      struct _Call2 {
        T1 _s0;
        std::shared_ptr<arith_expr> _s1;
        std::shared_ptr<arith_expr> _s2;
      };

      struct _Call3 {
        arith_expr *_s0;
        std::shared_ptr<arith_expr> _s1;
        std::shared_ptr<arith_expr> _s2;
      };

      struct _Call4 {
        T1 _s0;
        std::shared_ptr<arith_expr> _s1;
        std::shared_ptr<arith_expr> _s2;
      };

      struct _Call5 {
        arith_expr *_s0;
        std::shared_ptr<arith_expr> _s1;
        std::shared_ptr<arith_expr> _s2;
      };

      struct _Call6 {
        T1 _s0;
        std::shared_ptr<arith_expr> _s1;
        std::shared_ptr<arith_expr> _s2;
      };

      using _Frame =
          std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5, _Call6>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          const auto &_f = std::get<_Enter>(_frame);
          const arith_expr *_self = _f._self;
          if (std::holds_alternative<typename arith_expr::ANum>(_self->v())) {
            const auto &[d_a0] =
                std::get<typename arith_expr::ANum>(_self->v());
            _result = f(d_a0);
          } else if (std::holds_alternative<typename arith_expr::AAdd>(
                         _self->v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename arith_expr::AAdd>(_self->v());
            _stack.emplace_back(_Call1{d_a0.get(), d_a1, d_a0});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else if (std::holds_alternative<typename arith_expr::AMul>(
                         _self->v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename arith_expr::AMul>(_self->v());
            _stack.emplace_back(_Call3{d_a0.get(), d_a1, d_a0});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename arith_expr::ADiv>(_self->v());
            _stack.emplace_back(_Call5{d_a0.get(), d_a1, d_a0});
            _stack.emplace_back(_Enter{d_a1.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          const auto &_f = std::get<_Call1>(_frame);
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          const auto &_f = std::get<_Call2>(_frame);
          _result = f0(_f._s2, _result, _f._s1, _f._s0);
        } else if (std::holds_alternative<_Call3>(_frame)) {
          const auto &_f = std::get<_Call3>(_frame);
          _stack.emplace_back(_Call4{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call4>(_frame)) {
          const auto &_f = std::get<_Call4>(_frame);
          _result = f1(_f._s2, _result, _f._s1, _f._s0);
        } else if (std::holds_alternative<_Call5>(_frame)) {
          const auto &_f = std::get<_Call5>(_frame);
          _stack.emplace_back(_Call6{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          const auto &_f = std::get<_Call6>(_frame);
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
    explicit bool_expr(BTrue _v) : d_v_(_v) {}

    explicit bool_expr(BFalse _v) : d_v_(_v) {}

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

      using _Frame = std::variant<_Enter>;
      std::shared_ptr<bool_expr> _result{};
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        const auto &_f = std::get<_Enter>(_frame);
        const bool_expr *_self = _f._self;
        if (std::holds_alternative<typename bool_expr::BTrue>(_self->v())) {
          _result = bool_expr::btrue();
        } else if (std::holds_alternative<typename bool_expr::BFalse>(
                       _self->v())) {
          _result = bool_expr::bfalse();
        } else if (std::holds_alternative<typename bool_expr::BAnd>(
                       _self->v())) {
          const auto &[d_a0, d_a1] =
              std::get<typename bool_expr::BAnd>(_self->v());
          auto &&_sv0 = d_a0->simplify_bool();
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv0->v())) {
            auto &&_sv1 = d_a1->simplify_bool();
            if (std::holds_alternative<typename bool_expr::BTrue>(_sv1->v())) {
              _result = bool_expr::btrue();
            } else if (std::holds_alternative<typename bool_expr::BFalse>(
                           _sv1->v())) {
              _result = bool_expr::bfalse();
            } else if (std::holds_alternative<typename bool_expr::BAnd>(
                           _sv1->v())) {
              const auto &[d_a01, d_a11] =
                  std::get<typename bool_expr::BAnd>(_sv1->v());
              _result = bool_expr::band(d_a01, d_a11);
            } else if (std::holds_alternative<typename bool_expr::BOr>(
                           _sv1->v())) {
              const auto &[d_a01, d_a11] =
                  std::get<typename bool_expr::BOr>(_sv1->v());
              _result = bool_expr::bor(d_a01, d_a11);
            } else {
              const auto &[d_a01] =
                  std::get<typename bool_expr::BNot>(_sv1->v());
              _result = bool_expr::bnot(d_a01);
            }
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv0->v())) {
            _result = bool_expr::bfalse();
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv0->v())) {
            const auto &[d_a00, d_a10] =
                std::get<typename bool_expr::BAnd>(_sv0->v());
            std::shared_ptr<bool_expr> a_ = bool_expr::band(d_a00, d_a10);
            auto &&_sv1 = d_a1->simplify_bool();
            if (std::holds_alternative<typename bool_expr::BTrue>(_sv1->v())) {
              _result = std::move(a_);
            } else if (std::holds_alternative<typename bool_expr::BFalse>(
                           _sv1->v())) {
              _result = bool_expr::bfalse();
            } else if (std::holds_alternative<typename bool_expr::BAnd>(
                           _sv1->v())) {
              const auto &[d_a01, d_a11] =
                  std::get<typename bool_expr::BAnd>(_sv1->v());
              _result = bool_expr::band(a_, bool_expr::band(d_a01, d_a11));
            } else if (std::holds_alternative<typename bool_expr::BOr>(
                           _sv1->v())) {
              const auto &[d_a01, d_a11] =
                  std::get<typename bool_expr::BOr>(_sv1->v());
              _result = bool_expr::band(a_, bool_expr::bor(d_a01, d_a11));
            } else {
              const auto &[d_a01] =
                  std::get<typename bool_expr::BNot>(_sv1->v());
              _result = bool_expr::band(a_, bool_expr::bnot(d_a01));
            }
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _sv0->v())) {
            const auto &[d_a00, d_a10] =
                std::get<typename bool_expr::BOr>(_sv0->v());
            std::shared_ptr<bool_expr> a_ = bool_expr::bor(d_a00, d_a10);
            auto &&_sv1 = d_a1->simplify_bool();
            if (std::holds_alternative<typename bool_expr::BTrue>(_sv1->v())) {
              _result = std::move(a_);
            } else if (std::holds_alternative<typename bool_expr::BFalse>(
                           _sv1->v())) {
              _result = bool_expr::bfalse();
            } else if (std::holds_alternative<typename bool_expr::BAnd>(
                           _sv1->v())) {
              const auto &[d_a01, d_a11] =
                  std::get<typename bool_expr::BAnd>(_sv1->v());
              _result = bool_expr::band(a_, bool_expr::band(d_a01, d_a11));
            } else if (std::holds_alternative<typename bool_expr::BOr>(
                           _sv1->v())) {
              const auto &[d_a01, d_a11] =
                  std::get<typename bool_expr::BOr>(_sv1->v());
              _result = bool_expr::band(a_, bool_expr::bor(d_a01, d_a11));
            } else {
              const auto &[d_a01] =
                  std::get<typename bool_expr::BNot>(_sv1->v());
              _result = bool_expr::band(a_, bool_expr::bnot(d_a01));
            }
          } else {
            const auto &[d_a00] = std::get<typename bool_expr::BNot>(_sv0->v());
            std::shared_ptr<bool_expr> a_ = bool_expr::bnot(d_a00);
            auto &&_sv1 = d_a1->simplify_bool();
            if (std::holds_alternative<typename bool_expr::BTrue>(_sv1->v())) {
              _result = std::move(a_);
            } else if (std::holds_alternative<typename bool_expr::BFalse>(
                           _sv1->v())) {
              _result = bool_expr::bfalse();
            } else if (std::holds_alternative<typename bool_expr::BAnd>(
                           _sv1->v())) {
              const auto &[d_a01, d_a11] =
                  std::get<typename bool_expr::BAnd>(_sv1->v());
              _result = bool_expr::band(a_, bool_expr::band(d_a01, d_a11));
            } else if (std::holds_alternative<typename bool_expr::BOr>(
                           _sv1->v())) {
              const auto &[d_a01, d_a11] =
                  std::get<typename bool_expr::BOr>(_sv1->v());
              _result = bool_expr::band(a_, bool_expr::bor(d_a01, d_a11));
            } else {
              const auto &[d_a01] =
                  std::get<typename bool_expr::BNot>(_sv1->v());
              _result = bool_expr::band(a_, bool_expr::bnot(d_a01));
            }
          }
        } else if (std::holds_alternative<typename bool_expr::BOr>(
                       _self->v())) {
          const auto &[d_a0, d_a1] =
              std::get<typename bool_expr::BOr>(_self->v());
          auto &&_sv0 = d_a0->simplify_bool();
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv0->v())) {
            _result = bool_expr::btrue();
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv0->v())) {
            auto &&_sv1 = d_a1->simplify_bool();
            if (std::holds_alternative<typename bool_expr::BTrue>(_sv1->v())) {
              _result = bool_expr::btrue();
            } else if (std::holds_alternative<typename bool_expr::BFalse>(
                           _sv1->v())) {
              _result = bool_expr::bfalse();
            } else if (std::holds_alternative<typename bool_expr::BAnd>(
                           _sv1->v())) {
              const auto &[d_a01, d_a11] =
                  std::get<typename bool_expr::BAnd>(_sv1->v());
              _result = bool_expr::band(d_a01, d_a11);
            } else if (std::holds_alternative<typename bool_expr::BOr>(
                           _sv1->v())) {
              const auto &[d_a01, d_a11] =
                  std::get<typename bool_expr::BOr>(_sv1->v());
              _result = bool_expr::bor(d_a01, d_a11);
            } else {
              const auto &[d_a01] =
                  std::get<typename bool_expr::BNot>(_sv1->v());
              _result = bool_expr::bnot(d_a01);
            }
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv0->v())) {
            const auto &[d_a00, d_a10] =
                std::get<typename bool_expr::BAnd>(_sv0->v());
            std::shared_ptr<bool_expr> a_ = bool_expr::band(d_a00, d_a10);
            auto &&_sv1 = d_a1->simplify_bool();
            if (std::holds_alternative<typename bool_expr::BTrue>(_sv1->v())) {
              _result = bool_expr::btrue();
            } else if (std::holds_alternative<typename bool_expr::BFalse>(
                           _sv1->v())) {
              _result = std::move(a_);
            } else if (std::holds_alternative<typename bool_expr::BAnd>(
                           _sv1->v())) {
              const auto &[d_a01, d_a11] =
                  std::get<typename bool_expr::BAnd>(_sv1->v());
              _result = bool_expr::bor(a_, bool_expr::band(d_a01, d_a11));
            } else if (std::holds_alternative<typename bool_expr::BOr>(
                           _sv1->v())) {
              const auto &[d_a01, d_a11] =
                  std::get<typename bool_expr::BOr>(_sv1->v());
              _result = bool_expr::bor(a_, bool_expr::bor(d_a01, d_a11));
            } else {
              const auto &[d_a01] =
                  std::get<typename bool_expr::BNot>(_sv1->v());
              _result = bool_expr::bor(a_, bool_expr::bnot(d_a01));
            }
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _sv0->v())) {
            const auto &[d_a00, d_a10] =
                std::get<typename bool_expr::BOr>(_sv0->v());
            std::shared_ptr<bool_expr> a_ = bool_expr::bor(d_a00, d_a10);
            auto &&_sv1 = d_a1->simplify_bool();
            if (std::holds_alternative<typename bool_expr::BTrue>(_sv1->v())) {
              _result = bool_expr::btrue();
            } else if (std::holds_alternative<typename bool_expr::BFalse>(
                           _sv1->v())) {
              _result = std::move(a_);
            } else if (std::holds_alternative<typename bool_expr::BAnd>(
                           _sv1->v())) {
              const auto &[d_a01, d_a11] =
                  std::get<typename bool_expr::BAnd>(_sv1->v());
              _result = bool_expr::bor(a_, bool_expr::band(d_a01, d_a11));
            } else if (std::holds_alternative<typename bool_expr::BOr>(
                           _sv1->v())) {
              const auto &[d_a01, d_a11] =
                  std::get<typename bool_expr::BOr>(_sv1->v());
              _result = bool_expr::bor(a_, bool_expr::bor(d_a01, d_a11));
            } else {
              const auto &[d_a01] =
                  std::get<typename bool_expr::BNot>(_sv1->v());
              _result = bool_expr::bor(a_, bool_expr::bnot(d_a01));
            }
          } else {
            const auto &[d_a00] = std::get<typename bool_expr::BNot>(_sv0->v());
            std::shared_ptr<bool_expr> a_ = bool_expr::bnot(d_a00);
            auto &&_sv1 = d_a1->simplify_bool();
            if (std::holds_alternative<typename bool_expr::BTrue>(_sv1->v())) {
              _result = bool_expr::btrue();
            } else if (std::holds_alternative<typename bool_expr::BFalse>(
                           _sv1->v())) {
              _result = std::move(a_);
            } else if (std::holds_alternative<typename bool_expr::BAnd>(
                           _sv1->v())) {
              const auto &[d_a01, d_a11] =
                  std::get<typename bool_expr::BAnd>(_sv1->v());
              _result = bool_expr::bor(a_, bool_expr::band(d_a01, d_a11));
            } else if (std::holds_alternative<typename bool_expr::BOr>(
                           _sv1->v())) {
              const auto &[d_a01, d_a11] =
                  std::get<typename bool_expr::BOr>(_sv1->v());
              _result = bool_expr::bor(a_, bool_expr::bor(d_a01, d_a11));
            } else {
              const auto &[d_a01] =
                  std::get<typename bool_expr::BNot>(_sv1->v());
              _result = bool_expr::bor(a_, bool_expr::bnot(d_a01));
            }
          }
        } else {
          const auto &[d_a0] = std::get<typename bool_expr::BNot>(_self->v());
          auto &&_sv0 = d_a0->simplify_bool();
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv0->v())) {
            _result = bool_expr::bfalse();
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv0->v())) {
            _result = bool_expr::btrue();
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv0->v())) {
            const auto &[d_a00, d_a10] =
                std::get<typename bool_expr::BAnd>(_sv0->v());
            _result = bool_expr::bnot(bool_expr::band(d_a00, d_a10));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _sv0->v())) {
            const auto &[d_a00, d_a10] =
                std::get<typename bool_expr::BOr>(_sv0->v());
            _result = bool_expr::bnot(bool_expr::bor(d_a00, d_a10));
          } else {
            const auto &[d_a00] = std::get<typename bool_expr::BNot>(_sv0->v());
            _result = bool_expr::bnot(bool_expr::bnot(d_a00));
          }
        }
      }
      return _result;
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
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          const auto &_f = std::get<_Enter>(_frame);
          const bool_expr *_self = _f._self;
          if (std::holds_alternative<typename bool_expr::BTrue>(_self->v())) {
            _result = true;
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _self->v())) {
            _result = false;
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _self->v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename bool_expr::BAnd>(_self->v());
            _stack.emplace_back(_Call1{d_a0.get()});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _self->v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename bool_expr::BOr>(_self->v());
            _stack.emplace_back(_Call3{d_a0.get()});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0] = std::get<typename bool_expr::BNot>(_self->v());
            _stack.emplace_back(_Call5{});
            _stack.emplace_back(_Enter{d_a0.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          const auto &_f = std::get<_Call1>(_frame);
          _stack.emplace_back(_Call2{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          const auto &_f = std::get<_Call2>(_frame);
          _result = (_result && _f._s0);
        } else if (std::holds_alternative<_Call3>(_frame)) {
          const auto &_f = std::get<_Call3>(_frame);
          _stack.emplace_back(_Call4{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call4>(_frame)) {
          const auto &_f = std::get<_Call4>(_frame);
          _result = (_result || _f._s0);
        } else {
          const auto &_f = std::get<_Call5>(_frame);
          _result = !(_result);
        }
      }
      return _result;
    }

    template <typename T1,
              MapsTo<T1, std::shared_ptr<bool_expr>, T1,
                     std::shared_ptr<bool_expr>, T1>
                  F2,
              MapsTo<T1, std::shared_ptr<bool_expr>, T1,
                     std::shared_ptr<bool_expr>, T1>
                  F3,
              MapsTo<T1, std::shared_ptr<bool_expr>, T1> F4>
    T1 bool_expr_rec(const T1 f, const T1 f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      const bool_expr *_self = this;

      struct _Enter {
        const bool_expr *_self;
      };

      struct _Call1 {
        bool_expr *_s0;
        std::shared_ptr<bool_expr> _s1;
        std::shared_ptr<bool_expr> _s2;
      };

      struct _Call2 {
        T1 _s0;
        std::shared_ptr<bool_expr> _s1;
        std::shared_ptr<bool_expr> _s2;
      };

      struct _Call3 {
        bool_expr *_s0;
        std::shared_ptr<bool_expr> _s1;
        std::shared_ptr<bool_expr> _s2;
      };

      struct _Call4 {
        T1 _s0;
        std::shared_ptr<bool_expr> _s1;
        std::shared_ptr<bool_expr> _s2;
      };

      struct _Call5 {
        std::shared_ptr<bool_expr> _s0;
      };

      using _Frame =
          std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          const auto &_f = std::get<_Enter>(_frame);
          const bool_expr *_self = _f._self;
          if (std::holds_alternative<typename bool_expr::BTrue>(_self->v())) {
            _result = f;
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _self->v())) {
            _result = f0;
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _self->v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename bool_expr::BAnd>(_self->v());
            _stack.emplace_back(_Call1{d_a0.get(), d_a1, d_a0});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _self->v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename bool_expr::BOr>(_self->v());
            _stack.emplace_back(_Call3{d_a0.get(), d_a1, d_a0});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0] = std::get<typename bool_expr::BNot>(_self->v());
            _stack.emplace_back(_Call5{d_a0});
            _stack.emplace_back(_Enter{d_a0.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          const auto &_f = std::get<_Call1>(_frame);
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          const auto &_f = std::get<_Call2>(_frame);
          _result = f1(_f._s2, _result, _f._s1, _f._s0);
        } else if (std::holds_alternative<_Call3>(_frame)) {
          const auto &_f = std::get<_Call3>(_frame);
          _stack.emplace_back(_Call4{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call4>(_frame)) {
          const auto &_f = std::get<_Call4>(_frame);
          _result = f2(_f._s2, _result, _f._s1, _f._s0);
        } else {
          const auto &_f = std::get<_Call5>(_frame);
          _result = f3(_f._s0, _result);
        }
      }
      return _result;
    }

    template <typename T1,
              MapsTo<T1, std::shared_ptr<bool_expr>, T1,
                     std::shared_ptr<bool_expr>, T1>
                  F2,
              MapsTo<T1, std::shared_ptr<bool_expr>, T1,
                     std::shared_ptr<bool_expr>, T1>
                  F3,
              MapsTo<T1, std::shared_ptr<bool_expr>, T1> F4>
    T1 bool_expr_rect(const T1 f, const T1 f0, F2 &&f1, F3 &&f2,
                      F4 &&f3) const {
      const bool_expr *_self = this;

      struct _Enter {
        const bool_expr *_self;
      };

      struct _Call1 {
        bool_expr *_s0;
        std::shared_ptr<bool_expr> _s1;
        std::shared_ptr<bool_expr> _s2;
      };

      struct _Call2 {
        T1 _s0;
        std::shared_ptr<bool_expr> _s1;
        std::shared_ptr<bool_expr> _s2;
      };

      struct _Call3 {
        bool_expr *_s0;
        std::shared_ptr<bool_expr> _s1;
        std::shared_ptr<bool_expr> _s2;
      };

      struct _Call4 {
        T1 _s0;
        std::shared_ptr<bool_expr> _s1;
        std::shared_ptr<bool_expr> _s2;
      };

      struct _Call5 {
        std::shared_ptr<bool_expr> _s0;
      };

      using _Frame =
          std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          const auto &_f = std::get<_Enter>(_frame);
          const bool_expr *_self = _f._self;
          if (std::holds_alternative<typename bool_expr::BTrue>(_self->v())) {
            _result = f;
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _self->v())) {
            _result = f0;
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _self->v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename bool_expr::BAnd>(_self->v());
            _stack.emplace_back(_Call1{d_a0.get(), d_a1, d_a0});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _self->v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename bool_expr::BOr>(_self->v());
            _stack.emplace_back(_Call3{d_a0.get(), d_a1, d_a0});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0] = std::get<typename bool_expr::BNot>(_self->v());
            _stack.emplace_back(_Call5{d_a0});
            _stack.emplace_back(_Enter{d_a0.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          const auto &_f = std::get<_Call1>(_frame);
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          const auto &_f = std::get<_Call2>(_frame);
          _result = f1(_f._s2, _result, _f._s1, _f._s0);
        } else if (std::holds_alternative<_Call3>(_frame)) {
          const auto &_f = std::get<_Call3>(_frame);
          _stack.emplace_back(_Call4{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call4>(_frame)) {
          const auto &_f = std::get<_Call4>(_frame);
          _result = f2(_f._s2, _result, _f._s1, _f._s0);
        } else {
          const auto &_f = std::get<_Call5>(_frame);
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
    explicit list_expr(LNil _v) : d_v_(_v) {}

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
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          const auto &_f = std::get<_Enter>(_frame);
          const list_expr *_self = _f._self;
          if (std::holds_alternative<typename list_expr::LCons>(_self->v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename list_expr::LCons>(_self->v());
            _stack.emplace_back(_Call1{1u});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else if (std::holds_alternative<typename list_expr::LAppend>(
                         _self->v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename list_expr::LAppend>(_self->v());
            _stack.emplace_back(_Call2{d_a0.get(), 1u});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            _result = 1u;
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          const auto &_f = std::get<_Call1>(_frame);
          _result = (_f._s0 + _result);
        } else if (std::holds_alternative<_Call2>(_frame)) {
          const auto &_f = std::get<_Call2>(_frame);
          _stack.emplace_back(_Call3{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          const auto &_f = std::get<_Call3>(_frame);
          _result = ((_f._s1 + _result) + _f._s0);
        }
      }
      return _result;
    }

    std::shared_ptr<List<unsigned int>> eval_list() const {
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
        std::shared_ptr<List<unsigned int>> _s0;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
      std::shared_ptr<List<unsigned int>> _result{};
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          const auto &_f = std::get<_Enter>(_frame);
          const list_expr *_self = _f._self;
          if (std::holds_alternative<typename list_expr::LNil>(_self->v())) {
            _result = List<unsigned int>::nil();
          } else if (std::holds_alternative<typename list_expr::LCons>(
                         _self->v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename list_expr::LCons>(_self->v());
            _stack.emplace_back(_Call1{d_a0});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else if (std::holds_alternative<typename list_expr::LAppend>(
                         _self->v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename list_expr::LAppend>(_self->v());
            _stack.emplace_back(_Call2{d_a0.get()});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename list_expr::LReplicate>(_self->v());
            _result = ListDef::template repeat<unsigned int>(d_a1, d_a0);
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          const auto &_f = std::get<_Call1>(_frame);
          _result = List<unsigned int>::cons(_f._s0, _result);
        } else if (std::holds_alternative<_Call2>(_frame)) {
          const auto &_f = std::get<_Call2>(_frame);
          _stack.emplace_back(_Call3{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          const auto &_f = std::get<_Call3>(_frame);
          _result = _result->app(_f._s0);
        }
      }
      return _result;
    }

    template <typename T1,
              MapsTo<T1, unsigned int, std::shared_ptr<list_expr>, T1> F1,
              MapsTo<T1, std::shared_ptr<list_expr>, T1,
                     std::shared_ptr<list_expr>, T1>
                  F2,
              MapsTo<T1, unsigned int, unsigned int> F3>
    T1 list_expr_rec(const T1 f, F1 &&f0, F2 &&f1, F3 &&f2) const {
      const list_expr *_self = this;

      struct _Enter {
        const list_expr *_self;
      };

      struct _Call1 {
        std::shared_ptr<list_expr> _s0;
        unsigned int _s1;
      };

      struct _Call2 {
        list_expr *_s0;
        std::shared_ptr<list_expr> _s1;
        std::shared_ptr<list_expr> _s2;
      };

      struct _Call3 {
        T1 _s0;
        std::shared_ptr<list_expr> _s1;
        std::shared_ptr<list_expr> _s2;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          const auto &_f = std::get<_Enter>(_frame);
          const list_expr *_self = _f._self;
          if (std::holds_alternative<typename list_expr::LNil>(_self->v())) {
            _result = f;
          } else if (std::holds_alternative<typename list_expr::LCons>(
                         _self->v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename list_expr::LCons>(_self->v());
            _stack.emplace_back(_Call1{d_a1, d_a0});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else if (std::holds_alternative<typename list_expr::LAppend>(
                         _self->v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename list_expr::LAppend>(_self->v());
            _stack.emplace_back(_Call2{d_a0.get(), d_a1, d_a0});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename list_expr::LReplicate>(_self->v());
            _result = f2(d_a0, d_a1);
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          const auto &_f = std::get<_Call1>(_frame);
          _result = f0(_f._s1, _f._s0, _result);
        } else if (std::holds_alternative<_Call2>(_frame)) {
          const auto &_f = std::get<_Call2>(_frame);
          _stack.emplace_back(_Call3{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          const auto &_f = std::get<_Call3>(_frame);
          _result = f1(_f._s2, _result, _f._s1, _f._s0);
        }
      }
      return _result;
    }

    template <typename T1,
              MapsTo<T1, unsigned int, std::shared_ptr<list_expr>, T1> F1,
              MapsTo<T1, std::shared_ptr<list_expr>, T1,
                     std::shared_ptr<list_expr>, T1>
                  F2,
              MapsTo<T1, unsigned int, unsigned int> F3>
    T1 list_expr_rect(const T1 f, F1 &&f0, F2 &&f1, F3 &&f2) const {
      const list_expr *_self = this;

      struct _Enter {
        const list_expr *_self;
      };

      struct _Call1 {
        std::shared_ptr<list_expr> _s0;
        unsigned int _s1;
      };

      struct _Call2 {
        list_expr *_s0;
        std::shared_ptr<list_expr> _s1;
        std::shared_ptr<list_expr> _s2;
      };

      struct _Call3 {
        T1 _s0;
        std::shared_ptr<list_expr> _s1;
        std::shared_ptr<list_expr> _s2;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          const auto &_f = std::get<_Enter>(_frame);
          const list_expr *_self = _f._self;
          if (std::holds_alternative<typename list_expr::LNil>(_self->v())) {
            _result = f;
          } else if (std::holds_alternative<typename list_expr::LCons>(
                         _self->v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename list_expr::LCons>(_self->v());
            _stack.emplace_back(_Call1{d_a1, d_a0});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else if (std::holds_alternative<typename list_expr::LAppend>(
                         _self->v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename list_expr::LAppend>(_self->v());
            _stack.emplace_back(_Call2{d_a0.get(), d_a1, d_a0});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename list_expr::LReplicate>(_self->v());
            _result = f2(d_a0, d_a1);
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          const auto &_f = std::get<_Call1>(_frame);
          _result = f0(_f._s1, _f._s0, _result);
        } else if (std::holds_alternative<_Call2>(_frame)) {
          const auto &_f = std::get<_Call2>(_frame);
          _stack.emplace_back(_Call3{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          const auto &_f = std::get<_Call3>(_frame);
          _result = f1(_f._s2, _result, _f._s1, _f._s0);
        }
      }
      return _result;
    }
  };
};

template <typename T1>
std::shared_ptr<List<T1>> ListDef::repeat(const T1 x, const unsigned int n) {
  std::shared_ptr<List<T1>> _head{};
  std::shared_ptr<List<T1>> _last{};
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    if (_loop_n <= 0) {
      if (_last) {
        std::get<typename List<T1>::Cons>(_last->v_mut()).d_a1 =
            List<T1>::nil();
      } else {
        _head = List<T1>::nil();
      }
      _continue = false;
    } else {
      unsigned int k = _loop_n - 1;
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
  return _head;
}

#endif // INCLUDED_LOOPIFY_EXPR_VARIANTS
