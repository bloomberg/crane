#ifndef INCLUDED_WHERE_CLAUSE
#define INCLUDED_WHERE_CLAUSE

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

struct WhereClause {
  struct Expr {
    // TYPES
    struct Num {
      unsigned int d_a0;
    };

    struct Plus {
      std::shared_ptr<Expr> d_a0;
      std::shared_ptr<Expr> d_a1;
    };

    struct Times {
      std::shared_ptr<Expr> d_a0;
      std::shared_ptr<Expr> d_a1;
    };

    using variant_t = std::variant<Num, Plus, Times>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit Expr(Num _v) : d_v_(std::move(_v)) {}

    explicit Expr(Plus _v) : d_v_(std::move(_v)) {}

    explicit Expr(Times _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<Expr> num(unsigned int a0) {
      return std::make_shared<Expr>(Num{std::move(a0)});
    }

    static std::shared_ptr<Expr> plus(const std::shared_ptr<Expr> &a0,
                                      const std::shared_ptr<Expr> &a1) {
      return std::make_shared<Expr>(Plus{a0, a1});
    }

    static std::shared_ptr<Expr> plus(std::shared_ptr<Expr> &&a0,
                                      std::shared_ptr<Expr> &&a1) {
      return std::make_shared<Expr>(Plus{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<Expr> times(const std::shared_ptr<Expr> &a0,
                                       const std::shared_ptr<Expr> &a1) {
      return std::make_shared<Expr>(Times{a0, a1});
    }

    static std::shared_ptr<Expr> times(std::shared_ptr<Expr> &&a0,
                                       std::shared_ptr<Expr> &&a1) {
      return std::make_shared<Expr>(Times{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int expr_size() const {
      return std::visit(
          Overloaded{
              [](const typename Expr::Num) -> unsigned int { return 1u; },
              [](const typename Expr::Plus _args) -> unsigned int {
                return ((1u + _args.d_a0->expr_size()) +
                        _args.d_a1->expr_size());
              },
              [](const typename Expr::Times _args) -> unsigned int {
                return ((1u + _args.d_a0->expr_size()) +
                        _args.d_a1->expr_size());
              }},
          this->v());
    }

    __attribute__((pure)) unsigned int eval() const {
      return std::visit(
          Overloaded{[](const typename Expr::Num _args) -> unsigned int {
                       return _args.d_a0;
                     },
                     [](const typename Expr::Plus _args) -> unsigned int {
                       return (_args.d_a0->eval() + _args.d_a1->eval());
                     },
                     [](const typename Expr::Times _args) -> unsigned int {
                       return (_args.d_a0->eval() * _args.d_a1->eval());
                     }},
          this->v());
    }

    template <
        typename T1, MapsTo<T1, unsigned int> F0,
        MapsTo<T1, std::shared_ptr<Expr>, T1, std::shared_ptr<Expr>, T1> F1,
        MapsTo<T1, std::shared_ptr<Expr>, T1, std::shared_ptr<Expr>, T1> F2>
    T1 Expr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      return std::visit(
          Overloaded{[&](const typename Expr::Num _args) -> T1 {
                       return f(_args.d_a0);
                     },
                     [&](const typename Expr::Plus _args) -> T1 {
                       return f0(_args.d_a0,
                                 _args.d_a0->template Expr_rec<T1>(f, f0, f1),
                                 _args.d_a1,
                                 _args.d_a1->template Expr_rec<T1>(f, f0, f1));
                     },
                     [&](const typename Expr::Times _args) -> T1 {
                       return f1(_args.d_a0,
                                 _args.d_a0->template Expr_rec<T1>(f, f0, f1),
                                 _args.d_a1,
                                 _args.d_a1->template Expr_rec<T1>(f, f0, f1));
                     }},
          this->v());
    }

    template <
        typename T1, MapsTo<T1, unsigned int> F0,
        MapsTo<T1, std::shared_ptr<Expr>, T1, std::shared_ptr<Expr>, T1> F1,
        MapsTo<T1, std::shared_ptr<Expr>, T1, std::shared_ptr<Expr>, T1> F2>
    T1 Expr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      return std::visit(
          Overloaded{[&](const typename Expr::Num _args) -> T1 {
                       return f(_args.d_a0);
                     },
                     [&](const typename Expr::Plus _args) -> T1 {
                       return f0(_args.d_a0,
                                 _args.d_a0->template Expr_rect<T1>(f, f0, f1),
                                 _args.d_a1,
                                 _args.d_a1->template Expr_rect<T1>(f, f0, f1));
                     },
                     [&](const typename Expr::Times _args) -> T1 {
                       return f1(_args.d_a0,
                                 _args.d_a0->template Expr_rect<T1>(f, f0, f1),
                                 _args.d_a1,
                                 _args.d_a1->template Expr_rect<T1>(f, f0, f1));
                     }},
          this->v());
    }
  };

  struct BExpr {
    // TYPES
    struct BTrue {};

    struct BFalse {};

    struct BAnd {
      std::shared_ptr<BExpr> d_a0;
      std::shared_ptr<BExpr> d_a1;
    };

    struct BOr {
      std::shared_ptr<BExpr> d_a0;
      std::shared_ptr<BExpr> d_a1;
    };

    struct BNot {
      std::shared_ptr<BExpr> d_a0;
    };

    using variant_t = std::variant<BTrue, BFalse, BAnd, BOr, BNot>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit BExpr(BTrue _v) : d_v_(std::move(_v)) {}

    explicit BExpr(BFalse _v) : d_v_(std::move(_v)) {}

    explicit BExpr(BAnd _v) : d_v_(std::move(_v)) {}

    explicit BExpr(BOr _v) : d_v_(std::move(_v)) {}

    explicit BExpr(BNot _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<BExpr> btrue() {
      return std::make_shared<BExpr>(BTrue{});
    }

    static std::shared_ptr<BExpr> bfalse() {
      return std::make_shared<BExpr>(BFalse{});
    }

    static std::shared_ptr<BExpr> band(const std::shared_ptr<BExpr> &a0,
                                       const std::shared_ptr<BExpr> &a1) {
      return std::make_shared<BExpr>(BAnd{a0, a1});
    }

    static std::shared_ptr<BExpr> band(std::shared_ptr<BExpr> &&a0,
                                       std::shared_ptr<BExpr> &&a1) {
      return std::make_shared<BExpr>(BAnd{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<BExpr> bor(const std::shared_ptr<BExpr> &a0,
                                      const std::shared_ptr<BExpr> &a1) {
      return std::make_shared<BExpr>(BOr{a0, a1});
    }

    static std::shared_ptr<BExpr> bor(std::shared_ptr<BExpr> &&a0,
                                      std::shared_ptr<BExpr> &&a1) {
      return std::make_shared<BExpr>(BOr{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<BExpr> bnot(const std::shared_ptr<BExpr> &a0) {
      return std::make_shared<BExpr>(BNot{a0});
    }

    static std::shared_ptr<BExpr> bnot(std::shared_ptr<BExpr> &&a0) {
      return std::make_shared<BExpr>(BNot{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) bool beval() const {
      return std::visit(
          Overloaded{[](const typename BExpr::BTrue) -> bool { return true; },
                     [](const typename BExpr::BFalse) -> bool { return false; },
                     [](const typename BExpr::BAnd _args) -> bool {
                       return (_args.d_a0->beval() && _args.d_a1->beval());
                     },
                     [](const typename BExpr::BOr _args) -> bool {
                       return (_args.d_a0->beval() || _args.d_a1->beval());
                     },
                     [](const typename BExpr::BNot _args) -> bool {
                       return !(_args.d_a0->beval());
                     }},
          this->v());
    }
  };

  template <
      typename T1,
      MapsTo<T1, std::shared_ptr<BExpr>, T1, std::shared_ptr<BExpr>, T1> F2,
      MapsTo<T1, std::shared_ptr<BExpr>, T1, std::shared_ptr<BExpr>, T1> F3,
      MapsTo<T1, std::shared_ptr<BExpr>, T1> F4>
  static T1 BExpr_rect(const T1 f, const T1 f0, F2 &&f1, F3 &&f2, F4 &&f3,
                       const std::shared_ptr<BExpr> &b) {
    return std::visit(
        Overloaded{[&](const typename BExpr::BTrue) -> T1 { return f; },
                   [&](const typename BExpr::BFalse) -> T1 { return f0; },
                   [&](const typename BExpr::BAnd _args) -> T1 {
                     return f1(_args.d_a0,
                               BExpr_rect<T1>(f, f0, f1, f2, f3, _args.d_a0),
                               _args.d_a1,
                               BExpr_rect<T1>(f, f0, f1, f2, f3, _args.d_a1));
                   },
                   [&](const typename BExpr::BOr _args) -> T1 {
                     return f2(_args.d_a0,
                               BExpr_rect<T1>(f, f0, f1, f2, f3, _args.d_a0),
                               _args.d_a1,
                               BExpr_rect<T1>(f, f0, f1, f2, f3, _args.d_a1));
                   },
                   [&](const typename BExpr::BNot _args) -> T1 {
                     return f3(_args.d_a0,
                               BExpr_rect<T1>(f, f0, f1, f2, f3, _args.d_a0));
                   }},
        b->v());
  }

  template <
      typename T1,
      MapsTo<T1, std::shared_ptr<BExpr>, T1, std::shared_ptr<BExpr>, T1> F2,
      MapsTo<T1, std::shared_ptr<BExpr>, T1, std::shared_ptr<BExpr>, T1> F3,
      MapsTo<T1, std::shared_ptr<BExpr>, T1> F4>
  static T1 BExpr_rec(const T1 f, const T1 f0, F2 &&f1, F3 &&f2, F4 &&f3,
                      const std::shared_ptr<BExpr> &b) {
    return std::visit(
        Overloaded{[&](const typename BExpr::BTrue) -> T1 { return f; },
                   [&](const typename BExpr::BFalse) -> T1 { return f0; },
                   [&](const typename BExpr::BAnd _args) -> T1 {
                     return f1(_args.d_a0,
                               BExpr_rec<T1>(f, f0, f1, f2, f3, _args.d_a0),
                               _args.d_a1,
                               BExpr_rec<T1>(f, f0, f1, f2, f3, _args.d_a1));
                   },
                   [&](const typename BExpr::BOr _args) -> T1 {
                     return f2(_args.d_a0,
                               BExpr_rec<T1>(f, f0, f1, f2, f3, _args.d_a0),
                               _args.d_a1,
                               BExpr_rec<T1>(f, f0, f1, f2, f3, _args.d_a1));
                   },
                   [&](const typename BExpr::BNot _args) -> T1 {
                     return f3(_args.d_a0,
                               BExpr_rec<T1>(f, f0, f1, f2, f3, _args.d_a0));
                   }},
        b->v());
  }

  struct AExpr {
    // TYPES
    struct ANum {
      unsigned int d_a0;
    };

    struct APlus {
      std::shared_ptr<AExpr> d_a0;
      std::shared_ptr<AExpr> d_a1;
    };

    struct AIf {
      std::shared_ptr<BExpr> d_a0;
      std::shared_ptr<AExpr> d_a1;
      std::shared_ptr<AExpr> d_a2;
    };

    using variant_t = std::variant<ANum, APlus, AIf>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit AExpr(ANum _v) : d_v_(std::move(_v)) {}

    explicit AExpr(APlus _v) : d_v_(std::move(_v)) {}

    explicit AExpr(AIf _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<AExpr> anum(unsigned int a0) {
      return std::make_shared<AExpr>(ANum{std::move(a0)});
    }

    static std::shared_ptr<AExpr> aplus(const std::shared_ptr<AExpr> &a0,
                                        const std::shared_ptr<AExpr> &a1) {
      return std::make_shared<AExpr>(APlus{a0, a1});
    }

    static std::shared_ptr<AExpr> aplus(std::shared_ptr<AExpr> &&a0,
                                        std::shared_ptr<AExpr> &&a1) {
      return std::make_shared<AExpr>(APlus{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<AExpr> aif(const std::shared_ptr<BExpr> &a0,
                                      const std::shared_ptr<AExpr> &a1,
                                      const std::shared_ptr<AExpr> &a2) {
      return std::make_shared<AExpr>(AIf{a0, a1, a2});
    }

    static std::shared_ptr<AExpr> aif(std::shared_ptr<BExpr> &&a0,
                                      std::shared_ptr<AExpr> &&a1,
                                      std::shared_ptr<AExpr> &&a2) {
      return std::make_shared<AExpr>(
          AIf{std::move(a0), std::move(a1), std::move(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int aeval() const {
      return std::visit(
          Overloaded{[](const typename AExpr::ANum _args) -> unsigned int {
                       return _args.d_a0;
                     },
                     [](const typename AExpr::APlus _args) -> unsigned int {
                       return (_args.d_a0->aeval() + _args.d_a1->aeval());
                     },
                     [](const typename AExpr::AIf _args) -> unsigned int {
                       if (_args.d_a0->beval()) {
                         return _args.d_a1->aeval();
                       } else {
                         return _args.d_a2->aeval();
                       }
                     }},
          this->v());
    }

    template <
        typename T1, MapsTo<T1, unsigned int> F0,
        MapsTo<T1, std::shared_ptr<AExpr>, T1, std::shared_ptr<AExpr>, T1> F1,
        MapsTo<T1, std::shared_ptr<BExpr>, std::shared_ptr<AExpr>, T1,
               std::shared_ptr<AExpr>, T1>
            F2>
    T1 AExpr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      return std::visit(
          Overloaded{[&](const typename AExpr::ANum _args) -> T1 {
                       return f(_args.d_a0);
                     },
                     [&](const typename AExpr::APlus _args) -> T1 {
                       return f0(_args.d_a0,
                                 _args.d_a0->template AExpr_rec<T1>(f, f0, f1),
                                 _args.d_a1,
                                 _args.d_a1->template AExpr_rec<T1>(f, f0, f1));
                     },
                     [&](const typename AExpr::AIf _args) -> T1 {
                       return f1(_args.d_a0, _args.d_a1,
                                 _args.d_a1->template AExpr_rec<T1>(f, f0, f1),
                                 _args.d_a2,
                                 _args.d_a2->template AExpr_rec<T1>(f, f0, f1));
                     }},
          this->v());
    }

    template <
        typename T1, MapsTo<T1, unsigned int> F0,
        MapsTo<T1, std::shared_ptr<AExpr>, T1, std::shared_ptr<AExpr>, T1> F1,
        MapsTo<T1, std::shared_ptr<BExpr>, std::shared_ptr<AExpr>, T1,
               std::shared_ptr<AExpr>, T1>
            F2>
    T1 AExpr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      return std::visit(
          Overloaded{
              [&](const typename AExpr::ANum _args) -> T1 {
                return f(_args.d_a0);
              },
              [&](const typename AExpr::APlus _args) -> T1 {
                return f0(
                    _args.d_a0, _args.d_a0->template AExpr_rect<T1>(f, f0, f1),
                    _args.d_a1, _args.d_a1->template AExpr_rect<T1>(f, f0, f1));
              },
              [&](const typename AExpr::AIf _args) -> T1 {
                return f1(_args.d_a0, _args.d_a1,
                          _args.d_a1->template AExpr_rect<T1>(f, f0, f1),
                          _args.d_a2,
                          _args.d_a2->template AExpr_rect<T1>(f, f0, f1));
              }},
          this->v());
    }
  };

  static inline const unsigned int test_eval_plus =
      Expr::plus(Expr::num(3u), Expr::num(4u))->eval();
  static inline const unsigned int test_eval_times =
      Expr::times(Expr::num(5u), Expr::num(6u))->eval();
  static inline const unsigned int test_eval_nested =
      Expr::plus(Expr::times(Expr::num(2u), Expr::num(3u)), Expr::num(1u))
          ->eval();
  static inline const unsigned int test_size =
      Expr::plus(Expr::times(Expr::num(2u), Expr::num(3u)), Expr::num(1u))
          ->expr_size();
  static inline const bool test_beval =
      BExpr::band(BExpr::btrue(), BExpr::bnot(BExpr::bfalse()))->beval();
  static inline const unsigned int test_aeval =
      AExpr::aif(BExpr::band(BExpr::btrue(), BExpr::btrue()), AExpr::anum(10u),
                 AExpr::anum(20u))
          ->aeval();
};

#endif // INCLUDED_WHERE_CLAUSE
