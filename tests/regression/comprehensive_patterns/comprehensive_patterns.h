#ifndef INCLUDED_COMPREHENSIVE_PATTERNS
#define INCLUDED_COMPREHENSIVE_PATTERNS

#include <any>
#include <functional>
#include <memory>
#include <optional>
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

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        _drain(_cur->v_mut());
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename A> struct Sig {
  // DATA
  A x;

  // ACCESSORS
  Sig<A> clone() const { return {x}; }

  // CREATORS
  static Sig<A> exist(A x) { return {std::move(x)}; }
};

struct ComprehensivePatterns {
  struct S {
    uint64_t s_a;
    uint64_t s_b;
    uint64_t s_c;
  };

  static std::pair<std::pair<S, uint64_t>, uint64_t> syntactic_variation(S s);
  static std::pair<S, uint64_t> with_magic(S s);

  struct L1 {
    S l1_s;
  };

  struct L2 {
    L1 l2_l1;
  };

  struct L3 {
    L2 l3_l2;
  };

  struct L4 {
    L3 l4_l3;
  };

  struct L5 {
    L4 l5_l4;
  };

  static std::pair<
      std::pair<std::pair<std::pair<std::pair<std::pair<L5, L4>, L3>, L2>, L1>,
                S>,
      uint64_t>
  deep_nest(L5 l5);
  static std::pair<std::pair<std::pair<S, uint64_t>, uint64_t>, uint64_t>
  nested_pair_reuse(S s);
  static std::pair<S, uint64_t> compose(S s);
  static std::pair<std::function<uint64_t(uint64_t)>, S> lambda_proj(S s);
  static std::pair<std::pair<std::pair<S, uint64_t>, uint64_t>, uint64_t>
  proj_chain(S s);
  static std::pair<
      std::pair<std::pair<S, S>, std::pair<uint64_t, uint64_t>>,
      std::pair<std::pair<uint64_t, uint64_t>, std::pair<uint64_t, uint64_t>>>
  octuple(S s);
  static std::pair<std::optional<std::pair<S, uint64_t>>, S>
  nested_containers(S s);
  static std::pair<std::pair<S, uint64_t>, uint64_t>
  match_pair(std::pair<S, uint64_t> p);
  static List<std::pair<S, uint64_t>> make_list(uint64_t n, S s);
  static std::optional<std::pair<S, S>> multi_match(const std::optional<S> &o1,
                                                    const std::optional<S> &o2);
  enum class Three { A, B, C };

  template <typename T1> static T1 Three_rect(T1 f, T1 f0, T1 f3, Three t) {
    switch (t) {
    case Three::A: {
      return f;
    }
    case Three::B: {
      return f0;
    }
    case Three::C: {
      return f3;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 Three_rec(T1 f, T1 f0, T1 f3, Three t) {
    switch (t) {
    case Three::A: {
      return f;
    }
    case Three::B: {
      return f0;
    }
    case Three::C: {
      return f3;
    }
    default:
      std::unreachable();
    }
  }

  static std::pair<S, uint64_t> match_three(Three t, S s);
  static std::pair<S, uint64_t> let_in_arg(S s);
  static std::pair<S, uint64_t> match_record(S s);
  static std::pair<S, uint64_t> rebind(S s1);
  static std::pair<std::function<uint64_t(std::monostate)>,
                   std::function<uint64_t(std::monostate)>>
  closure_pair(S s);
  static Sig<S> sigma_reuse(S s);
  static std::pair<uint64_t, std::pair<uint64_t, uint64_t>>
  multi_proj_arg(const S &s);

  struct Either {
    // TYPES
    struct Left_S {
      S s;
    };

    struct Right_N {
      uint64_t n;
    };

    using variant_t = std::variant<Left_S, Right_N>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    Either() {}

    explicit Either(Left_S _v) : v_(std::move(_v)) {}

    explicit Either(Right_N _v) : v_(std::move(_v)) {}

    static Either left_s(S s) { return Either(Left_S{std::move(s)}); }

    static Either right_n(uint64_t n) { return Either(Right_N{n}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, S &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &>
    T1 Either_rec(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename Either::Left_S>(this->v())) {
        const auto &[s0] = std::get<typename Either::Left_S>(this->v());
        return f(s0);
      } else {
        const auto &[n0] = std::get<typename Either::Right_N>(this->v());
        return f0(n0);
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, S &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &>
    T1 Either_rect(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename Either::Left_S>(this->v())) {
        const auto &[s0] = std::get<typename Either::Left_S>(this->v());
        return f(s0);
      } else {
        const auto &[n0] = std::get<typename Either::Right_N>(this->v());
        return f0(n0);
      }
    }
  };

  static std::pair<Either, Either> both_in_sum(S s);

  struct R1 {
    uint64_t r1_val;
  };

  struct R2 {
    R1 r2_inner;
    uint64_t r2_data;
  };

  struct R3 {
    R2 r3_r2;
    R1 r3_r1;
    uint64_t r3_num;
  };

  static std::pair<std::pair<std::pair<R3, R2>, R1>, uint64_t>
  hard_proj_chain(R3 r3);
  static std::pair<std::pair<R2, R1>, uint64_t> multi_path(const R3 &r3);
  static std::pair<std::pair<R2, R1>, uint64_t> let_proj(R2 r2);
  static uint64_t extract_val(const R1 &r1);
  static std::pair<R2, uint64_t> nested_call(R2 r2);
  static std::pair<std::pair<R2, R1>, uint64_t> multi_proj_let(uint64_t n);
  static std::optional<std::pair<R2, R1>> match_proj(R2 r2);
  static std::pair<std::pair<R1, uint64_t>, uint64_t>
  proj_multi_use(const R2 &r2);
  static std::pair<std::pair<R3, R2>, std::pair<R1, uint64_t>>
  complex_nest(R3 r3);
  static R2 make_r2(uint64_t n);
  static std::pair<std::pair<R2, R1>, uint64_t> from_func(uint64_t n);
  static std::pair<std::pair<R2, R1>, std::pair<R1, uint64_t>>
  pair_of_pairs(R2 r2);
  static std::pair<R2, R1> cond_proj(bool b, R2 r2);
  static List<std::pair<R2, R1>> repeat_r2(uint64_t n, R2 r2);
  static std::pair<std::pair<R3, R2>, R1> nested_lets(R3 r3);
  static std::pair<R1, uint64_t> double_proj(const R3 &r3);
  static std::pair<std::pair<R3, R2>, R2> mixed_access(R3 r3);
  static std::pair<R2, R1> return_proj_h(R2 r2);
  static std::pair<std::pair<std::pair<R3, R2>, R1>, uint64_t>
  all_levels(R3 r3);
  static std::pair<R1, R1> let_and_proj(const R2 &r2);
  static std::pair<R2, R2> multi_construct(R1 r1);
  static std::optional<std::pair<R2, R1>>
  option_proj(const std::optional<R2> &o);

  struct R {
    uint64_t val;
    uint64_t dat;
  };

  static std::pair<R, uint64_t> pair_inline_proj(R r);
  static std::pair<std::pair<R, uint64_t>, uint64_t> nested_pair_inline(R r);
  static uint64_t match_bind_and_use(const R &r);
  static uint64_t let_with_type(const R &r);
  static uint64_t proj_of_last_use(const R &r1);
  static uint64_t multi_let_same(const R &r);
  static uint64_t option_unwrap_proj(const std::optional<R> &o);
  static std::pair<R, uint64_t> fun_result_and_proj(uint64_t n);
  static std::optional<uint64_t> match_multi_use(const std::optional<R> &o);
  static std::pair<std::pair<R, uint64_t>, uint64_t> tuple_proj(R r);
  static std::pair<R, uint64_t> chain_to_pair(R r1);
  static List<std::pair<R, uint64_t>> repeat_pair(uint64_t n, R r);
  static std::pair<R, uint64_t> cond_pair(bool b, R r);
  static uint64_t nested_match(const std::optional<R> &o1,
                               const std::optional<R> &o2);
  static std::pair<uint64_t, uint64_t> both_proj(const R &r);
  static uint64_t compose_proj(const R &r);
  static std::optional<uint64_t> proj_through_option(const R &r);

  struct NC {
    uint64_t nc_a;
    uint64_t nc_b;
    uint64_t nc_c;
  };

  static uint64_t use_proj(uint64_t n);
  static uint64_t proj_as_arg(const NC &r);
  static uint64_t use_two(uint64_t _x0, uint64_t _x1);
  static uint64_t multi_proj_args(const NC &r);
  static uint64_t let_proj_then_base(const NC &r);
  static uint64_t base_then_multi_proj(const NC &r);
  static uint64_t proj_in_condition(const NC &r);
  static uint64_t proj_in_scrutinee(const NC &r);
  static uint64_t return_proj_nc(const NC &r);
  static uint64_t call_return_proj(const NC &r);
  static uint64_t inc(uint64_t n);
  static uint64_t nested_proj_calls(const NC &r);
  static uint64_t count_down(uint64_t n, const NC &r);
  static uint64_t f1(const NC &r);
  static uint64_t f2(const NC &r);
  static uint64_t multi_function_calls(const NC &r);
  static uint64_t proj_then_match(const NC &r);
  static uint64_t let_used_twice(const NC &r);
  static bool base_in_call_and_proj(const NC &r);
  static uint64_t chained_lets_same_base(const NC &r);

  struct OuterNC {
    NC outer_nc;
  };

  static uint64_t double_proj_nc(const OuterNC &o);
  static uint64_t multi_positions(const NC &r);
  static uint64_t sum_proj(uint64_t n, const NC &r);

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, NC &>
  static uint64_t apply(F0 &&f, NC _x0) {
    return f(std::move(_x0));
  }

  static uint64_t hof_test(const NC &r);

  struct State {
    uint64_t state_value;
    uint64_t state_data;
  };

  static uint64_t use_two_fc(uint64_t _x0, uint64_t _x1);
  static uint64_t bug_two_args(const State &s);
  static uint64_t use_three(uint64_t x, uint64_t y, uint64_t z);
  static uint64_t bug_three_args(const State &s);
  static uint64_t take_state_and_val(const State &_x, uint64_t n);
  static uint64_t bug_state_and_proj(const State &s);
  static uint64_t inner_func(uint64_t n);
  static uint64_t bug_nested_calls(const State &s);
  static uint64_t bug_in_condition(const State &s);
  static uint64_t f1_fc(uint64_t n);
  static uint64_t f2_fc(uint64_t n);
  static uint64_t bug_multi_calls(const State &s);
  static std::pair<State, uint64_t> bug_base_and_proj(const State &s);
  static uint64_t sequential_lets(const State &s);
  static std::pair<State, uint64_t> let_then_use_base(State s);
  static uint64_t two_proj_sequence(const State &s);
  static uint64_t let_multi_proj(const State &s);
  static uint64_t nested_lets_same_base(const State &s);
  static uint64_t if_with_proj(const State &s);
  static uint64_t match_scrutinee_proj(const State &s);
  static std::pair<State, uint64_t> bind_proj_use_base(State s);

  struct RSeq {
    uint64_t seq_val;
  };

  static RSeq side_effect(RSeq r);
  static uint64_t after_side_effect(const RSeq &r);
  static uint64_t two_side_effects(const RSeq &r);
  static uint64_t side_effect_in_branch(bool b, const RSeq &r);

  struct StateStmt {
    uint64_t stmt_value;
    uint64_t stmt_data;
  };

  static uint64_t return_proj_stmt(const StateStmt &s);
  static uint64_t return_complex(const StateStmt &s);
  static std::pair<uint64_t, uint64_t> return_pair(const StateStmt &s);

  struct InnerStmt {
    uint64_t inner_stmt_val;
  };

  struct OuterStmt {
    InnerStmt outer_stmt_inner;
    uint64_t outer_stmt_data;
  };

  static uint64_t chained_proj(const OuterStmt &o);

  struct Level3Stmt {
    OuterStmt l3_outer_stmt;
  };

  static uint64_t triple_chain(const Level3Stmt &l3);
  static uint64_t proj_in_arith(const StateStmt &s);
  static uint64_t multi_proj_expr(const StateStmt &s);
  static List<uint64_t> proj_in_list(const StateStmt &s);
  static bool compare_projs(const StateStmt &s);
  static bool bool_with_proj(const StateStmt &s);

  template <typename T1> static T1 _bug_base_and_proj_consume(const T1 x) {
    return x;
  }

  static uint64_t sum_values(uint64_t n, const StateStmt &s);

  struct RCF {
    uint64_t cf_val;
  };

  static uint64_t branch_use(bool b, const RCF &r);
  static std::pair<RCF, uint64_t> branch_different(bool b, RCF r);
  static uint64_t match_with_wild(const std::optional<RCF> &o);
  static uint64_t sum_with_state(uint64_t n, const RCF &r);
  static uint64_t even_count(uint64_t n, const RCF &r);
  static uint64_t odd_count(uint64_t n, const RCF &r);

  struct StateLB {
    uint64_t lb_value;
    uint64_t lb_data;
  };

  struct Tree {
    // TYPES
    struct Leaf {
      uint64_t a0;
    };

    struct Node {
      std::shared_ptr<Tree> a0;
      uint64_t a1;
      std::shared_ptr<Tree> a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    Tree() {}

    explicit Tree(Leaf _v) : v_(std::move(_v)) {}

    explicit Tree(Node _v) : v_(std::move(_v)) {}

    static Tree leaf(uint64_t a0) { return Tree(Leaf{a0}); }

    static Tree node(Tree a0, uint64_t a1, Tree a2) {
      return Tree(Node{std::make_shared<Tree>(std::move(a0)), a1,
                       std::make_shared<Tree>(std::move(a2))});
    }

    // MANIPULATORS
    ~Tree() {
      std::vector<std::shared_ptr<Tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a2) {
            _stack.push_back(std::move(_alt->a2));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          _drain(_cur->v_mut());
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    Tree nested_reuse() const {
      Tree t2 = this->transform_tree();
      return std::move(t2).transform_tree();
    }

    Tree flip_tree() const {
      if (std::holds_alternative<typename Tree::Leaf>(this->v())) {
        auto &[a0] = std::get<typename Tree::Leaf>(this->v());
        return Tree::node(*this, std::move(a0), *this);
      } else {
        auto &[a0, a1, a2] = std::get<typename Tree::Node>(this->v());
        return Tree::leaf(std::move(a1));
      }
    }

    Tree transform_tree() const {
      if (std::holds_alternative<typename Tree::Leaf>(this->v())) {
        const auto &[a0] = std::get<typename Tree::Leaf>(this->v());
        return Tree::leaf((a0 + UINT64_C(1)));
      } else {
        const auto &[a0, a1, a2] = std::get<typename Tree::Node>(this->v());
        return Tree::node(*a0, (a1 + UINT64_C(1)), *a2);
      }
    }

    uint64_t consume_tree_with_state(const StateLB &s) const {
      if (std::holds_alternative<typename Tree::Leaf>(this->v())) {
        const auto &[a0] = std::get<typename Tree::Leaf>(this->v());
        return (a0 + s.lb_value);
      } else {
        const auto &[a0, a1, a2] = std::get<typename Tree::Node>(this->v());
        return (((a1 + s.lb_value) + a0->consume_tree_with_state(s)) +
                a2->consume_tree_with_state(s));
      }
    }

    uint64_t tree_sum() const {
      if (std::holds_alternative<typename Tree::Leaf>(this->v())) {
        const auto &[a0] = std::get<typename Tree::Leaf>(this->v());
        return a0;
      } else {
        const auto &[a0, a1, a2] = std::get<typename Tree::Node>(this->v());
        return ((a1 + a0->tree_sum()) + a2->tree_sum());
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, Tree &, T1 &, uint64_t &, Tree &,
                                     T1 &>
    T1 Tree_rec(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename Tree::Leaf>(this->v())) {
        const auto &[a0] = std::get<typename Tree::Leaf>(this->v());
        return f(a0);
      } else {
        const auto &[a0, a1, a2] = std::get<typename Tree::Node>(this->v());
        return f0(*a0, a0->template Tree_rec<T1>(f, f0), a1, *a2,
                  a2->template Tree_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, Tree &, T1 &, uint64_t &, Tree &,
                                     T1 &>
    T1 Tree_rect(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename Tree::Leaf>(this->v())) {
        const auto &[a0] = std::get<typename Tree::Leaf>(this->v());
        return f(a0);
      } else {
        const auto &[a0, a1, a2] = std::get<typename Tree::Node>(this->v());
        return f0(*a0, a0->template Tree_rect<T1>(f, f0), a1, *a2,
                  a2->template Tree_rect<T1>(f, f0));
      }
    }
  };

  static uint64_t accum_with_state(uint64_t n, const StateLB &s);

  struct StateRO {
    uint64_t ro_value;
    uint64_t ro_data;
  };

  struct Container {
    // TYPES
    struct Empty {};

    struct Full {
      StateRO a0;
    };

    using variant_t = std::variant<Empty, Full>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    Container() {}

    explicit Container(Empty _v) : v_(_v) {}

    explicit Container(Full _v) : v_(std::move(_v)) {}

    static Container empty() { return Container(Empty{}); }

    static Container full(StateRO a0) { return Container(Full{std::move(a0)}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t extract_from_container() const {
      if (std::holds_alternative<typename Container::Empty>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0] = std::get<typename Container::Full>(this->v());
        return (a0.ro_value + a0.ro_data);
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, StateRO &>
    T1 Container_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename Container::Empty>(this->v())) {
        return f;
      } else {
        const auto &[a0] = std::get<typename Container::Full>(this->v());
        return f0(a0);
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, StateRO &>
    T1 Container_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename Container::Empty>(this->v())) {
        return f;
      } else {
        const auto &[a0] = std::get<typename Container::Full>(this->v());
        return f0(a0);
      }
    }
  };

  struct StateOP {
    uint64_t op_value;
    uint64_t op_data;
  };

  static StateOP identity(StateOP s);
  static uint64_t extract_via_match(const StateOP &s);
  static StateOP consume_state(StateOP s);
  static uint64_t match_consumed(const StateOP &s);
  static std::pair<StateOP, uint64_t> force_owned(StateOP s);
  static std::pair<std::pair<StateOP, StateOP>, uint64_t>
  pair_then_match(StateOP s);
};

#endif // INCLUDED_COMPREHENSIVE_PATTERNS
