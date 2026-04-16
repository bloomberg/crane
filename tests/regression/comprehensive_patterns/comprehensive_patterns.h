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

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

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
};

template <typename t_A> struct Sig {
  // TYPES
  struct Exist {
    t_A d_x;
  };

  using variant_t = std::variant<Exist>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Sig(Exist _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Sig<t_A>> exist(t_A x) {
    return std::make_shared<Sig<t_A>>(Exist{std::move(x)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct ComprehensivePatterns {
  struct S {
    unsigned int s_a;
    unsigned int s_b;
    unsigned int s_c;
  };

  __attribute__((pure)) static std::pair<
      std::pair<std::shared_ptr<S>, unsigned int>, unsigned int>
  syntactic_variation(std::shared_ptr<S> s);
  __attribute__((pure)) static std::pair<std::shared_ptr<S>, unsigned int>
  with_magic(std::shared_ptr<S> s);

  struct L1 {
    std::shared_ptr<S> l1_s;
  };

  struct L2 {
    std::shared_ptr<L1> l2_l1;
  };

  struct L3 {
    std::shared_ptr<L2> l3_l2;
  };

  struct L4 {
    std::shared_ptr<L3> l4_l3;
  };

  struct L5 {
    std::shared_ptr<L4> l5_l4;
  };

  __attribute__((pure)) static std::pair<
      std::pair<std::pair<std::pair<std::pair<std::pair<std::shared_ptr<L5>,
                                                        std::shared_ptr<L4>>,
                                              std::shared_ptr<L3>>,
                                    std::shared_ptr<L2>>,
                          std::shared_ptr<L1>>,
                std::shared_ptr<S>>,
      unsigned int>
  deep_nest(std::shared_ptr<L5> l5);
  __attribute__((pure)) static std::pair<
      std::pair<std::pair<std::shared_ptr<S>, unsigned int>, unsigned int>,
      unsigned int>
  nested_pair_reuse(std::shared_ptr<S> s);
  __attribute__((pure)) static std::pair<std::shared_ptr<S>, unsigned int>
  compose(std::shared_ptr<S> s);
  __attribute__((pure)) static std::pair<
      std::function<unsigned int(unsigned int)>, std::shared_ptr<S>>
  lambda_proj(std::shared_ptr<S> s);
  __attribute__((pure)) static std::pair<
      std::pair<std::pair<std::shared_ptr<S>, unsigned int>, unsigned int>,
      unsigned int>
  proj_chain(std::shared_ptr<S> s);
  __attribute__((pure)) static std::pair<
      std::pair<std::pair<std::shared_ptr<S>, std::shared_ptr<S>>,
                std::pair<unsigned int, unsigned int>>,
      std::pair<std::pair<unsigned int, unsigned int>,
                std::pair<unsigned int, unsigned int>>>
  octuple(std::shared_ptr<S> s);
  __attribute__((pure)) static std::pair<
      std::optional<std::pair<std::shared_ptr<S>, unsigned int>>,
      std::shared_ptr<S>>
  nested_containers(std::shared_ptr<S> s);
  __attribute__((pure)) static std::pair<
      std::pair<std::shared_ptr<S>, unsigned int>, unsigned int>
  match_pair(const std::pair<std::shared_ptr<S>, unsigned int> p);
  static std::shared_ptr<List<std::pair<std::shared_ptr<S>, unsigned int>>>
  make_list(const unsigned int n, std::shared_ptr<S> s);
  __attribute__((pure)) static std::optional<
      std::pair<std::shared_ptr<S>, std::shared_ptr<S>>>
  multi_match(const std::optional<std::shared_ptr<S>> o1,
              const std::optional<std::shared_ptr<S>> o2);
  enum class Three { e_A, e_B, e_C };

  template <typename T1>
  static T1 Three_rect(const T1 f, const T1 f0, const T1 f3, const Three t) {
    switch (t) {
    case Three::e_A: {
      return f;
    }
    case Three::e_B: {
      return f0;
    }
    case Three::e_C: {
      return f3;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 Three_rec(const T1 f, const T1 f0, const T1 f3, const Three t) {
    switch (t) {
    case Three::e_A: {
      return f;
    }
    case Three::e_B: {
      return f0;
    }
    case Three::e_C: {
      return f3;
    }
    default:
      std::unreachable();
    }
  }

  __attribute__((pure)) static std::pair<std::shared_ptr<S>, unsigned int>
  match_three(const Three t, std::shared_ptr<S> s);
  __attribute__((pure)) static std::pair<std::shared_ptr<S>, unsigned int>
  let_in_arg(std::shared_ptr<S> s);
  __attribute__((pure)) static std::pair<std::shared_ptr<S>, unsigned int>
  match_record(std::shared_ptr<S> s);
  __attribute__((pure)) static std::pair<std::shared_ptr<S>, unsigned int>
  rebind(std::shared_ptr<S> s1);
  __attribute__((
      pure)) static std::pair<std::function<unsigned int(std::monostate)>,
                              std::function<unsigned int(std::monostate)>>
  closure_pair(std::shared_ptr<S> s);
  static std::shared_ptr<Sig<std::shared_ptr<S>>>
  sigma_reuse(std::shared_ptr<S> s);
  __attribute__((pure)) static std::pair<unsigned int,
                                         std::pair<unsigned int, unsigned int>>
  multi_proj_arg(const std::shared_ptr<S> &s);

  struct Either {
    // TYPES
    struct Left_S {
      std::shared_ptr<S> d_s;
    };

    struct Right_N {
      unsigned int d_n;
    };

    using variant_t = std::variant<Left_S, Right_N>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit Either(Left_S _v) : d_v_(std::move(_v)) {}

    explicit Either(Right_N _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<Either> left_s(const std::shared_ptr<S> &s) {
      return std::make_shared<Either>(Left_S{s});
    }

    static std::shared_ptr<Either> left_s(std::shared_ptr<S> &&s) {
      return std::make_shared<Either>(Left_S{std::move(s)});
    }

    static std::shared_ptr<Either> right_n(unsigned int n) {
      return std::make_shared<Either>(Right_N{std::move(n)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, std::shared_ptr<S>> F0,
              MapsTo<T1, unsigned int> F1>
    T1 Either_rec(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename Either::Left_S>(this->v())) {
        const auto &[d_s] = std::get<typename Either::Left_S>(this->v());
        return f(d_s);
      } else {
        const auto &[d_n] = std::get<typename Either::Right_N>(this->v());
        return f0(d_n);
      }
    }

    template <typename T1, MapsTo<T1, std::shared_ptr<S>> F0,
              MapsTo<T1, unsigned int> F1>
    T1 Either_rect(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename Either::Left_S>(this->v())) {
        const auto &[d_s] = std::get<typename Either::Left_S>(this->v());
        return f(d_s);
      } else {
        const auto &[d_n] = std::get<typename Either::Right_N>(this->v());
        return f0(d_n);
      }
    }
  };

  __attribute__((
      pure)) static std::pair<std::shared_ptr<Either>, std::shared_ptr<Either>>
  both_in_sum(std::shared_ptr<S> s);

  struct R1 {
    unsigned int r1_val;
  };

  struct R2 {
    std::shared_ptr<R1> r2_inner;
    unsigned int r2_data;
  };

  struct R3 {
    std::shared_ptr<R2> r3_r2;
    std::shared_ptr<R1> r3_r1;
    unsigned int r3_num;
  };

  __attribute__((pure)) static std::pair<
      std::pair<std::pair<std::shared_ptr<R3>, std::shared_ptr<R2>>,
                std::shared_ptr<R1>>,
      unsigned int>
  hard_proj_chain(std::shared_ptr<R3> r3);
  __attribute__((pure)) static std::pair<
      std::pair<std::shared_ptr<R2>, std::shared_ptr<R1>>, unsigned int>
  multi_path(const std::shared_ptr<R3> &r3);
  __attribute__((pure)) static std::pair<
      std::pair<std::shared_ptr<R2>, std::shared_ptr<R1>>, unsigned int>
  let_proj(std::shared_ptr<R2> r2);
  __attribute__((pure)) static unsigned int
  extract_val(const std::shared_ptr<R1> &r1);
  __attribute__((pure)) static std::pair<std::shared_ptr<R2>, unsigned int>
  nested_call(std::shared_ptr<R2> r2);
  __attribute__((pure)) static std::pair<
      std::pair<std::shared_ptr<R2>, std::shared_ptr<R1>>, unsigned int>
  multi_proj_let(const unsigned int n);
  __attribute__((pure)) static std::optional<
      std::pair<std::shared_ptr<R2>, std::shared_ptr<R1>>>
  match_proj(std::shared_ptr<R2> r2);
  __attribute__((pure)) static std::pair<
      std::pair<std::shared_ptr<R1>, unsigned int>, unsigned int>
  proj_multi_use(const std::shared_ptr<R2> &r2);
  __attribute__((pure)) static std::pair<
      std::pair<std::shared_ptr<R3>, std::shared_ptr<R2>>,
      std::pair<std::shared_ptr<R1>, unsigned int>>
  complex_nest(std::shared_ptr<R3> r3);
  static std::shared_ptr<R2> make_r2(const unsigned int n);
  __attribute__((pure)) static std::pair<
      std::pair<std::shared_ptr<R2>, std::shared_ptr<R1>>, unsigned int>
  from_func(const unsigned int n);
  __attribute__((pure)) static std::pair<
      std::pair<std::shared_ptr<R2>, std::shared_ptr<R1>>,
      std::pair<std::shared_ptr<R1>, unsigned int>>
  pair_of_pairs(std::shared_ptr<R2> r2);
  __attribute__((
      pure)) static std::pair<std::shared_ptr<R2>, std::shared_ptr<R1>>
  cond_proj(const bool b, std::shared_ptr<R2> r2);
  static std::shared_ptr<
      List<std::pair<std::shared_ptr<R2>, std::shared_ptr<R1>>>>
  repeat_r2(const unsigned int n, std::shared_ptr<R2> r2);
  __attribute__((pure)) static std::pair<
      std::pair<std::shared_ptr<R3>, std::shared_ptr<R2>>, std::shared_ptr<R1>>
  nested_lets(std::shared_ptr<R3> r3);
  __attribute__((pure)) static std::pair<std::shared_ptr<R1>, unsigned int>
  double_proj(const std::shared_ptr<R3> &r3);
  __attribute__((pure)) static std::pair<
      std::pair<std::shared_ptr<R3>, std::shared_ptr<R2>>, std::shared_ptr<R2>>
  mixed_access(std::shared_ptr<R3> r3);
  __attribute__((
      pure)) static std::pair<std::shared_ptr<R2>, std::shared_ptr<R1>>
  return_proj_h(std::shared_ptr<R2> r2);
  __attribute__((pure)) static std::pair<
      std::pair<std::pair<std::shared_ptr<R3>, std::shared_ptr<R2>>,
                std::shared_ptr<R1>>,
      unsigned int>
  all_levels(std::shared_ptr<R3> r3);
  __attribute__((
      pure)) static std::pair<std::shared_ptr<R1>, std::shared_ptr<R1>>
  let_and_proj(const std::shared_ptr<R2> &r2);
  __attribute__((
      pure)) static std::pair<std::shared_ptr<R2>, std::shared_ptr<R2>>
  multi_construct(std::shared_ptr<R1> r1);
  __attribute__((pure)) static std::optional<
      std::pair<std::shared_ptr<R2>, std::shared_ptr<R1>>>
  option_proj(const std::optional<std::shared_ptr<R2>> o);

  struct R {
    unsigned int val;
    unsigned int dat;
  };

  __attribute__((pure)) static std::pair<std::shared_ptr<R>, unsigned int>
  pair_inline_proj(std::shared_ptr<R> r);
  __attribute__((pure)) static std::pair<
      std::pair<std::shared_ptr<R>, unsigned int>, unsigned int>
  nested_pair_inline(std::shared_ptr<R> r);
  __attribute__((pure)) static unsigned int
  match_bind_and_use(const std::shared_ptr<R> &r);
  __attribute__((pure)) static unsigned int
  let_with_type(const std::shared_ptr<R> &r);
  __attribute__((pure)) static unsigned int
  proj_of_last_use(const std::shared_ptr<R> &r1);
  __attribute__((pure)) static unsigned int
  multi_let_same(const std::shared_ptr<R> &r);
  __attribute__((pure)) static unsigned int
  option_unwrap_proj(const std::optional<std::shared_ptr<R>> o);
  __attribute__((pure)) static std::pair<std::shared_ptr<R>, unsigned int>
  fun_result_and_proj(const unsigned int n);
  __attribute__((pure)) static std::optional<unsigned int>
  match_multi_use(const std::optional<std::shared_ptr<R>> o);
  __attribute__((pure)) static std::pair<
      std::pair<std::shared_ptr<R>, unsigned int>, unsigned int>
  tuple_proj(std::shared_ptr<R> r);
  __attribute__((pure)) static std::pair<std::shared_ptr<R>, unsigned int>
  chain_to_pair(std::shared_ptr<R> r1);
  static std::shared_ptr<List<std::pair<std::shared_ptr<R>, unsigned int>>>
  repeat_pair(const unsigned int n, std::shared_ptr<R> r);
  __attribute__((pure)) static std::pair<std::shared_ptr<R>, unsigned int>
  cond_pair(const bool b, std::shared_ptr<R> r);
  __attribute__((pure)) static unsigned int
  nested_match(const std::optional<std::shared_ptr<R>> o1,
               const std::optional<std::shared_ptr<R>> o2);
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  both_proj(const std::shared_ptr<R> &r);
  __attribute__((pure)) static unsigned int
  compose_proj(const std::shared_ptr<R> &r);
  __attribute__((pure)) static std::optional<unsigned int>
  proj_through_option(const std::shared_ptr<R> &r);

  struct NC {
    unsigned int nc_a;
    unsigned int nc_b;
    unsigned int nc_c;
  };

  __attribute__((pure)) static unsigned int use_proj(const unsigned int n);
  __attribute__((pure)) static unsigned int
  proj_as_arg(const std::shared_ptr<NC> &r);
  __attribute__((pure)) static unsigned int use_two(const unsigned int _x0,
                                                    const unsigned int _x1);
  __attribute__((pure)) static unsigned int
  multi_proj_args(const std::shared_ptr<NC> &r);
  __attribute__((pure)) static unsigned int
  let_proj_then_base(const std::shared_ptr<NC> &r);
  __attribute__((pure)) static unsigned int
  base_then_multi_proj(const std::shared_ptr<NC> &r);
  __attribute__((pure)) static unsigned int
  proj_in_condition(const std::shared_ptr<NC> &r);
  __attribute__((pure)) static unsigned int
  proj_in_scrutinee(const std::shared_ptr<NC> &r);
  __attribute__((pure)) static unsigned int
  return_proj_nc(const std::shared_ptr<NC> &r);
  __attribute__((pure)) static unsigned int
  call_return_proj(const std::shared_ptr<NC> &r);
  __attribute__((pure)) static unsigned int inc(const unsigned int n);
  __attribute__((pure)) static unsigned int
  nested_proj_calls(const std::shared_ptr<NC> &r);
  __attribute__((pure)) static unsigned int
  count_down(const unsigned int n, const std::shared_ptr<NC> &r);
  __attribute__((pure)) static unsigned int f1(const std::shared_ptr<NC> &r);
  __attribute__((pure)) static unsigned int f2(const std::shared_ptr<NC> &r);
  __attribute__((pure)) static unsigned int
  multi_function_calls(const std::shared_ptr<NC> &r);
  __attribute__((pure)) static unsigned int
  proj_then_match(const std::shared_ptr<NC> &r);
  __attribute__((pure)) static unsigned int
  let_used_twice(const std::shared_ptr<NC> &r);
  __attribute__((pure)) static bool
  base_in_call_and_proj(const std::shared_ptr<NC> &r);
  __attribute__((pure)) static unsigned int
  chained_lets_same_base(const std::shared_ptr<NC> &r);

  struct OuterNC {
    std::shared_ptr<NC> outer_nc;
  };

  __attribute__((pure)) static unsigned int
  double_proj_nc(const std::shared_ptr<OuterNC> &o);
  __attribute__((pure)) static unsigned int
  multi_positions(const std::shared_ptr<NC> &r);
  __attribute__((pure)) static unsigned int
  sum_proj(const unsigned int n, const std::shared_ptr<NC> &r);

  template <MapsTo<unsigned int, std::shared_ptr<NC>> F0>
  __attribute__((pure)) static unsigned int apply(F0 &&f,
                                                  std::shared_ptr<NC> _x0) {
    return f(std::move(_x0));
  }

  __attribute__((pure)) static unsigned int
  hof_test(const std::shared_ptr<NC> &r);

  struct State {
    unsigned int state_value;
    unsigned int state_data;
  };

  __attribute__((pure)) static unsigned int use_two_fc(const unsigned int _x0,
                                                       const unsigned int _x1);
  __attribute__((pure)) static unsigned int
  bug_two_args(const std::shared_ptr<State> &s);
  __attribute__((pure)) static unsigned int
  use_three(const unsigned int x, const unsigned int y, const unsigned int z);
  __attribute__((pure)) static unsigned int
  bug_three_args(const std::shared_ptr<State> &s);
  __attribute__((pure)) static unsigned int
  take_state_and_val(const std::shared_ptr<State> &_x, const unsigned int n);
  __attribute__((pure)) static unsigned int
  bug_state_and_proj(const std::shared_ptr<State> &s);
  __attribute__((pure)) static unsigned int inner_func(const unsigned int n);
  __attribute__((pure)) static unsigned int
  bug_nested_calls(const std::shared_ptr<State> &s);
  __attribute__((pure)) static unsigned int
  bug_in_condition(const std::shared_ptr<State> &s);
  __attribute__((pure)) static unsigned int f1_fc(const unsigned int n);
  __attribute__((pure)) static unsigned int f2_fc(const unsigned int n);
  __attribute__((pure)) static unsigned int
  bug_multi_calls(const std::shared_ptr<State> &s);
  __attribute__((pure)) static std::pair<std::shared_ptr<State>, unsigned int>
  bug_base_and_proj(const std::shared_ptr<State> &s);
  __attribute__((pure)) static unsigned int
  sequential_lets(const std::shared_ptr<State> &s);
  __attribute__((pure)) static std::pair<std::shared_ptr<State>, unsigned int>
  let_then_use_base(std::shared_ptr<State> s);
  __attribute__((pure)) static unsigned int
  two_proj_sequence(const std::shared_ptr<State> &s);
  __attribute__((pure)) static unsigned int
  let_multi_proj(const std::shared_ptr<State> &s);
  __attribute__((pure)) static unsigned int
  nested_lets_same_base(const std::shared_ptr<State> &s);
  __attribute__((pure)) static unsigned int
  if_with_proj(const std::shared_ptr<State> &s);
  __attribute__((pure)) static unsigned int
  match_scrutinee_proj(const std::shared_ptr<State> &s);
  __attribute__((pure)) static std::pair<std::shared_ptr<State>, unsigned int>
  bind_proj_use_base(std::shared_ptr<State> s);

  struct RSeq {
    unsigned int seq_val;
  };

  static std::shared_ptr<RSeq> side_effect(std::shared_ptr<RSeq> r);
  __attribute__((pure)) static unsigned int
  after_side_effect(const std::shared_ptr<RSeq> &r);
  __attribute__((pure)) static unsigned int
  two_side_effects(const std::shared_ptr<RSeq> &r);
  __attribute__((pure)) static unsigned int
  side_effect_in_branch(const bool b, const std::shared_ptr<RSeq> &r);

  struct StateStmt {
    unsigned int stmt_value;
    unsigned int stmt_data;
  };

  __attribute__((pure)) static unsigned int
  return_proj_stmt(const std::shared_ptr<StateStmt> &s);
  __attribute__((pure)) static unsigned int
  return_complex(const std::shared_ptr<StateStmt> &s);
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  return_pair(const std::shared_ptr<StateStmt> &s);

  struct InnerStmt {
    unsigned int inner_stmt_val;
  };

  struct OuterStmt {
    std::shared_ptr<InnerStmt> outer_stmt_inner;
    unsigned int outer_stmt_data;
  };

  __attribute__((pure)) static unsigned int
  chained_proj(const std::shared_ptr<OuterStmt> &o);

  struct Level3Stmt {
    std::shared_ptr<OuterStmt> l3_outer_stmt;
  };

  __attribute__((pure)) static unsigned int
  triple_chain(const std::shared_ptr<Level3Stmt> &l3);
  __attribute__((pure)) static unsigned int
  proj_in_arith(const std::shared_ptr<StateStmt> &s);
  __attribute__((pure)) static unsigned int
  multi_proj_expr(const std::shared_ptr<StateStmt> &s);
  static std::shared_ptr<List<unsigned int>>
  proj_in_list(const std::shared_ptr<StateStmt> &s);
  __attribute__((pure)) static bool
  compare_projs(const std::shared_ptr<StateStmt> &s);
  __attribute__((pure)) static bool
  bool_with_proj(const std::shared_ptr<StateStmt> &s);

  template <typename T1> static T1 _bug_base_and_proj_consume(const T1 x) {
    return x;
  }

  __attribute__((pure)) static unsigned int
  sum_values(const unsigned int n, const std::shared_ptr<StateStmt> &s);

  struct RCF {
    unsigned int cf_val;
  };

  __attribute__((pure)) static unsigned int
  branch_use(const bool b, const std::shared_ptr<RCF> &r);
  __attribute__((pure)) static std::pair<std::shared_ptr<RCF>, unsigned int>
  branch_different(const bool b, std::shared_ptr<RCF> r);
  __attribute__((pure)) static unsigned int
  match_with_wild(const std::optional<std::shared_ptr<RCF>> o);
  __attribute__((pure)) static unsigned int
  sum_with_state(const unsigned int n, const std::shared_ptr<RCF> &r);
  __attribute__((pure)) static unsigned int
  even_count(const unsigned int n, const std::shared_ptr<RCF> &r);
  __attribute__((pure)) static unsigned int
  odd_count(const unsigned int n, const std::shared_ptr<RCF> &r);

  struct StateLB {
    unsigned int lb_value;
    unsigned int lb_data;
  };

  struct Tree : public std::enable_shared_from_this<Tree> {
    // TYPES
    struct Leaf {
      unsigned int d_a0;
    };

    struct Node {
      std::shared_ptr<Tree> d_a0;
      unsigned int d_a1;
      std::shared_ptr<Tree> d_a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit Tree(Leaf _v) : d_v_(std::move(_v)) {}

    explicit Tree(Node _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<Tree> leaf(unsigned int a0) {
      return std::make_shared<Tree>(Leaf{std::move(a0)});
    }

    static std::shared_ptr<Tree> node(const std::shared_ptr<Tree> &a0,
                                      unsigned int a1,
                                      const std::shared_ptr<Tree> &a2) {
      return std::make_shared<Tree>(Node{a0, std::move(a1), a2});
    }

    static std::shared_ptr<Tree> node(std::shared_ptr<Tree> &&a0,
                                      unsigned int a1,
                                      std::shared_ptr<Tree> &&a2) {
      return std::make_shared<Tree>(
          Node{std::move(a0), std::move(a1), std::move(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    std::shared_ptr<Tree> nested_reuse() const {
      std::shared_ptr<Tree> t2 = this->transform_tree();
      return std::move(t2)->transform_tree();
    }

    std::shared_ptr<Tree> flip_tree() const {
      if (std::holds_alternative<typename Tree::Leaf>(this->v())) {
        const auto &[d_a0] = std::get<typename Tree::Leaf>(this->v());
        return Tree::node(
            std::const_pointer_cast<Tree>(this->shared_from_this()), d_a0,
            std::const_pointer_cast<Tree>(this->shared_from_this()));
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename Tree::Node>(this->v());
        return Tree::leaf(d_a1);
      }
    }

    std::shared_ptr<Tree> transform_tree() const {
      if (std::holds_alternative<typename Tree::Leaf>(this->v())) {
        const auto &[d_a0] = std::get<typename Tree::Leaf>(this->v());
        return Tree::leaf((d_a0 + 1u));
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename Tree::Node>(this->v());
        return Tree::node(d_a0, (d_a1 + 1u), d_a2);
      }
    }

    __attribute__((pure)) unsigned int
    consume_tree_with_state(const std::shared_ptr<StateLB> &s) const {
      const Tree *_self = this;

      struct _Enter {
        const Tree *_self;
      };

      struct _Call1 {
        Tree *_s0;
        decltype((
            std::declval<unsigned int &>() +
            std::declval<const std::shared_ptr<StateLB> &>()->lb_value)) _s1;
      };

      struct _Call2 {
        unsigned int _s0;
        decltype((
            std::declval<unsigned int &>() +
            std::declval<const std::shared_ptr<StateLB> &>()->lb_value)) _s1;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          const auto &_f = std::get<_Enter>(_frame);
          const Tree *_self = _f._self;
          if (std::holds_alternative<typename Tree::Leaf>(_self->v())) {
            const auto &[d_a0] = std::get<typename Tree::Leaf>(_self->v());
            _result = (d_a0 + s->lb_value);
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename Tree::Node>(_self->v());
            _stack.emplace_back(_Call1{d_a0.get(), (d_a1 + s->lb_value)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          const auto &_f = std::get<_Call1>(_frame);
          _stack.emplace_back(_Call2{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          const auto &_f = std::get<_Call2>(_frame);
          _result = ((_f._s1 + _result) + _f._s0);
        }
      }
      return _result;
    }

    __attribute__((pure)) unsigned int tree_sum() const {
      const Tree *_self = this;

      struct _Enter {
        const Tree *_self;
      };

      struct _Call1 {
        Tree *_s0;
        unsigned int _s1;
      };

      struct _Call2 {
        unsigned int _s0;
        unsigned int _s1;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          const auto &_f = std::get<_Enter>(_frame);
          const Tree *_self = _f._self;
          if (std::holds_alternative<typename Tree::Leaf>(_self->v())) {
            const auto &[d_a0] = std::get<typename Tree::Leaf>(_self->v());
            _result = d_a0;
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename Tree::Node>(_self->v());
            _stack.emplace_back(_Call1{d_a0.get(), d_a1});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          const auto &_f = std::get<_Call1>(_frame);
          _stack.emplace_back(_Call2{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          const auto &_f = std::get<_Call2>(_frame);
          _result = ((_f._s1 + _result) + _f._s0);
        }
      }
      return _result;
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, std::shared_ptr<Tree>, T1, unsigned int,
                     std::shared_ptr<Tree>, T1>
                  F1>
    T1 Tree_rec(F0 &&f, F1 &&f0) const {
      const Tree *_self = this;

      struct _Enter {
        const Tree *_self;
      };

      struct _Call1 {
        Tree *_s0;
        std::shared_ptr<Tree> _s1;
        unsigned int _s2;
        std::shared_ptr<Tree> _s3;
      };

      struct _Call2 {
        T1 _s0;
        std::shared_ptr<Tree> _s1;
        unsigned int _s2;
        std::shared_ptr<Tree> _s3;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          const auto &_f = std::get<_Enter>(_frame);
          const Tree *_self = _f._self;
          if (std::holds_alternative<typename Tree::Leaf>(_self->v())) {
            const auto &[d_a0] = std::get<typename Tree::Leaf>(_self->v());
            _result = f(d_a0);
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename Tree::Node>(_self->v());
            _stack.emplace_back(_Call1{d_a0.get(), d_a2, d_a1, d_a0});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          const auto &_f = std::get<_Call1>(_frame);
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2, _f._s3});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          const auto &_f = std::get<_Call2>(_frame);
          _result = f0(_f._s3, _result, _f._s2, _f._s1, _f._s0);
        }
      }
      return _result;
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, std::shared_ptr<Tree>, T1, unsigned int,
                     std::shared_ptr<Tree>, T1>
                  F1>
    T1 Tree_rect(F0 &&f, F1 &&f0) const {
      const Tree *_self = this;

      struct _Enter {
        const Tree *_self;
      };

      struct _Call1 {
        Tree *_s0;
        std::shared_ptr<Tree> _s1;
        unsigned int _s2;
        std::shared_ptr<Tree> _s3;
      };

      struct _Call2 {
        T1 _s0;
        std::shared_ptr<Tree> _s1;
        unsigned int _s2;
        std::shared_ptr<Tree> _s3;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          const auto &_f = std::get<_Enter>(_frame);
          const Tree *_self = _f._self;
          if (std::holds_alternative<typename Tree::Leaf>(_self->v())) {
            const auto &[d_a0] = std::get<typename Tree::Leaf>(_self->v());
            _result = f(d_a0);
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename Tree::Node>(_self->v());
            _stack.emplace_back(_Call1{d_a0.get(), d_a2, d_a1, d_a0});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          const auto &_f = std::get<_Call1>(_frame);
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2, _f._s3});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          const auto &_f = std::get<_Call2>(_frame);
          _result = f0(_f._s3, _result, _f._s2, _f._s1, _f._s0);
        }
      }
      return _result;
    }
  };

  __attribute__((pure)) static unsigned int
  accum_with_state(const unsigned int n, const std::shared_ptr<StateLB> &s);

  struct StateRO {
    unsigned int ro_value;
    unsigned int ro_data;
  };

  struct Container {
    // TYPES
    struct Empty {};

    struct Full {
      std::shared_ptr<StateRO> d_a0;
    };

    using variant_t = std::variant<Empty, Full>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit Container(Empty _v) : d_v_(_v) {}

    explicit Container(Full _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<Container> empty() {
      return std::make_shared<Container>(Empty{});
    }

    static std::shared_ptr<Container> full(const std::shared_ptr<StateRO> &a0) {
      return std::make_shared<Container>(Full{a0});
    }

    static std::shared_ptr<Container> full(std::shared_ptr<StateRO> &&a0) {
      return std::make_shared<Container>(Full{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int extract_from_container() const {
      if (std::holds_alternative<typename Container::Empty>(this->v())) {
        return 0u;
      } else {
        const auto &[d_a0] = std::get<typename Container::Full>(this->v());
        return (d_a0->ro_value + d_a0->ro_data);
      }
    }

    template <typename T1, MapsTo<T1, std::shared_ptr<StateRO>> F1>
    T1 Container_rec(const T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename Container::Empty>(this->v())) {
        return f;
      } else {
        const auto &[d_a0] = std::get<typename Container::Full>(this->v());
        return f0(d_a0);
      }
    }

    template <typename T1, MapsTo<T1, std::shared_ptr<StateRO>> F1>
    T1 Container_rect(const T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename Container::Empty>(this->v())) {
        return f;
      } else {
        const auto &[d_a0] = std::get<typename Container::Full>(this->v());
        return f0(d_a0);
      }
    }
  };

  struct StateOP {
    unsigned int op_value;
    unsigned int op_data;
  };

  static std::shared_ptr<StateOP> identity(std::shared_ptr<StateOP> s);
  __attribute__((pure)) static unsigned int
  extract_via_match(const std::shared_ptr<StateOP> &s);
  static std::shared_ptr<StateOP> consume_state(std::shared_ptr<StateOP> s);
  __attribute__((pure)) static unsigned int
  match_consumed(const std::shared_ptr<StateOP> &s);
  __attribute__((pure)) static std::pair<std::shared_ptr<StateOP>, unsigned int>
  force_owned(std::shared_ptr<StateOP> s);
  __attribute__((pure)) static std::pair<
      std::pair<std::shared_ptr<StateOP>, std::shared_ptr<StateOP>>,
      unsigned int>
  pair_then_match(std::shared_ptr<StateOP> s);
};

#endif // INCLUDED_COMPREHENSIVE_PATTERNS
