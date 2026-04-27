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
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
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

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

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
  Sig() {}

  explicit Sig(Exist _v) : d_v_(std::move(_v)) {}

  Sig(const Sig<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Sig(Sig<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  Sig<t_A> &operator=(const Sig<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Sig<t_A> &operator=(Sig<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) Sig<t_A> clone() const {
    auto &&_sv = *(this);
    const auto &[d_x] = std::get<Exist>(_sv.v());
    return Sig<t_A>(Exist{d_x});
  }

  // CREATORS
  template <typename _U> explicit Sig(const Sig<_U> &_other) {
    const auto &[d_x] = std::get<typename Sig<_U>::Exist>(_other.v());
    d_v_ = Exist{t_A(d_x)};
  }

  __attribute__((pure)) static Sig<t_A> exist(t_A x) {
    return Sig(Exist{std::move(x)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) Sig<t_A> *operator->() { return this; }

  __attribute__((pure)) const Sig<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = Sig<t_A>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct ComprehensivePatterns {
  struct S {
    unsigned int s_a;
    unsigned int s_b;
    unsigned int s_c;

    __attribute__((pure)) S *operator->() { return this; }

    __attribute__((pure)) const S *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) S clone() const {
      return S{(*(this)).s_a, (*(this)).s_b, (*(this)).s_c};
    }
  };

  __attribute__((
      pure)) static std::pair<std::pair<S, unsigned int>, unsigned int>
  syntactic_variation(S s);
  __attribute__((pure)) static std::pair<S, unsigned int> with_magic(S s);

  struct L1 {
    S l1_s;

    __attribute__((pure)) L1 *operator->() { return this; }

    __attribute__((pure)) const L1 *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) L1 clone() const {
      return L1{(*(this)).l1_s.clone()};
    }
  };

  struct L2 {
    L1 l2_l1;

    __attribute__((pure)) L2 *operator->() { return this; }

    __attribute__((pure)) const L2 *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) L2 clone() const {
      return L2{(*(this)).l2_l1.clone()};
    }
  };

  struct L3 {
    L2 l3_l2;

    __attribute__((pure)) L3 *operator->() { return this; }

    __attribute__((pure)) const L3 *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) L3 clone() const {
      return L3{(*(this)).l3_l2.clone()};
    }
  };

  struct L4 {
    L3 l4_l3;

    __attribute__((pure)) L4 *operator->() { return this; }

    __attribute__((pure)) const L4 *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) L4 clone() const {
      return L4{(*(this)).l4_l3.clone()};
    }
  };

  struct L5 {
    L4 l5_l4;

    __attribute__((pure)) L5 *operator->() { return this; }

    __attribute__((pure)) const L5 *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) L5 clone() const {
      return L5{(*(this)).l5_l4.clone()};
    }
  };

  __attribute__((pure)) static std::pair<
      std::pair<std::pair<std::pair<std::pair<std::pair<L5, L4>, L3>, L2>, L1>,
                S>,
      unsigned int>
  deep_nest(L5 l5);
  __attribute__((pure)) static std::pair<
      std::pair<std::pair<S, unsigned int>, unsigned int>, unsigned int>
  nested_pair_reuse(S s);
  __attribute__((pure)) static std::pair<S, unsigned int> compose(S s);
  __attribute__((
      pure)) static std::pair<std::function<unsigned int(unsigned int)>, S>
  lambda_proj(S s);
  __attribute__((pure)) static std::pair<
      std::pair<std::pair<S, unsigned int>, unsigned int>, unsigned int>
  proj_chain(S s);
  __attribute__((pure)) static std::pair<
      std::pair<std::pair<S, S>, std::pair<unsigned int, unsigned int>>,
      std::pair<std::pair<unsigned int, unsigned int>,
                std::pair<unsigned int, unsigned int>>>
  octuple(S s);
  __attribute__((
      pure)) static std::pair<std::optional<std::pair<S, unsigned int>>, S>
  nested_containers(S s);
  __attribute__((
      pure)) static std::pair<std::pair<S, unsigned int>, unsigned int>
  match_pair(const std::pair<S, unsigned int> &p);
  __attribute__((pure)) static List<std::pair<S, unsigned int>>
  make_list(const unsigned int &n, S s);
  __attribute__((pure)) static std::optional<std::pair<S, S>>
  multi_match(const std::optional<S> &o1, const std::optional<S> &o2);
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

  __attribute__((pure)) static std::pair<S, unsigned int>
  match_three(const Three t, S s);
  __attribute__((pure)) static std::pair<S, unsigned int> let_in_arg(S s);
  __attribute__((pure)) static std::pair<S, unsigned int> match_record(S s);
  __attribute__((pure)) static std::pair<S, unsigned int> rebind(S s1);
  __attribute__((
      pure)) static std::pair<std::function<unsigned int(std::monostate)>,
                              std::function<unsigned int(std::monostate)>>
  closure_pair(S s);
  __attribute__((pure)) static Sig<S> sigma_reuse(S s);
  __attribute__((pure)) static std::pair<unsigned int,
                                         std::pair<unsigned int, unsigned int>>
  multi_proj_arg(const S &s);

  struct Either {
    // TYPES
    struct Left_S {
      S d_s;
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
    Either() {}

    explicit Either(Left_S _v) : d_v_(std::move(_v)) {}

    explicit Either(Right_N _v) : d_v_(std::move(_v)) {}

    Either(const Either &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    Either(Either &&_other) : d_v_(std::move(_other.d_v_)) {}

    Either &operator=(const Either &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    Either &operator=(Either &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) Either clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Left_S>(_sv.v())) {
        const auto &[d_s] = std::get<Left_S>(_sv.v());
        return Either(Left_S{d_s.clone()});
      } else {
        const auto &[d_n] = std::get<Right_N>(_sv.v());
        return Either(Right_N{d_n});
      }
    }

    // CREATORS
    __attribute__((pure)) static Either left_s(S s) {
      return Either(Left_S{std::move(s)});
    }

    __attribute__((pure)) static Either right_n(unsigned int n) {
      return Either(Right_N{std::move(n)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) Either *operator->() { return this; }

    __attribute__((pure)) const Either *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = Either(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, S> F0, MapsTo<T1, unsigned int> F1>
    T1 Either_rec(F0 &&f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename Either::Left_S>(_sv.v())) {
        const auto &[d_s] = std::get<typename Either::Left_S>(_sv.v());
        return f(d_s);
      } else {
        const auto &[d_n] = std::get<typename Either::Right_N>(_sv.v());
        return f0(d_n);
      }
    }

    template <typename T1, MapsTo<T1, S> F0, MapsTo<T1, unsigned int> F1>
    T1 Either_rect(F0 &&f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename Either::Left_S>(_sv.v())) {
        const auto &[d_s] = std::get<typename Either::Left_S>(_sv.v());
        return f(d_s);
      } else {
        const auto &[d_n] = std::get<typename Either::Right_N>(_sv.v());
        return f0(d_n);
      }
    }
  };

  __attribute__((pure)) static std::pair<Either, Either> both_in_sum(S s);

  struct R1 {
    unsigned int r1_val;

    __attribute__((pure)) R1 *operator->() { return this; }

    __attribute__((pure)) const R1 *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) R1 clone() const { return R1{(*(this)).r1_val}; }
  };

  struct R2 {
    R1 r2_inner;
    unsigned int r2_data;

    __attribute__((pure)) R2 *operator->() { return this; }

    __attribute__((pure)) const R2 *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) R2 clone() const {
      return R2{(*(this)).r2_inner.clone(), (*(this)).r2_data};
    }
  };

  struct R3 {
    R2 r3_r2;
    R1 r3_r1;
    unsigned int r3_num;

    __attribute__((pure)) R3 *operator->() { return this; }

    __attribute__((pure)) const R3 *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) R3 clone() const {
      return R3{(*(this)).r3_r2.clone(), (*(this)).r3_r1.clone(),
                (*(this)).r3_num};
    }
  };

  __attribute__((
      pure)) static std::pair<std::pair<std::pair<R3, R2>, R1>, unsigned int>
  hard_proj_chain(R3 r3);
  __attribute__((pure)) static std::pair<std::pair<R2, R1>, unsigned int>
  multi_path(const R3 &r3);
  __attribute__((pure)) static std::pair<std::pair<R2, R1>, unsigned int>
  let_proj(R2 r2);
  __attribute__((pure)) static unsigned int extract_val(const R1 &r1);
  __attribute__((pure)) static std::pair<R2, unsigned int> nested_call(R2 r2);
  __attribute__((pure)) static std::pair<std::pair<R2, R1>, unsigned int>
  multi_proj_let(unsigned int n);
  __attribute__((pure)) static std::optional<std::pair<R2, R1>>
  match_proj(R2 r2);
  __attribute__((
      pure)) static std::pair<std::pair<R1, unsigned int>, unsigned int>
  proj_multi_use(const R2 &r2);
  __attribute__((
      pure)) static std::pair<std::pair<R3, R2>, std::pair<R1, unsigned int>>
  complex_nest(R3 r3);
  __attribute__((pure)) static R2 make_r2(unsigned int n);
  __attribute__((pure)) static std::pair<std::pair<R2, R1>, unsigned int>
  from_func(const unsigned int &n);
  __attribute__((
      pure)) static std::pair<std::pair<R2, R1>, std::pair<R1, unsigned int>>
  pair_of_pairs(R2 r2);
  __attribute__((pure)) static std::pair<R2, R1> cond_proj(const bool &b,
                                                           R2 r2);
  __attribute__((pure)) static List<std::pair<R2, R1>>
  repeat_r2(const unsigned int &n, R2 r2);
  __attribute__((pure)) static std::pair<std::pair<R3, R2>, R1>
  nested_lets(R3 r3);
  __attribute__((pure)) static std::pair<R1, unsigned int>
  double_proj(const R3 &r3);
  __attribute__((pure)) static std::pair<std::pair<R3, R2>, R2>
  mixed_access(R3 r3);
  __attribute__((pure)) static std::pair<R2, R1> return_proj_h(R2 r2);
  __attribute__((
      pure)) static std::pair<std::pair<std::pair<R3, R2>, R1>, unsigned int>
  all_levels(R3 r3);
  __attribute__((pure)) static std::pair<R1, R1> let_and_proj(const R2 &r2);
  __attribute__((pure)) static std::pair<R2, R2> multi_construct(R1 r1);
  __attribute__((pure)) static std::optional<std::pair<R2, R1>>
  option_proj(const std::optional<R2> &o);

  struct R {
    unsigned int val;
    unsigned int dat;

    __attribute__((pure)) R *operator->() { return this; }

    __attribute__((pure)) const R *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) R clone() const {
      return R{(*(this)).val, (*(this)).dat};
    }
  };

  __attribute__((pure)) static std::pair<R, unsigned int> pair_inline_proj(R r);
  __attribute__((
      pure)) static std::pair<std::pair<R, unsigned int>, unsigned int>
  nested_pair_inline(R r);
  __attribute__((pure)) static unsigned int match_bind_and_use(const R &r);
  __attribute__((pure)) static unsigned int let_with_type(const R &r);
  __attribute__((pure)) static unsigned int proj_of_last_use(const R &r1);
  __attribute__((pure)) static unsigned int multi_let_same(const R &r);
  __attribute__((pure)) static unsigned int
  option_unwrap_proj(const std::optional<R> &o);
  __attribute__((pure)) static std::pair<R, unsigned int>
  fun_result_and_proj(unsigned int n);
  __attribute__((pure)) static std::optional<unsigned int>
  match_multi_use(const std::optional<R> &o);
  __attribute__((
      pure)) static std::pair<std::pair<R, unsigned int>, unsigned int>
  tuple_proj(R r);
  __attribute__((pure)) static std::pair<R, unsigned int> chain_to_pair(R r1);
  __attribute__((pure)) static List<std::pair<R, unsigned int>>
  repeat_pair(const unsigned int &n, R r);
  __attribute__((pure)) static std::pair<R, unsigned int>
  cond_pair(const bool &b, R r);
  __attribute__((pure)) static unsigned int
  nested_match(const std::optional<R> &o1, const std::optional<R> &o2);
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  both_proj(const R &r);
  __attribute__((pure)) static unsigned int compose_proj(const R &r);
  __attribute__((pure)) static std::optional<unsigned int>
  proj_through_option(const R &r);

  struct NC {
    unsigned int nc_a;
    unsigned int nc_b;
    unsigned int nc_c;

    __attribute__((pure)) NC *operator->() { return this; }

    __attribute__((pure)) const NC *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) NC clone() const {
      return NC{(*(this)).nc_a, (*(this)).nc_b, (*(this)).nc_c};
    }
  };

  __attribute__((pure)) static unsigned int use_proj(unsigned int n);
  __attribute__((pure)) static unsigned int proj_as_arg(const NC &r);
  __attribute__((pure)) static unsigned int use_two(const unsigned int &_x0,
                                                    const unsigned int &_x1);
  __attribute__((pure)) static unsigned int multi_proj_args(const NC &r);
  __attribute__((pure)) static unsigned int let_proj_then_base(const NC &r);
  __attribute__((pure)) static unsigned int base_then_multi_proj(const NC &r);
  __attribute__((pure)) static unsigned int proj_in_condition(const NC &r);
  __attribute__((pure)) static unsigned int proj_in_scrutinee(const NC &r);
  __attribute__((pure)) static unsigned int return_proj_nc(const NC &r);
  __attribute__((pure)) static unsigned int call_return_proj(const NC &r);
  __attribute__((pure)) static unsigned int inc(const unsigned int &n);
  __attribute__((pure)) static unsigned int nested_proj_calls(const NC &r);
  __attribute__((pure)) static unsigned int count_down(const unsigned int &n,
                                                       const NC &r);
  __attribute__((pure)) static unsigned int f1(const NC &r);
  __attribute__((pure)) static unsigned int f2(const NC &r);
  __attribute__((pure)) static unsigned int multi_function_calls(const NC &r);
  __attribute__((pure)) static unsigned int proj_then_match(const NC &r);
  __attribute__((pure)) static unsigned int let_used_twice(const NC &r);
  __attribute__((pure)) static bool base_in_call_and_proj(const NC &r);
  __attribute__((pure)) static unsigned int chained_lets_same_base(const NC &r);

  struct OuterNC {
    NC outer_nc;

    __attribute__((pure)) OuterNC *operator->() { return this; }

    __attribute__((pure)) const OuterNC *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) OuterNC clone() const {
      return OuterNC{(*(this)).outer_nc.clone()};
    }
  };

  __attribute__((pure)) static unsigned int double_proj_nc(const OuterNC &o);
  __attribute__((pure)) static unsigned int multi_positions(const NC &r);
  __attribute__((pure)) static unsigned int sum_proj(const unsigned int &n,
                                                     const NC &r);

  template <MapsTo<unsigned int, NC> F0>
  __attribute__((pure)) static unsigned int apply(F0 &&f, NC _x0) {
    return f(_x0);
  }

  __attribute__((pure)) static unsigned int hof_test(const NC &r);

  struct State {
    unsigned int state_value;
    unsigned int state_data;

    __attribute__((pure)) State *operator->() { return this; }

    __attribute__((pure)) const State *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) State clone() const {
      return State{(*(this)).state_value, (*(this)).state_data};
    }
  };

  __attribute__((pure)) static unsigned int use_two_fc(const unsigned int &_x0,
                                                       const unsigned int &_x1);
  __attribute__((pure)) static unsigned int bug_two_args(const State &s);
  __attribute__((pure)) static unsigned int use_three(const unsigned int &x,
                                                      const unsigned int &y,
                                                      const unsigned int &z);
  __attribute__((pure)) static unsigned int bug_three_args(const State &s);
  __attribute__((pure)) static unsigned int take_state_and_val(const State &_x,
                                                               unsigned int n);
  __attribute__((pure)) static unsigned int bug_state_and_proj(const State &s);
  __attribute__((pure)) static unsigned int inner_func(const unsigned int &n);
  __attribute__((pure)) static unsigned int bug_nested_calls(const State &s);
  __attribute__((pure)) static unsigned int bug_in_condition(const State &s);
  __attribute__((pure)) static unsigned int f1_fc(unsigned int n);
  __attribute__((pure)) static unsigned int f2_fc(const unsigned int &n);
  __attribute__((pure)) static unsigned int bug_multi_calls(const State &s);
  __attribute__((pure)) static std::pair<State, unsigned int>
  bug_base_and_proj(const State &s);
  __attribute__((pure)) static unsigned int sequential_lets(const State &s);
  __attribute__((pure)) static std::pair<State, unsigned int>
  let_then_use_base(State s);
  __attribute__((pure)) static unsigned int two_proj_sequence(const State &s);
  __attribute__((pure)) static unsigned int let_multi_proj(const State &s);
  __attribute__((pure)) static unsigned int
  nested_lets_same_base(const State &s);
  __attribute__((pure)) static unsigned int if_with_proj(const State &s);
  __attribute__((pure)) static unsigned int
  match_scrutinee_proj(const State &s);
  __attribute__((pure)) static std::pair<State, unsigned int>
  bind_proj_use_base(State s);

  struct RSeq {
    unsigned int seq_val;

    __attribute__((pure)) RSeq *operator->() { return this; }

    __attribute__((pure)) const RSeq *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) RSeq clone() const { return RSeq{(*(this)).seq_val}; }
  };

  __attribute__((pure)) static RSeq side_effect(RSeq r);
  __attribute__((pure)) static unsigned int after_side_effect(const RSeq &r);
  __attribute__((pure)) static unsigned int two_side_effects(const RSeq &r);
  __attribute__((pure)) static unsigned int
  side_effect_in_branch(const bool &b, const RSeq &r);

  struct StateStmt {
    unsigned int stmt_value;
    unsigned int stmt_data;

    __attribute__((pure)) StateStmt *operator->() { return this; }

    __attribute__((pure)) const StateStmt *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) StateStmt clone() const {
      return StateStmt{(*(this)).stmt_value, (*(this)).stmt_data};
    }
  };

  __attribute__((pure)) static unsigned int
  return_proj_stmt(const StateStmt &s);
  __attribute__((pure)) static unsigned int return_complex(const StateStmt &s);
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  return_pair(const StateStmt &s);

  struct InnerStmt {
    unsigned int inner_stmt_val;

    __attribute__((pure)) InnerStmt *operator->() { return this; }

    __attribute__((pure)) const InnerStmt *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) InnerStmt clone() const {
      return InnerStmt{(*(this)).inner_stmt_val};
    }
  };

  struct OuterStmt {
    InnerStmt outer_stmt_inner;
    unsigned int outer_stmt_data;

    __attribute__((pure)) OuterStmt *operator->() { return this; }

    __attribute__((pure)) const OuterStmt *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) OuterStmt clone() const {
      return OuterStmt{(*(this)).outer_stmt_inner.clone(),
                       (*(this)).outer_stmt_data};
    }
  };

  __attribute__((pure)) static unsigned int chained_proj(const OuterStmt &o);

  struct Level3Stmt {
    OuterStmt l3_outer_stmt;

    __attribute__((pure)) Level3Stmt *operator->() { return this; }

    __attribute__((pure)) const Level3Stmt *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) Level3Stmt clone() const {
      return Level3Stmt{(*(this)).l3_outer_stmt.clone()};
    }
  };

  __attribute__((pure)) static unsigned int triple_chain(const Level3Stmt &l3);
  __attribute__((pure)) static unsigned int proj_in_arith(const StateStmt &s);
  __attribute__((pure)) static unsigned int multi_proj_expr(const StateStmt &s);
  __attribute__((pure)) static List<unsigned int>
  proj_in_list(const StateStmt &s);
  __attribute__((pure)) static bool compare_projs(const StateStmt &s);
  __attribute__((pure)) static bool bool_with_proj(const StateStmt &s);

  template <typename T1> static T1 _bug_base_and_proj_consume(const T1 x) {
    return x;
  }

  __attribute__((pure)) static unsigned int sum_values(const unsigned int &n,
                                                       const StateStmt &s);

  struct RCF {
    unsigned int cf_val;

    __attribute__((pure)) RCF *operator->() { return this; }

    __attribute__((pure)) const RCF *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) RCF clone() const { return RCF{(*(this)).cf_val}; }
  };

  __attribute__((pure)) static unsigned int branch_use(const bool &b,
                                                       const RCF &r);
  __attribute__((pure)) static std::pair<RCF, unsigned int>
  branch_different(const bool &b, RCF r);
  __attribute__((pure)) static unsigned int
  match_with_wild(const std::optional<RCF> &o);
  __attribute__((pure)) static unsigned int
  sum_with_state(const unsigned int &n, const RCF &r);
  __attribute__((pure)) static unsigned int even_count(const unsigned int &n,
                                                       const RCF &r);
  __attribute__((pure)) static unsigned int odd_count(const unsigned int &n,
                                                      const RCF &r);

  struct StateLB {
    unsigned int lb_value;
    unsigned int lb_data;

    __attribute__((pure)) StateLB *operator->() { return this; }

    __attribute__((pure)) const StateLB *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) StateLB clone() const {
      return StateLB{(*(this)).lb_value, (*(this)).lb_data};
    }
  };

  struct Tree {
    // TYPES
    struct Leaf {
      unsigned int d_a0;
    };

    struct Node {
      std::unique_ptr<Tree> d_a0;
      unsigned int d_a1;
      std::unique_ptr<Tree> d_a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    Tree() {}

    explicit Tree(Leaf _v) : d_v_(std::move(_v)) {}

    explicit Tree(Node _v) : d_v_(std::move(_v)) {}

    Tree(const Tree &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    Tree(Tree &&_other) : d_v_(std::move(_other.d_v_)) {}

    Tree &operator=(const Tree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    Tree &operator=(Tree &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) Tree clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Leaf>(_sv.v())) {
        const auto &[d_a0] = std::get<Leaf>(_sv.v());
        return Tree(Leaf{d_a0});
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<Node>(_sv.v());
        return Tree(Node{
            d_a0 ? std::make_unique<ComprehensivePatterns::Tree>(d_a0->clone())
                 : nullptr,
            d_a1,
            d_a2 ? std::make_unique<ComprehensivePatterns::Tree>(d_a2->clone())
                 : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static Tree leaf(unsigned int a0) {
      return Tree(Leaf{std::move(a0)});
    }

    __attribute__((pure)) static Tree node(const Tree &a0, unsigned int a1,
                                           const Tree &a2) {
      return Tree(Node{std::make_unique<Tree>(a0), std::move(a1),
                       std::make_unique<Tree>(a2)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) Tree *operator->() { return this; }

    __attribute__((pure)) const Tree *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = Tree(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) Tree nested_reuse() const {
      Tree t2 = (*(this)).transform_tree();
      return t2.transform_tree();
    }

    __attribute__((pure)) Tree flip_tree() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename Tree::Leaf>(_sv.v())) {
        const auto &[d_a0] = std::get<typename Tree::Leaf>(_sv.v());
        return Tree::node(*(this), d_a0, *(this));
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename Tree::Node>(_sv.v());
        return Tree::leaf(d_a1);
      }
    }

    __attribute__((pure)) Tree transform_tree() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename Tree::Leaf>(_sv.v())) {
        const auto &[d_a0] = std::get<typename Tree::Leaf>(_sv.v());
        return Tree::leaf((d_a0 + 1u));
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename Tree::Node>(_sv.v());
        return Tree::node(*(d_a0), (d_a1 + 1u), *(d_a2));
      }
    }

    __attribute__((pure)) unsigned int
    consume_tree_with_state(const StateLB &s) const {
      const Tree *_self = this;

      struct _Enter {
        const Tree *_self;
      };

      struct _Call1 {
        Tree *_s0;
        decltype((std::declval<unsigned int &>() +
                  (std::declval<const StateLB &>()).lb_value)) _s1;
      };

      struct _Call2 {
        unsigned int _s0;
        decltype((std::declval<unsigned int &>() +
                  (std::declval<const StateLB &>()).lb_value)) _s1;
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
          auto _f = std::move(std::get<_Enter>(_frame));
          const Tree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename Tree::Leaf>(_sv.v())) {
            const auto &[d_a0] = std::get<typename Tree::Leaf>(_sv.v());
            _result = (d_a0 + s.lb_value);
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename Tree::Node>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get(), (d_a1 + s.lb_value)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Call2>(_frame));
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
          auto _f = std::move(std::get<_Enter>(_frame));
          const Tree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename Tree::Leaf>(_sv.v())) {
            const auto &[d_a0] = std::get<typename Tree::Leaf>(_sv.v());
            _result = d_a0;
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename Tree::Node>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get(), d_a1});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = ((_f._s1 + _result) + _f._s0);
        }
      }
      return _result;
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, Tree, T1, unsigned int, Tree, T1> F1>
    T1 Tree_rec(F0 &&f, F1 &&f0) const {
      const Tree *_self = this;

      struct _Enter {
        const Tree *_self;
      };

      struct _Call1 {
        Tree *_s0;
        Tree _s1;
        unsigned int _s2;
        Tree _s3;
      };

      struct _Call2 {
        T1 _s0;
        Tree _s1;
        unsigned int _s2;
        Tree _s3;
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
          auto _f = std::move(std::get<_Enter>(_frame));
          const Tree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename Tree::Leaf>(_sv.v())) {
            const auto &[d_a0] = std::get<typename Tree::Leaf>(_sv.v());
            _result = f(d_a0);
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename Tree::Node>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get(), *(d_a2), d_a1, *(d_a0)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2, _f._s3});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = f0(_f._s3, _result, _f._s2, _f._s1, _f._s0);
        }
      }
      return _result;
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, Tree, T1, unsigned int, Tree, T1> F1>
    T1 Tree_rect(F0 &&f, F1 &&f0) const {
      const Tree *_self = this;

      struct _Enter {
        const Tree *_self;
      };

      struct _Call1 {
        Tree *_s0;
        Tree _s1;
        unsigned int _s2;
        Tree _s3;
      };

      struct _Call2 {
        T1 _s0;
        Tree _s1;
        unsigned int _s2;
        Tree _s3;
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
          auto _f = std::move(std::get<_Enter>(_frame));
          const Tree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename Tree::Leaf>(_sv.v())) {
            const auto &[d_a0] = std::get<typename Tree::Leaf>(_sv.v());
            _result = f(d_a0);
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename Tree::Node>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get(), *(d_a2), d_a1, *(d_a0)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2, _f._s3});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = f0(_f._s3, _result, _f._s2, _f._s1, _f._s0);
        }
      }
      return _result;
    }
  };

  __attribute__((pure)) static unsigned int
  accum_with_state(const unsigned int &n, const StateLB &s);

  struct StateRO {
    unsigned int ro_value;
    unsigned int ro_data;

    __attribute__((pure)) StateRO *operator->() { return this; }

    __attribute__((pure)) const StateRO *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) StateRO clone() const {
      return StateRO{(*(this)).ro_value, (*(this)).ro_data};
    }
  };

  struct Container {
    // TYPES
    struct Empty {};

    struct Full {
      StateRO d_a0;
    };

    using variant_t = std::variant<Empty, Full>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    Container() {}

    explicit Container(Empty _v) : d_v_(_v) {}

    explicit Container(Full _v) : d_v_(std::move(_v)) {}

    Container(const Container &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    Container(Container &&_other) : d_v_(std::move(_other.d_v_)) {}

    Container &operator=(const Container &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    Container &operator=(Container &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) Container clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Empty>(_sv.v())) {
        return Container(Empty{});
      } else {
        const auto &[d_a0] = std::get<Full>(_sv.v());
        return Container(Full{d_a0.clone()});
      }
    }

    // CREATORS
    __attribute__((pure)) static Container empty() {
      return Container(Empty{});
    }

    __attribute__((pure)) static Container full(StateRO a0) {
      return Container(Full{std::move(a0)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) Container *operator->() { return this; }

    __attribute__((pure)) const Container *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = Container(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int extract_from_container() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename Container::Empty>(_sv.v())) {
        return 0u;
      } else {
        const auto &[d_a0] = std::get<typename Container::Full>(_sv.v());
        return (d_a0.ro_value + d_a0.ro_data);
      }
    }

    template <typename T1, MapsTo<T1, StateRO> F1>
    T1 Container_rec(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename Container::Empty>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0] = std::get<typename Container::Full>(_sv.v());
        return f0(d_a0);
      }
    }

    template <typename T1, MapsTo<T1, StateRO> F1>
    T1 Container_rect(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename Container::Empty>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0] = std::get<typename Container::Full>(_sv.v());
        return f0(d_a0);
      }
    }
  };

  struct StateOP {
    unsigned int op_value;
    unsigned int op_data;

    __attribute__((pure)) StateOP *operator->() { return this; }

    __attribute__((pure)) const StateOP *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) StateOP clone() const {
      return StateOP{(*(this)).op_value, (*(this)).op_data};
    }
  };

  __attribute__((pure)) static StateOP identity(StateOP s);
  __attribute__((pure)) static unsigned int extract_via_match(const StateOP &s);
  __attribute__((pure)) static StateOP consume_state(StateOP s);
  __attribute__((pure)) static unsigned int match_consumed(const StateOP &s);
  __attribute__((pure)) static std::pair<StateOP, unsigned int>
  force_owned(StateOP s);

  __attribute__((
      pure)) static std::pair<std::pair<StateOP, StateOP>, unsigned int>
  pair_then_match(StateOP s);
};

#endif // INCLUDED_COMPREHENSIVE_PATTERNS
