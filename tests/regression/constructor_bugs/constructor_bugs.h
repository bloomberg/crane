#ifndef INCLUDED_CONSTRUCTOR_BUGS
#define INCLUDED_CONSTRUCTOR_BUGS

#include <any>
#include <memory>
#include <optional>
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

struct ConstructorBugs {
  struct field_a {
    unsigned int a_value;
  };

  struct field_b {
    unsigned int b_value;
  };

  struct source_state {
    std::shared_ptr<field_a> source_a;
    std::shared_ptr<field_b> source_b;
    unsigned int source_flag;
  };

  struct packed_state {
    std::shared_ptr<source_state> packed_source;
    std::shared_ptr<field_a> packed_a;
    std::shared_ptr<field_b> packed_b;
  };

  static std::shared_ptr<source_state> step(std::shared_ptr<source_state> s);
  __attribute__((pure)) static std::pair<bool, std::shared_ptr<packed_state>>
  bad_branch(const std::shared_ptr<source_state> &s1);
  __attribute__((pure)) static std::pair<bool, std::shared_ptr<packed_state>>
  bad_direct(const std::shared_ptr<source_state> &s1);
  static std::shared_ptr<source_state>
  step2(const std::shared_ptr<source_state> &s);
  __attribute__((pure)) static std::pair<bool, std::shared_ptr<packed_state>>
  bad_complex_step(const std::shared_ptr<source_state> &s1);
  __attribute__((pure)) static std::pair<bool, std::shared_ptr<packed_state>>
  bad_nested(const std::shared_ptr<source_state> &s1);

  struct source_state_list {
    std::shared_ptr<field_a> source_a_list;
    std::shared_ptr<List<std::shared_ptr<field_b>>> source_b_list;
    unsigned int source_flag_list;
  };

  struct packed_state_list {
    std::shared_ptr<source_state_list> packed_source_list;
    std::shared_ptr<field_a> packed_a_list;
    std::shared_ptr<List<std::shared_ptr<field_b>>> packed_b_list;
  };

  static std::shared_ptr<source_state_list>
  step_list(std::shared_ptr<source_state_list> s);
  __attribute__((
      pure)) static std::pair<bool, std::shared_ptr<packed_state_list>>
  bad_branch_list(const std::shared_ptr<source_state_list> &s1);

  struct state {
    unsigned int value;
    std::shared_ptr<List<unsigned int>> data;
  };

  static std::shared_ptr<state> get_state(const unsigned int n);
  __attribute__((pure)) static std::pair<
      std::pair<std::shared_ptr<state>, std::shared_ptr<state>>, unsigned int>
  tuple_from_call(const unsigned int n);
  __attribute__((pure)) static std::pair<
      std::pair<std::shared_ptr<state>, unsigned int>,
      std::pair<unsigned int, std::shared_ptr<List<unsigned int>>>>
  nested_tuples(std::shared_ptr<state> s);
  __attribute__((
      pure)) static std::pair<std::pair<std::shared_ptr<state>, unsigned int>,
                              std::shared_ptr<List<unsigned int>>>
  conditional_tuple(const bool b, const unsigned int n);
  __attribute__((pure)) static unsigned int
  extract_value(const std::shared_ptr<state> &s);
  static std::shared_ptr<List<unsigned int>>
  extract_data(const std::shared_ptr<state> &s);
  __attribute__((
      pure)) static std::pair<std::pair<std::shared_ptr<state>, unsigned int>,
                              std::shared_ptr<List<unsigned int>>>
  multi_call_tuple(const unsigned int n);
  __attribute__((pure)) static std::pair<
      unsigned int, std::pair<std::shared_ptr<state>, unsigned int>>
  pair_test(const unsigned int n);
  __attribute__((pure)) static std::optional<
      std::pair<std::shared_ptr<state>, unsigned int>>
  match_test(const std::optional<std::shared_ptr<state>> o);
  static std::shared_ptr<List<std::shared_ptr<state>>>
  list_test(std::shared_ptr<state> s);
  __attribute__((pure)) static std::pair<
      std::pair<std::pair<std::shared_ptr<state>, unsigned int>,
                std::pair<unsigned int, std::shared_ptr<List<unsigned int>>>>,
      std::shared_ptr<List<unsigned int>>>
  triple_proj(std::shared_ptr<state> s);
  __attribute__((pure)) static std::pair<std::shared_ptr<state>, unsigned int>
  inner_pair(std::shared_ptr<state> s);
  __attribute__((pure)) static std::pair<std::shared_ptr<state>, unsigned int>
  outer_call(const unsigned int n);
  __attribute__((pure)) static std::pair<
      std::pair<
          std::pair<std::pair<std::shared_ptr<state>, std::shared_ptr<state>>,
                    unsigned int>,
          unsigned int>,
      std::shared_ptr<List<unsigned int>>>
  extreme_reuse(std::shared_ptr<state> s);

  struct Inner {
    unsigned int inner_val;
  };

  struct Outer {
    std::shared_ptr<Inner> outer_inner;
    unsigned int outer_data;
  };

  static std::shared_ptr<Outer> nested_record(std::shared_ptr<Inner> i);
  static std::shared_ptr<Outer>
  self_referential(const std::shared_ptr<Outer> &o);
  __attribute__((pure)) static std::pair<std::shared_ptr<Inner>, unsigned int>
  pair_with_proj(std::shared_ptr<Inner> i);
  __attribute__((
      pure)) static std::pair<std::pair<std::shared_ptr<Inner>, unsigned int>,
                              std::pair<unsigned int, unsigned int>>
  nested_pairs(std::shared_ptr<Inner> i);
  __attribute__((
      pure)) static std::pair<std::shared_ptr<Inner>, std::shared_ptr<Inner>>
  pair_duplicate(std::shared_ptr<Inner> i);
  static std::shared_ptr<Inner> mk_inner(const unsigned int n);
  __attribute__((pure)) static std::pair<std::shared_ptr<Inner>, unsigned int>
  pair_from_func(const unsigned int n);
  __attribute__((pure)) static std::optional<
      std::pair<std::shared_ptr<Inner>, unsigned int>>
  match_option_record(const std::optional<std::shared_ptr<Inner>> o);

  struct MySum {
    // TYPES
    struct Left {
      std::shared_ptr<Inner> d_a0;
    };

    struct Right {
      unsigned int d_a0;
    };

    using variant_t = std::variant<Left, Right>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit MySum(Left _v) : d_v_(std::move(_v)) {}

    explicit MySum(Right _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<MySum> left(const std::shared_ptr<Inner> &a0) {
      return std::make_shared<MySum>(Left{a0});
    }

    static std::shared_ptr<MySum> left(std::shared_ptr<Inner> &&a0) {
      return std::make_shared<MySum>(Left{std::move(a0)});
    }

    static std::shared_ptr<MySum> right(unsigned int a0) {
      return std::make_shared<MySum>(Right{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, std::shared_ptr<Inner>> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 MySum_rect(F0 &&f, F1 &&f0, const std::shared_ptr<MySum> &m) {
    return std::visit(Overloaded{[&](const typename MySum::Left &_args) -> T1 {
                                   return f(_args.d_a0);
                                 },
                                 [&](const typename MySum::Right &_args) -> T1 {
                                   return f0(_args.d_a0);
                                 }},
                      m->v());
  }

  template <typename T1, MapsTo<T1, std::shared_ptr<Inner>> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 MySum_rec(F0 &&f, F1 &&f0, const std::shared_ptr<MySum> &m) {
    return std::visit(Overloaded{[&](const typename MySum::Left &_args) -> T1 {
                                   return f(_args.d_a0);
                                 },
                                 [&](const typename MySum::Right &_args) -> T1 {
                                   return f0(_args.d_a0);
                                 }},
                      m->v());
  }

  __attribute__((pure)) static std::pair<std::shared_ptr<Inner>, unsigned int>
  match_sum(const std::shared_ptr<MySum> &s);
  __attribute__((pure)) static std::pair<std::shared_ptr<Inner>, unsigned int>
  with_cast(std::shared_ptr<Inner> i);
  __attribute__((
      pure)) static std::pair<std::pair<std::shared_ptr<Inner>, unsigned int>,
                              std::pair<std::shared_ptr<Inner>, unsigned int>>
  chain_lets(const std::shared_ptr<Inner> &i1);

  struct Container {
    std::shared_ptr<Outer> cont_outer;
  };

  __attribute__((pure)) static std::pair<
      std::pair<std::shared_ptr<Outer>, std::shared_ptr<Inner>>, unsigned int>
  deep_proj(const std::shared_ptr<Container> &c);
  __attribute__((pure)) static std::pair<
      std::shared_ptr<List<std::shared_ptr<Inner>>>, unsigned int>
  list_with_proj(std::shared_ptr<Inner> i);
  __attribute__((pure)) static std::pair<std::shared_ptr<Inner>, unsigned int>
  tail_pair(std::shared_ptr<Inner> i, const bool b);
  __attribute__((pure)) static std::pair<
      std::pair<std::shared_ptr<Inner>, std::shared_ptr<Inner>>,
      std::pair<unsigned int, unsigned int>>
  quad_tuple(std::shared_ptr<Inner> i);
  __attribute__((pure)) static std::pair<std::optional<std::shared_ptr<Inner>>,
                                         unsigned int>
  match_both_branches(const std::optional<std::shared_ptr<Inner>> o);
  static std::shared_ptr<Sig<std::shared_ptr<Inner>>>
  sigma_test(std::shared_ptr<Inner> i);
  __attribute__((pure)) static unsigned int
  extract(const std::shared_ptr<Inner> &i);
  __attribute__((pure)) static std::pair<std::shared_ptr<Inner>, unsigned int>
  nested_extract(std::shared_ptr<Inner> i);
  __attribute__((pure)) static std::pair<std::shared_ptr<Outer>, unsigned int>
  update_test(const std::shared_ptr<Outer> &o);

  struct State {
    unsigned int value_inline;
    unsigned int data_inline;
    unsigned int flag;
  };

  __attribute__((pure)) static std::pair<std::shared_ptr<State>, unsigned int>
  inline_pair(std::shared_ptr<State> s);
  __attribute__((pure)) static std::pair<
      std::pair<std::shared_ptr<State>, unsigned int>, unsigned int>
  inline_triple(std::shared_ptr<State> s);
  __attribute__((pure)) static std::pair<
      std::pair<std::shared_ptr<State>, unsigned int>, unsigned int>
  inline_nested(std::shared_ptr<State> s);
  static std::shared_ptr<State> get_state_inline(const unsigned int n);
  __attribute__((pure)) static std::pair<std::shared_ptr<State>, unsigned int>
  inline_from_call(const unsigned int n);
  __attribute__((pure)) static std::pair<
      std::pair<std::shared_ptr<State>, unsigned int>, unsigned int>
  same_call_multi_proj(const unsigned int n);
  __attribute__((pure)) static std::optional<
      std::pair<std::shared_ptr<State>, unsigned int>>
  inline_match(const std::optional<std::shared_ptr<State>> o);
  __attribute__((pure)) static std::pair<std::shared_ptr<State>, unsigned int>
  inline_if(const bool b, std::shared_ptr<State> s);

  struct OuterInline {
    std::shared_ptr<State> outer_state;
    unsigned int outer_num;
  };

  __attribute__((pure)) static std::pair<
      std::pair<std::shared_ptr<OuterInline>, std::shared_ptr<State>>,
      unsigned int>
  inline_deep(std::shared_ptr<OuterInline> o);
  __attribute__((pure)) static std::pair<std::shared_ptr<State>, unsigned int>
  inline_double_proj(const std::shared_ptr<OuterInline> &o);
  __attribute__((
      pure)) static std::pair<std::pair<std::shared_ptr<State>, unsigned int>,
                              std::pair<unsigned int, unsigned int>>
  inline_many(std::shared_ptr<State> s);
  __attribute__((pure)) static std::pair<
      std::pair<unsigned int, std::shared_ptr<State>>, unsigned int>
  inline_pattern(std::shared_ptr<State> s);
  static std::shared_ptr<List<std::pair<std::shared_ptr<State>, unsigned int>>>
  inline_recursive(const unsigned int n, std::shared_ptr<State> s);
  __attribute__((pure)) static std::pair<
      std::pair<std::pair<std::shared_ptr<State>, unsigned int>, unsigned int>,
      std::pair<unsigned int, std::shared_ptr<State>>>
  inline_complex(std::shared_ptr<State> s);
  __attribute__((pure)) static std::pair<
      std::pair<std::shared_ptr<State>, std::shared_ptr<State>>,
      std::pair<unsigned int, unsigned int>>
  inline_quad(std::shared_ptr<State> s);
  __attribute__((pure)) static std::pair<std::shared_ptr<State>, unsigned int>
  inline_both_branches(const bool b, std::shared_ptr<State> s);

  template <MapsTo<unsigned int, std::shared_ptr<State>> F0>
  __attribute__((pure)) static std::pair<
      std::pair<std::shared_ptr<State>, unsigned int>, unsigned int>
  apply_twice(F0 &&f, std::shared_ptr<State> s) {
    return std::make_pair(std::make_pair(s, f(s)), f(s));
  }

  __attribute__((pure)) static std::pair<
      std::pair<std::shared_ptr<State>, unsigned int>, unsigned int>
  test_apply(const std::shared_ptr<State> &s);
  __attribute__((pure)) static unsigned int
  get_value_inline(const std::shared_ptr<State> &s);
  __attribute__((pure)) static unsigned int
  get_data_inline(const std::shared_ptr<State> &s);
  __attribute__((pure)) static std::pair<
      std::pair<std::shared_ptr<State>, unsigned int>, unsigned int>
  inline_nested_calls(std::shared_ptr<State> s);
  __attribute__((pure)) static std::pair<std::optional<std::shared_ptr<State>>,
                                         std::optional<unsigned int>>
  inline_option(std::shared_ptr<State> s);
  __attribute__((
      pure)) static std::pair<std::shared_ptr<List<std::shared_ptr<State>>>,
                              std::shared_ptr<List<unsigned int>>>
  inline_list(std::shared_ptr<State> s);
};

#endif // INCLUDED_CONSTRUCTOR_BUGS
