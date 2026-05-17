#ifndef INCLUDED_CONSTRUCTOR_BUGS
#define INCLUDED_CONSTRUCTOR_BUGS

#include <any>
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
    A a0;
    std::unique_ptr<List<A>> a1;
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

  List(List<A> &&_other) : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) {
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
        _dst->v_ =
            Cons{_alt.a0, _alt.a1 ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
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
      const auto &[a0, a1] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a0), a1 ? std::make_unique<List<A>>(*a1) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a0, List<A> a1) {
    return List(Cons{std::move(a0), std::make_unique<List<A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
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
};

template <typename A> struct Sig {
  // TYPES
  struct Exist {
    A x;
  };

  using variant_t = std::variant<Exist>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Sig() {}

  explicit Sig(Exist _v) : v_(std::move(_v)) {}

  Sig(const Sig<A> &_other) : v_(std::move(_other.clone().v_)) {}

  Sig(Sig<A> &&_other) : v_(std::move(_other.v_)) {}

  Sig<A> &operator=(const Sig<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  Sig<A> &operator=(Sig<A> &&_other) {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  Sig<A> clone() const {
    const auto &[x] = std::get<Exist>(this->v());
    return Sig<A>(Exist{x});
  }

  // CREATORS
  template <typename _U> explicit Sig(const Sig<_U> &_other) {
    const auto &[x] = std::get<typename Sig<_U>::Exist>(_other.v());
    this->v_ = Exist{A(x)};
  }

  static Sig<A> exist(A x) { return Sig(Exist{std::move(x)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct ConstructorBugs {
  struct field_a {
    unsigned int a_value;

    // ACCESSORS
    field_a clone() const { return field_a{(*this).a_value}; }
  };

  struct field_b {
    unsigned int b_value;

    // ACCESSORS
    field_b clone() const { return field_b{(*this).b_value}; }
  };

  struct source_state {
    field_a source_a;
    field_b source_b;
    unsigned int source_flag;

    // ACCESSORS
    source_state clone() const {
      return source_state{(*this).source_a.clone(), (*this).source_b.clone(),
                          (*this).source_flag};
    }
  };

  struct packed_state {
    source_state packed_source;
    field_a packed_a;
    field_b packed_b;

    // ACCESSORS
    packed_state clone() const {
      return packed_state{(*this).packed_source.clone(),
                          (*this).packed_a.clone(), (*this).packed_b.clone()};
    }
  };

  static source_state step(source_state s);
  static std::pair<bool, packed_state> bad_branch(const source_state &s1);
  static std::pair<bool, packed_state> bad_direct(const source_state &s1);
  static source_state step2(const source_state &s);
  static std::pair<bool, packed_state> bad_complex_step(const source_state &s1);
  static std::pair<bool, packed_state> bad_nested(const source_state &s1);

  struct source_state_list {
    field_a source_a_list;
    List<field_b> source_b_list;
    unsigned int source_flag_list;

    // ACCESSORS
    source_state_list clone() const {
      return source_state_list{(*this).source_a_list.clone(),
                               (*this).source_b_list.clone(),
                               (*this).source_flag_list};
    }
  };

  struct packed_state_list {
    source_state_list packed_source_list;
    field_a packed_a_list;
    List<field_b> packed_b_list;

    // ACCESSORS
    packed_state_list clone() const {
      return packed_state_list{(*this).packed_source_list.clone(),
                               (*this).packed_a_list.clone(),
                               (*this).packed_b_list.clone()};
    }
  };

  static source_state_list step_list(source_state_list s);
  static std::pair<bool, packed_state_list>
  bad_branch_list(const source_state_list &s1);

  struct state {
    unsigned int value;
    List<unsigned int> data;

    // ACCESSORS
    state clone() const { return state{(*this).value, (*this).data.clone()}; }
  };

  static state get_state(unsigned int n);
  static std::pair<std::pair<state, state>, unsigned int>
  tuple_from_call(unsigned int n);
  static std::pair<std::pair<state, unsigned int>,
                   std::pair<unsigned int, List<unsigned int>>>
  nested_tuples(state s);
  static std::pair<std::pair<state, unsigned int>, List<unsigned int>>
  conditional_tuple(bool b, unsigned int n);
  static unsigned int extract_value(const state &s);
  static List<unsigned int> extract_data(const state &s);
  static std::pair<std::pair<state, unsigned int>, List<unsigned int>>
  multi_call_tuple(unsigned int n);
  static std::pair<unsigned int, std::pair<state, unsigned int>>
  pair_test(unsigned int n);
  static std::optional<std::pair<state, unsigned int>>
  match_test(const std::optional<state> &o);
  static List<state> list_test(state s);
  static std::pair<std::pair<std::pair<state, unsigned int>,
                             std::pair<unsigned int, List<unsigned int>>>,
                   List<unsigned int>>
  triple_proj(state s);
  static std::pair<state, unsigned int> inner_pair(state s);
  static std::pair<state, unsigned int> outer_call(unsigned int n);
  static std::pair<
      std::pair<std::pair<std::pair<state, state>, unsigned int>, unsigned int>,
      List<unsigned int>>
  extreme_reuse(state s);

  struct Inner {
    unsigned int inner_val;

    // ACCESSORS
    Inner clone() const { return Inner{(*this).inner_val}; }
  };

  struct Outer {
    Inner outer_inner;
    unsigned int outer_data;

    // ACCESSORS
    Outer clone() const {
      return Outer{(*this).outer_inner.clone(), (*this).outer_data};
    }
  };

  static Outer nested_record(Inner i);
  static Outer self_referential(const Outer &o);
  static std::pair<Inner, unsigned int> pair_with_proj(Inner i);
  static std::pair<std::pair<Inner, unsigned int>,
                   std::pair<unsigned int, unsigned int>>
  nested_pairs(Inner i);
  static std::pair<Inner, Inner> pair_duplicate(Inner i);
  static Inner mk_inner(unsigned int n);
  static std::pair<Inner, unsigned int> pair_from_func(unsigned int n);
  static std::optional<std::pair<Inner, unsigned int>>
  match_option_record(const std::optional<Inner> &o);

  struct MySum {
    // TYPES
    struct Left {
      Inner a0;
    };

    struct Right {
      unsigned int a0;
    };

    using variant_t = std::variant<Left, Right>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    MySum() {}

    explicit MySum(Left _v) : v_(std::move(_v)) {}

    explicit MySum(Right _v) : v_(std::move(_v)) {}

    MySum(const MySum &_other) : v_(std::move(_other.clone().v_)) {}

    MySum(MySum &&_other) : v_(std::move(_other.v_)) {}

    MySum &operator=(const MySum &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    MySum &operator=(MySum &&_other) {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    MySum clone() const {
      if (std::holds_alternative<Left>(this->v())) {
        const auto &[a0] = std::get<Left>(this->v());
        return MySum(Left{a0.clone()});
      } else {
        const auto &[a0] = std::get<Right>(this->v());
        return MySum(Right{a0});
      }
    }

    // CREATORS
    static MySum left(Inner a0) { return MySum(Left{std::move(a0)}); }

    static MySum right(unsigned int a0) { return MySum(Right{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, Inner &> &&
             std::is_invocable_r_v<T1, F1 &, unsigned int &>
  static T1 MySum_rect(F0 &&f, F1 &&f0, const MySum &m) {
    if (std::holds_alternative<typename MySum::Left>(m.v())) {
      const auto &[a0] = std::get<typename MySum::Left>(m.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename MySum::Right>(m.v());
      return f0(a0);
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, Inner &> &&
             std::is_invocable_r_v<T1, F1 &, unsigned int &>
  static T1 MySum_rec(F0 &&f, F1 &&f0, const MySum &m) {
    if (std::holds_alternative<typename MySum::Left>(m.v())) {
      const auto &[a0] = std::get<typename MySum::Left>(m.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename MySum::Right>(m.v());
      return f0(a0);
    }
  }

  static std::pair<Inner, unsigned int> match_sum(const MySum &s);
  static std::pair<Inner, unsigned int> with_cast(Inner i);
  static std::pair<std::pair<Inner, unsigned int>,
                   std::pair<Inner, unsigned int>>
  chain_lets(const Inner &i1);

  struct Container {
    Outer cont_outer;

    // ACCESSORS
    Container clone() const { return Container{(*this).cont_outer.clone()}; }
  };

  static std::pair<std::pair<Outer, Inner>, unsigned int>
  deep_proj(const Container &c);
  static std::pair<List<Inner>, unsigned int> list_with_proj(Inner i);
  static std::pair<Inner, unsigned int> tail_pair(Inner i, bool b);
  static std::pair<std::pair<Inner, Inner>,
                   std::pair<unsigned int, unsigned int>>
  quad_tuple(Inner i);
  static std::pair<std::optional<Inner>, unsigned int>
  match_both_branches(const std::optional<Inner> &o);
  static Sig<Inner> sigma_test(Inner i);
  static unsigned int extract(const Inner &i);
  static std::pair<Inner, unsigned int> nested_extract(Inner i);
  static std::pair<Outer, unsigned int> update_test(const Outer &o);

  struct State {
    unsigned int value_inline;
    unsigned int data_inline;
    unsigned int flag;

    // ACCESSORS
    State clone() const {
      return State{(*this).value_inline, (*this).data_inline, (*this).flag};
    }
  };

  static std::pair<State, unsigned int> inline_pair(State s);
  static std::pair<std::pair<State, unsigned int>, unsigned int>
  inline_triple(State s);
  static std::pair<std::pair<State, unsigned int>, unsigned int>
  inline_nested(State s);
  static State get_state_inline(unsigned int n);
  static std::pair<State, unsigned int> inline_from_call(unsigned int n);
  static std::pair<std::pair<State, unsigned int>, unsigned int>
  same_call_multi_proj(unsigned int n);
  static std::optional<std::pair<State, unsigned int>>
  inline_match(const std::optional<State> &o);
  static std::pair<State, unsigned int> inline_if(bool b, State s);

  struct OuterInline {
    State outer_state;
    unsigned int outer_num;

    // ACCESSORS
    OuterInline clone() const {
      return OuterInline{(*this).outer_state.clone(), (*this).outer_num};
    }
  };

  static std::pair<std::pair<OuterInline, State>, unsigned int>
  inline_deep(OuterInline o);
  static std::pair<State, unsigned int>
  inline_double_proj(const OuterInline &o);
  static std::pair<std::pair<State, unsigned int>,
                   std::pair<unsigned int, unsigned int>>
  inline_many(State s);
  static std::pair<std::pair<unsigned int, State>, unsigned int>
  inline_pattern(State s);
  static List<std::pair<State, unsigned int>> inline_recursive(unsigned int n,
                                                               State s);
  static std::pair<std::pair<std::pair<State, unsigned int>, unsigned int>,
                   std::pair<unsigned int, State>>
  inline_complex(State s);
  static std::pair<std::pair<State, State>,
                   std::pair<unsigned int, unsigned int>>
  inline_quad(State s);
  static std::pair<State, unsigned int> inline_both_branches(bool b, State s);

  template <typename F0>
    requires std::is_invocable_r_v<unsigned int, F0 &, State &>
  static std::pair<std::pair<State, unsigned int>, unsigned int>
  apply_twice(F0 &&f, State s) {
    return std::make_pair(std::make_pair(s, f(s)), f(s));
  }

  static std::pair<std::pair<State, unsigned int>, unsigned int>
  test_apply(const State &s);
  static unsigned int get_value_inline(const State &s);
  static unsigned int get_data_inline(const State &s);
  static std::pair<std::pair<State, unsigned int>, unsigned int>
  inline_nested_calls(State s);
  static std::pair<std::optional<State>, std::optional<unsigned int>>
  inline_option(State s);
  static std::pair<List<State>, List<unsigned int>> inline_list(State s);
};

#endif // INCLUDED_CONSTRUCTOR_BUGS
