#ifndef INCLUDED_CONSTRUCTOR_BUGS
#define INCLUDED_CONSTRUCTOR_BUGS

#include <any>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

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
  using crane_element_type = t_A;

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

  __attribute__((pure)) List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) List<t_A> &operator=(List<t_A> &&_other) {
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
      t_A __c0;
      if constexpr (
          requires { d_a0 ? 0 : 0; } && requires { *d_a0; } &&
          requires { d_a0->clone(); } && requires { d_a0.get(); }) {
        using _E = std::remove_cvref_t<decltype(*d_a0)>;
        __c0 = d_a0 ? std::make_unique<_E>(d_a0->clone()) : nullptr;
      } else if constexpr (requires { d_a0.clone(); }) {
        __c0 = d_a0.clone();
      } else {
        __c0 = d_a0;
      }
      return List<t_A>(
          Cons{std::move(__c0),
               d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ = Cons{
          [&]<typename _DstT = t_A>(auto &&__v) -> _DstT {
            if constexpr (
                requires { *__v; } &&
                !requires { std::declval<_DstT>().get(); })
              return _DstT(*__v);
            else if constexpr (
                !requires { *__v; } &&
                requires { std::declval<_DstT>().get(); }) {
              using _E =
                  std::remove_pointer_t<decltype(std::declval<_DstT>().get())>;
              return std::make_unique<_E>(std::move(__v));
            } else
              return _DstT(__v);
          }(d_a0),
          d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

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
  using crane_element_type = t_A;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Sig() {}

  explicit Sig(Exist _v) : d_v_(std::move(_v)) {}

  Sig(const Sig<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Sig(Sig<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  __attribute__((pure)) Sig<t_A> &operator=(const Sig<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) Sig<t_A> &operator=(Sig<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) Sig<t_A> clone() const {
    auto &&_sv = *(this);
    const auto &[d_x] = std::get<Exist>(_sv.v());
    t_A __c0;
    if constexpr (
        requires { d_x ? 0 : 0; } && requires { *d_x; } &&
        requires { d_x->clone(); } && requires { d_x.get(); }) {
      using _E = std::remove_cvref_t<decltype(*d_x)>;
      __c0 = d_x ? std::make_unique<_E>(d_x->clone()) : nullptr;
    } else if constexpr (requires { d_x.clone(); }) {
      __c0 = d_x.clone();
    } else {
      __c0 = d_x;
    }
    return Sig<t_A>(Exist{std::move(__c0)});
  }

  // CREATORS
  template <typename _U> explicit Sig(const Sig<_U> &_other) {
    const auto &[d_x] = std::get<typename Sig<_U>::Exist>(_other.v());
    d_v_ = Exist{[&]<typename _DstT = t_A>(auto &&__v) -> _DstT {
      if constexpr (
          requires { *__v; } && !requires { std::declval<_DstT>().get(); })
        return _DstT(*__v);
      else if constexpr (
          !requires { *__v; } && requires { std::declval<_DstT>().get(); }) {
        using _E = std::remove_pointer_t<decltype(std::declval<_DstT>().get())>;
        return std::make_unique<_E>(std::move(__v));
      } else
        return _DstT(__v);
    }(d_x)};
  }

  __attribute__((pure)) static Sig<t_A> exist(t_A x) {
    return Sig(Exist{std::move(x)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

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

struct ConstructorBugs {
  struct field_a {
    unsigned int a_value;

    __attribute__((pure)) field_a *operator->() { return this; }

    __attribute__((pure)) const field_a *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) field_a clone() const {
      return field_a{[](auto &&__v) -> unsigned int {
        if constexpr (
            requires { __v ? 0 : 0; } && requires { *__v; } &&
            requires { __v->clone(); } && requires { __v.get(); }) {
          using _E = std::remove_cvref_t<decltype(*__v)>;
          return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
        } else if constexpr (requires { __v.clone(); }) {
          return __v.clone();
        } else {
          return __v;
        }
      }((*this).a_value)};
    }
  };

  struct field_b {
    unsigned int b_value;

    __attribute__((pure)) field_b *operator->() { return this; }

    __attribute__((pure)) const field_b *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) field_b clone() const {
      return field_b{[](auto &&__v) -> unsigned int {
        if constexpr (
            requires { __v ? 0 : 0; } && requires { *__v; } &&
            requires { __v->clone(); } && requires { __v.get(); }) {
          using _E = std::remove_cvref_t<decltype(*__v)>;
          return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
        } else if constexpr (requires { __v.clone(); }) {
          return __v.clone();
        } else {
          return __v;
        }
      }((*this).b_value)};
    }
  };

  struct source_state {
    field_a source_a;
    field_b source_b;
    unsigned int source_flag;

    __attribute__((pure)) source_state *operator->() { return this; }

    __attribute__((pure)) const source_state *operator->() const {
      return this;
    }

    // ACCESSORS
    __attribute__((pure)) source_state clone() const {
      return source_state{
          (*(this)).source_a.clone(), (*(this)).source_b.clone(),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).source_flag)};
    }
  };

  struct packed_state {
    source_state packed_source;
    field_a packed_a;
    field_b packed_b;

    __attribute__((pure)) packed_state *operator->() { return this; }

    __attribute__((pure)) const packed_state *operator->() const {
      return this;
    }

    // ACCESSORS
    __attribute__((pure)) packed_state clone() const {
      return packed_state{(*(this)).packed_source.clone(),
                          (*(this)).packed_a.clone(),
                          (*(this)).packed_b.clone()};
    }
  };

  __attribute__((pure)) static source_state step(source_state s);
  __attribute__((pure)) static std::pair<bool, packed_state>
  bad_branch(const source_state &s1);
  __attribute__((pure)) static std::pair<bool, packed_state>
  bad_direct(const source_state &s1);
  __attribute__((pure)) static source_state step2(const source_state &s);
  __attribute__((pure)) static std::pair<bool, packed_state>
  bad_complex_step(const source_state &s1);
  __attribute__((pure)) static std::pair<bool, packed_state>
  bad_nested(const source_state &s1);

  struct source_state_list {
    field_a source_a_list;
    List<field_b> source_b_list;
    unsigned int source_flag_list;

    __attribute__((pure)) source_state_list *operator->() { return this; }

    __attribute__((pure)) const source_state_list *operator->() const {
      return this;
    }

    // ACCESSORS
    __attribute__((pure)) source_state_list clone() const {
      return source_state_list{
          (*(this)).source_a_list.clone(), (*(this)).source_b_list.clone(),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).source_flag_list)};
    }
  };

  struct packed_state_list {
    source_state_list packed_source_list;
    field_a packed_a_list;
    List<field_b> packed_b_list;

    __attribute__((pure)) packed_state_list *operator->() { return this; }

    __attribute__((pure)) const packed_state_list *operator->() const {
      return this;
    }

    // ACCESSORS
    __attribute__((pure)) packed_state_list clone() const {
      return packed_state_list{(*(this)).packed_source_list.clone(),
                               (*(this)).packed_a_list.clone(),
                               (*(this)).packed_b_list.clone()};
    }
  };

  __attribute__((pure)) static source_state_list step_list(source_state_list s);
  __attribute__((pure)) static std::pair<bool, packed_state_list>
  bad_branch_list(const source_state_list &s1);

  struct state {
    unsigned int value;
    List<unsigned int> data;

    __attribute__((pure)) state *operator->() { return this; }

    __attribute__((pure)) const state *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) state clone() const {
      return state{
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).value),
          (*(this)).data.clone()};
    }
  };

  __attribute__((pure)) static state get_state(unsigned int n);
  __attribute__((pure)) static std::pair<std::pair<state, state>, unsigned int>
  tuple_from_call(const unsigned int &n);
  __attribute__((
      pure)) static std::pair<std::pair<state, unsigned int>,
                              std::pair<unsigned int, List<unsigned int>>>
  nested_tuples(state s);
  __attribute__((pure)) static std::pair<std::pair<state, unsigned int>,
                                         List<unsigned int>>
  conditional_tuple(const bool &b, const unsigned int &n);
  __attribute__((pure)) static unsigned int extract_value(const state &s);
  __attribute__((pure)) static List<unsigned int> extract_data(const state &s);
  __attribute__((pure)) static std::pair<std::pair<state, unsigned int>,
                                         List<unsigned int>>
  multi_call_tuple(const unsigned int &n);
  __attribute__((
      pure)) static std::pair<unsigned int, std::pair<state, unsigned int>>
  pair_test(unsigned int n);
  __attribute__((pure)) static std::optional<std::pair<state, unsigned int>>
  match_test(const std::optional<state> &o);
  __attribute__((pure)) static List<state> list_test(state s);
  __attribute__((pure)) static std::pair<
      std::pair<std::pair<state, unsigned int>,
                std::pair<unsigned int, List<unsigned int>>>,
      List<unsigned int>>
  triple_proj(state s);
  __attribute__((pure)) static std::pair<state, unsigned int>
  inner_pair(state s);
  __attribute__((pure)) static std::pair<state, unsigned int>
  outer_call(const unsigned int &n);
  __attribute__((pure)) static std::pair<
      std::pair<std::pair<std::pair<state, state>, unsigned int>, unsigned int>,
      List<unsigned int>>
  extreme_reuse(state s);

  struct Inner {
    unsigned int inner_val;

    __attribute__((pure)) Inner *operator->() { return this; }

    __attribute__((pure)) const Inner *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) Inner clone() const {
      return Inner{[](auto &&__v) -> unsigned int {
        if constexpr (
            requires { __v ? 0 : 0; } && requires { *__v; } &&
            requires { __v->clone(); } && requires { __v.get(); }) {
          using _E = std::remove_cvref_t<decltype(*__v)>;
          return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
        } else if constexpr (requires { __v.clone(); }) {
          return __v.clone();
        } else {
          return __v;
        }
      }((*this).inner_val)};
    }
  };

  struct Outer {
    Inner outer_inner;
    unsigned int outer_data;

    __attribute__((pure)) Outer *operator->() { return this; }

    __attribute__((pure)) const Outer *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) Outer clone() const {
      return Outer{
          (*(this)).outer_inner.clone(), [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).outer_data)};
    }
  };

  __attribute__((pure)) static Outer nested_record(Inner i);
  __attribute__((pure)) static Outer self_referential(const Outer &o);
  __attribute__((pure)) static std::pair<Inner, unsigned int>
  pair_with_proj(Inner i);
  __attribute__((pure)) static std::pair<std::pair<Inner, unsigned int>,
                                         std::pair<unsigned int, unsigned int>>
  nested_pairs(Inner i);
  __attribute__((pure)) static std::pair<Inner, Inner> pair_duplicate(Inner i);
  __attribute__((pure)) static Inner mk_inner(unsigned int n);
  __attribute__((pure)) static std::pair<Inner, unsigned int>
  pair_from_func(const unsigned int &n);
  __attribute__((pure)) static std::optional<std::pair<Inner, unsigned int>>
  match_option_record(const std::optional<Inner> &o);

  struct MySum {
    // TYPES
    struct Left {
      Inner d_a0;
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
    MySum() {}

    explicit MySum(Left _v) : d_v_(std::move(_v)) {}

    explicit MySum(Right _v) : d_v_(std::move(_v)) {}

    MySum(const MySum &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    MySum(MySum &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) MySum &operator=(const MySum &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) MySum &operator=(MySum &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) MySum clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Left>(_sv.v())) {
        const auto &[d_a0] = std::get<Left>(_sv.v());
        return MySum(Left{d_a0.clone()});
      } else {
        const auto &[d_a0] = std::get<Right>(_sv.v());
        return MySum(Right{[](auto &&__v) -> unsigned int {
          if constexpr (
              requires { __v ? 0 : 0; } && requires { *__v; } &&
              requires { __v->clone(); } && requires { __v.get(); }) {
            using _E = std::remove_cvref_t<decltype(*__v)>;
            return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
          } else if constexpr (requires { __v.clone(); }) {
            return __v.clone();
          } else {
            return __v;
          }
        }(d_a0)});
      }
    }

    // CREATORS
    constexpr static MySum left(Inner a0) { return MySum(Left{std::move(a0)}); }

    __attribute__((pure)) static MySum right(unsigned int a0) {
      return MySum(Right{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) MySum *operator->() { return this; }

    __attribute__((pure)) const MySum *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = MySum(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, Inner> F0, MapsTo<T1, unsigned int> F1>
  static T1 MySum_rect(F0 &&f, F1 &&f0, const MySum &m) {
    if (std::holds_alternative<typename MySum::Left>(m.v())) {
      const auto &[d_a0] = std::get<typename MySum::Left>(m.v());
      return f(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename MySum::Right>(m.v());
      return f0(d_a0);
    }
  }

  template <typename T1, MapsTo<T1, Inner> F0, MapsTo<T1, unsigned int> F1>
  static T1 MySum_rec(F0 &&f, F1 &&f0, const MySum &m) {
    if (std::holds_alternative<typename MySum::Left>(m.v())) {
      const auto &[d_a0] = std::get<typename MySum::Left>(m.v());
      return f(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename MySum::Right>(m.v());
      return f0(d_a0);
    }
  }

  __attribute__((pure)) static std::pair<Inner, unsigned int>
  match_sum(const MySum &s);
  __attribute__((pure)) static std::pair<Inner, unsigned int>
  with_cast(Inner i);
  __attribute__((pure)) static std::pair<std::pair<Inner, unsigned int>,
                                         std::pair<Inner, unsigned int>>
  chain_lets(const Inner &i1);

  struct Container {
    Outer cont_outer;

    __attribute__((pure)) Container *operator->() { return this; }

    __attribute__((pure)) const Container *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) Container clone() const {
      return Container{(*(this)).cont_outer.clone()};
    }
  };

  __attribute__((pure)) static std::pair<std::pair<Outer, Inner>, unsigned int>
  deep_proj(const Container &c);
  __attribute__((pure)) static std::pair<List<Inner>, unsigned int>
  list_with_proj(Inner i);
  __attribute__((pure)) static std::pair<Inner, unsigned int>
  tail_pair(Inner i, const bool &b);
  __attribute__((pure)) static std::pair<std::pair<Inner, Inner>,
                                         std::pair<unsigned int, unsigned int>>
  quad_tuple(Inner i);
  __attribute__((pure)) static std::pair<std::optional<Inner>, unsigned int>
  match_both_branches(const std::optional<Inner> &o);
  __attribute__((pure)) static Sig<Inner> sigma_test(Inner i);
  __attribute__((pure)) static unsigned int extract(const Inner &i);
  __attribute__((pure)) static std::pair<Inner, unsigned int>
  nested_extract(Inner i);
  __attribute__((pure)) static std::pair<Outer, unsigned int>
  update_test(const Outer &o);

  struct State {
    unsigned int value_inline;
    unsigned int data_inline;
    unsigned int flag;

    __attribute__((pure)) State *operator->() { return this; }

    __attribute__((pure)) const State *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) State clone() const {
      return State{
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).value_inline),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).data_inline),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).flag)};
    }
  };

  __attribute__((pure)) static std::pair<State, unsigned int>
  inline_pair(State s);
  __attribute__((
      pure)) static std::pair<std::pair<State, unsigned int>, unsigned int>
  inline_triple(State s);
  __attribute__((
      pure)) static std::pair<std::pair<State, unsigned int>, unsigned int>
  inline_nested(State s);
  __attribute__((pure)) static State get_state_inline(unsigned int n);
  __attribute__((pure)) static std::pair<State, unsigned int>
  inline_from_call(const unsigned int &n);
  __attribute__((
      pure)) static std::pair<std::pair<State, unsigned int>, unsigned int>
  same_call_multi_proj(const unsigned int &n);
  __attribute__((pure)) static std::optional<std::pair<State, unsigned int>>
  inline_match(const std::optional<State> &o);
  __attribute__((pure)) static std::pair<State, unsigned int>
  inline_if(const bool &b, State s);

  struct OuterInline {
    State outer_state;
    unsigned int outer_num;

    __attribute__((pure)) OuterInline *operator->() { return this; }

    __attribute__((pure)) const OuterInline *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) OuterInline clone() const {
      return OuterInline{
          (*(this)).outer_state.clone(), [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).outer_num)};
    }
  };

  __attribute__((
      pure)) static std::pair<std::pair<OuterInline, State>, unsigned int>
  inline_deep(OuterInline o);
  __attribute__((pure)) static std::pair<State, unsigned int>
  inline_double_proj(const OuterInline &o);
  __attribute__((pure)) static std::pair<std::pair<State, unsigned int>,
                                         std::pair<unsigned int, unsigned int>>
  inline_many(State s);
  __attribute__((
      pure)) static std::pair<std::pair<unsigned int, State>, unsigned int>
  inline_pattern(State s);
  __attribute__((pure)) static List<std::pair<State, unsigned int>>
  inline_recursive(const unsigned int &n, State s);
  __attribute__((pure)) static std::pair<
      std::pair<std::pair<State, unsigned int>, unsigned int>,
      std::pair<unsigned int, State>>
  inline_complex(State s);
  __attribute__((pure)) static std::pair<std::pair<State, State>,
                                         std::pair<unsigned int, unsigned int>>
  inline_quad(State s);
  __attribute__((pure)) static std::pair<State, unsigned int>
  inline_both_branches(const bool &b, State s);

  template <MapsTo<unsigned int, State> F0>
  __attribute__((
      pure)) static std::pair<std::pair<State, unsigned int>, unsigned int>
  apply_twice(F0 &&f, State s) {
    return std::make_pair(std::make_pair(s, f(s)), f(s));
  }

  __attribute__((
      pure)) static std::pair<std::pair<State, unsigned int>, unsigned int>
  test_apply(const State &s);
  __attribute__((pure)) static unsigned int get_value_inline(const State &s);
  __attribute__((pure)) static unsigned int get_data_inline(const State &s);
  __attribute__((
      pure)) static std::pair<std::pair<State, unsigned int>, unsigned int>
  inline_nested_calls(State s);
  __attribute__((
      pure)) static std::pair<std::optional<State>, std::optional<unsigned int>>
  inline_option(State s);
  __attribute__((pure)) static std::pair<List<State>, List<unsigned int>>
  inline_list(State s);
};

#endif // INCLUDED_CONSTRUCTOR_BUGS
