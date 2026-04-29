#ifndef INCLUDED_CUSTOM_INLINE_BUG
#define INCLUDED_CUSTOM_INLINE_BUG

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

  __attribute__((pure)) static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List>> _stack;
    auto _drain = [&](List &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
        if (_alt.d_a1)
          _stack.push_back(std::move(_alt.d_a1));
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node)
        _drain(*_node);
    }
  }

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct CustomInlineBug {
  struct State {
    unsigned int value;
    unsigned int data;

    // ACCESSORS
    __attribute__((pure)) State clone() const {
      return State{(*(this)).value, (*(this)).data};
    }
  };

  __attribute__((pure)) static std::optional<unsigned int>
  bug_some_proj(const State &s);
  __attribute__((pure)) static std::pair<State, unsigned int>
  bug_pair_proj(State s);
  __attribute__((pure)) static std::optional<std::optional<unsigned int>>
  bug_nested_option(const State &s);
  __attribute__((pure)) static std::optional<std::pair<State, unsigned int>>
  bug_option_pair(State s);
  __attribute__((pure)) static State get_state(unsigned int n);
  __attribute__((pure)) static std::optional<unsigned int>
  bug_some_of_call(const unsigned int &n);
  __attribute__((pure)) static std::pair<State, unsigned int>
  pair_simple(State s);
  __attribute__((pure)) static std::pair<State, unsigned int>
  pair_let(unsigned int n);
  __attribute__((pure)) static std::pair<std::pair<State, unsigned int>,
                                         std::pair<unsigned int, unsigned int>>
  pair_nested(State s);
  __attribute__((pure)) static std::pair<State, unsigned int>
  pair_if(const bool &b, State s);
  __attribute__((pure)) static std::optional<std::pair<State, unsigned int>>
  pair_match(const std::optional<State> &o);
  __attribute__((
      pure)) static std::pair<std::pair<State, unsigned int>, unsigned int>
  pair_multi_proj(State s);
  __attribute__((pure)) static std::pair<State, unsigned int>
  pair_chain(const State &s1);
  __attribute__((pure)) static std::pair<std::pair<State, State>,
                                         std::pair<unsigned int, unsigned int>>
  pair_extreme(State s);
  __attribute__((pure)) static std::pair<State, unsigned int>
  make_pair(State s);
  __attribute__((pure)) static std::pair<State, unsigned int>
  outer_pair(unsigned int n);
  __attribute__((pure)) static List<std::pair<State, unsigned int>>
  count_pairs(const unsigned int &n, State s);
};

#endif // INCLUDED_CUSTOM_INLINE_BUG
