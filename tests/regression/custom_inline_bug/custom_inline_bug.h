#ifndef INCLUDED_CUSTOM_INLINE_BUG
#define INCLUDED_CUSTOM_INLINE_BUG

#include <memory>
#include <optional>
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

struct CustomInlineBug {
  struct State {
    unsigned int value;
    unsigned int data;

    // ACCESSORS
    State clone() const { return State{(*this).value, (*this).data}; }
  };

  static std::optional<unsigned int> bug_some_proj(const State &s);
  static std::pair<State, unsigned int> bug_pair_proj(State s);
  static std::optional<std::optional<unsigned int>>
  bug_nested_option(const State &s);
  static std::optional<std::pair<State, unsigned int>> bug_option_pair(State s);
  static State get_state(unsigned int n);
  static std::optional<unsigned int> bug_some_of_call(unsigned int n);
  static std::pair<State, unsigned int> pair_simple(State s);
  static std::pair<State, unsigned int> pair_let(unsigned int n);
  static std::pair<std::pair<State, unsigned int>,
                   std::pair<unsigned int, unsigned int>>
  pair_nested(State s);
  static std::pair<State, unsigned int> pair_if(bool b, State s);
  static std::optional<std::pair<State, unsigned int>>
  pair_match(const std::optional<State> &o);
  static std::pair<std::pair<State, unsigned int>, unsigned int>
  pair_multi_proj(State s);
  static std::pair<State, unsigned int> pair_chain(const State &s1);
  static std::pair<std::pair<State, State>,
                   std::pair<unsigned int, unsigned int>>
  pair_extreme(State s);
  static std::pair<State, unsigned int> make_pair(State s);
  static std::pair<State, unsigned int> outer_pair(unsigned int n);
  static List<std::pair<State, unsigned int>> count_pairs(unsigned int n,
                                                          State s);
};

#endif // INCLUDED_CUSTOM_INLINE_BUG
