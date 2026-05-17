#ifndef INCLUDED_STACK_OPS
#define INCLUDED_STACK_OPS

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

  unsigned int length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return 0u;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return ((*a1).length() + 1);
    }
  }
};

struct StackOps {
  struct state_basic {
    List<unsigned int> stack_basic;

    // ACCESSORS
    state_basic clone() const {
      return state_basic{(*this).stack_basic.clone()};
    }
  };

  struct state_with_acc {
    List<unsigned int> stack_with_acc;
    unsigned int acc;

    // ACCESSORS
    state_with_acc clone() const {
      return state_with_acc{(*this).stack_with_acc.clone(), (*this).acc};
    }
  };

  static std::pair<std::optional<unsigned int>, state_basic>
  pop_stack(state_basic s);
  static bool is_none(const std::optional<unsigned int> &o);
  static unsigned int option_or_zero(const std::optional<unsigned int> &o);
  static inline const bool empty_is_none =
      is_none(pop_stack(state_basic{List<unsigned int>::nil()}).first);
  static inline const unsigned int some_addr = option_or_zero(
      pop_stack(
          state_basic{List<unsigned int>::cons(
              9u, List<unsigned int>::cons(8u, List<unsigned int>::nil()))})
          .first);
  static std::pair<std::optional<unsigned int>, state_with_acc>
  pop_stack_acc(state_with_acc s);
  static inline const unsigned int pop_acc_test = []() -> unsigned int {
    auto _cs = pop_stack_acc(state_with_acc{
        List<unsigned int>::cons(
            9u, List<unsigned int>::cons(8u, List<unsigned int>::nil())),
        3u});
    const std::optional<unsigned int> &o = _cs.first;
    const state_with_acc &s_ = _cs.second;
    if (o.has_value()) {
      const unsigned int &a = *o;
      return ((a + s_.stack_with_acc.length()) + s_.acc);
    } else {
      return s_.acc;
    }
  }();
  static state_basic push_stack(const state_basic &s, unsigned int addr);
  static unsigned int top_or_zero(const state_basic &s);
  static inline const unsigned int empty_len =
      push_stack(state_basic{List<unsigned int>::nil()}, 12u)
          .stack_basic.length();
  static inline const unsigned int overflow_head = top_or_zero(push_stack(
      state_basic{List<unsigned int>::cons(
          1u,
          List<unsigned int>::cons(
              2u, List<unsigned int>::cons(3u, List<unsigned int>::nil())))},
      9u));
  static inline const unsigned int overflow_len =
      push_stack(state_basic{List<unsigned int>::cons(
                     1u, List<unsigned int>::cons(
                             2u, List<unsigned int>::cons(
                                     3u, List<unsigned int>::nil())))},
                 9u)
          .stack_basic.length();
  static state_basic push_stack_cap(const state_basic &s, unsigned int addr);
  static inline const unsigned int push_cap_test =
      push_stack_cap(
          state_basic{List<unsigned int>::cons(
              10u, List<unsigned int>::cons(
                       20u, List<unsigned int>::cons(
                                30u, List<unsigned int>::cons(
                                         40u, List<unsigned int>::nil()))))},
          7u)
          .stack_basic.length();
  static inline const std::pair<
      std::pair<std::pair<std::pair<unsigned int, bool>, unsigned int>,
                std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>,
      unsigned int>
      t = std::make_pair(
          std::make_pair(
              std::make_pair(std::make_pair(some_addr, empty_is_none),
                             pop_acc_test),
              std::make_pair(std::make_pair(empty_len, overflow_head),
                             overflow_len)),
          push_cap_test);
};

#endif // INCLUDED_STACK_OPS
