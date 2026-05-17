#ifndef INCLUDED_FUNCTOR_COMP
#define INCLUDED_FUNCTOR_COMP

#include <concepts>
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

  List(List<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) noexcept {
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

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &, A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return a0;
    } else {
      const auto &[a1, a2] = std::get<typename List<A>::Cons>(this->v());
      return (*a2).template fold_left<T1>(f, f(a0, a1));
    }
  }

  List<A> rev() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return List<A>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (*a1).rev().app(List<A>::cons(a0, List<A>::nil()));
    }
  }

  unsigned int length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return 0u;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return ((*a1).length() + 1);
    }
  }

  List<A> app(List<A> m) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return m;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return List<A>::cons(a0, (*a1).app(std::move(m)));
    }
  }
};

template <typename M>
concept CONTAINER = requires {
  typename M::t;
  requires(
      requires {
        { M::empty } -> std::convertible_to<typename M::t>;
      } ||
      requires {
        { M::empty() } -> std::convertible_to<typename M::t>;
      });
  {
    M::push(std::declval<unsigned int>(), std::declval<typename M::t>())
  } -> std::same_as<typename M::t>;
  {
    M::pop(std::declval<typename M::t>())
  } -> std::same_as<std::optional<std::pair<unsigned int, typename M::t>>>;
  { M::size(std::declval<typename M::t>()) } -> std::same_as<unsigned int>;
};

struct FunctorComp {
  struct Stack {
    using t = List<unsigned int>;
    static inline const t empty = List<unsigned int>::nil();
    static t push(unsigned int x, List<unsigned int> s);
    static std::optional<std::pair<unsigned int, t>>
    pop(const List<unsigned int> &s);
    static unsigned int size(t _x0);
  };

  struct Queue {
    using t = std::pair<List<unsigned int>, List<unsigned int>>;
    static inline const t empty =
        std::make_pair(List<unsigned int>::nil(), List<unsigned int>::nil());
    static t push(unsigned int x,
                  const std::pair<List<unsigned int>, List<unsigned int>> &q);
    static std::optional<std::pair<unsigned int, t>>
    pop(const std::pair<List<unsigned int>, List<unsigned int>> &q);
    static unsigned int
    size(const std::pair<List<unsigned int>, List<unsigned int>> &q);
  };

  template <CONTAINER C> struct ContainerOps {
    static typename C::t push_list(const List<unsigned int> &l,
                                   typename C::t c) {
      return l.template fold_left<typename C::t>(
          [](typename C::t acc, unsigned int x) { return C::push(x, acc); }, c);
    }

    static List<unsigned int> to_list(typename C::t c) {
      auto go_impl = [](auto &_self_go, unsigned int fuel,
                        List<unsigned int> acc,
                        typename C::t c0) -> List<unsigned int> {
        if (fuel <= 0) {
          return std::move(acc).rev();
        } else {
          unsigned int f = fuel - 1;
          auto _cs = C::pop(c0);
          if (_cs.has_value()) {
            const std::pair<unsigned int, typename C::t> &p = *_cs;
            const unsigned int &x = p.first;
            const typename C::t &c_ = p.second;
            return _self_go(_self_go, f,
                            List<unsigned int>::cons(x, std::move(acc)), c_);
          } else {
            return std::move(acc).rev();
          }
        }
      };
      auto go = [&](unsigned int fuel, List<unsigned int> acc,
                    typename C::t c0) -> List<unsigned int> {
        return go_impl(go_impl, fuel, acc, c0);
      };
      return go(C::size(c), List<unsigned int>::nil(), c);
    }
  };

  using StackOps = ContainerOps<Stack>;
  using QueueOps = ContainerOps<Queue>;
  static inline const List<unsigned int> test_stack =
      StackOps::to_list(StackOps::push_list(
          List<unsigned int>::cons(
              1u,
              List<unsigned int>::cons(
                  2u, List<unsigned int>::cons(3u, List<unsigned int>::nil()))),
          Stack::empty));
  static inline const List<unsigned int> test_queue =
      QueueOps::to_list(QueueOps::push_list(
          List<unsigned int>::cons(
              1u,
              List<unsigned int>::cons(
                  2u, List<unsigned int>::cons(3u, List<unsigned int>::nil()))),
          Queue::empty));
  static inline const unsigned int test_stack_size =
      Stack::size(StackOps::push_list(
          List<unsigned int>::cons(
              10u, List<unsigned int>::cons(
                       20u, List<unsigned int>::cons(
                                30u, List<unsigned int>::nil()))),
          Stack::empty));
  static inline const unsigned int test_queue_size =
      Queue::size(QueueOps::push_list(
          List<unsigned int>::cons(
              10u, List<unsigned int>::cons(
                       20u, List<unsigned int>::cons(
                                30u, List<unsigned int>::nil()))),
          Queue::empty));
};

#endif // INCLUDED_FUNCTOR_COMP
