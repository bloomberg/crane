#ifndef INCLUDED_LET_FIX_MOVE_ACC
#define INCLUDED_LET_FIX_MOVE_ACC

#include <memory>
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
};

struct LetFixMoveAcc {
  template <typename T1> static List<T1> reverse_list(const List<T1> &l) {
    auto go_impl = [](auto &_self_go, const List<T1> &xs,
                      List<T1> acc) -> List<T1> {
      if (std::holds_alternative<typename List<T1>::Nil>(xs.v())) {
        return acc;
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(xs.v());
        return _self_go(_self_go, *a1, List<T1>::cons(a0, std::move(acc)));
      }
    };
    auto go = [&](const List<T1> &xs, List<T1> acc) -> List<T1> {
      return go_impl(go_impl, xs, acc);
    };
    return go(l, List<T1>::nil());
  }

  template <typename T1> static List<T1> snoc(const List<T1> &l, T1 x) {
    auto rev_impl = [](auto &_self_rev, const List<T1> &xs,
                       List<T1> acc) -> List<T1> {
      if (std::holds_alternative<typename List<T1>::Nil>(xs.v())) {
        return acc;
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(xs.v());
        return _self_rev(_self_rev, *a1, List<T1>::cons(a0, std::move(acc)));
      }
    };
    auto rev = [&](const List<T1> &xs, List<T1> acc) -> List<T1> {
      return rev_impl(rev_impl, xs, acc);
    };
    return rev(rev(l, List<T1>::nil()), List<T1>::cons(x, List<T1>::nil()));
  }

  static inline const List<unsigned int> test_rev =
      reverse_list<unsigned int>(List<unsigned int>::cons(
          1u,
          List<unsigned int>::cons(
              2u, List<unsigned int>::cons(3u, List<unsigned int>::nil()))));
  static inline const List<unsigned int> test_snoc = snoc<unsigned int>(
      List<unsigned int>::cons(
          10u, List<unsigned int>::cons(20u, List<unsigned int>::nil())),
      30u);
};

#endif // INCLUDED_LET_FIX_MOVE_ACC
