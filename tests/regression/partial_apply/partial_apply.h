#ifndef INCLUDED_PARTIAL_APPLY
#define INCLUDED_PARTIAL_APPLY

#include <functional>
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

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, A &>
  List<T1> map(F0 &&f) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return List<T1>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return List<T1>::cons(f(a0), (*a1).template map<T1>(f));
    }
  }
};

struct PartialApply {
  static List<unsigned int> inc_all(const List<unsigned int> &l);
  static List<std::pair<unsigned int, unsigned int>>
  tag_all(const List<unsigned int> &l);
  static List<std::optional<unsigned int>>
  wrap_all(const List<unsigned int> &l);
  static List<std::function<List<unsigned int>(List<unsigned int>)>>
  prepend_each(const List<unsigned int> &l);

  template <typename A> struct tagged {
    // DATA
    unsigned int a0;
    A a1;

    // ACCESSORS
    tagged<A> clone() const { return {a0, a1}; }

    // CREATORS
    static tagged<A> tag(unsigned int a0, A a1) { return {a0, std::move(a1)}; }
  };

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, unsigned int &, T1 &>
  static T2 tagged_rect(F0 &&f, const tagged<T1> &t) {
    const auto &[a0, a1] = t;
    return f(a0, a1);
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, unsigned int &, T1 &>
  static T2 tagged_rec(F0 &&f, const tagged<T1> &t) {
    const auto &[a0, a1] = t;
    return f(a0, a1);
  }

  static List<tagged<bool>> tag_with(unsigned int n, const List<bool> &l);
  static List<std::pair<unsigned int, std::pair<unsigned int, unsigned int>>>
  double_tag(const List<unsigned int> &l);
  static unsigned int sum_with_init(unsigned int init,
                                    const List<unsigned int> &l);
  static inline const List<unsigned int> test_inc =
      inc_all(List<unsigned int>::cons(
          1u,
          List<unsigned int>::cons(
              2u, List<unsigned int>::cons(3u, List<unsigned int>::nil()))));
  static inline const List<std::pair<unsigned int, unsigned int>> test_tag =
      tag_all(List<unsigned int>::cons(
          10u,
          List<unsigned int>::cons(
              20u, List<unsigned int>::cons(30u, List<unsigned int>::nil()))));
  static inline const List<std::optional<unsigned int>> test_wrap =
      wrap_all(List<unsigned int>::cons(
          5u,
          List<unsigned int>::cons(
              6u, List<unsigned int>::cons(7u, List<unsigned int>::nil()))));
  static inline const List<tagged<bool>> test_tag_with = tag_with(
      99u, List<bool>::cons(
               true, List<bool>::cons(
                         false, List<bool>::cons(true, List<bool>::nil()))));
  static inline const unsigned int test_sum =
      sum_with_init(100u, List<unsigned int>::cons(
                              1u, List<unsigned int>::cons(
                                      2u, List<unsigned int>::cons(
                                              3u, List<unsigned int>::nil()))));
};

#endif // INCLUDED_PARTIAL_APPLY
