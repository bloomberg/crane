#ifndef INCLUDED_LET_FIX
#define INCLUDED_LET_FIX

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
  List<t_A> clone() const {
    List<t_A> _out{};

    struct _CloneFrame {
      const List<t_A> *_src;
      List<t_A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<t_A> *_src = _frame._src;
      List<t_A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ = Cons{_alt.d_a0,
                          _alt.d_a1 ? std::make_unique<List<t_A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1) {
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
      }
    }
    return _out;
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

  static List<t_A> nil() { return List(Nil{}); }

  static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<t_A>>> _stack{};
    auto _drain = [&](List<t_A> &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
        if (_alt.d_a1) {
          _stack.push_back(std::move(_alt.d_a1));
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

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
};

struct LetFix {
  static unsigned int local_sum(const List<unsigned int> &l);

  template <typename T1> static List<T1> local_rev(const List<T1> &l) {
    std::function<List<T1>(List<T1>, List<T1>)> go;
    go = [&](List<T1> acc, List<T1> xs) -> List<T1> {
      if (std::holds_alternative<typename List<T1>::Nil>(xs.v())) {
        return acc;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(xs.v());
        return go(List<T1>::cons(d_a0, std::move(acc)), *(d_a1));
      }
    };
    return go(List<T1>::nil(), l);
  }

  static List<unsigned int> local_flatten(const List<List<unsigned int>> &xss);
  static bool local_mem(const unsigned int &n, const List<unsigned int> &l);

  template <typename T1> static unsigned int local_length(const List<T1> &xs) {
    if (std::holds_alternative<typename List<T1>::Nil>(xs.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(xs.v());
      return (local_length<T1>(*(d_a1)) + 1);
    }
  }

  static inline const unsigned int test_sum =
      local_sum(List<unsigned int>::cons(
          1u, List<unsigned int>::cons(
                  2u, List<unsigned int>::cons(
                          3u, List<unsigned int>::cons(
                                  4u, List<unsigned int>::cons(
                                          5u, List<unsigned int>::nil()))))));
  static inline const List<unsigned int> test_rev =
      local_rev<unsigned int>(List<unsigned int>::cons(
          1u,
          List<unsigned int>::cons(
              2u, List<unsigned int>::cons(3u, List<unsigned int>::nil()))));
  static inline const List<unsigned int> test_flatten =
      local_flatten(List<List<unsigned int>>::cons(
          List<unsigned int>::cons(
              1u, List<unsigned int>::cons(2u, List<unsigned int>::nil())),
          List<List<unsigned int>>::cons(
              List<unsigned int>::cons(3u, List<unsigned int>::nil()),
              List<List<unsigned int>>::cons(
                  List<unsigned int>::cons(
                      4u, List<unsigned int>::cons(
                              5u, List<unsigned int>::cons(
                                      6u, List<unsigned int>::nil()))),
                  List<List<unsigned int>>::nil()))));
  static inline const bool test_mem_found = local_mem(
      3u, List<unsigned int>::cons(
              1u, List<unsigned int>::cons(
                      2u, List<unsigned int>::cons(
                              3u, List<unsigned int>::cons(
                                      4u, List<unsigned int>::nil())))));
  static inline const bool test_mem_missing = local_mem(
      9u, List<unsigned int>::cons(
              1u, List<unsigned int>::cons(
                      2u, List<unsigned int>::cons(
                              3u, List<unsigned int>::cons(
                                      4u, List<unsigned int>::nil())))));
  static inline const unsigned int test_length =
      local_length<unsigned int>(List<unsigned int>::cons(
          10u, List<unsigned int>::cons(
                   20u, List<unsigned int>::cons(
                            30u, List<unsigned int>::cons(
                                     40u, List<unsigned int>::nil())))));
};

#endif // INCLUDED_LET_FIX
