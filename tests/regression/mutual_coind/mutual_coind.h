#ifndef INCLUDED_MUTUAL_COIND
#define INCLUDED_MUTUAL_COIND

#include "lazy.h"
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

struct MutualCoind {
  template <typename t_A> struct streamA;
  template <typename t_A> struct streamB;

  template <typename t_A> struct streamA {
    // TYPES
    struct ConsA {
      t_A d_a0;
      std::shared_ptr<streamB<t_A>> d_a1;
    };

    using variant_t = std::variant<ConsA>;

  private:
    // DATA
    crane::lazy<variant_t> d_lazyV_;

  public:
    // CREATORS
    explicit streamA(ConsA _v)
        : d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit streamA(std::function<variant_t()> _thunk)
        : d_lazyV_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static streamA<t_A> consa(t_A a0, const streamB<t_A> &a1) {
      return streamA(ConsA{std::move(a0), std::make_shared<streamB<t_A>>(a1)});
    }

    static streamA<t_A> lazy_(std::function<streamA<t_A>()> thunk) {
      return streamA<t_A>(
          std::function<variant_t()>([=]() mutable -> variant_t {
            streamA<t_A> _tmp = thunk();
            return _tmp.v();
          }));
    }

    // ACCESSORS
    const variant_t &v() const { return d_lazyV_.force(); }
  };

  template <typename t_A> struct streamB {
    // TYPES
    struct ConsB {
      t_A d_a0;
      std::shared_ptr<streamA<t_A>> d_a1;
    };

    using variant_t = std::variant<ConsB>;

  private:
    // DATA
    crane::lazy<variant_t> d_lazyV_;

  public:
    // CREATORS
    explicit streamB(ConsB _v)
        : d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit streamB(std::function<variant_t()> _thunk)
        : d_lazyV_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static streamB<t_A> consb(t_A a0, const streamA<t_A> &a1) {
      return streamB(ConsB{std::move(a0), std::make_shared<streamA<t_A>>(a1)});
    }

    static streamB<t_A> lazy_(std::function<streamB<t_A>()> thunk) {
      return streamB<t_A>(
          std::function<variant_t()>([=]() mutable -> variant_t {
            streamB<t_A> _tmp = thunk();
            return _tmp.v();
          }));
    }

    // ACCESSORS
    const variant_t &v() const { return d_lazyV_.force(); }
  };

  template <typename T1> static T1 headA(const streamA<T1> s) {
    const auto &[d_a0, d_a1] = std::get<typename streamA<T1>::ConsA>(s.v());
    return d_a0;
  }

  template <typename T1> static streamB<T1> tailA(const streamA<T1> s) {
    const auto &[d_a0, d_a1] = std::get<typename streamA<T1>::ConsA>(s.v());
    return streamB<T1>::lazy_([=]() mutable -> streamB<T1> { return *(d_a1); });
  }

  template <typename T1> static T1 headB(const streamB<T1> s) {
    const auto &[d_a0, d_a1] = std::get<typename streamB<T1>::ConsB>(s.v());
    return d_a0;
  }

  template <typename T1> static streamA<T1> tailB(const streamB<T1> s) {
    const auto &[d_a0, d_a1] = std::get<typename streamB<T1>::ConsB>(s.v());
    return streamA<T1>::lazy_([=]() mutable -> streamA<T1> { return *(d_a1); });
  }

  static streamA<unsigned int> countA(unsigned int n);
  static streamB<unsigned int> countB(unsigned int n);

  template <typename T1>
  static List<T1> takeA(const unsigned int &fuel, const streamA<T1> s) {
    if (fuel <= 0) {
      return List<T1>::nil();
    } else {
      unsigned int f = fuel - 1;
      const auto &[d_a0, d_a1] = std::get<typename streamA<T1>::ConsA>(s.v());
      return List<T1>::cons(d_a0, takeB<T1>(f, *(d_a1)));
    }
  }

  template <typename T1>
  static List<T1> takeB(const unsigned int &fuel, const streamB<T1> s) {
    if (fuel <= 0) {
      return List<T1>::nil();
    } else {
      unsigned int f = fuel - 1;
      const auto &[d_a0, d_a1] = std::get<typename streamB<T1>::ConsB>(s.v());
      return List<T1>::cons(d_a0, takeA<T1>(f, *(d_a1)));
    }
  }

  static inline const unsigned int test_headA = headA<unsigned int>(countA(0u));
  static inline const unsigned int test_headB =
      headB<unsigned int>(countB(10u));
  static inline const List<unsigned int> test_take5 =
      takeA<unsigned int>(5u, countA(0u));
};

#endif // INCLUDED_MUTUAL_COIND
