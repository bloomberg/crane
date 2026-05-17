#ifndef INCLUDED_MUTUAL_COIND
#define INCLUDED_MUTUAL_COIND

#include "lazy.h"
#include <functional>
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

struct MutualCoind {
  template <typename A> struct streamA;
  template <typename A> struct streamB;

  template <typename A> struct streamA {
    // TYPES
    struct ConsA {
      A a0;
      std::shared_ptr<streamB<A>> a1;
    };

    using variant_t = std::variant<ConsA>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    explicit streamA(ConsA _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit streamA(std::function<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static streamA<A> consa(A a0, const streamB<A> &a1) {
      return streamA(ConsA{std::move(a0), std::make_shared<streamB<A>>(a1)});
    }

    static streamA<A> lazy_(std::function<streamA<A>()> thunk) {
      return streamA<A>(std::function<variant_t()>([=]() mutable -> variant_t {
        streamA<A> _tmp = thunk();
        return _tmp.v();
      }));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }
  };

  template <typename A> struct streamB {
    // TYPES
    struct ConsB {
      A a0;
      std::shared_ptr<streamA<A>> a1;
    };

    using variant_t = std::variant<ConsB>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    explicit streamB(ConsB _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit streamB(std::function<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static streamB<A> consb(A a0, const streamA<A> &a1) {
      return streamB(ConsB{std::move(a0), std::make_shared<streamA<A>>(a1)});
    }

    static streamB<A> lazy_(std::function<streamB<A>()> thunk) {
      return streamB<A>(std::function<variant_t()>([=]() mutable -> variant_t {
        streamB<A> _tmp = thunk();
        return _tmp.v();
      }));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }
  };

  template <typename T1> static T1 headA(streamA<T1> s) {
    const auto &[a0, a1] = std::get<typename streamA<T1>::ConsA>(s.v());
    return a0;
  }

  template <typename T1> static streamB<T1> tailA(streamA<T1> s) {
    const auto &[a0, a1] = std::get<typename streamA<T1>::ConsA>(s.v());
    return streamB<T1>::lazy_([=]() mutable -> streamB<T1> { return *a1; });
  }

  template <typename T1> static T1 headB(streamB<T1> s) {
    const auto &[a0, a1] = std::get<typename streamB<T1>::ConsB>(s.v());
    return a0;
  }

  template <typename T1> static streamA<T1> tailB(streamB<T1> s) {
    const auto &[a0, a1] = std::get<typename streamB<T1>::ConsB>(s.v());
    return streamA<T1>::lazy_([=]() mutable -> streamA<T1> { return *a1; });
  }

  static streamA<uint64_t> countA(uint64_t n);
  static streamB<uint64_t> countB(uint64_t n);

  template <typename T1> static List<T1> takeA(uint64_t fuel, streamA<T1> s) {
    if (fuel <= 0) {
      return List<T1>::nil();
    } else {
      uint64_t f = fuel - 1;
      const auto &[a0, a1] = std::get<typename streamA<T1>::ConsA>(s.v());
      return List<T1>::cons(a0, takeB<T1>(f, *a1));
    }
  }

  template <typename T1> static List<T1> takeB(uint64_t fuel, streamB<T1> s) {
    if (fuel <= 0) {
      return List<T1>::nil();
    } else {
      uint64_t f = fuel - 1;
      const auto &[a0, a1] = std::get<typename streamB<T1>::ConsB>(s.v());
      return List<T1>::cons(a0, takeA<T1>(f, *a1));
    }
  }

  static inline const uint64_t test_headA =
      headA<uint64_t>(countA(UINT64_C(0)));
  static inline const uint64_t test_headB =
      headB<uint64_t>(countB(UINT64_C(10)));
  static inline const List<uint64_t> test_take5 =
      takeA<uint64_t>(UINT64_C(5), countA(UINT64_C(0)));
};

#endif // INCLUDED_MUTUAL_COIND
