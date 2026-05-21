#ifndef INCLUDED_LOOPIFY_COIND_COLIST
#define INCLUDED_LOOPIFY_COIND_COLIST

#include "lazy.h"
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
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
        _dst->v_ = Cons{_alt.a, _alt.l ? std::make_shared<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.l) {
          _stack.push_back({_alt.l.get(), _dst_alt.l.get()});
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
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a), l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.l) {
          _stack.push_back(std::move(_alt.l));
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

struct LoopifyCoindColist {
  template <typename A> struct colist {
    // TYPES
    struct Conil {};

    struct Cocons {
      A a0;
      std::shared_ptr<colist<A>> a1;
    };

    using variant_t = std::variant<Conil, Cocons>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    explicit colist(Conil _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit colist(Cocons _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit colist(std::function<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static colist<A> conil() { return colist(Conil{}); }

    static colist<A> cocons(A a0, const colist<A> &a1) {
      return colist(Cocons{std::move(a0), std::make_shared<colist<A>>(a1)});
    }

    static colist<A> lazy_(std::function<colist<A>()> thunk) {
      return colist<A>(std::function<variant_t()>([=]() mutable -> variant_t {
        colist<A> _tmp = thunk();
        return _tmp.v();
      }));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }
  };

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static colist<T2> comap(F0 &&f, colist<T1> l) {
    if (std::holds_alternative<typename colist<T1>::Conil>(l.v())) {
      return colist<T2>::lazy_(
          []() -> colist<T2> { return colist<T2>::conil(); });
    } else {
      const auto &[a0, a1] = std::get<typename colist<T1>::Cocons>(l.v());
      return colist<T2>::lazy_([=]() mutable -> colist<T2> {
        return colist<T2>::cocons(f(a0), comap<T1, T2>(f, *a1));
      });
    }
  }

  template <typename T1> static colist<T1> cotake(uint64_t n, colist<T1> l) {
    if (n <= 0) {
      return colist<T1>::lazy_(
          []() -> colist<T1> { return colist<T1>::conil(); });
    } else {
      uint64_t n_ = n - 1;
      if (std::holds_alternative<typename colist<T1>::Conil>(l.v())) {
        return colist<T1>::lazy_(
            []() -> colist<T1> { return colist<T1>::conil(); });
      } else {
        const auto &[a0, a1] = std::get<typename colist<T1>::Cocons>(l.v());
        return colist<T1>::lazy_([=]() mutable -> colist<T1> {
          return colist<T1>::cocons(a0, cotake<T1>(n_, *a1));
        });
      }
    }
  }

  template <typename T1> static colist<T1> from_list(const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return colist<T1>::lazy_(
          []() -> colist<T1> { return colist<T1>::conil(); });
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      const List<T1> &a1_value = *a1;
      return colist<T1>::lazy_([=]() mutable -> colist<T1> {
        return colist<T1>::cocons(a0, from_list<T1>(a1_value));
      });
    }
  }

  template <typename T1> static List<T1> to_list(uint64_t fuel, colist<T1> l) {
    std::shared_ptr<List<T1>> _head{};
    std::shared_ptr<List<T1>> *_write = &_head;
    colist<T1> _loop_l = std::move(l);
    uint64_t _loop_fuel = std::move(fuel);
    while (true) {
      if (_loop_fuel <= 0) {
        *_write = std::make_shared<List<T1>>(List<T1>::nil());
        break;
      } else {
        uint64_t f = _loop_fuel - 1;
        if (std::holds_alternative<typename colist<T1>::Conil>(_loop_l.v())) {
          *_write = std::make_shared<List<T1>>(List<T1>::nil());
          break;
        } else {
          const auto &[a0, a1] =
              std::get<typename colist<T1>::Cocons>(_loop_l.v());
          auto _cell =
              std::make_shared<List<T1>>(typename List<T1>::Cons(a0, nullptr));
          *_write = std::move(_cell);
          _write = &std::get<typename List<T1>::Cons>((*_write)->v_mut()).l;
          _loop_l = std::move(*a1);
          _loop_fuel = f;
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  static inline const List<uint64_t> test_comap = to_list<uint64_t>(
      UINT64_C(5),
      comap<uint64_t, uint64_t>(
          [](uint64_t n) { return (n * UINT64_C(2)); },
          from_list<uint64_t>(List<uint64_t>::cons(
              UINT64_C(1),
              List<uint64_t>::cons(
                  UINT64_C(2),
                  List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))))));
  static inline const List<uint64_t> test_cotake = to_list<uint64_t>(
      UINT64_C(10),
      cotake<uint64_t>(
          UINT64_C(2),
          from_list<uint64_t>(List<uint64_t>::cons(
              UINT64_C(10),
              List<uint64_t>::cons(
                  UINT64_C(20), List<uint64_t>::cons(
                                    UINT64_C(30), List<uint64_t>::nil()))))));
};

#endif // INCLUDED_LOOPIFY_COIND_COLIST
