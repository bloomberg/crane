#ifndef INCLUDED_LOOPIFY_COIND_COLIST
#define INCLUDED_LOOPIFY_COIND_COLIST

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
  List clone() const {
    List _out{};

    struct _CloneFrame {
      const List *_src;
      List *_dst;
    };

    std::vector<_CloneFrame> _stack;
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List *_src = _frame._src;
      List *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        const auto &_alt = std::get<Nil>(_src->v());
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ =
            Cons{_alt.d_a0, _alt.d_a1 ? std::make_unique<List>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1)
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
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
  const variant_t &v() const { return d_v_; }
};

struct LoopifyCoindColist {
  template <typename t_A> struct colist {
    // TYPES
    struct Conil {};

    struct Cocons {
      t_A d_a0;
      std::shared_ptr<colist<t_A>> d_a1;
    };

    using variant_t = std::variant<Conil, Cocons>;

  private:
    // DATA
    crane::lazy<variant_t> d_lazyV_;

  public:
    // CREATORS
    explicit colist(Conil _v)
        : d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit colist(Cocons _v)
        : d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit colist(std::function<variant_t()> _thunk)
        : d_lazyV_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static colist<t_A> conil() { return colist(Conil{}); }

    static colist<t_A> cocons(t_A a0, const colist<t_A> &a1) {
      return colist(Cocons{std::move(a0), std::make_shared<colist<t_A>>(a1)});
    }

    static colist<t_A> lazy_(std::function<colist<t_A>()> thunk) {
      return colist<t_A>(std::function<variant_t()>([=]() mutable -> variant_t {
        colist<t_A> _tmp = thunk();
        return _tmp.v();
      }));
    }

    // ACCESSORS
    const variant_t &v() const { return d_lazyV_.force(); }
  };

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static colist<T2> comap(F0 &&f, const colist<T1> l) {
    if (std::holds_alternative<typename colist<T1>::Conil>(l.v())) {
      return colist<T2>::lazy_(
          []() -> colist<T2> { return colist<T2>::conil(); });
    } else {
      const auto &[d_a0, d_a1] = std::get<typename colist<T1>::Cocons>(l.v());
      return colist<T2>::lazy_([=]() mutable -> colist<T2> {
        return colist<T2>::cocons(f(d_a0), comap<T1, T2>(f, *(d_a1)));
      });
    }
  }

  template <typename T1>
  static colist<T1> cotake(const unsigned int &n, const colist<T1> l) {
    if (n <= 0) {
      return colist<T1>::lazy_(
          []() -> colist<T1> { return colist<T1>::conil(); });
    } else {
      unsigned int n_ = n - 1;
      if (std::holds_alternative<typename colist<T1>::Conil>(l.v())) {
        return colist<T1>::lazy_(
            []() -> colist<T1> { return colist<T1>::conil(); });
      } else {
        const auto &[d_a0, d_a1] = std::get<typename colist<T1>::Cocons>(l.v());
        return colist<T1>::lazy_([=]() mutable -> colist<T1> {
          return colist<T1>::cocons(d_a0, cotake<T1>(n_, *(d_a1)));
        });
      }
    }
  }

  template <typename T1> static colist<T1> from_list(const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return colist<T1>::lazy_(
          []() -> colist<T1> { return colist<T1>::conil(); });
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
      List<T1> d_a1_value = List<T1>(*(d_a1));
      return colist<T1>::lazy_([=]() mutable -> colist<T1> {
        return colist<T1>::cocons(d_a0, from_list<T1>(d_a1_value));
      });
    }
  }

  template <typename T1>
  static List<T1> to_list(const unsigned int &fuel, const colist<T1> l) {
    std::unique_ptr<List<T1>> _head{};
    std::unique_ptr<List<T1>> *_write = &_head;
    colist<T1> _loop_l = l;
    unsigned int _loop_fuel = fuel;
    while (true) {
      if (_loop_fuel <= 0) {
        *(_write) = std::make_unique<List<T1>>(List<T1>::nil());
        break;
      } else {
        unsigned int f = _loop_fuel - 1;
        if (std::holds_alternative<typename colist<T1>::Conil>(_loop_l.v())) {
          *(_write) = std::make_unique<List<T1>>(List<T1>::nil());
          break;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename colist<T1>::Cocons>(_loop_l.v());
          auto _cell = std::make_unique<List<T1>>(
              typename List<T1>::Cons(d_a0, nullptr));
          *(_write) = std::move(_cell);
          _write = &std::get<typename List<T1>::Cons>((*_write)->v_mut()).d_a1;
          colist<T1> _next_l = std::move(*(d_a1));
          unsigned int _next_fuel = f;
          _loop_l = std::move(_next_l);
          _loop_fuel = std::move(_next_fuel);
          continue;
        }
      }
    }
    return std::move(*(_head));
  }

  static inline const List<unsigned int> test_comap = to_list<unsigned int>(
      5u, comap<unsigned int, unsigned int>(
              [](const unsigned int &n) { return (n * 2u); },
              from_list<unsigned int>(List<unsigned int>::cons(
                  1u, List<unsigned int>::cons(
                          2u, List<unsigned int>::cons(
                                  3u, List<unsigned int>::nil()))))));
  static inline const List<unsigned int> test_cotake = to_list<unsigned int>(
      10u, cotake<unsigned int>(
               2u, from_list<unsigned int>(List<unsigned int>::cons(
                       10u, List<unsigned int>::cons(
                                20u, List<unsigned int>::cons(
                                         30u, List<unsigned int>::nil()))))));
};

#endif // INCLUDED_LOOPIFY_COIND_COLIST
