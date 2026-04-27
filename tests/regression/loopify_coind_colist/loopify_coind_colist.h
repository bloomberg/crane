#ifndef INCLUDED_LOOPIFY_COIND_COLIST
#define INCLUDED_LOOPIFY_COIND_COLIST

#include "lazy.h"
#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

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
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
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

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
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

    static std::shared_ptr<colist<t_A>> conil() {
      return std::make_shared<colist<t_A>>(Conil{});
    }

    static std::shared_ptr<colist<t_A>>
    cocons(t_A a0, std::shared_ptr<colist<t_A>> a1) {
      return std::make_shared<colist<t_A>>(
          Cocons{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<colist<t_A>>
    lazy_(std::function<std::shared_ptr<colist<t_A>>()> thunk) {
      return std::make_shared<colist<t_A>>(
          std::function<variant_t()>([=]() mutable -> variant_t {
            std::shared_ptr<colist<t_A>> _tmp = thunk();
            return _tmp->v();
          }));
    }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const {
      return d_lazyV_.force();
    }
  };

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::shared_ptr<colist<T2>>
  comap(F0 &&f, const std::shared_ptr<colist<T1>> &l) {
    if (std::holds_alternative<typename colist<T1>::Conil>(l->v())) {
      return colist<T2>::lazy_(
          []() -> std::shared_ptr<colist<T2>> { return colist<T2>::conil(); });
    } else {
      const auto &[d_a0, d_a1] = std::get<typename colist<T1>::Cocons>(l->v());
      return colist<T2>::lazy_([=]() mutable -> std::shared_ptr<colist<T2>> {
        return colist<T2>::cocons(f(d_a0), comap<T1, T2>(f, d_a1));
      });
    }
  }

  template <typename T1>
  static std::shared_ptr<colist<T1>>
  cotake(const unsigned int &n, const std::shared_ptr<colist<T1>> &l) {
    if (n <= 0) {
      return colist<T1>::lazy_(
          []() -> std::shared_ptr<colist<T1>> { return colist<T1>::conil(); });
    } else {
      unsigned int n_ = n - 1;
      if (std::holds_alternative<typename colist<T1>::Conil>(l->v())) {
        return colist<T1>::lazy_([]() -> std::shared_ptr<colist<T1>> {
          return colist<T1>::conil();
        });
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename colist<T1>::Cocons>(l->v());
        return colist<T1>::lazy_([=]() mutable -> std::shared_ptr<colist<T1>> {
          return colist<T1>::cocons(d_a0, cotake<T1>(n_, d_a1));
        });
      }
    }
  }

  template <typename T1>
  static std::shared_ptr<colist<T1>> from_list(const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return colist<T1>::lazy_(
          []() -> std::shared_ptr<colist<T1>> { return colist<T1>::conil(); });
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
      return colist<T1>::lazy_([&]() -> std::shared_ptr<colist<T1>> {
        return colist<T1>::cocons(d_a0, from_list<T1>(*(d_a1)));
      });
    }
  }

  template <typename T1>
  __attribute__((pure)) static List<T1>
  to_list(const unsigned int &fuel, const std::shared_ptr<colist<T1>> &l) {
    std::unique_ptr<List<T1>> _head{};
    std::unique_ptr<List<T1>> *_write = &_head;
    std::shared_ptr<colist<T1>> _loop_l = l;
    unsigned int _loop_fuel = fuel;
    while (true) {
      if (_loop_fuel <= 0) {
        *(_write) = std::make_unique<List<T1>>(List<T1>::nil());
        break;
      } else {
        unsigned int f = _loop_fuel - 1;
        if (std::holds_alternative<typename colist<T1>::Conil>(_loop_l->v())) {
          *(_write) = std::make_unique<List<T1>>(List<T1>::nil());
          break;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename colist<T1>::Cocons>(_loop_l->v());
          auto _cell = std::make_unique<List<T1>>(
              typename List<T1>::Cons(d_a0, nullptr));
          *(_write) = std::move(_cell);
          _write = &std::get<typename List<T1>::Cons>((*_write)->v_mut()).d_a1;
          std::shared_ptr<colist<T1>> _next_l = d_a1;
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
