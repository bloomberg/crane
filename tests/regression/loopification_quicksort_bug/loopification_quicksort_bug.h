#ifndef INCLUDED_LOOPIFICATION_QUICKSORT_BUG
#define INCLUDED_LOOPIFICATION_QUICKSORT_BUG

#include <any>
#include <memory>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

using namespace std::string_literals;

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

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        _drain(_cur->v_mut());
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, A &>
  List<A> filter(F0 &&f) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return List<A>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      if (f(a0)) {
        return List<A>::cons(a0, a1->filter(f));
      } else {
        return a1->filter(f);
      }
    }
  }

  List<A> app(List<A> m) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return m;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return List<A>::cons(a0, a1->app(std::move(m)));
    }
  }
};

struct QuicksortFun {
  template <typename F1>
    requires std::is_invocable_r_v<List<uint64_t>, F1 &, List<uint64_t> &>
  static List<uint64_t> quicksort_fun_functional(const List<uint64_t> &l,
                                                 F1 &&quicksort_fun0) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
      return List<uint64_t>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
      const List<uint64_t> &a1_value = *a1;
      return quicksort_fun0(
                 a1_value.filter([=](uint64_t x) mutable { return x < a0; }))
          .app(List<uint64_t>::cons(a0, List<uint64_t>::nil())
                   .app(quicksort_fun0(a1_value.filter(
                       [=](uint64_t x) mutable { return a0 <= x; }))));
    }
  }

  static List<uint64_t> quicksort_fun(const List<uint64_t> &x);
  static std::string list_to_string_helper(const List<uint64_t> &l);
  static std::string list_to_string(const List<uint64_t> &l);
  static inline const List<uint64_t> input_lst1 = List<uint64_t>::cons(
      UINT64_C(212498),
      List<uint64_t>::cons(
          UINT64_C(127),
          List<uint64_t>::cons(
              UINT64_C(5981),
              List<uint64_t>::cons(
                  UINT64_C(2749812),
                  List<uint64_t>::cons(
                      UINT64_C(74879),
                      List<uint64_t>::cons(
                          UINT64_C(126),
                          List<uint64_t>::cons(
                              UINT64_C(4),
                              List<uint64_t>::cons(
                                  UINT64_C(51),
                                  List<uint64_t>::cons(
                                      UINT64_C(2412),
                                      List<uint64_t>::cons(
                                          UINT64_C(10645),
                                          List<uint64_t>::nil()))))))))));

  static std::string test_quicksort_fun(std::monostate _x);
};

#endif // INCLUDED_LOOPIFICATION_QUICKSORT_BUG
