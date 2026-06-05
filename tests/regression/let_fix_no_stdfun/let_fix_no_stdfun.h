#ifndef INCLUDED_LET_FIX_NO_STDFUN
#define INCLUDED_LET_FIX_NO_STDFUN

#include <any>
#include <memory>
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
};

struct LetFixNoStdfun {
  static uint64_t sum_list(const List<uint64_t> &l);
  static uint64_t flat_map_sum(const List<List<uint64_t>> &xss);
  static List<uint64_t> flatten(const List<List<uint64_t>> &xss);
  static inline const uint64_t test_sum = sum_list(List<uint64_t>::cons(
      UINT64_C(1),
      List<uint64_t>::cons(
          UINT64_C(2),
          List<uint64_t>::cons(
              UINT64_C(3),
              List<uint64_t>::cons(
                  UINT64_C(4),
                  List<uint64_t>::cons(UINT64_C(5), List<uint64_t>::nil()))))));
  static inline const uint64_t test_flat_map_sum =
      flat_map_sum(List<List<uint64_t>>::cons(
          List<uint64_t>::cons(
              UINT64_C(1),
              List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil())),
          List<List<uint64_t>>::cons(
              List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()),
              List<List<uint64_t>>::cons(
                  List<uint64_t>::cons(
                      UINT64_C(4),
                      List<uint64_t>::cons(
                          UINT64_C(5),
                          List<uint64_t>::cons(UINT64_C(6),
                                               List<uint64_t>::nil()))),
                  List<List<uint64_t>>::nil()))));
  static inline const List<uint64_t> test_flatten =
      flatten(List<List<uint64_t>>::cons(
          List<uint64_t>::cons(
              UINT64_C(10),
              List<uint64_t>::cons(UINT64_C(20), List<uint64_t>::nil())),
          List<List<uint64_t>>::cons(
              List<uint64_t>::cons(UINT64_C(30), List<uint64_t>::nil()),
              List<List<uint64_t>>::cons(
                  List<uint64_t>::cons(
                      UINT64_C(40), List<uint64_t>::cons(
                                        UINT64_C(50), List<uint64_t>::nil())),
                  List<List<uint64_t>>::nil()))));
};

#endif // INCLUDED_LET_FIX_NO_STDFUN
