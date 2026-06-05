#ifndef INCLUDED_DEEP_PATTERNS
#define INCLUDED_DEEP_PATTERNS

#include <any>
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

  uint64_t length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (a1->length() + 1);
    }
  }
};

struct DeepPatterns {
  static uint64_t
  deep_option(const std::optional<std::optional<std::optional<uint64_t>>> &x);
  static uint64_t deep_pair(const std::pair<std::pair<uint64_t, uint64_t>,
                                            std::pair<uint64_t, uint64_t>> &p);
  static uint64_t list_shape(const List<uint64_t> &l);
  struct outer;
  struct inner;

  struct outer {
    // TYPES
    struct OLeft {
      std::shared_ptr<inner> a0;
    };

    struct ORight {
      uint64_t a0;
    };

    using variant_t = std::variant<OLeft, ORight>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    outer() {}

    explicit outer(OLeft _v) : v_(std::move(_v)) {}

    explicit outer(ORight _v) : v_(std::move(_v)) {}

    static outer oleft(inner a0) {
      return outer(OLeft{std::make_shared<inner>(std::move(a0))});
    }

    static outer oright(uint64_t a0) { return outer(ORight{a0}); }

    // MANIPULATORS
    ~outer() {
      std::vector<std::any> _stack = {};
      auto _drain_self = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<OLeft>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
        }
      };
      _drain_self(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (auto *_sp = std::any_cast<std::shared_ptr<outer>>(&_cur)) {
          if (*_sp && (*_sp).use_count() == 1) {
            _drain_self((*_sp)->v_mut());
          }
        } else {
          if (auto *_sp = std::any_cast<std::shared_ptr<inner>>(&_cur)) {
            if (*_sp && (*_sp).use_count() == 1) {
              auto &_pv = (*_sp)->v_mut();
            }
          }
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  struct inner {
    // TYPES
    struct ILeft {
      uint64_t a0;
    };

    struct IRight {
      bool a0;
    };

    using variant_t = std::variant<ILeft, IRight>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    inner() {}

    explicit inner(ILeft _v) : v_(std::move(_v)) {}

    explicit inner(IRight _v) : v_(std::move(_v)) {}

    static inner ileft(uint64_t a0) { return inner(ILeft{a0}); }

    static inner iright(bool a0) { return inner(IRight{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, inner &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &>
  static T1 outer_rect(F0 &&f, F1 &&f0, const outer &o) {
    if (std::holds_alternative<typename outer::OLeft>(o.v())) {
      const auto &[a0] = std::get<typename outer::OLeft>(o.v());
      return f(*a0);
    } else {
      const auto &[a0] = std::get<typename outer::ORight>(o.v());
      return f0(a0);
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, inner &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &>
  static T1 outer_rec(F0 &&f, F1 &&f0, const outer &o) {
    if (std::holds_alternative<typename outer::OLeft>(o.v())) {
      const auto &[a0] = std::get<typename outer::OLeft>(o.v());
      return f(*a0);
    } else {
      const auto &[a0] = std::get<typename outer::ORight>(o.v());
      return f0(a0);
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, bool &>
  static T1 inner_rect(F0 &&f, F1 &&f0, const inner &i) {
    if (std::holds_alternative<typename inner::ILeft>(i.v())) {
      const auto &[a0] = std::get<typename inner::ILeft>(i.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename inner::IRight>(i.v());
      return f0(a0);
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, bool &>
  static T1 inner_rec(F0 &&f, F1 &&f0, const inner &i) {
    if (std::holds_alternative<typename inner::ILeft>(i.v())) {
      const auto &[a0] = std::get<typename inner::ILeft>(i.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename inner::IRight>(i.v());
      return f0(a0);
    }
  }

  static uint64_t deep_sum(const outer &o);
  static uint64_t
  complex_match(const std::optional<std::pair<uint64_t, List<uint64_t>>> &x);
  static uint64_t guarded_match(const std::pair<uint64_t, uint64_t> &p);

  template <typename A, typename B> struct pair {
    // DATA
    A a0;
    B a1;

    // ACCESSORS
    pair<A, B> clone() const { return {a0, a1}; }

    // CREATORS
    static pair<A, B> pair0(A a0, B a1) {
      return {std::move(a0), std::move(a1)};
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &, B &>
    T1 pair_rec(F0 &&f) const {
      const auto &[a0, a1] = *this;
      return f(a0, a1);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &, B &>
    T1 pair_rect(F0 &&f) const {
      const auto &[a0, a1] = *this;
      return f(a0, a1);
    }
  };

  template <typename A> struct mylist {
    // TYPES
    struct Nil {};

    struct Cons {
      A a0;
      std::shared_ptr<mylist<A>> a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Nil _v) : v_(_v) {}

    explicit mylist(Cons _v) : v_(std::move(_v)) {}

    template <typename _U> explicit mylist(const mylist<_U> &_other) {
      if (std::holds_alternative<typename mylist<_U>::Nil>(_other.v())) {
        this->v_ = Nil{};
      } else {
        const auto &[a0, a1] = std::get<typename mylist<_U>::Cons>(_other.v());
        this->v_ = Cons{
            [&]() -> A {
              if constexpr (std::is_same_v<_U, std::any>) {
                if (a0.type() == typeid(A))
                  return std::any_cast<A>(a0);
                if constexpr (requires {
                                typename A::first_type;
                                typename A::second_type;
                              }) {
                  const auto &[_k, _v] =
                      std::any_cast<std::pair<std::any, std::any>>(a0);
                  return A{
                      [&]() -> typename A::first_type {
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
                return std::any_cast<A>(a0);
              } else
                return A(a0);
            }(),
            a1 ? std::make_shared<mylist<A>>(*a1) : nullptr};
      }
    }

    static mylist<A> nil() { return mylist(Nil{}); }

    static mylist<A> cons(A a0, mylist<A> a1) {
      return mylist(
          Cons{std::move(a0), std::make_shared<mylist<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      std::vector<std::shared_ptr<mylist<A>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
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

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, mylist<A> &, T1 &>
    T1 mylist_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename mylist<A>::Nil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Cons>(this->v());
        return f0(a0, *a1, a1->template mylist_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, mylist<A> &, T1 &>
    T1 mylist_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename mylist<A>::Nil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Cons>(this->v());
        return f0(a0, *a1, a1->template mylist_rect<T1>(f, f0));
      }
    }
  };

  static uint64_t match_pair_list(const mylist<pair<uint64_t, uint64_t>> &l);
  static uint64_t match_two(const mylist<uint64_t> &l);
  static uint64_t match_triple(const mylist<mylist<mylist<uint64_t>>> &l);
  static uint64_t deep_wildcard(
      const pair<pair<uint64_t, uint64_t>, pair<uint64_t, uint64_t>> &p);
  static inline const uint64_t test_deep_some =
      deep_option(std::make_optional<std::optional<std::optional<uint64_t>>>(
          std::make_optional<std::optional<uint64_t>>(
              std::make_optional<uint64_t>(UINT64_C(42)))));
  static inline const uint64_t test_deep_none =
      deep_option(std::make_optional<std::optional<std::optional<uint64_t>>>(
          std::make_optional<std::optional<uint64_t>>(
              std::optional<uint64_t>())));
  static inline const uint64_t test_deep_pair =
      deep_pair(std::make_pair(std::make_pair(UINT64_C(1), UINT64_C(2)),
                               std::make_pair(UINT64_C(3), UINT64_C(4))));
  static inline const uint64_t test_shape_3 = list_shape(List<uint64_t>::cons(
      UINT64_C(10),
      List<uint64_t>::cons(
          UINT64_C(20),
          List<uint64_t>::cons(UINT64_C(30), List<uint64_t>::nil()))));
  static inline const uint64_t test_shape_long =
      list_shape(List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(
              UINT64_C(2),
              List<uint64_t>::cons(
                  UINT64_C(3),
                  List<uint64_t>::cons(
                      UINT64_C(4),
                      List<uint64_t>::cons(
                          UINT64_C(5),
                          List<uint64_t>::cons(UINT64_C(6),
                                               List<uint64_t>::nil())))))));
  static inline const uint64_t test_deep_sum =
      deep_sum(outer::oleft(inner::ileft(UINT64_C(77))));
  static inline const uint64_t test_complex = complex_match(
      std::make_optional<std::pair<uint64_t, List<uint64_t>>>(std::make_pair(
          UINT64_C(5),
          List<uint64_t>::cons(
              UINT64_C(10),
              List<uint64_t>::cons(
                  UINT64_C(20), List<uint64_t>::cons(
                                    UINT64_C(30), List<uint64_t>::nil()))))));
  static inline const uint64_t test_guarded =
      guarded_match(std::make_pair(UINT64_C(3), UINT64_C(7)));
  static inline const uint64_t test_pair_list =
      match_pair_list(mylist<pair<uint64_t, uint64_t>>::cons(
          pair<uint64_t, uint64_t>::pair0(UINT64_C(5), UINT64_C(3)),
          mylist<pair<uint64_t, uint64_t>>::nil()));
  static inline const uint64_t test_two_one =
      match_two(mylist<uint64_t>::cons(UINT64_C(7), mylist<uint64_t>::nil()));
  static inline const uint64_t test_two_many = match_two(mylist<uint64_t>::cons(
      UINT64_C(7),
      mylist<uint64_t>::cons(UINT64_C(8), mylist<uint64_t>::nil())));
  static inline const uint64_t test_triple =
      match_triple(mylist<mylist<mylist<uint64_t>>>::cons(
          mylist<mylist<uint64_t>>::cons(
              mylist<uint64_t>::cons(UINT64_C(9), mylist<uint64_t>::nil()),
              mylist<mylist<uint64_t>>::nil()),
          mylist<mylist<mylist<uint64_t>>>::nil()));
  static inline const uint64_t test_wildcard = deep_wildcard(
      pair<pair<uint64_t, uint64_t>, pair<uint64_t, uint64_t>>::pair0(
          pair<uint64_t, uint64_t>::pair0(UINT64_C(1), UINT64_C(2)),
          pair<uint64_t, uint64_t>::pair0(UINT64_C(3), UINT64_C(4))));
  static inline const uint64_t t =
      ((((((((((((test_deep_some + test_deep_none) + test_deep_pair) +
                test_shape_3) +
               test_shape_long) +
              test_deep_sum) +
             test_complex) +
            test_guarded) +
           test_pair_list) +
          test_two_one) +
         test_two_many) +
        test_triple) +
       test_wildcard);
};

#endif // INCLUDED_DEEP_PATTERNS
