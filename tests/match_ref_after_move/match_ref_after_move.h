#ifndef INCLUDED_MATCH_REF_AFTER_MOVE
#define INCLUDED_MATCH_REF_AFTER_MOVE

#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct MatchRefAfterMove {
  template <typename A> struct mylist {
    // TYPES
    struct Mynil {};

    struct Mycons {
      A a0;
      std::shared_ptr<mylist<A>> a1;
    };

    using variant_t = std::variant<Mynil, Mycons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Mynil _v) : v_(_v) {}

    explicit mylist(Mycons _v) : v_(std::move(_v)) {}

    template <typename _U> mylist(const mylist<_U> &_other) {
      if (std::holds_alternative<typename mylist<_U>::Mynil>(_other.v())) {
        this->v_ = Mynil{};
      } else {
        const auto &[a0, a1] =
            std::get<typename mylist<_U>::Mycons>(_other.v());
        this->v_ = Mycons{
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

    static mylist<A> mynil() { return mylist<A>(Mynil{}); }

    static mylist<A> mycons(A a0, mylist<A> a1) {
      return mylist<A>(
          Mycons{std::move(a0), std::make_shared<mylist<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      crane::small_vector<std::shared_ptr<mylist<A>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Mycons>(&_v)) {
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
          std::atomic_thread_fence(std::memory_order_acquire);
          _drain(_cur->v_mut());
        }
      }
    }

    mylist(const mylist &) = default;
    mylist &operator=(const mylist &) = default;
    mylist(mylist &&) noexcept = default;
    mylist &operator=(mylist &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t mylist_length() const {
      if (std::holds_alternative<typename mylist<A>::Mynil>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(this->v());
        return (UINT64_C(1) + a1->mylist_length());
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, mylist<A> &, T1 &>
    T1 mylist_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename mylist<A>::Mynil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(this->v());
        return f0(a0, *a1, a1->template mylist_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, mylist<A> &, T1 &>
    T1 mylist_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename mylist<A>::Mynil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(this->v());
        return f0(a0, *a1, a1->template mylist_rect<T1>(f, f0));
      }
    }
  };

  template <typename A, typename B> struct mypair {
    // DATA
    A a0;
    B a1;

    // ACCESSORS
    mypair<A, B> clone() const { return {a0, a1}; }

    // CREATORS
    static mypair<A, B> mkpair(A a0, B a1) {
      return {std::move(a0), std::move(a1)};
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &, B &>
    T1 mypair_rec(F0 &&f) const {
      const auto &[a0, a1] = *this;
      return f(a0, a1);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &, B &>
    T1 mypair_rect(F0 &&f) const {
      const auto &[a0, a1] = *this;
      return f(a0, a1);
    }
  };

  static mypair<uint64_t, uint64_t>
  head_and_tail_length(const mylist<uint64_t> &l);
  static uint64_t nested_match_probe(const mylist<uint64_t> &l);
  static mypair<uint64_t, mylist<uint64_t>>
  match_into_pair(const mylist<uint64_t> &l);
  static mypair<uint64_t, mylist<uint64_t>>
  double_match(const mylist<uint64_t> &l);
  static uint64_t mylist_sum(const mylist<uint64_t> &l);
  static inline const uint64_t test1 = []() {
    const auto &_sv0 = head_and_tail_length(mylist<uint64_t>::mycons(
        UINT64_C(10),
        mylist<uint64_t>::mycons(
            UINT64_C(20), mylist<uint64_t>::mycons(
                              UINT64_C(30), mylist<uint64_t>::mynil()))));
    const auto &[a00, a10] = _sv0;
    return (a00 + a10);
  }();
  static inline const uint64_t test2 =
      nested_match_probe(mylist<uint64_t>::mycons(
          UINT64_C(10),
          mylist<uint64_t>::mycons(
              UINT64_C(20), mylist<uint64_t>::mycons(
                                UINT64_C(30), mylist<uint64_t>::mynil()))));
  static inline const uint64_t test3 = []() {
    const auto &_sv1 = match_into_pair(mylist<uint64_t>::mycons(
        UINT64_C(5),
        mylist<uint64_t>::mycons(UINT64_C(10), mylist<uint64_t>::mynil())));
    const auto &[a01, a11] = _sv1;
    return (a01 + mylist_sum(a11));
  }();
  static inline const uint64_t test4 = []() {
    const auto &_sv2 = double_match(mylist<uint64_t>::mycons(
        UINT64_C(7),
        mylist<uint64_t>::mycons(
            UINT64_C(8),
            mylist<uint64_t>::mycons(UINT64_C(9), mylist<uint64_t>::mynil()))));
    const auto &[a02, a12] = _sv2;
    return (a02 + mylist_sum(a12));
  }();

  template <typename F1>
    requires std::is_invocable_r_v<uint64_t, F1 &, uint64_t &, uint64_t &>
  static uint64_t match_with_cont(const mylist<uint64_t> &l, F1 &&k) {
    if (std::holds_alternative<typename mylist<uint64_t>::Mynil>(l.v())) {
      return k(UINT64_C(0), UINT64_C(0));
    } else {
      const auto &[a0, a1] = std::get<typename mylist<uint64_t>::Mycons>(l.v());
      return k(a0, a1->mylist_length());
    }
  }

  static inline const uint64_t test5 = match_with_cont(
      mylist<uint64_t>::mycons(
          UINT64_C(100),
          mylist<uint64_t>::mycons(
              UINT64_C(200), mylist<uint64_t>::mycons(
                                 UINT64_C(300), mylist<uint64_t>::mynil()))),
      [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); });

  template <typename A, typename B> struct either {
    // TYPES
    struct Left {
      A a0;
    };

    struct Right {
      B a0;
    };

    using variant_t = std::variant<Left, Right>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    either() {}

    explicit either(Left _v) : v_(std::move(_v)) {}

    explicit either(Right _v) : v_(std::move(_v)) {}

    template <typename _U0, typename _U1>
    either(const either<_U0, _U1> &_other) {
      if (std::holds_alternative<typename either<_U0, _U1>::Left>(_other.v())) {
        const auto &[a0] =
            std::get<typename either<_U0, _U1>::Left>(_other.v());
        this->v_ = Left{[&]() -> A {
          if constexpr (std::is_same_v<_U0, std::any>) {
            if (a0.type() == typeid(A))
              return std::any_cast<A>(a0);
            if constexpr (requires {
                            typename A::first_type;
                            typename A::second_type;
                          }) {
              const auto &[_k, _v] =
                  std::any_cast<std::pair<std::any, std::any>>(a0);
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
            return std::any_cast<A>(a0);
          } else
            return A(a0);
        }()};
      } else {
        const auto &[a0] =
            std::get<typename either<_U0, _U1>::Right>(_other.v());
        this->v_ = Right{[&]() -> B {
          if constexpr (std::is_same_v<_U1, std::any>) {
            if (a0.type() == typeid(B))
              return std::any_cast<B>(a0);
            if constexpr (requires {
                            typename B::first_type;
                            typename B::second_type;
                          }) {
              const auto &[_k, _v] =
                  std::any_cast<std::pair<std::any, std::any>>(a0);
              return B{[&]() -> typename B::first_type {
                         if constexpr (std::is_same_v<typename B::first_type,
                                                      std::any>)
                           return _k;
                         else
                           return std::any_cast<typename B::first_type>(_k);
                       }(),
                       [&]() -> typename B::second_type {
                         if constexpr (std::is_same_v<typename B::second_type,
                                                      std::any>)
                           return _v;
                         else
                           return std::any_cast<typename B::second_type>(_v);
                       }()};
            }
            return std::any_cast<B>(a0);
          } else
            return B(a0);
        }()};
      }
    }

    static either<A, B> left(A a0) { return either<A, B>(Left{std::move(a0)}); }

    static either<A, B> right(B a0) {
      return either<A, B>(Right{std::move(a0)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, A &> &&
               std::is_invocable_r_v<T1, F1 &, B &>
    T1 either_rec(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename either<A, B>::Left>(this->v())) {
        const auto &[a0] = std::get<typename either<A, B>::Left>(this->v());
        return f(a0);
      } else {
        const auto &[a0] = std::get<typename either<A, B>::Right>(this->v());
        return f0(a0);
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, A &> &&
               std::is_invocable_r_v<T1, F1 &, B &>
    T1 either_rect(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename either<A, B>::Left>(this->v())) {
        const auto &[a0] = std::get<typename either<A, B>::Left>(this->v());
        return f(a0);
      } else {
        const auto &[a0] = std::get<typename either<A, B>::Right>(this->v());
        return f0(a0);
      }
    }
  };

  static uint64_t
  complex_match(const either<mylist<uint64_t>, mylist<uint64_t>> &e);
  static inline const uint64_t test6 =
      complex_match(either<mylist<uint64_t>, mylist<uint64_t>>::right(
          mylist<uint64_t>::mycons(
              UINT64_C(50), mylist<uint64_t>::mycons(
                                UINT64_C(60), mylist<uint64_t>::mynil()))));
};

#endif // INCLUDED_MATCH_REF_AFTER_MOVE
