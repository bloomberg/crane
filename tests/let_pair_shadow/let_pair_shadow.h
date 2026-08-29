#ifndef INCLUDED_LET_PAIR_SHADOW
#define INCLUDED_LET_PAIR_SHADOW

#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct LetPairShadow {
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
  };

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, mylist<T1> &, T2 &>
  static T2 mylist_rect(T2 f, F1 &&f0, const mylist<T1> &m) {
    if (std::holds_alternative<typename mylist<T1>::Mynil>(m.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename mylist<T1>::Mycons>(m.v());
      return f0(a0, *a1, mylist_rect<T1, T2>(f, f0, *a1));
    }
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, mylist<T1> &, T2 &>
  static T2 mylist_rec(T2 f, F1 &&f0, const mylist<T1> &m) {
    if (std::holds_alternative<typename mylist<T1>::Mynil>(m.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename mylist<T1>::Mycons>(m.v());
      return f0(a0, *a1, mylist_rec<T1, T2>(f, f0, *a1));
    }
  }

  static uint64_t mylist_sum(const mylist<uint64_t> &l);

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<std::pair<T3, T2>, F0 &, T3 &, T1 &>
  static std::pair<mylist<T2>, T3> map_accum(F0 &&f, T3 acc,
                                             const mylist<T1> &l) {
    if (std::holds_alternative<typename mylist<T1>::Mynil>(l.v())) {
      return std::make_pair(mylist<T2>::mynil(), acc);
    } else {
      const auto &[a0, a1] = std::get<typename mylist<T1>::Mycons>(l.v());
      auto [new_acc, y] = f(acc, a0);
      auto [rest, final_acc] = map_accum<T1, T2, T3>(f, new_acc, *a1);
      return std::make_pair(mylist<T2>::mycons(y, std::move(rest)), final_acc);
    }
  }

  static inline const uint64_t test1 = []() -> uint64_t {
    auto [l, acc] = map_accum<uint64_t, uint64_t, uint64_t>(
        [](uint64_t s, uint64_t x) { return std::make_pair((s + x), s); },
        UINT64_C(0),
        mylist<uint64_t>::mycons(
            UINT64_C(10),
            mylist<uint64_t>::mycons(
                UINT64_C(20), mylist<uint64_t>::mycons(
                                  UINT64_C(30), mylist<uint64_t>::mynil()))));
    return (mylist_sum(std::move(l)) + acc);
  }();
  static std::pair<uint64_t, uint64_t> add_pair(uint64_t a, uint64_t b);
  static std::pair<uint64_t, uint64_t> sub_pair(uint64_t a, uint64_t b);
  static uint64_t double_call_destruct(uint64_t a, uint64_t b, uint64_t c,
                                       uint64_t d);
  static inline const uint64_t test2 =
      double_call_destruct(UINT64_C(3), UINT64_C(4), UINT64_C(10), UINT64_C(3));
  static uint64_t triple_call_destruct(uint64_t a, uint64_t b, uint64_t c,
                                       uint64_t d, uint64_t e, uint64_t f);
  static inline const uint64_t test3 =
      triple_call_destruct(UINT64_C(1), UINT64_C(2), UINT64_C(3), UINT64_C(4),
                           UINT64_C(5), UINT64_C(6));
};

#endif // INCLUDED_LET_PAIR_SHADOW
