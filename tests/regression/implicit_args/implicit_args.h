#ifndef INCLUDED_IMPLICIT_ARGS
#define INCLUDED_IMPLICIT_ARGS

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct ImplicitArgs {
  template <typename T1> static T1 id(T1 x) { return x; }

  template <typename T1, typename T2> static T1 fst_of(T1 x, const T2 &) {
    return x;
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &&>
  static T2 apply(F0 &&f, T1 x0_) {
    return f(std::move(x0_));
  }

  template <typename T1, typename T2, typename T3, typename F0, typename F1>
    requires std::is_invocable_r_v<T3, F0 &, T2> &&
             std::is_invocable_r_v<T2, F1 &, const T1 &>
  static T3 compose(F0 &&g, F1 &&f, const T1 &x) {
    return g(f(x));
  }

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

    template <typename CraneU>
    mylist(const mylist<CraneU> &_other)
        : v_(crane_convert_spine(
              _other, std::shared_ptr<mylist<A>>(nullptr),
              [](const mylist<CraneU> &_cell) -> const mylist<CraneU> * {
                if (std::holds_alternative<typename mylist<CraneU>::Mycons>(
                        _cell.v())) {
                  return std::get<typename mylist<CraneU>::Mycons>(_cell.v())
                      .a1.get();
                } else {
                  return nullptr;
                }
              },
              [&](const mylist<CraneU> &_other,
                  std::shared_ptr<mylist<A>> _below) -> variant_t {
                if (std::holds_alternative<typename mylist<CraneU>::Mynil>(
                        _other.v())) {
                  return Mynil{};
                } else {
                  const auto &[a0, a1] =
                      std::get<typename mylist<CraneU>::Mycons>(_other.v());
                  return Mycons{
                      [&]() -> A {
                        if constexpr (crane_convertible<A, const CraneU &>) {
                          return crane_convert<A>(a0);
                        } else {
                          throw std::logic_error(
                              "unreachable: inactive constructor field at this "
                              "instantiation");
                        }
                      }(),
                      std::move(_below)};
                }
              },
              [](auto &&_alt) {
                return std::make_shared<mylist<A>>(std::move(_alt));
              })) {}

    static mylist<A> mynil() { return mylist<A>(Mynil{}); }

    static mylist<A> mycons(A a0, mylist<A> a1) {
      return mylist<A>(
          Mycons{std::move(a0), std::make_shared<mylist<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<mylist<A>> {
        if (auto *_alt = std::get_if<Mycons>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      std::shared_ptr<mylist<A>> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    mylist(const mylist &) = default;
    mylist &operator=(const mylist &) = default;
    mylist(mylist &&) = default;
    mylist &operator=(mylist &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
  static T2 mylist_rect(T2 f, F1 &&f0, const mylist<T1> &m) {
    if (std::holds_alternative<typename mylist<T1>::Mynil>(m.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename mylist<T1>::Mycons>(m.v());
      return f0(a0, *a1, mylist_rect<T1, T2>(std::move(f), f0, *a1));
    }
  }

  template <typename T1, typename T2, typename F1>
  static T2 mylist_rec(const T2 &f, F1 &&f0, const mylist<T1> &m) {
    return mylist_rect<T1, T2>(f, f0, m);
  }

  template <typename T1> static uint64_t length(const mylist<T1> &l) {
    {
      const mylist<T1> &_lc1_l0 = l;
      uint64_t _lc1_acc = UINT64_C(0);
      uint64_t _lc1_loop_acc = _lc1_acc;
      const mylist<T1> *_lc1_loop_l0 = &_lc1_l0;
      while (true) {
        if (std::holds_alternative<typename mylist<T1>::Mynil>(
                _lc1_loop_l0->v())) {
          return _lc1_loop_acc;
        } else {
          const auto &[a0, a1] =
              std::get<typename mylist<T1>::Mycons>(_lc1_loop_l0->v());
          _lc1_loop_acc = (_lc1_loop_acc + UINT64_C(1));
          _lc1_loop_l0 = crane_raw(a1);
        }
      }
    }
  }

  static constexpr uint64_t explicit_id = UINT64_C(5);
  static constexpr uint64_t explicit_fst = UINT64_C(3);
  static uint64_t add_one(uint64_t x0_);
  static uint64_t double_nat(uint64_t n);
  static uint64_t add_implicit(uint64_t x0_, uint64_t x1_);
  static constexpr uint64_t use_add_implicit = UINT64_C(8);
  static uint64_t scale(uint64_t x0_, uint64_t x1_);
  static constexpr uint64_t use_scale = UINT64_C(21);
  static uint64_t combine(uint64_t a, uint64_t b, uint64_t x);
  static constexpr uint64_t use_combine = UINT64_C(9);

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static uint64_t apply_implicit(F0 &&f, uint64_t x0_) {
    return f(x0_);
  }

  static constexpr uint64_t use_apply_implicit = UINT64_C(6);
  static uint64_t with_base(uint64_t x0_, uint64_t x1_);
  static uint64_t from_zero(uint64_t x0_);
  static uint64_t from_ten(uint64_t x0_);
  static constexpr uint64_t use_from_zero = UINT64_C(5);
  static constexpr uint64_t use_from_ten = UINT64_C(15);

  template <typename T1> static T1 head_or(T1 default0, const mylist<T1> &l) {
    if (std::holds_alternative<typename mylist<T1>::Mynil>(l.v())) {
      return default0;
    } else {
      const auto &[a0, a1] = std::get<typename mylist<T1>::Mycons>(l.v());
      return a0;
    }
  }

  static constexpr uint64_t use_head_empty = UINT64_C(0);
  static constexpr uint64_t use_head_nonempty = UINT64_C(7);
  static uint64_t sum_with_init(uint64_t init, const mylist<uint64_t> &l);
  static constexpr uint64_t use_sum_init = UINT64_C(8);
  static uint64_t nested_implicits(uint64_t a, uint64_t b, uint64_t c);
  static constexpr uint64_t use_nested = UINT64_C(6);
  static uint64_t choose_branch(bool flag, uint64_t t, uint64_t f);
  static constexpr uint64_t use_choose_true = UINT64_C(7);
  static constexpr uint64_t use_choose_false = UINT64_C(3);
  static constexpr uint64_t test_id = UINT64_C(5);
  static constexpr uint64_t test_fst = UINT64_C(3);
  static constexpr uint64_t test_apply = UINT64_C(10);
  static constexpr uint64_t test_compose = UINT64_C(8);
  static constexpr uint64_t test_length = UINT64_C(3);
  static constexpr uint64_t test_explicit_id = UINT64_C(5);
  static constexpr uint64_t test_explicit_fst = UINT64_C(3);
  static constexpr uint64_t test_add_implicit = UINT64_C(8);
  static constexpr uint64_t test_scale = UINT64_C(21);
  static constexpr uint64_t test_combine = UINT64_C(9);
  static constexpr uint64_t test_apply_implicit = UINT64_C(6);
  static constexpr uint64_t test_from_zero = UINT64_C(5);
  static constexpr uint64_t test_from_ten = UINT64_C(15);
  static constexpr uint64_t test_head_empty = UINT64_C(0);
  static constexpr uint64_t test_head_nonempty = UINT64_C(7);
  static constexpr uint64_t test_sum_init = UINT64_C(8);
  static constexpr uint64_t test_nested = UINT64_C(6);
  static constexpr uint64_t test_choose_true = UINT64_C(7);
  static constexpr uint64_t test_choose_false = UINT64_C(3);
};

#endif // INCLUDED_IMPLICIT_ARGS
