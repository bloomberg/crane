#ifndef INCLUDED_FIX_SHARED_PTR_FIELD
#define INCLUDED_FIX_SHARED_PTR_FIELD

#include "small_vector.h"
#include <atomic>
#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

struct FixSharedPtrField {
  struct mylist {
    // TYPES
    struct Mynil {};

    struct Mycons {
      uint64_t a0;
      std::shared_ptr<mylist> a1;
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

    static mylist mynil() { return mylist(Mynil{}); }

    static mylist mycons(uint64_t a0, mylist a1) {
      return mylist(Mycons{a0, std::make_shared<mylist>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      crane::small_vector<std::shared_ptr<mylist>> _stack = {};
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

    std::optional<std::function<uint64_t(uint64_t)>> make_list_fn() const {
      if (std::holds_alternative<typename mylist::Mynil>(this->v())) {
        return std::optional<std::function<uint64_t(uint64_t)>>();
      } else {
        const auto &[a0, a1] = std::get<typename mylist::Mycons>(this->v());
        const mylist &a1_value = *a1;
        auto compute_impl = [=](auto &_self_compute,
                                uint64_t x) mutable -> uint64_t {
          if (x <= 0) {
            return (a0 + a1_value.mylist_sum());
          } else {
            uint64_t x_ = x - 1;
            return (UINT64_C(1) + _self_compute(_self_compute, x_));
          }
        };
        auto compute = [=](uint64_t x) mutable -> uint64_t {
          return compute_impl(compute_impl, x);
        };
        return std::make_optional<std::function<uint64_t(uint64_t)>>(compute);
      }
    }

    uint64_t mylist_length() const {
      if (std::holds_alternative<typename mylist::Mynil>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename mylist::Mycons>(this->v());
        return (UINT64_C(1) + a1->mylist_length());
      }
    }

    uint64_t mylist_sum() const {
      if (std::holds_alternative<typename mylist::Mynil>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename mylist::Mycons>(this->v());
        return (a0 + a1->mylist_sum());
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, uint64_t &, mylist &, T1 &>
    T1 mylist_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename mylist::Mynil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename mylist::Mycons>(this->v());
        return f0(a0, *a1, a1->template mylist_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, uint64_t &, mylist &, T1 &>
    T1 mylist_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename mylist::Mynil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename mylist::Mycons>(this->v());
        return f0(a0, *a1, a1->template mylist_rect<T1>(f, f0));
      }
    }
  };

  struct wrapper {
    // DATA
    mylist a0;

    // ACCESSORS
    wrapper clone() const { return {a0}; }

    // CREATORS
    static wrapper wrap(mylist a0) { return {std::move(a0)}; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, mylist &>
  static T1 wrapper_rect(F0 &&f, const wrapper &w) {
    const auto &[a0] = w;
    return f(a0);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, mylist &>
  static T1 wrapper_rec(F0 &&f, const wrapper &w) {
    const auto &[a0] = w;
    return f(a0);
  }

  static inline const uint64_t test1 = []() -> uint64_t {
    auto _cs = mylist::mycons(UINT64_C(10),
                              mylist::mycons(UINT64_C(20),
                                             mylist::mycons(UINT64_C(30),
                                                            mylist::mynil())))
                   .make_list_fn();
    if (_cs.has_value()) {
      const std::function<uint64_t(uint64_t)> &f = *_cs;
      return f(UINT64_C(5));
    } else {
      return UINT64_C(999);
    }
  }();
  static inline const uint64_t test2 = []() {
    std::optional<std::function<uint64_t(uint64_t)>> opt =
        mylist::mycons(UINT64_C(100),
                       mylist::mycons(UINT64_C(200), mylist::mynil()))
            .make_list_fn();
    uint64_t noise =
        mylist::mycons(
            UINT64_C(1),
            mylist::mycons(UINT64_C(2),
                           mylist::mycons(UINT64_C(3), mylist::mynil())))
            .mylist_sum();
    if (opt.has_value()) {
      const std::function<uint64_t(uint64_t)> &f = *opt;
      return f(UINT64_C(0));
    } else {
      return noise;
    }
  }();
  static inline const uint64_t test3 = []() -> uint64_t {
    auto _cs = mylist::mycons(
                   UINT64_C(5),
                   mylist::mycons(
                       UINT64_C(10),
                       mylist::mycons(
                           UINT64_C(15),
                           mylist::mycons(
                               UINT64_C(20),
                               mylist::mycons(UINT64_C(25), mylist::mynil())))))
                   .make_list_fn();
    if (_cs.has_value()) {
      const std::function<uint64_t(uint64_t)> &f = *_cs;
      return f(UINT64_C(10));
    } else {
      return UINT64_C(999);
    }
  }();
  static wrapper wrap_list(mylist l);
};

#endif // INCLUDED_FIX_SHARED_PTR_FIELD
