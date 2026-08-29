#ifndef INCLUDED_FIX_DIRECT_RETURN
#define INCLUDED_FIX_DIRECT_RETURN

#include <functional>
#include <type_traits>

struct FixDirectReturn {
  template <typename F1>
    requires std::is_invocable_r_v<uint64_t, F1 &, uint64_t &>
  static uint64_t make_callback(uint64_t base, F1 &&_x0) {
    return [=]() mutable {
      auto add_impl = [=](auto &_self_add, uint64_t x) mutable -> uint64_t {
        if (x <= 0) {
          return base;
        } else {
          uint64_t x_ = x - 1;
          return (_self_add(_self_add, x_) + 1);
        }
      };
      auto add = [=](uint64_t x) mutable -> uint64_t {
        return add_impl(add_impl, x);
      };
      return [=](std::function<uint64_t(uint64_t)> g) mutable {
        return (g(add(UINT64_C(0))) + add(UINT64_C(1)));
      };
    }()(_x0);
  }

  static inline const uint64_t test1 =
      make_callback(UINT64_C(42), [](uint64_t x) { return x; });
  static inline const uint64_t test2 =
      make_callback(UINT64_C(10), [](uint64_t x) { return (x * UINT64_C(2)); });
  static inline const uint64_t test3 = []() {
    return []() {
      std::function<uint64_t(std::function<uint64_t(uint64_t)>)> cb1 =
          [](std::function<uint64_t(uint64_t)> _x0) -> uint64_t {
        return make_callback(UINT64_C(5), _x0);
      };
      std::function<uint64_t(std::function<uint64_t(uint64_t)>)> cb2 =
          [](std::function<uint64_t(uint64_t)> _x0) -> uint64_t {
        return make_callback(UINT64_C(100), _x0);
      };
      return cb1(
          [=](uint64_t) mutable { return cb2([](uint64_t x) { return x; }); });
    }();
  }();
};

#endif // INCLUDED_FIX_DIRECT_RETURN
