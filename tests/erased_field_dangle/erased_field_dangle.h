#ifndef INCLUDED_ERASED_FIELD_DANGLE
#define INCLUDED_ERASED_FIELD_DANGLE

#include "crane_fn.h"
#include <any>
#include <functional>
#include <type_traits>
#include <utility>
#include <variant>

struct ErasedFieldDangle {
  struct box {
    // DATA
    std::any a;

    // ACCESSORS
    box clone() const { return {a}; }

    // CREATORS
    static box mkbox(std::any a) { return {std::move(a)}; }

    template <typename T1> T1 unbox() const {
      const auto &[a] = *this;
      return std::any_cast<T1>(a);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, std::any &>
    T1 box_rec(F0 &&f) const {
      const auto &[a0] = *this;
      return crane_call_erased(f, a0);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, std::any &>
    T1 box_rect(F0 &&f) const {
      const auto &[a0] = *this;
      return crane_call_erased(f, a0);
    }
  };

  static inline const box nested_box =
      box::mkbox(std::make_pair(UINT64_C(42), UINT64_C(58)));
  static inline const uint64_t test_unbox_nested = []() {
    std::pair<uint64_t, uint64_t> p =
        nested_box.template unbox<std::pair<uint64_t, uint64_t>>();
    return (p.first + p.second);
  }();
  static inline const uint64_t test_unbox_compute = []() {
    uint64_t x = box::mkbox(UINT64_C(10)).template unbox<uint64_t>();
    uint64_t y = box::mkbox(UINT64_C(20)).template unbox<uint64_t>();
    return (x + y);
  }();
  static inline const uint64_t test_chain_unbox = []() {
    box b1 = box::mkbox(UINT64_C(5));
    box b2 = box::mkbox(
        (std::any_cast<uint64_t>(std::move(b1).template unbox<uint64_t>()) +
         UINT64_C(10)));
    box b3 = box::mkbox(
        (std::any_cast<uint64_t>(std::move(b2).template unbox<uint64_t>()) +
         UINT64_C(20)));
    return std::move(b3).template unbox<uint64_t>();
  }();
  static inline const uint64_t test_hof_unbox = []() {
    box b = box::mkbox(std::function<uint64_t(uint64_t)>(
        [](uint64_t x) { return (x * UINT64_C(2)); }));
    return std::move(b).template unbox<std::function<uint64_t(uint64_t)>>()(
        UINT64_C(21));
  }();

  struct exists_box {
    // DATA
    std::any a;
    std::function<uint64_t(std::any)> a1;

    // ACCESSORS
    exists_box clone() const { return {a, a1}; }

    // CREATORS
    static exists_box pack(std::any a, std::function<uint64_t(std::any)> a1) {
      return {std::move(a), std::move(a1)};
    }

    uint64_t run_exists() const {
      const auto &[a, a1] = *this;
      return a1(a);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, std::any &,
                                     std::function<uint64_t(std::any)> &>
    T1 exists_box_rec(F0 &&f) const {
      const auto &[a0, a1] = *this;
      return f(a0, a1);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, std::any &,
                                     std::function<uint64_t(std::any)> &>
    T1 exists_box_rect(F0 &&f) const {
      const auto &[a0, a1] = *this;
      return f(a0, a1);
    }
  };

  static inline const uint64_t test_exists = []() {
    exists_box e = exists_box::pack(
        UINT64_C(7),
        std::function<uint64_t(std::any)>([](const std::any &x) -> uint64_t {
          return (std::any_cast<uint64_t>(x) * std::any_cast<uint64_t>(x));
        }));
    return std::move(e).run_exists();
  }();
};

#endif // INCLUDED_ERASED_FIELD_DANGLE
