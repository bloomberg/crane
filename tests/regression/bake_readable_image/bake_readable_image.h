#pragma once

#include <conslist.h>
#include <crane_string.h>
#include <cstdint>
#include <string>
#include <string_view>
#include <type_traits>
#include <utility>
#include <variant>

#include "crane_bake.h"
extern const crane::bake::image crane_baked_forest_ac321626c191;
extern const crane::bake::image crane_baked_numbers_f28e8ab85c63;
extern const crane::bake::image crane_baked_odd_strings_48cd7c9a95e8;

struct ListDef {
  template <typename T1, typename T2, typename F0>
  static crane::list<T2> map(F0 &&f, const crane::list<T1> &l);
};

struct List {
  template <typename T1, typename T2, typename F0>
  static T1 fold_left(F0 &&f, const crane::list<T2> &l, T1 a0);
};

struct BakeReadableImage {
  enum class Color { RED, GREEN, BLUE };

  template <typename T1> static T1 color_rect(T1 f, T1 f0, T1 f1, Color c) {
    switch (c) {
    case Color::RED: {
      return f;
    }
    case Color::GREEN: {
      return f0;
    }
    case Color::BLUE: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 color_rec(T1 f, T1 f0, T1 f1, Color c) {
    return color_rect<T1>(std::move(f), std::move(f0), std::move(f1), c);
  }

  struct rose {
    // TYPES
    struct Rose0 {
      std::string label;
      Color shade;
      crane::list<crane::box<rose>> kids;
    };

    using variant_t = std::variant<Rose0>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    rose() {}

    explicit rose(Rose0 _v) : v_(std::move(_v)) {}

    static rose rose0(std::string label, Color shade,
                      crane::list<crane::box<rose>> kids) {
      return rose(Rose0{std::move(label), shade, std::move(kids)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const std::string &, const Color &,
                                   const crane::list<crane::box<rose>> &>
  static T1 rose_rect(F0 &&f, const rose &r) {
    const auto &[label0, shade0, kids0] = std::get<typename rose::Rose0>(r.v());
    return f(label0, shade0, kids0);
  }

  template <typename T1, typename F0>
  static T1 rose_rec(F0 &&f, const rose &r) {
    return rose_rect<T1>(f, r);
  }

  static rose leaf(const std::string &s, Color c);
  /// shared is all of "a"'s children and the tail of "d"'s.
  static inline const crane::list<crane::box<rose>> shared = crane::cons(
      leaf("b", Color::GREEN),
      crane::cons(leaf("c", Color::BLUE), crane::list<crane::box<rose>>{}));
  static inline const crane::list<crane::box<rose>> forest =
      crane::bake::read<crane::list<crane::box<rose>>>(
          crane_baked_forest_ac321626c191);
  static inline const crane::list<std::string> odd_strings =
      crane::bake::read<crane::list<std::string>>(
          crane_baked_odd_strings_48cd7c9a95e8);
  static inline const std::pair<int64_t, double> numbers =
      crane::bake::read<std::pair<int64_t, double>>(
          crane_baked_numbers_f28e8ab85c63);
  static std::string labels(const rose &r);
  static inline const std::string all_labels =
      List::template fold_left<std::string, rose>(
          [](const std::string &acc,
             const rose &r) { return crane::string_capped(acc + labels(r)); },
          forest,
          "");
  static inline const uint64_t blue_count = []() {
    return []() {
      auto count_impl = [](auto &_self_count, rose r) -> uint64_t {
        auto &[_, shade, kids] = std::get<typename rose::Rose0>(r.v_mut());
        return ([&]() {
          switch (std::move(shade)) {
          case Color::BLUE: {
            return UINT64_C(1);
          }
          default: {
            return UINT64_C(0);
          }
          }
        }() +
                List::template fold_left<uint64_t, rose>(
                    [=](uint64_t n,
                        const rose &k) {
                      return (n + _self_count(_self_count, k));
                    },
                    std::move(kids),
                    UINT64_C(0)));
      };
      auto count =
          [=, count_impl = std::move(count_impl)](rose r) -> uint64_t {
            return count_impl(count_impl, std::move(r));
          };
      return List::template fold_left<uint64_t, rose>(
          [=, count = std::move(count)](uint64_t n,
                                        const rose &r) {
            return (n + count(r));
          },
          forest,
          UINT64_C(0));
    }();
  }();
  static inline const crane::list<int64_t> string_lengths =
      ListDef::template map<std::string, int64_t>(
          [](std::string _x0) -> int64_t {
            return static_cast<int64_t>(_x0.size());
          },
          odd_strings);
};

template <typename T1, typename T2, typename F0>
crane::list<T2> ListDef::map(F0 &&f, const crane::list<T1> &l) {
  if (l.empty()) {
    return crane::list<T2>{};
  } else {
    const T1 &a = l.front();
    auto l0 = l.tail();
    return crane::cons(f(a), ListDef::template map<T1, T2>(f, std::move(l0)));
  }
}

template <typename T1, typename T2, typename F0>
T1 List::fold_left(F0 &&f, const crane::list<T2> &l, T1 a0) {
  if (l.empty()) {
    return a0;
  } else {
    const T2 &b = l.front();
    auto l0 = l.tail();
    return List::template fold_left<T1, T2>(f, std::move(l0),
                                            f(std::move(a0), b));
  }
}
