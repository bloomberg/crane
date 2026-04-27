#ifndef INCLUDED_RECORD_USE_AFTER_MOVE
#define INCLUDED_RECORD_USE_AFTER_MOVE

#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct RecordUseAfterMove {
  struct box {
    unsigned int payload;
    bool enabled;

    __attribute__((pure)) box *operator->() { return this; }

    __attribute__((pure)) const box *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) box clone() const {
      return box{[](auto &&__v) -> unsigned int {
                   if constexpr (
                       requires { __v ? 0 : 0; } && requires { *__v; } &&
                       requires { __v->clone(); } && requires { __v.get(); }) {
                     using _E = std::remove_cvref_t<decltype(*__v)>;
                     return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
                   } else if constexpr (requires { __v.clone(); }) {
                     return __v.clone();
                   } else {
                     return __v;
                   }
                 }((*this).payload),
                 [](auto &&__v) -> bool {
                   if constexpr (
                       requires { __v ? 0 : 0; } && requires { *__v; } &&
                       requires { __v->clone(); } && requires { __v.get(); }) {
                     using _E = std::remove_cvref_t<decltype(*__v)>;
                     return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
                   } else if constexpr (requires { __v.clone(); }) {
                     return __v.clone();
                   } else {
                     return __v;
                   }
                 }((*this).enabled)};
    }
  };

  __attribute__((pure)) static box clone_box(const box &b);
  __attribute__((pure)) static box keep_box(box b);
  __attribute__((pure)) static unsigned int use_box(const box &b);
  static inline const box initial_box = box{41u, true};
  /// BUG: The same shared_ptr local b is moved into multiple call sites.
  /// After the first std::move(b), subsequent uses dereference a
  /// moved-from shared_ptr, causing a segfault.
  static inline const box problematic = []() {
    box b = keep_box(initial_box);
    box b1 = clone_box(b);
    box b2 = clone_box(b);
    if (keep_box(b).enabled) {
      if (b.enabled) {
        return b2;
      } else {
        return b1;
      }
    } else {
      return b1;
    }
  }();
  /// Simple case: same record used twice in let bindings.
  static inline const unsigned int double_let = []() {
    unsigned int x = initial_box.payload;
    unsigned int y = initial_box.payload;
    return (x + y);
  }();
  /// Record passed to two different functions.
  static inline const unsigned int two_consumers = []() {
    unsigned int p = use_box(initial_box);
    unsigned int q = use_box(initial_box);
    return (p + q);
  }();
};

#endif // INCLUDED_RECORD_USE_AFTER_MOVE
