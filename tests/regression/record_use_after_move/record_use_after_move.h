#ifndef INCLUDED_RECORD_USE_AFTER_MOVE
#define INCLUDED_RECORD_USE_AFTER_MOVE

#include <memory>
#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct RecordUseAfterMove {
  struct box {
    unsigned int payload;
    bool enabled;
  };

  static std::shared_ptr<box> clone_box(std::shared_ptr<box> b);
  static std::shared_ptr<box> keep_box(std::shared_ptr<box> b);
  __attribute__((pure)) static unsigned int
  use_box(const std::shared_ptr<box> &b);
  static inline const std::shared_ptr<box> initial_box = std::make_shared<box>(
      box{41u, true}); /// BUG: The same shared_ptr local b is moved into
                       /// multiple call sites.
  /// After the first std::move(b), subsequent uses dereference a
  /// moved-from shared_ptr, causing a segfault.
  static inline const std::shared_ptr<box> problematic = []() {
    std::shared_ptr<box> b = keep_box(initial_box);
    std::shared_ptr<box> b1 = clone_box(b);
    std::shared_ptr<box> b2 = clone_box(b);
    if (keep_box(b)->enabled) {
      if (std::move(b)->enabled) {
        return std::move(b2);
      } else {
        return std::move(b1);
      }
    } else {
      return std::move(b1);
    }
  }();
  /// Simple case: same record used twice in let bindings.
  static inline const unsigned int double_let = []() {
    unsigned int x = initial_box->payload;
    unsigned int y = initial_box->payload;
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
