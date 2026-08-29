#ifndef INCLUDED_FIX_MOVE_CAPTURE
#define INCLUDED_FIX_MOVE_CAPTURE

#include "small_vector.h"
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct FixMoveCapture {
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
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &, mylist &, T1 &>
  static T1 mylist_rect(T1 f0, F1 &&f1, const mylist &m) {
    if (std::holds_alternative<typename mylist::Mynil>(m.v())) {
      return f0;
    } else {
      const auto &[a0, a1] = std::get<typename mylist::Mycons>(m.v());
      return f1(a0, *a1, mylist_rect<T1>(f0, f1, *a1));
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &, mylist &, T1 &>
  static T1 mylist_rec(T1 f0, F1 &&f1, const mylist &m) {
    if (std::holds_alternative<typename mylist::Mynil>(m.v())) {
      return f0;
    } else {
      const auto &[a0, a1] = std::get<typename mylist::Mycons>(m.v());
      return f1(a0, *a1, mylist_rec<T1>(f0, f1, *a1));
    }
  }

  static uint64_t length(const mylist &l);
  static uint64_t sum(const mylist &l);
  static mylist dup_head(mylist l);
  static uint64_t f(mylist l);
  static inline const uint64_t test1 = f(mylist::mycons(
      UINT64_C(10),
      mylist::mycons(UINT64_C(20),
                     mylist::mycons(UINT64_C(30), mylist::mynil()))));
  static uint64_t f2(mylist l);
  static inline const uint64_t test2 = f2(mylist::mycons(
      UINT64_C(5), mylist::mycons(UINT64_C(15), mylist::mynil())));
};

#endif // INCLUDED_FIX_MOVE_CAPTURE
