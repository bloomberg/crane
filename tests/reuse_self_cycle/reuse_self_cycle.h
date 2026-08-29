#ifndef INCLUDED_REUSE_SELF_CYCLE
#define INCLUDED_REUSE_SELF_CYCLE

#include "small_vector.h"
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct ReuseSelfCycle {
  struct mylist {
    // TYPES
    struct Mycons {
      uint64_t a0;
      std::shared_ptr<mylist> a1;
    };

    struct Mynil {};

    using variant_t = std::variant<Mycons, Mynil>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Mycons _v) : v_(std::move(_v)) {}

    explicit mylist(Mynil _v) : v_(_v) {}

    static mylist mycons(uint64_t a0, mylist a1) {
      return mylist(Mycons{a0, std::make_shared<mylist>(std::move(a1))});
    }

    static mylist mynil() { return mylist(Mynil{}); }

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

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, mylist &, T1 &>
  static T1 mylist_rect(F0 &&f, T1 f0, const mylist &m) {
    if (std::holds_alternative<typename mylist::Mycons>(m.v())) {
      const auto &[a0, a1] = std::get<typename mylist::Mycons>(m.v());
      return f(a0, *a1, mylist_rect<T1>(f, f0, *a1));
    } else {
      return f0;
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, mylist &, T1 &>
  static T1 mylist_rec(F0 &&f, T1 f0, const mylist &m) {
    if (std::holds_alternative<typename mylist::Mycons>(m.v())) {
      const auto &[a0, a1] = std::get<typename mylist::Mycons>(m.v());
      return f(a0, *a1, mylist_rec<T1>(f, f0, *a1));
    } else {
      return f0;
    }
  }

  static uint64_t length(const mylist &l);
  static mylist prepend_self(mylist l, bool b);
  static inline const uint64_t test1 = length(prepend_self(
      mylist::mycons(UINT64_C(1), mylist::mycons(UINT64_C(2), mylist::mynil())),
      true));
  static inline const uint64_t test2 =
      length(prepend_self(mylist::mycons(UINT64_C(42), mylist::mynil()), true));
};

#endif // INCLUDED_REUSE_SELF_CYCLE
