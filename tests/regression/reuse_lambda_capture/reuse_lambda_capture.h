#ifndef INCLUDED_REUSE_LAMBDA_CAPTURE
#define INCLUDED_REUSE_LAMBDA_CAPTURE

#include "crane_fn.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct ReuseLambdaCapture {
  /// Define mycons FIRST so it gets variant index 0.
  /// The reuse optimization picks List.hd reuse_candidates, i.e. the
  /// first constructor branch with a matching tail constructor.
  /// By putting mycons at index 0, reuse fires on the mycons branch.
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
      auto _next = [&](variant_t &_v) -> std::shared_ptr<mylist> {
        if (auto *_alt = std::get_if<Mycons>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      std::shared_ptr<mylist> _cur = _next(v_mut());
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

  template <typename T1, typename F0>
  static T1 mylist_rect(F0 &&f, T1 f0, const mylist &m) {
    if (std::holds_alternative<typename mylist::Mycons>(m.v())) {
      const auto &[a0, a1] = std::get<typename mylist::Mycons>(m.v());
      return f(a0, *a1, mylist_rect<T1>(f, std::move(f0), *a1));
    } else {
      return f0;
    }
  }

  template <typename T1, typename F0>
  static T1 mylist_rec(F0 &&f, T1 f0, const mylist &m) {
    if (std::holds_alternative<typename mylist::Mycons>(m.v())) {
      const auto &[a0, a1] = std::get<typename mylist::Mycons>(m.v());
      return f(a0, *a1, mylist_rec<T1>(f, std::move(f0), *a1));
    } else {
      return f0;
    }
  }

  static uint64_t length(const mylist &l);

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, const uint64_t &>
  static mylist map(F0 &&f, const mylist &l) {
    if (std::holds_alternative<typename mylist::Mycons>(l.v())) {
      const auto &[a0, a1] = std::get<typename mylist::Mycons>(l.v());
      return mylist::mycons(f(a0), map(f, *a1));
    } else {
      return mylist::mynil();
    }
  }

  /// BUG: reuse fires, then length l inside the lambda accesses
  /// moved-from fields of l.
  ///
  /// The reuse path does:
  /// auto x  = std::move(_rf.d_a0);
  /// auto xs = std::move(_rf.d_a1);   // _rf.d_a1 is now null
  /// _rf.d_a0 = x + 1;
  /// _rf.d_a1 = map(lambda, xs);      // lambda calls length(l)
  /// // l is the same object as _rf
  /// // l.d_a1 is null -> crash
  /// return _rf;
  static mylist add_length_to_each(mylist l, bool b);
  static constexpr uint64_t test1 = UINT64_C(3);
  /// Expected: map adds length(original list)=3 to each tail element.
  /// Original: 10, 20, 30
  /// Result:   11, 23, 33  (h+1=11, 20+3=23, 30+3=33)
  /// Length = 3
  static constexpr uint64_t test2 = UINT64_C(6);
};

#endif // INCLUDED_REUSE_LAMBDA_CAPTURE
