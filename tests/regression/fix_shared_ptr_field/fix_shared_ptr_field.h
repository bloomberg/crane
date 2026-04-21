#ifndef INCLUDED_FIX_SHARED_PTR_FIELD
#define INCLUDED_FIX_SHARED_PTR_FIELD

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct FixSharedPtrField {
  /// A value-type inductive with recursive self-reference (shared_ptr).
  /// Pattern matching creates structured bindings to fields including
  /// the shared_ptr tail. A local fixpoint captures these bindings
  /// by &, then escapes through option.
  ///
  /// BUG: The structured bindings h and t from the match are
  /// references into the variant's data. The shared_ptr t is a
  /// reference to the shared_ptr field of the variant. When the
  /// fixpoint escapes, the references dangle. The shared_ptr t
  /// may be destroyed, freeing the tail list. Calling the closure
  /// then dereferences freed heap memory.
  ///
  /// This differs from closure_map_escape: the captured shared_ptr
  /// t is used to traverse heap-allocated data (mylist_sum t),
  /// not just read a POD value. Freeing the shared_ptr causes
  /// a use-after-free on HEAP memory (not just stack).
  struct mylist {
    // TYPES
    struct Mynil {};

    struct Mycons {
      unsigned int d_a0;
      std::shared_ptr<mylist> d_a1;
    };

    using variant_t = std::variant<Mynil, Mycons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit mylist(Mynil _v) : d_v_(_v) {}

    explicit mylist(Mycons _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<mylist> mynil() {
      return std::make_shared<mylist>(Mynil{});
    }

    static std::shared_ptr<mylist> mycons(unsigned int a0,
                                          const std::shared_ptr<mylist> &a1) {
      return std::make_shared<mylist>(Mycons{std::move(a0), a1});
    }

    static std::shared_ptr<mylist> mycons(unsigned int a0,
                                          std::shared_ptr<mylist> &&a1) {
      return std::make_shared<mylist>(Mycons{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// Local fixpoint captures h : nat (POD) and t : shared_ptr<mylist>
    /// from the match on value-type mylist. Both are captured by &.
    __attribute__((pure))
    std::optional<std::function<unsigned int(unsigned int)>>
    make_list_fn() const {
      if (std::holds_alternative<typename mylist::Mynil>(this->v())) {
        return std::optional<std::function<unsigned int(unsigned int)>>();
      } else {
        const auto &[d_a0, d_a1] = std::get<typename mylist::Mycons>(this->v());
        auto compute =
            std::make_shared<std::function<unsigned int(unsigned int)>>();
        *compute = [=](unsigned int x) mutable -> unsigned int {
          if (x <= 0) {
            return (d_a0 + d_a1->mylist_sum());
          } else {
            unsigned int x_ = x - 1;
            return (1u + (*compute)(x_));
          }
        };
        return std::make_optional<std::function<unsigned int(unsigned int)>>(
            *compute);
      }
    }

    __attribute__((pure)) unsigned int mylist_length() const {
      if (std::holds_alternative<typename mylist::Mynil>(this->v())) {
        return 0u;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename mylist::Mycons>(this->v());
        return (1u + d_a1->mylist_length());
      }
    }

    __attribute__((pure)) unsigned int mylist_sum() const {
      if (std::holds_alternative<typename mylist::Mynil>(this->v())) {
        return 0u;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename mylist::Mycons>(this->v());
        return (d_a0 + d_a1->mylist_sum());
      }
    }

    template <typename T1,
              MapsTo<T1, unsigned int, std::shared_ptr<mylist>, T1> F1>
    T1 mylist_rec(const T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename mylist::Mynil>(this->v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename mylist::Mycons>(this->v());
        return f0(d_a0, d_a1, d_a1->template mylist_rec<T1>(f, f0));
      }
    }

    template <typename T1,
              MapsTo<T1, unsigned int, std::shared_ptr<mylist>, T1> F1>
    T1 mylist_rect(const T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename mylist::Mynil>(this->v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename mylist::Mycons>(this->v());
        return f0(d_a0, d_a1, d_a1->template mylist_rect<T1>(f, f0));
      }
    }
  };

  /// A second inductive to prevent methodification of make_list_fn.
  struct wrapper {
    // TYPES
    struct Wrap {
      std::shared_ptr<mylist> d_a0;
    };

    using variant_t = std::variant<Wrap>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit wrapper(Wrap _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<wrapper> wrap(const std::shared_ptr<mylist> &a0) {
      return std::make_shared<wrapper>(Wrap{a0});
    }

    static std::shared_ptr<wrapper> wrap(std::shared_ptr<mylist> &&a0) {
      return std::make_shared<wrapper>(Wrap{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, std::shared_ptr<mylist>> F0>
  static T1 wrapper_rect(F0 &&f, const std::shared_ptr<wrapper> &w) {
    const auto &[d_a0] = std::get<typename wrapper::Wrap>(w->v());
    return f(d_a0);
  }

  template <typename T1, MapsTo<T1, std::shared_ptr<mylist>> F0>
  static T1 wrapper_rec(F0 &&f, const std::shared_ptr<wrapper> &w) {
    const auto &[d_a0] = std::get<typename wrapper::Wrap>(w->v());
    return f(d_a0);
  }

  /// test1: l = 10, 20, 30, h=10, t=20,30, mylist_sum(t)=50.
  /// compute(5) = (10+50) + 5 = 65.
  /// Bug: h and t captured by &, dangle after match scope ends.
  static inline const unsigned int test1 = []() -> unsigned int {
    auto _cs =
        mylist::mycons(
            10u, mylist::mycons(20u, mylist::mycons(30u, mylist::mynil())))
            ->make_list_fn();
    if (_cs.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *_cs;
      return f(5u);
    } else {
      return 999u;
    }
  }();
  /// test2: With intervening allocation to increase stack pressure.
  /// l = 100, 200, h=100, t=200, mylist_sum(t)=200.
  /// compute(0) = 100+200 = 300.
  static inline const unsigned int test2 = []() {
    std::optional<std::function<unsigned int(unsigned int)>> opt =
        mylist::mycons(100u, mylist::mycons(200u, mylist::mynil()))
            ->make_list_fn();
    unsigned int noise =
        mylist::mycons(1u,
                       mylist::mycons(2u, mylist::mycons(3u, mylist::mynil())))
            ->mylist_sum();
    if (opt.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *opt;
      return f(0u);
    } else {
      return noise;
    }
  }();
  /// test3: Longer list, use mylist_length on captured tail.
  /// l = 5, 10, 15, 20, 25, h=5, t=10,15,20,25,
  /// mylist_sum(t) = 70, compute(10) = (5+70)+10 = 85.
  static inline const unsigned int test3 = []() -> unsigned int {
    auto _cs =
        mylist::mycons(
            5u,
            mylist::mycons(
                10u, mylist::mycons(
                         15u, mylist::mycons(
                                  20u, mylist::mycons(25u, mylist::mynil())))))
            ->make_list_fn();
    if (_cs.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *_cs;
      return f(10u);
    } else {
      return 999u;
    }
  }();
  /// Dummy use of wrapper to keep it alive for extraction.
  static std::shared_ptr<wrapper> wrap_list(std::shared_ptr<mylist> l);
};

#endif // INCLUDED_FIX_SHARED_PTR_FIELD
