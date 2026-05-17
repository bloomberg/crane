#ifndef INCLUDED_FIX_SHARED_PTR_FIELD
#define INCLUDED_FIX_SHARED_PTR_FIELD

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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
      unsigned int a0;
      std::unique_ptr<mylist> a1;
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

    mylist(const mylist &_other) : v_(std::move(_other.clone().v_)) {}

    mylist(mylist &&_other) noexcept : v_(std::move(_other.v_)) {}

    mylist &operator=(const mylist &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    mylist &operator=(mylist &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    mylist clone() const {
      mylist _out{};

      struct _CloneFrame {
        const mylist *_src;
        mylist *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const mylist *_src = _frame._src;
        mylist *_dst = _frame._dst;
        if (std::holds_alternative<Mynil>(_src->v())) {
          _dst->v_ = Mynil{};
        } else {
          const auto &_alt = std::get<Mycons>(_src->v());
          _dst->v_ =
              Mycons{_alt.a0, _alt.a1 ? std::make_unique<mylist>() : nullptr};
          auto &_dst_alt = std::get<Mycons>(_dst->v_);
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static mylist mynil() { return mylist(Mynil{}); }

    static mylist mycons(unsigned int a0, mylist a1) {
      return mylist(Mycons{a0, std::make_unique<mylist>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      std::vector<std::unique_ptr<mylist>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](mylist &_node) {
        if (std::holds_alternative<Mycons>(_node.v_)) {
          auto &_alt = std::get<Mycons>(_node.v_);
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// Local fixpoint captures h : nat (POD) and t : shared_ptr<mylist>
    /// from the match on value-type mylist. Both are captured by &.
    std::optional<std::function<unsigned int(unsigned int)>>
    make_list_fn() const {
      if (std::holds_alternative<typename mylist::Mynil>(this->v())) {
        return std::optional<std::function<unsigned int(unsigned int)>>();
      } else {
        const auto &[a0, a1] = std::get<typename mylist::Mycons>(this->v());
        mylist a1_value = *a1;
        auto compute_impl = [=](auto &_self_compute,
                                unsigned int x) mutable -> unsigned int {
          if (x <= 0) {
            return (a0 + a1_value.mylist_sum());
          } else {
            unsigned int x_ = x - 1;
            return (1u + _self_compute(_self_compute, x_));
          }
        };
        auto compute = [=](unsigned int x) mutable -> unsigned int {
          return compute_impl(compute_impl, x);
        };
        return std::make_optional<std::function<unsigned int(unsigned int)>>(
            compute);
      }
    }

    unsigned int mylist_length() const {
      if (std::holds_alternative<typename mylist::Mynil>(this->v())) {
        return 0u;
      } else {
        const auto &[a0, a1] = std::get<typename mylist::Mycons>(this->v());
        return (1u + (*a1).mylist_length());
      }
    }

    unsigned int mylist_sum() const {
      if (std::holds_alternative<typename mylist::Mynil>(this->v())) {
        return 0u;
      } else {
        const auto &[a0, a1] = std::get<typename mylist::Mycons>(this->v());
        return (a0 + (*a1).mylist_sum());
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, unsigned int &, mylist &, T1 &>
    T1 mylist_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename mylist::Mynil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename mylist::Mycons>(this->v());
        return f0(a0, *a1, (*a1).template mylist_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, unsigned int &, mylist &, T1 &>
    T1 mylist_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename mylist::Mynil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename mylist::Mycons>(this->v());
        return f0(a0, *a1, (*a1).template mylist_rect<T1>(f, f0));
      }
    }
  };

  /// A second inductive to prevent methodification of make_list_fn.
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

  /// test1: l = 10, 20, 30, h=10, t=20,30, mylist_sum(t)=50.
  /// compute(5) = (10+50) + 5 = 65.
  /// Bug: h and t captured by &, dangle after match scope ends.
  static inline const unsigned int test1 = []() -> unsigned int {
    auto _cs =
        mylist::mycons(
            10u, mylist::mycons(20u, mylist::mycons(30u, mylist::mynil())))
            .make_list_fn();
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
            .make_list_fn();
    unsigned int noise =
        mylist::mycons(1u,
                       mylist::mycons(2u, mylist::mycons(3u, mylist::mynil())))
            .mylist_sum();
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
            .make_list_fn();
    if (_cs.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *_cs;
      return f(10u);
    } else {
      return 999u;
    }
  }();
  /// Dummy use of wrapper to keep it alive for extraction.
  static wrapper wrap_list(mylist l);
};

#endif // INCLUDED_FIX_SHARED_PTR_FIELD
