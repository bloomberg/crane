#ifndef INCLUDED_FIX_SHARED_PTR_FIELD
#define INCLUDED_FIX_SHARED_PTR_FIELD

#include "crane_fn.h"
#include "fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

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

    /// Local fixpoint captures h : nat (POD) and t : shared_ptr<mylist>
    /// from the match on value-type mylist. Both are captured by &.
    std::optional<crane::fn<uint64_t(uint64_t)>> make_list_fn() const {
      if (std::holds_alternative<typename mylist::Mynil>(this->v())) {
        return std::optional<crane::fn<uint64_t(uint64_t)>>();
      } else {
        const auto &[a0, a1] = std::get<typename mylist::Mycons>(this->v());
        const mylist &a1_value = *a1;
        auto compute_impl = [=](auto &_self_compute, uint64_t x) -> uint64_t {
          if (x <= 0) {
            return (a0 + a1_value.mylist_sum());
          } else {
            uint64_t x_ = x - 1;
            return (UINT64_C(1) + _self_compute(_self_compute, x_));
          }
        };
        auto compute = [=, compute_impl = std::move(compute_impl)](
                           uint64_t x) -> uint64_t {
          return compute_impl(compute_impl, x);
        };
        return std::make_optional<crane::fn<uint64_t(uint64_t)>>(
            std::move(compute));
      }
    }

    uint64_t mylist_length() const {
      const mylist *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const mylist *_self;
      };

      /// CraneCont_Mycons: resumes after recursive call, then processes rest.
      struct CraneCont_Mycons {};

      using CraneFrame = std::variant<CraneEnter, CraneCont_Mycons>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified mylist_length: CraneEnter -> CraneCont_Mycons.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const mylist *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename mylist::Mynil>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1] = std::get<typename mylist::Mycons>(_sv.v());
            _stack.emplace_back(CraneCont_Mycons{});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<CraneCont_Mycons>(_frame));
          _result = (UINT64_C(1) + std::move(_result));
        }
      }
      return _result;
    }

    uint64_t mylist_sum() const {
      const mylist *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const mylist *_self;
      };

      /// CraneCont_Mycons: saves [a0], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Mycons {
        uint64_t a0;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_Mycons>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified mylist_sum: CraneEnter -> CraneCont_Mycons.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const mylist *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename mylist::Mynil>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1] = std::get<typename mylist::Mycons>(_sv.v());
            _stack.emplace_back(CraneCont_Mycons{a0});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<CraneCont_Mycons>(_frame));
          uint64_t a0 = _f.a0;
          _result = (a0 + std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1> T1 mylist_rec(T1 f, F1 &&f0) const {
      return this->template mylist_rect<T1>(std::move(f), f0);
    }

    template <typename T1, typename F1> T1 mylist_rect(T1 f, F1 &&f0) const {
      const mylist *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const mylist *_self;
      };

      /// CraneCont_Mycons: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Mycons {
        uint64_t a0;
        std::shared_ptr<mylist> a1;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_Mycons>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified mylist_rect: CraneEnter -> CraneCont_Mycons.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const mylist *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename mylist::Mynil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = std::get<typename mylist::Mycons>(_sv.v());
            _stack.emplace_back(CraneCont_Mycons{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<CraneCont_Mycons>(_frame));
          uint64_t a0 = _f.a0;
          std::shared_ptr<mylist> a1 = std::move(_f.a1);
          _result = f0(a0, *a1, std::move(_result));
        }
      }
      return _result;
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
    requires std::is_invocable_r_v<T1, F0 &, const mylist &>
  static T1 wrapper_rect(F0 &&f, const wrapper &w) {
    const auto &[a0] = w;
    return f(a0);
  }

  template <typename T1, typename F0>
  static T1 wrapper_rec(F0 &&f, const wrapper &w) {
    return wrapper_rect<T1>(f, w);
  }

  /// test1: l = 10, 20, 30, h=10, t=20,30, mylist_sum(t)=50.
  /// compute(5) = (10+50) + 5 = 65.
  /// Bug: h and t captured by &, dangle after match scope ends.
  static inline const uint64_t test1 = []() -> uint64_t {
    auto _cs = mylist::mycons(UINT64_C(10),
                              mylist::mycons(UINT64_C(20),
                                             mylist::mycons(UINT64_C(30),
                                                            mylist::mynil())))
                   .make_list_fn();
    if (_cs.has_value()) {
      const crane::fn<uint64_t(uint64_t)> &f = *_cs;
      return f(UINT64_C(5));
    } else {
      return UINT64_C(999);
    }
  }();
  /// test2: With intervening allocation to increase stack pressure.
  /// l = 100, 200, h=100, t=200, mylist_sum(t)=200.
  /// compute(0) = 100+200 = 300.
  static inline const uint64_t test2 = []() {
    std::optional<crane::fn<uint64_t(uint64_t)>> opt =
        mylist::mycons(UINT64_C(100),
                       mylist::mycons(UINT64_C(200), mylist::mynil()))
            .make_list_fn();
    uint64_t noise =
        mylist::mycons(
            UINT64_C(1),
            mylist::mycons(UINT64_C(2),
                           mylist::mycons(UINT64_C(3), mylist::mynil())))
            .mylist_sum();
    if (opt.has_value()) {
      const crane::fn<uint64_t(uint64_t)> &f = *opt;
      return f(UINT64_C(0));
    } else {
      return noise;
    }
  }();
  /// test3: Longer list, use mylist_length on captured tail.
  /// l = 5, 10, 15, 20, 25, h=5, t=10,15,20,25,
  /// mylist_sum(t) = 70, compute(10) = (5+70)+10 = 85.
  static inline const uint64_t test3 = []() -> uint64_t {
    auto _cs = mylist::mycons(
                   UINT64_C(5),
                   mylist::mycons(
                       UINT64_C(10),
                       mylist::mycons(
                           UINT64_C(15),
                           mylist::mycons(
                               UINT64_C(20),
                               mylist::mycons(UINT64_C(25), mylist::mynil())))))
                   .make_list_fn();
    if (_cs.has_value()) {
      const crane::fn<uint64_t(uint64_t)> &f = *_cs;
      return f(UINT64_C(10));
    } else {
      return UINT64_C(999);
    }
  }();
  /// Dummy use of wrapper to keep it alive for extraction.
  static wrapper wrap_list(const mylist &l);
};

#endif // INCLUDED_FIX_SHARED_PTR_FIELD
