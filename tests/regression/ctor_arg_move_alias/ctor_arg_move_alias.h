#ifndef INCLUDED_CTOR_ARG_MOVE_ALIAS
#define INCLUDED_CTOR_ARG_MOVE_ALIAS

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

/// Use-after-move: a constructor field is moved out of an owned scrutinee
/// while a sibling argument of the same call still reads that scrutinee.
///
/// Ingredients, all of which are needed:
///
/// - mylist is polymorphic, so grab stays a free function instead of
/// being methodified onto a const this (a const receiver silently
/// degrades std::move to a copy and hides the problem).
/// - o escapes through the mynil branch, so escape analysis marks it
/// {i owned} and it is passed by value.  Owned scrutinees are destructured
/// with auto& [a0, a1] = std::get<Mycons>(o.v_mut()), i.e. a0 is a
/// mutable reference {i into} o.
/// - the element type inner is a non-trivial inductive, so moving a0
/// really does hollow out o's head (a trivial nat element would make
/// the move a no-op).
/// - h occurs exactly once in the branch, so move-on-last-use fires and
/// emits std::move(a0).
///
/// Crane used to emit
///
/// {
/// auto& [a0, a1] = std::get<Mycons>(o.v_mut());
/// return pack::pack0(std::move(a0), osum(o));
/// }
///
/// The two arguments are {i unsequenced}: std::move(a0) consumes o's
/// head element, and osum(o) walks the very same o.  Whichever order
/// the compiler picks, one of them is wrong; with clang the move happened
/// first, so osum read a moved-from inner whose tail shared_ptr was
/// null and dereferenced it.
///
/// gen_match_branch now suppresses field moves whenever the branch body
/// still reads the owned scrutinee, so the field is copied instead and
/// run 1 = 6.
struct CtorArgMoveAlias {
  struct inner {
    // TYPES
    struct INil {};

    struct ICons {
      uint64_t a0;
      std::shared_ptr<inner> a1;
    };

    using variant_t = std::variant<INil, ICons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    inner() {}

    explicit inner(INil _v) : v_(_v) {}

    explicit inner(ICons _v) : v_(std::move(_v)) {}

    static inner inil() { return inner(INil{}); }

    static inner icons(uint64_t a0, inner a1) {
      return inner(ICons{a0, std::make_shared<inner>(std::move(a1))});
    }

    // MANIPULATORS
    ~inner() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<inner> {
        if (auto *_alt = std::get_if<ICons>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      std::shared_ptr<inner> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    inner(const inner &) = default;
    inner &operator=(const inner &) = default;
    inner(inner &&) = default;
    inner &operator=(inner &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t isum() const {
      auto go_impl = [](auto &_self_go, const inner &l,
                        uint64_t acc) -> uint64_t {
        if (std::holds_alternative<typename inner::INil>(l.v())) {
          return acc;
        } else {
          const auto &[a0, a1] = std::get<typename inner::ICons>(l.v());
          return _self_go(_self_go, *a1, (acc + a0));
        }
      };
      {
        const inner &_lc1_l = *this;
        uint64_t _lc1_acc = UINT64_C(0);
        return go_impl(go_impl, _lc1_l, _lc1_acc);
      }
    }

    template <typename T1, typename F1> T1 inner_rec(T1 f, F1 &&f0) const {
      const inner *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const inner *_self;
      };

      /// CraneCont_ICons: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_ICons {
        uint64_t a0;
        std::shared_ptr<inner> a1;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_ICons>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified inner_rec: CraneEnter -> CraneCont_ICons.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const inner *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename inner::INil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = std::get<typename inner::ICons>(_sv.v());
            _stack.emplace_back(CraneCont_ICons{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<CraneCont_ICons>(_frame));
          uint64_t a0 = _f.a0;
          std::shared_ptr<inner> a1 = std::move(_f.a1);
          _result = f0(a0, *a1, std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1> T1 inner_rect(T1 f, F1 &&f0) const {
      const inner *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const inner *_self;
      };

      /// CraneCont_ICons: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_ICons {
        uint64_t a0;
        std::shared_ptr<inner> a1;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_ICons>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified inner_rect: CraneEnter -> CraneCont_ICons.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const inner *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename inner::INil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = std::get<typename inner::ICons>(_sv.v());
            _stack.emplace_back(CraneCont_ICons{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<CraneCont_ICons>(_frame));
          uint64_t a0 = _f.a0;
          std::shared_ptr<inner> a1 = std::move(_f.a1);
          _result = f0(a0, *a1, std::move(_result));
        }
      }
      return _result;
    }
  };

  template <typename A> struct mylist {
    // TYPES
    struct Mynil {};

    struct Mycons {
      A a0;
      std::shared_ptr<mylist<A>> a1;
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

    template <typename CraneU>
    mylist(const mylist<CraneU> &_other)
        : v_(crane_convert_spine(
              _other, std::shared_ptr<mylist<A>>(nullptr),
              [](const mylist<CraneU> &_cell) -> const mylist<CraneU> * {
                if (std::holds_alternative<typename mylist<CraneU>::Mycons>(
                        _cell.v())) {
                  return std::get<typename mylist<CraneU>::Mycons>(_cell.v())
                      .a1.get();
                } else {
                  return nullptr;
                }
              },
              [&](const mylist<CraneU> &_other,
                  std::shared_ptr<mylist<A>> _below) -> variant_t {
                if (std::holds_alternative<typename mylist<CraneU>::Mynil>(
                        _other.v())) {
                  return Mynil{};
                } else {
                  const auto &[a0, a1] =
                      std::get<typename mylist<CraneU>::Mycons>(_other.v());
                  return Mycons{
                      [&]() -> A {
                        if constexpr (crane_convertible<A, const CraneU &>) {
                          return crane_convert<A>(a0);
                        } else {
                          throw std::logic_error(
                              "unreachable: inactive constructor field at this "
                              "instantiation");
                        }
                      }(),
                      std::move(_below)};
                }
              },
              [](auto &&_alt) {
                return std::make_shared<mylist<A>>(std::move(_alt));
              })) {}

    static mylist<A> mynil() { return mylist<A>(Mynil{}); }

    static mylist<A> mycons(A a0, mylist<A> a1) {
      return mylist<A>(
          Mycons{std::move(a0), std::make_shared<mylist<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<mylist<A>> {
        if (auto *_alt = std::get_if<Mycons>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      std::shared_ptr<mylist<A>> _cur = _next(v_mut());
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

    template <typename T1, typename F1> T1 mylist_rec(T1 f, F1 &&f0) const {
      const mylist<A> *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const mylist<A> *_self;
      };

      /// CraneCont_Mycons: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Mycons {
        A a0;
        std::shared_ptr<mylist<A>> a1;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_Mycons>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified mylist_rec: CraneEnter -> CraneCont_Mycons.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const mylist<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] =
                std::get<typename mylist<A>::Mycons>(_sv.v());
            _stack.emplace_back(CraneCont_Mycons{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<CraneCont_Mycons>(_frame));
          auto a0 = std::move(_f.a0);
          std::shared_ptr<mylist<A>> a1 = std::move(_f.a1);
          _result = f0(a0, *a1, std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1> T1 mylist_rect(T1 f, F1 &&f0) const {
      const mylist<A> *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const mylist<A> *_self;
      };

      /// CraneCont_Mycons: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Mycons {
        A a0;
        std::shared_ptr<mylist<A>> a1;
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
          const mylist<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] =
                std::get<typename mylist<A>::Mycons>(_sv.v());
            _stack.emplace_back(CraneCont_Mycons{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<CraneCont_Mycons>(_frame));
          auto a0 = std::move(_f.a0);
          std::shared_ptr<mylist<A>> a1 = std::move(_f.a1);
          _result = f0(a0, *a1, std::move(_result));
        }
      }
      return _result;
    }
  };

  struct pack {
    // TYPES
    struct Pack0 {
      inner a0;
      uint64_t a1;
    };

    struct PList {
      mylist<inner> a0;
    };

    using variant_t = std::variant<Pack0, PList>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    pack() {}

    explicit pack(Pack0 _v) : v_(std::move(_v)) {}

    explicit pack(PList _v) : v_(std::move(_v)) {}

    static pack pack0(inner a0, uint64_t a1) {
      return pack(Pack0{std::move(a0), a1});
    }

    static pack plist(mylist<inner> a0) { return pack(PList{std::move(a0)}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, const inner &, const uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, const mylist<inner> &>
  static T1 pack_rect(F0 &&f, F1 &&f0, const pack &p) {
    if (std::holds_alternative<typename pack::Pack0>(p.v())) {
      const auto &[a0, a1] = std::get<typename pack::Pack0>(p.v());
      return f(a0, a1);
    } else {
      const auto &[a0] = std::get<typename pack::PList>(p.v());
      return f0(a0);
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, const inner &, const uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, const mylist<inner> &>
  static T1 pack_rec(F0 &&f, F1 &&f0, const pack &p) {
    if (std::holds_alternative<typename pack::Pack0>(p.v())) {
      const auto &[a0, a1] = std::get<typename pack::Pack0>(p.v());
      return f(a0, a1);
    } else {
      const auto &[a0] = std::get<typename pack::PList>(p.v());
      return f0(a0);
    }
  }

  static uint64_t osum(const mylist<inner> &o);
  /// h is the sole occurrence of the head field, so Crane moves it out of
  /// o; the sibling argument osum o still reads the whole o.
  static pack grab(const mylist<inner> &o);
  /// o = [ICons n (ICons (S n) INil)], so osum o = 2n+1 and
  /// isum h = 2n+1; the result is 4n+2, i.e. 6 for n = 1.
  static uint64_t run(uint64_t n);
};

#endif // INCLUDED_CTOR_ARG_MOVE_ALIAS
