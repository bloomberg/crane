#ifndef INCLUDED_CTOR_ARG_MOVE_ALIAS
#define INCLUDED_CTOR_ARG_MOVE_ALIAS

#include "small_vector.h"
#include <any>
#include <memory>
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
/// Crane emits
///
/// {
/// auto& [a0, a1] = std::get<Mycons>(o.v_mut());
/// return pack::pack0(std::move(a0), osum(o));
/// }
///
/// The two arguments are {i unsequenced}: std::move(a0) consumes o's
/// head element, and osum(o) walks the very same o.  Whichever order
/// the compiler picks, one of them is wrong; with clang the move happens
/// first, so osum reads a moved-from inner whose tail shared_ptr is
/// now null and dereferences it.
///
/// Expected run 1 = 6; the extracted program segfaults instead
/// (UBSan: "member call on null pointer of type 'inner'").
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
      crane::small_vector<std::shared_ptr<inner>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<ICons>(&_v)) {
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
          _drain(_cur->v_mut());
        }
      }
    }

    inner(const inner &) = default;
    inner &operator=(const inner &) = default;
    inner(inner &&) noexcept = default;
    inner &operator=(inner &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t isum() const {
      if (std::holds_alternative<typename inner::INil>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename inner::ICons>(this->v());
        return (a0 + a1->isum());
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, uint64_t &, inner &, T1 &>
    T1 inner_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename inner::INil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename inner::ICons>(this->v());
        return f0(a0, *a1, a1->template inner_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, uint64_t &, inner &, T1 &>
    T1 inner_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename inner::INil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename inner::ICons>(this->v());
        return f0(a0, *a1, a1->template inner_rect<T1>(f, f0));
      }
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

    template <typename _U> mylist(const mylist<_U> &_other) {
      if (std::holds_alternative<typename mylist<_U>::Mynil>(_other.v())) {
        this->v_ = Mynil{};
      } else {
        const auto &[a0, a1] =
            std::get<typename mylist<_U>::Mycons>(_other.v());
        this->v_ = Mycons{
            [&]() -> A {
              if constexpr (std::is_same_v<_U, std::any>) {
                if (a0.type() == typeid(A))
                  return std::any_cast<A>(a0);
                if constexpr (requires {
                                typename A::first_type;
                                typename A::second_type;
                              }) {
                  const auto &[_k, _v] =
                      std::any_cast<std::pair<std::any, std::any>>(a0);
                  return A{
                      [&]() -> typename A::first_type {
                        if constexpr (std::is_same_v<typename A::first_type,
                                                     std::any>)
                          return _k;
                        else
                          return std::any_cast<typename A::first_type>(_k);
                      }(),
                      [&]() -> typename A::second_type {
                        if constexpr (std::is_same_v<typename A::second_type,
                                                     std::any>)
                          return _v;
                        else
                          return std::any_cast<typename A::second_type>(_v);
                      }()};
                }
                return std::any_cast<A>(a0);
              } else
                return A(a0);
            }(),
            a1 ? std::make_shared<mylist<A>>(*a1) : nullptr};
      }
    }

    static mylist<A> mynil() { return mylist(Mynil{}); }

    static mylist<A> mycons(A a0, mylist<A> a1) {
      return mylist(
          Mycons{std::move(a0), std::make_shared<mylist<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      crane::small_vector<std::shared_ptr<mylist<A>>> _stack = {};
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

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, mylist<A> &, T1 &>
    T1 mylist_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename mylist<A>::Mynil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(this->v());
        return f0(a0, *a1, a1->template mylist_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, mylist<A> &, T1 &>
    T1 mylist_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename mylist<A>::Mynil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(this->v());
        return f0(a0, *a1, a1->template mylist_rect<T1>(f, f0));
      }
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
    requires std::is_invocable_r_v<T1, F0 &, inner &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, mylist<inner> &>
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
    requires std::is_invocable_r_v<T1, F0 &, inner &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, mylist<inner> &>
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
  static pack grab(mylist<inner> o);
  /// o = [ICons n (ICons (S n) INil)], so osum o = 2n+1 and
  /// isum h = 2n+1; the result is 4n+2, i.e. 6 for n = 1.
  static uint64_t run(uint64_t n);
};

#endif // INCLUDED_CTOR_ARG_MOVE_ALIAS
