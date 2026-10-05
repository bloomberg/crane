#ifndef INCLUDED_DEEP_PATTERNS
#define INCLUDED_DEEP_PATTERNS

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  uint64_t length() const {
    const List<A> *_self = this;

    /// CraneEnter: captures varying parameters for each recursive call.
    struct CraneEnter {
      const List<A> *_self;
    };

    /// CraneCont_Cons: resumes after recursive call, then processes rest.
    struct CraneCont_Cons {};

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    uint64_t _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{_self});
    /// Loopified length: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(CraneCont_Cons{});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }
};

struct DeepPatterns {
  static uint64_t
  deep_option(const std::optional<std::optional<std::optional<uint64_t>>> &x);
  static uint64_t deep_pair(const std::pair<std::pair<uint64_t, uint64_t>,
                                            std::pair<uint64_t, uint64_t>> &p);
  static uint64_t list_shape(const List<uint64_t> &l);
  struct outer;
  struct inner;

  struct outer {
    // TYPES
    struct OLeft {
      std::shared_ptr<inner> a0;
    };

    struct ORight {
      uint64_t a0;
    };

    using variant_t = std::variant<OLeft, ORight>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    outer() {}

    explicit outer(OLeft _v) : v_(std::move(_v)) {}

    explicit outer(ORight _v) : v_(std::move(_v)) {}

    static outer oleft(inner a0) {
      return outer(OLeft{std::make_shared<inner>(std::move(a0))});
    }

    static outer oright(uint64_t a0) { return outer(ORight{a0}); }

    // MANIPULATORS
    ~outer() {
      crane::small_vector<crane::obj> _stack = {};
      auto _drain_self = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<OLeft>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
        }
      };
      _drain_self(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (auto *_sp = crane::any_cast<std::shared_ptr<outer>>(&_cur)) {
          if (*_sp && (*_sp).use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            _drain_self((*_sp)->v_mut());
          }
        } else {
          if (auto *_sp = crane::any_cast<std::shared_ptr<inner>>(&_cur)) {
            if (*_sp && (*_sp).use_count() == 1) {
              auto &_pv = (*_sp)->v_mut();
            }
          }
        }
      }
    }

    outer(const outer &) = default;
    outer &operator=(const outer &) = default;
    outer(outer &&) = default;
    outer &operator=(outer &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  struct inner {
    // TYPES
    struct ILeft {
      uint64_t a0;
    };

    struct IRight {
      bool a0;
    };

    using variant_t = std::variant<ILeft, IRight>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    inner() {}

    explicit inner(ILeft _v) : v_(std::move(_v)) {}

    explicit inner(IRight _v) : v_(std::move(_v)) {}

    static inner ileft(uint64_t a0) { return inner(ILeft{a0}); }

    static inner iright(bool a0) { return inner(IRight{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, const uint64_t &>
  static T1 outer_rect(F0 &&f, F1 &&f0, const outer &o) {
    if (std::holds_alternative<typename outer::OLeft>(o.v())) {
      const auto &[a0] = std::get<typename outer::OLeft>(o.v());
      return f(*a0);
    } else {
      const auto &[a0] = std::get<typename outer::ORight>(o.v());
      return f0(a0);
    }
  }

  template <typename T1, typename F0, typename F1>
  static T1 outer_rec(F0 &&f, F1 &&f0, const outer &o) {
    return outer_rect<T1>(f, f0, o);
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, const bool &>
  static T1 inner_rect(F0 &&f, F1 &&f0, const inner &i) {
    if (std::holds_alternative<typename inner::ILeft>(i.v())) {
      const auto &[a0] = std::get<typename inner::ILeft>(i.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename inner::IRight>(i.v());
      return f0(a0);
    }
  }

  template <typename T1, typename F0, typename F1>
  static T1 inner_rec(F0 &&f, F1 &&f0, const inner &i) {
    return inner_rect<T1>(f, f0, i);
  }

  static uint64_t deep_sum(const outer &o);
  static uint64_t
  complex_match(const std::optional<std::pair<uint64_t, List<uint64_t>>> &x);
  static uint64_t guarded_match(const std::pair<uint64_t, uint64_t> &p);

  template <typename A, typename B> struct pair {
    // DATA
    A a0;
    B a1;

    // ACCESSORS
    pair<A, B> clone() const { return {a0, a1}; }

    template <typename CraneU0, typename CraneU1>
    operator pair<CraneU0, CraneU1>() const {
      return {[&]() -> CraneU0 {
                if constexpr (crane_convertible<CraneU0, const A &>) {
                  return crane_convert<CraneU0>(a0);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }(),
              [&]() -> CraneU1 {
                if constexpr (crane_convertible<CraneU1, const B &>) {
                  return crane_convert<CraneU1>(a1);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }()};
    }

    // CREATORS
    static pair<A, B> pair0(A a0, B a1) {
      return {std::move(a0), std::move(a1)};
    }

    template <typename T1, typename F0> T1 pair_rec(F0 &&f) const {
      return this->template pair_rect<T1>(f);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, const A &, const B &>
    T1 pair_rect(F0 &&f) const {
      const auto &[a0, a1] = *this;
      return f(a0, a1);
    }
  };

  template <typename A> struct mylist {
    // TYPES
    struct Nil {};

    struct Cons {
      A a0;
      std::shared_ptr<mylist<A>> a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Nil _v) : v_(_v) {}

    explicit mylist(Cons _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    mylist(const mylist<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename mylist<CraneU>::Nil>(
                    _other.v())) {
              return Nil{};
            } else {
              const auto &[a0, a1] =
                  std::get<typename mylist<CraneU>::Cons>(_other.v());
              return Cons{
                  [&]() -> A {
                    if constexpr (crane_convertible<A, const CraneU &>) {
                      return crane_convert<A>(a0);
                    } else {
                      throw std::logic_error(
                          "unreachable: inactive constructor field at this "
                          "instantiation");
                    }
                  }(),
                  (a1 ? std::make_shared<mylist<A>>(
                            crane_convert<mylist<A>>(*a1))
                      : nullptr)};
            }
          }()) {}

    static mylist<A> nil() { return mylist<A>(Nil{}); }

    static mylist<A> cons(A a0, mylist<A> a1) {
      return mylist<A>(
          Cons{std::move(a0), std::make_shared<mylist<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<mylist<A>> {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
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

    template <typename T1, typename F1>
    T1 mylist_rec(const T1 &f, F1 &&f0) const {
      return this->template mylist_rect<T1>(f, f0);
    }

    template <typename T1, typename F1> T1 mylist_rect(T1 f, F1 &&f0) const {
      const mylist<A> *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const mylist<A> *_self;
      };

      /// CraneCont_Cons: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Cons {
        A a0;
        std::shared_ptr<mylist<A>> a1;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified mylist_rect: CraneEnter -> CraneCont_Cons.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const mylist<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename mylist<A>::Nil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = std::get<typename mylist<A>::Cons>(_sv.v());
            _stack.emplace_back(CraneCont_Cons{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<CraneCont_Cons>(_frame));
          auto a0 = std::move(_f.a0);
          std::shared_ptr<mylist<A>> a1 = std::move(_f.a1);
          _result = f0(a0, *a1, std::move(_result));
        }
      }
      return _result;
    }
  };

  static uint64_t match_pair_list(const mylist<pair<uint64_t, uint64_t>> &l);
  static uint64_t match_two(const mylist<uint64_t> &l);
  static uint64_t match_triple(const mylist<mylist<mylist<uint64_t>>> &l);
  static uint64_t deep_wildcard(
      const pair<pair<uint64_t, uint64_t>, pair<uint64_t, uint64_t>> &p);
  static constexpr uint64_t test_deep_some = UINT64_C(42);
  static constexpr uint64_t test_deep_none = UINT64_C(1);
  static constexpr uint64_t test_deep_pair = UINT64_C(10);
  static constexpr uint64_t test_shape_3 = UINT64_C(60);
  static constexpr uint64_t test_shape_long = UINT64_C(8);
  static constexpr uint64_t test_deep_sum = UINT64_C(77);
  static constexpr uint64_t test_complex = UINT64_C(16);
  static constexpr uint64_t test_guarded = UINT64_C(4);
  static constexpr uint64_t test_pair_list = UINT64_C(5);
  static constexpr uint64_t test_two_one = UINT64_C(7);
  static constexpr uint64_t test_two_many = UINT64_C(7);
  static constexpr uint64_t test_triple = UINT64_C(9);
  static constexpr uint64_t test_wildcard = UINT64_C(1);
  static constexpr uint64_t t = UINT64_C(247);
};

#endif // INCLUDED_DEEP_PATTERNS
