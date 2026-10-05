#ifndef INCLUDED_EXISTENTIAL_ERASED_APPLY_BAD_CPP
#define INCLUDED_EXISTENTIAL_ERASED_APPLY_BAD_CPP

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
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
      : v_(crane_convert_spine(
            _other, std::shared_ptr<List<A>>(nullptr),
            [](const List<CraneU> &_cell) -> const List<CraneU> * {
              if (std::holds_alternative<typename List<CraneU>::Cons>(
                      _cell.v())) {
                return std::get<typename List<CraneU>::Cons>(_cell.v()).l.get();
              } else {
                return nullptr;
              }
            },
            [&](const List<CraneU> &_other,
                std::shared_ptr<List<A>> _below) -> variant_t {
              if (std::holds_alternative<typename List<CraneU>::Nil>(
                      _other.v())) {
                return Nil{};
              } else {
                const auto &[a, l] =
                    std::get<typename List<CraneU>::Cons>(_other.v());
                return Cons{
                    [&]() -> A {
                      if constexpr (crane_convertible<A, const CraneU &>) {
                        return crane_convert<A>(a);
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
              return std::make_shared<List<A>>(std::move(_alt));
            })) {}

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

struct ExistentialErasedApplyBadCpp {
  /// dyn packages a value with a consumer for it, hiding the value's type.
  /// The quantified A has no C++ counterpart, so both the value field and
  /// the consumer's argument erase to std::any.
  ///
  /// The consumer is emitted with the erased signature it actually has --
  /// const std::any & in, uint64_t out. For the identity fun k => k the
  /// erased std::any used to be returned directly, with no any_cast back
  /// to the concrete return type:
  ///
  /// (const std::any &k) -> uint64_t { return k; }
  ///
  /// which does not compile. The other two consumers were already fine: they
  /// use their argument at a site with a known expected type (.first, a
  /// method call), which is where the cast was being inserted. A bare return
  /// has no such site, so the lambda's declared return type is now threaded
  /// through as the expected type there.
  struct dyn {
    // DATA
    crane::obj a;
    crane::fn<uint64_t(crane::obj)> a1;

    // ACCESSORS
    dyn clone() const { return {a, a1}; }

    // CREATORS
    static dyn dyn0(crane::obj a, crane::fn<uint64_t(crane::obj)> a1) {
      return {std::move(a), std::move(a1)};
    }
  };

  template <typename T1, typename F0> static T1 dyn_rect(F0 &&f, const dyn &d) {
    const auto &[a0, a1] = d;
    return crane_any_cast<T1>(f(a0, a1));
  }

  template <typename T1, typename F0> static T1 dyn_rec(F0 &&f, const dyn &d) {
    return dyn_rect<T1>(crane_erase_fn<T1>(f), d);
  }

  static uint64_t force(const dyn &d);
  static List<dyn> mk(uint64_t n);
  static uint64_t total(const List<dyn> &l);
  static uint64_t run(uint64_t n);
};

#endif // INCLUDED_EXISTENTIAL_ERASED_APPLY_BAD_CPP
