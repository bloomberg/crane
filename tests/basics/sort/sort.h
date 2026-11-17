#ifndef INCLUDED_SORT
#define INCLUDED_SORT

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

template <typename A> struct List;
template <typename A> struct Sig;

struct Compare_dec {
  static bool le_gt_dec(uint64_t x0_, uint64_t x1_);
  static bool le_dec(uint64_t n, uint64_t m);
};

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

  static List<A> cons(A a, crane::shared_child_slot<List<A>> l) {
    return List<A>(Cons{std::move(a), l.take()});
  }

  // MANIPULATORS
  ~List() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
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

    // Explicit stack replaces the non-tail recursion of length: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const List<A> *_self;
    };

    struct _after_length_in_Cons {};

    using _frame = std::variant<_call, _after_length_in_Cons>;
    uint64_t _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{_self});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[_, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_after_length_in_Cons{});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_after_length_in_Cons>(_popped));
        _stack.pop_back();
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }
};

template <typename A> struct Sig {
  // DATA
  A x;

  // ACCESSORS
  Sig<A> clone() const { return {x}; }

  template <typename CraneU> operator Sig<CraneU>() const {
    return {[&]() -> CraneU {
      if constexpr (crane_convertible<CraneU, const A &>) {
        return crane_convert<CraneU>(x);
      } else {
        throw std::logic_error("unreachable: inactive constructor field at "
                               "this instantiation");
      }
    }()};
  }

  // CREATORS
  static Sig<A> exist(A x) { return {std::move(x)}; }
};

struct Sort {
  template <typename T1, typename T2, typename F0, typename F2, typename F3>
  static T2 div_conq(F0 &&splitF, T2 x, F2 &&x0, F3 &&x1, const List<T1> &ls) {
    bool s = UINT64_C(2) <= ls.length();
    if (s) {
      return x1(ls, div_conq<T1, T2>(splitF, x, x0, x1, splitF(ls).first),
                div_conq<T1, T2>(splitF, x, x0, x1, splitF(ls).second));
    } else {
      if (std::holds_alternative<typename List<T1>::Nil>(ls.v())) {
        return x;
      } else {
        const auto &[a0, _] = std::get<typename List<T1>::Cons>(ls.v());
        return x0(a0);
      }
    }
  }

  template <typename T1>
  static std::pair<List<T1>, List<T1>> split(const List<T1> &ls) {
    if (std::holds_alternative<typename List<T1>::Nil>(ls.v())) {
      return std::make_pair(List<T1>::nil(), List<T1>::nil());
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(ls.v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename List<T1>::Nil>(_sv0.v())) {
        return std::make_pair(List<T1>::cons(a0, List<T1>::nil()),
                              List<T1>::nil());
      } else {
        const auto &[a00, a10] = std::get<typename List<T1>::Cons>(_sv0.v());
        auto [ls1, ls2] = split<T1>(*a10);
        return std::make_pair(List<T1>::cons(a0, std::move(ls1)),
                              List<T1>::cons(a00, std::move(ls2)));
      }
    }
  }

  template <typename T1, typename T2, typename F1, typename F2>
  static T2 div_conq_split(T2 x, F1 &&x0_, F2 &&x1_, const List<T1> &x2_) {
    return div_conq<T1, T2>(split<T1>, std::move(x), x0_, x1_, x2_);
  }

  template <typename T1, typename T2, typename F1, typename F2, typename F3>
    requires std::is_invocable_r_v<T2, F1 &, const T1 &> &&
             std::is_invocable_r_v<T2, F2 &, const T1 &, const T1 &>
  static T2 div_conq_pair(T2 x, F1 &&x0, F2 &&x1, F3 &&x2, const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return x;
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename List<T1>::Nil>(_sv0.v())) {
        return x0(a0);
      } else {
        const auto &[a00, a10] = std::get<typename List<T1>::Cons>(_sv0.v());
        return x2(a0, a00, *a10, x1(a0, a00),
                  div_conq_pair<T1, T2>(std::move(x), x0, x1, x2, *a10));
      }
    }
  }

  template <typename T1, typename F0>
  static std::pair<List<T1>, List<T1>>
  split_pivot(F0 &&le_dec0, const T1 &pivot, const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return std::make_pair(List<T1>::nil(), List<T1>::nil());
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      auto [l1, l2] = split_pivot<T1>(le_dec0, pivot, *a1);
      if (le_dec0(a0, pivot)) {
        return std::make_pair(List<T1>::cons(a0, std::move(l1)), std::move(l2));
      } else {
        return std::make_pair(std::move(l1), List<T1>::cons(a0, std::move(l2)));
      }
    }
  }

  template <typename T1, typename T2, typename F0, typename F2>
  static T2 div_conq_pivot(F0 &&le_dec0, T2 x, F2 &&x0, const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return x;
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      return x0(
          a0, *a1, div_conq_pivot<T1, T2>(
                       le_dec0, x, x0, split_pivot<T1>(le_dec0, a0, *a1).first),
          div_conq_pivot<T1, T2>(le_dec0, x, x0,
                                 split_pivot<T1>(le_dec0, a0, *a1).second));
    }
  }

  static Sig<List<uint64_t>>
  sort_cons_prog(uint64_t a, const List<uint64_t> &_x,
                 const List<uint64_t> &l_);
  static Sig<List<uint64_t>> isort(const List<uint64_t> &l);
  static List<uint64_t> merge(List<uint64_t> l1, const List<uint64_t> &l2);
  static Sig<List<uint64_t>>
  merge_prog(const List<uint64_t> &_x, List<uint64_t> l1,
             const List<uint64_t> &l2);
  static Sig<List<uint64_t>> msort(const List<uint64_t> &x0_);
  static Sig<List<uint64_t>>
  pair_merge_prog(uint64_t _x, uint64_t _x0, const List<uint64_t> &_x1,
                  const List<uint64_t> &l_, List<uint64_t> l_0);
  static Sig<List<uint64_t>> psort(const List<uint64_t> &x0_);
  static Sig<List<uint64_t>> qsort(const List<uint64_t> &x0_);
};

#endif // INCLUDED_SORT
