#ifndef INCLUDED_LOOPIFY_SORTING
#define INCLUDED_LOOPIFY_SORTING

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
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
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
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

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  List<A> app(List<A> m) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return m;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return List<A>::cons(a0, a1->app(std::move(m)));
    }
  }
};

/// Consolidated UNIQUE sorting algorithms and related operations.
struct LoopifySorting {
  template <typename T1>
  static uint64_t
  len_impl(const List<T1> &l) { /// _Enter: captures varying parameters for each
                                /// recursive call.

    struct _Enter {
      const List<T1> *l;
    };

    /// _Resume_Cons: resumes after recursive call with _result.
    struct _Resume_Cons {};

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    uint64_t _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified len_impl: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<T1> &l = *_f.l;
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }

  static List<uint64_t> insert(uint64_t x, List<uint64_t> l);
  static List<uint64_t> insertion_sort(const List<uint64_t> &l);

  template <typename T1>
  static std::pair<List<T1>, List<T1>>
  split(const List<T1> &l) { /// _Enter: captures varying parameters for each
                             /// recursive call.

    struct _Enter {
      const List<T1> *l;
    };

    /// _Cont_Cons: saves [a0, a00], resumes after recursive call, then
    /// processes rest.
    struct _Cont_Cons {
      std::decay_t<T1> a0;
      std::decay_t<T1> a00;
    };

    using _Frame = std::variant<_Enter, _Cont_Cons>;
    std::pair<List<T1>, List<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified split: _Enter -> _Cont_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<T1> &l = *_f.l;
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          _result = std::make_pair(List<T1>::nil(), List<T1>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
          auto &&_sv0 = *a1;
          if (std::holds_alternative<typename List<T1>::Nil>(_sv0.v())) {
            _result = std::make_pair(List<T1>::cons(a0, List<T1>::nil()),
                                     List<T1>::nil());
          } else {
            const auto &[a00, a10] =
                std::get<typename List<T1>::Cons>(_sv0.v());
            _stack.emplace_back(_Cont_Cons{a0, a00});
            _stack.emplace_back(_Enter{a10.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Cont_Cons>(_frame));
        auto a0 = std::move(_f.a0);
        auto a00 = std::move(_f.a00);
        auto _cs = std::move(_result);
        List<T1> l1 = std::move(_cs.first);
        List<T1> l2 = std::move(_cs.second);
        _result = std::make_pair(List<T1>::cons(a0, std::move(l1)),
                                 List<T1>::cons(a00, std::move(l2)));
      }
    }
    return _result;
  }

  static List<uint64_t> merge_fuel(uint64_t fuel, List<uint64_t> l1,
                                   List<uint64_t> l2);
  static List<uint64_t> merge(const List<uint64_t> &l1,
                              const List<uint64_t> &l2);
  static List<uint64_t> merge_sort_fuel(uint64_t fuel, List<uint64_t> l);
  static List<uint64_t> merge_sort(const List<uint64_t> &l);
  static std::pair<List<uint64_t>, List<uint64_t>>
  partition(uint64_t pivot, const List<uint64_t> &l);
  static List<uint64_t> quicksort_fuel(uint64_t fuel, List<uint64_t> l);
  static List<uint64_t> quicksort(const List<uint64_t> &l);
  static bool is_sorted_aux(uint64_t prev, const List<uint64_t> &l);
  static bool is_sorted(const List<uint64_t> &l);

  /// merge_by cmp merges with custom comparator.
  template <typename F1>
    requires std::is_invocable_r_v<bool, F1 &, uint64_t &, uint64_t &>
  static List<uint64_t>
  merge_by_fuel(uint64_t fuel, F1 &&cmp, List<uint64_t> l1,
                List<uint64_t> l2) { /// _Enter: captures varying parameters for
                                     /// each recursive call.

    struct _Enter {
      List<uint64_t> l2;
      List<uint64_t> l1;
      uint64_t fuel;
    };

    /// _Resume1: saves [a0], resumes after recursive call with _result.
    struct _Resume1 {
      uint64_t a0;
    };

    /// _Resume2: saves [a00], resumes after recursive call with _result.
    struct _Resume2 {
      uint64_t a00;
    };

    using _Frame = std::variant<_Enter, _Resume1, _Resume2>;
    List<uint64_t> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{std::move(l2), std::move(l1), fuel});
    /// Loopified merge_by_fuel: _Enter -> _Resume1 -> _Resume2.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        List<uint64_t> l2 = std::move(_f.l2);
        List<uint64_t> l1 = std::move(_f.l1);
        uint64_t fuel = _f.fuel;
        if (fuel <= 0) {
          _result = List<uint64_t>::nil();
        } else {
          uint64_t f = fuel - 1;
          if (std::holds_alternative<typename List<uint64_t>::Nil>(
                  l1.v_mut())) {
            _result = std::move(l2);
          } else {
            auto &[a0, a1] =
                std::get<typename List<uint64_t>::Cons>(l1.v_mut());
            if (std::holds_alternative<typename List<uint64_t>::Nil>(
                    l2.v_mut())) {
              _result = std::move(l1);
            } else {
              auto &[a00, a10] =
                  std::get<typename List<uint64_t>::Cons>(l2.v_mut());
              if (cmp(a0, a00)) {
                _stack.emplace_back(_Resume1{std::move(a0)});
                _stack.emplace_back(_Enter{l2, *a1, f});
              } else {
                _stack.emplace_back(_Resume2{std::move(a00)});
                _stack.emplace_back(_Enter{*a10, l1, f});
              }
            }
          }
        }
      } else if (std::holds_alternative<_Resume1>(_frame)) {
        auto _f = std::move(std::get<_Resume1>(_frame));
        _result = List<uint64_t>::cons(_f.a0, std::move(_result));
      } else {
        auto _f = std::move(std::get<_Resume2>(_frame));
        _result = List<uint64_t>::cons(_f.a00, std::move(_result));
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &, uint64_t &>
  static List<uint64_t> merge_by(F0 &&cmp, const List<uint64_t> &l1,
                                 const List<uint64_t> &l2) {
    return merge_by_fuel((len_impl<uint64_t>(l1) + len_impl<uint64_t>(l2)), cmp,
                         l1, l2);
  }

  /// remove_duplicates removes consecutive duplicates from sorted list.
  static List<uint64_t> remove_duplicates(const List<uint64_t> &l);
  /// uniq_sorted variant that preserves order.
  static List<uint64_t> uniq_sorted_aux(uint64_t prev, bool seen,
                                        const List<uint64_t> &l);
  static List<uint64_t> uniq_sorted(const List<uint64_t> &l);
};

#endif // INCLUDED_LOOPIFY_SORTING
