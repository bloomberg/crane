#ifndef INCLUDED_LOOPIFY_HOFS
#define INCLUDED_LOOPIFY_HOFS

#include <any>
#include <memory>
#include <optional>
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
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  uint64_t length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (a1->length() + 1);
    }
  }

  List<A> app(List<A> m) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return m;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return List<A>::cons(a0, a1->app(std::move(m)));
    }
  }
};

struct LoopifyHofs {
  /// foldl1 f l folds from left with no initial value. Returns 0 for empty
  /// list.
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &, T1 &>
  static T1 foldl1_aux(F0 &&f, T1 acc, const List<T1> &l) {
    const List<T1> *_loop_l = &l;
    T1 _loop_acc = std::move(acc);
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
        return _loop_acc;
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(_loop_l->v());
        _loop_l = a1.get();
        _loop_acc = f(_loop_acc, a0);
      }
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &, T1 &>
  static T1 foldl1(F0 &&f, T1 default0, const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      return foldl1_aux<T1>(f, a0, *a1);
    }
  }

  /// forall_ p l checks if all elements satisfy predicate p.
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &>
  static bool forall_(F0 &&p, const List<T1> &l) {
    const List<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
        return true;
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(_loop_l->v());
        if (p(a0)) {
          _loop_l = a1.get();
        } else {
          return false;
        }
      }
    }
  }

  /// exists_fn p l checks if any element satisfies predicate p.
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &>
  static bool exists_fn(F0 &&p, const List<T1> &l) {
    const List<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
        return false;
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(_loop_l->v());
        if (p(a0)) {
          return true;
        } else {
          _loop_l = a1.get();
        }
      }
    }
  } /// drop_while p l drops elements while predicate holds.

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &>
  static List<T1> drop_while(F0 &&p, const List<T1> &l) {
    const List<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
        return List<T1>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(_loop_l->v());
        if (p(a0)) {
          _loop_l = a1.get();
        } else {
          return List<T1>::cons(a0, *a1);
        }
      }
    }
  } /// take_while p l takes elements while predicate holds.

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &>
  static List<T1>
  take_while(F0 &&p,
             const List<T1> &l) { /// _Enter: captures varying parameters for
                                  /// each recursive call.

    struct _Enter {
      const List<T1> *l;
    };

    /// _Resume1: saves [a0], resumes after recursive call with _result.
    struct _Resume1 {
      T1 a0;
    };

    using _Frame = std::variant<_Enter, _Resume1>;
    List<T1> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified take_while: _Enter -> _Resume1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<T1> &l = *_f.l;
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          _result = List<T1>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
          if (p(a0)) {
            _stack.emplace_back(_Resume1{a0});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            _result = List<T1>::nil();
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume1>(_frame));
        _result = List<T1>::cons(_f.a0, _result);
      }
    }
    return _result;
  }

  /// flat_map f l maps f and flattens results.
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<List<T2>, F0 &, T1 &>
  static List<T2>
  flat_map(F0 &&f,
           const List<T1> &l) { /// _Enter: captures varying parameters for each
                                /// recursive call.

    struct _Enter {
      const List<T1> *l;
    };

    /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
    struct _Resume_Cons {
      List<T2> _s0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    List<T2> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified flat_map: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<T1> &l = *_f.l;
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          _result = List<T2>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{std::move(f(a0))});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = _f._s0.app(_result);
      }
    }
    return _result;
  }

  /// all_pairs l1 l2 returns all pairs from two lists.
  template <typename T1, typename T2>
  static List<std::pair<T1, T2>>
  all_pairs(const List<T1> &l1,
            const List<T2> &l2) { /// _Enter: captures varying parameters for
                                  /// each recursive call.

    struct _Enter {
      const List<T1> *l1;
    };

    /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
    struct _Resume_Cons {
      List<std::pair<T1, T2>> _s0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    List<std::pair<T1, T2>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l1});
    /// Loopified all_pairs: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<T1> &l1 = *_f.l1;
        auto pair_with_impl = [](auto &_self_pair_with, T1 x,
                                 const List<T2> &l) -> List<std::pair<T1, T2>> {
          if (std::holds_alternative<typename List<T2>::Nil>(l.v())) {
            return List<std::pair<T1, T2>>::nil();
          } else {
            const auto &[a0, a1] = std::get<typename List<T2>::Cons>(l.v());
            return List<std::pair<T1, T2>>::cons(
                std::make_pair(x, a0),
                _self_pair_with(_self_pair_with, x, *a1));
          }
        };
        auto pair_with = [&](T1 x,
                             const List<T2> &l) -> List<std::pair<T1, T2>> {
          return pair_with_impl(pair_with_impl, x, l);
        };
        if (std::holds_alternative<typename List<T1>::Nil>(l1.v())) {
          _result = List<std::pair<T1, T2>>::nil();
        } else {
          const auto &[a00, a10] = std::get<typename List<T1>::Cons>(l1.v());
          _stack.emplace_back(_Resume_Cons{std::move(pair_with(a00, l2))});
          _stack.emplace_back(_Enter{a10.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = _f._s0.app(_result);
      }
    }
    return _result;
  }

  /// find_indices p l finds all indices where p is true.
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static List<uint64_t>
  find_indices_aux(F0 &&p, const List<uint64_t> &l,
                   uint64_t i) { /// _Enter: captures varying parameters for
                                 /// each recursive call.

    struct _Enter {
      uint64_t i;
      const List<uint64_t> *l;
    };

    /// _Resume1: saves [i], resumes after recursive call with _result.
    struct _Resume1 {
      uint64_t i;
    };

    using _Frame = std::variant<_Enter, _Resume1>;
    List<uint64_t> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{i, &l});
    /// Loopified find_indices_aux: _Enter -> _Resume1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        uint64_t i = _f.i;
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<uint64_t>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          if (p(a0)) {
            _stack.emplace_back(_Resume1{i});
            _stack.emplace_back(_Enter{(i + 1), a1.get()});
          } else {
            _stack.emplace_back(_Enter{(i + 1), a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume1>(_frame));
        _result = List<uint64_t>::cons(_f.i, _result);
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static List<uint64_t> find_indices(F0 &&p, const List<uint64_t> &l) {
    return find_indices_aux(p, l, UINT64_C(0));
  }

  /// delete_by eq x l deletes first element equal to x.
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &, uint64_t &>
  static List<uint64_t>
  delete_by(F0 &&eq, uint64_t x,
            const List<uint64_t> &l) { /// _Enter: captures varying parameters
                                       /// for each recursive call.

    struct _Enter {
      const List<uint64_t> *l;
    };

    /// _Resume1: saves [a0], resumes after recursive call with _result.
    struct _Resume1 {
      uint64_t a0;
    };

    using _Frame = std::variant<_Enter, _Resume1>;
    List<uint64_t> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified delete_by: _Enter -> _Resume1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<uint64_t>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          if (eq(x, a0)) {
            _result = *a1;
          } else {
            _stack.emplace_back(_Resume1{a0});
            _stack.emplace_back(_Enter{a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume1>(_frame));
        _result = List<uint64_t>::cons(_f.a0, _result);
      }
    }
    return _result;
  }

  /// is_prefix_of l1 l2 checks if l1 is a prefix of l2.
  static bool is_prefix_of(const List<uint64_t> &l1, const List<uint64_t> &l2);
  /// lookup_all key l finds all values associated with key in association list.
  static List<uint64_t>
  lookup_all(uint64_t key, const List<std::pair<uint64_t, uint64_t>> &l);

  /// scanl f acc l scan from left with accumulator.
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &, uint64_t &>
  static List<uint64_t>
  scanl(F0 &&f, uint64_t acc,
        const List<uint64_t> &l) { /// _Enter: captures varying parameters for
                                   /// each recursive call.

    struct _Enter {
      const List<uint64_t> *l;
      uint64_t acc;
    };

    /// _Resume_Cons: saves [acc], resumes after recursive call with _result.
    struct _Resume_Cons {
      uint64_t acc;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    List<uint64_t> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l, acc});
    /// Loopified scanl: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<uint64_t> &l = *_f.l;
        uint64_t acc = _f.acc;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<uint64_t>::cons(acc, List<uint64_t>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{acc});
          _stack.emplace_back(_Enter{a1.get(), f(acc, a0)});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = List<uint64_t>::cons(_f.acc, _result);
      }
    }
    return _result;
  }

  /// scanl1 f l like scanl but no initial value, uses first element.
  template <typename F1>
    requires std::is_invocable_r_v<uint64_t, F1 &, uint64_t &, uint64_t &>
  static List<uint64_t>
  scanl1_fuel(uint64_t fuel, F1 &&f,
              List<uint64_t> l) { /// _Enter: captures varying parameters for
                                  /// each recursive call.

    struct _Enter {
      List<uint64_t> l;
      uint64_t fuel;
    };

    /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
    struct _Resume_Cons {
      uint64_t a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    List<uint64_t> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{l, fuel});
    /// Loopified scanl1_fuel: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        List<uint64_t> l = std::move(_f.l);
        uint64_t fuel = _f.fuel;
        if (fuel <= 0) {
          _result = std::move(l);
        } else {
          uint64_t g = fuel - 1;
          if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v_mut())) {
            _result = List<uint64_t>::nil();
          } else {
            auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v_mut());
            auto &&_sv0 = *a1;
            if (std::holds_alternative<typename List<uint64_t>::Nil>(
                    _sv0.v())) {
              _result =
                  List<uint64_t>::cons(std::move(a0), List<uint64_t>::nil());
            } else {
              const auto &[a00, a10] =
                  std::get<typename List<uint64_t>::Cons>(_sv0.v());
              _stack.emplace_back(_Resume_Cons{a0});
              _stack.emplace_back(
                  _Enter{List<uint64_t>::cons(f(a0, a00), *a10), g});
            }
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = List<uint64_t>::cons(_f.a0, _result);
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &, uint64_t &>
  static List<uint64_t> scanl1(F0 &&f, const List<uint64_t> &l) {
    return scanl1_fuel(l.length(), f, l);
  }

  /// foldr1 f l fold right with no initial value.
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &, uint64_t &>
  static uint64_t
  foldr1(F0 &&f,
         const List<uint64_t> &l) { /// _Enter: captures varying parameters for
                                    /// each recursive call.

    struct _Enter {
      const List<uint64_t> *l;
    };

    /// _Resume_Cons: saves [f, a0], resumes after recursive call with _result.
    struct _Resume_Cons {
      F0 f;
      uint64_t a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    uint64_t _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified foldr1: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          auto &&_sv = *a1;
          if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
            _result = std::move(a0);
          } else {
            _stack.emplace_back(_Resume_Cons{f, a0});
            _stack.emplace_back(_Enter{a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = _f.f(_f.a0, _result);
      }
    }
    return _result;
  }

  /// Helper: get head of list with default.
  static uint64_t head_default(uint64_t default0, const List<uint64_t> &l);

  /// scanr f acc l scan from right.
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &, uint64_t &>
  static List<uint64_t>
  scanr(F0 &&f, uint64_t acc,
        const List<uint64_t> &l) { /// _Enter: captures varying parameters for
                                   /// each recursive call.

    struct _Enter {
      const List<uint64_t> *l;
    };

    /// _Cont_Cons: saves [a0, acc, f], resumes after recursive call, then
    /// processes rest.
    struct _Cont_Cons {
      uint64_t a0;
      uint64_t acc;
      F0 f;
    };

    using _Frame = std::variant<_Enter, _Cont_Cons>;
    List<uint64_t> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified scanr: _Enter -> _Cont_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<uint64_t>::cons(acc, List<uint64_t>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(_Cont_Cons{a0, acc, f});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Cont_Cons>(_frame));
        uint64_t a0 = _f.a0;
        uint64_t acc = _f.acc;
        F0 f = _f.f;
        List<uint64_t> rest = _result;
        uint64_t h = head_default(acc, rest);
        _result = List<uint64_t>::cons(f(a0, h), std::move(rest));
      }
    }
    return _result;
  } /// scanr1 f l scanr with no initial value.

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &, uint64_t &>
  static List<uint64_t>
  scanr1(F0 &&f,
         const List<uint64_t> &l) { /// _Enter: captures varying parameters for
                                    /// each recursive call.

    struct _Enter {
      const List<uint64_t> *l;
    };

    /// _Cont_Cons: saves [a0, f], resumes after recursive call, then processes
    /// rest.
    struct _Cont_Cons {
      uint64_t a0;
      F0 f;
    };

    using _Frame = std::variant<_Enter, _Cont_Cons>;
    List<uint64_t> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified scanr1: _Enter -> _Cont_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<uint64_t>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          auto &&_sv = *a1;
          if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
            _result = List<uint64_t>::cons(a0, List<uint64_t>::nil());
          } else {
            _stack.emplace_back(_Cont_Cons{a0, f});
            _stack.emplace_back(_Enter{a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Cont_Cons>(_frame));
        uint64_t a0 = _f.a0;
        F0 f = _f.f;
        List<uint64_t> rest = _result;
        uint64_t h = head_default(a0, rest);
        _result = List<uint64_t>::cons(f(a0, h), std::move(rest));
      }
    }
    return _result;
  }

  /// mapcat f l maps f and concatenates results (concat_map).
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<List<T1>, F0 &, uint64_t &>
  static List<T1>
  mapcat(F0 &&f,
         const List<uint64_t> &l) { /// _Enter: captures varying parameters for
                                    /// each recursive call.

    struct _Enter {
      const List<uint64_t> *l;
    };

    /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
    struct _Resume_Cons {
      List<T1> _s0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    List<T1> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified mapcat: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<T1>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{std::move(f(a0))});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = _f._s0.app(_result);
      }
    }
    return _result;
  }

  /// map_maybe f l maps f and filters out None results.
  template <typename F0>
    requires std::is_invocable_r_v<std::optional<uint64_t>, F0 &, uint64_t &>
  static List<uint64_t>
  map_maybe(F0 &&f,
            const List<uint64_t> &l) { /// _Enter: captures varying parameters
                                       /// for each recursive call.

    struct _Enter {
      const List<uint64_t> *l;
    };

    /// _Cont_Cons: saves [a0, f], resumes after recursive call, then processes
    /// rest.
    struct _Cont_Cons {
      uint64_t a0;
      F0 f;
    };

    using _Frame = std::variant<_Enter, _Cont_Cons>;
    List<uint64_t> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified map_maybe: _Enter -> _Cont_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<uint64_t>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(_Cont_Cons{a0, f});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Cont_Cons>(_frame));
        uint64_t a0 = _f.a0;
        F0 f = _f.f;
        List<uint64_t> rest = _result;
        auto _cs = f(a0);
        if (_cs.has_value()) {
          const uint64_t &y = *_cs;
          _result = List<uint64_t>::cons(y, std::move(rest));
        } else {
          _result = std::move(rest);
        }
      }
    }
    return _result;
  }

  /// bool_all p l checks if all elements satisfy p (same as forall_).
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static bool
  bool_all(F0 &&p,
           const List<uint64_t> &l) { /// _Enter: captures varying parameters
                                      /// for each recursive call.

    struct _Enter {
      const List<uint64_t> *l;
    };

    /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
    struct _Resume_Cons {
      bool a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    bool _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified bool_all: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = true;
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{p(a0)});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = (_f.a0 && _result);
      }
    }
    return _result;
  }

  /// merge_by cmp l1 l2 merges two lists using comparison function.
  template <typename F1>
    requires std::is_invocable_r_v<uint64_t, F1 &, uint64_t &, uint64_t &>
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
    _stack.emplace_back(_Enter{l2, l1, fuel});
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
          _result = std::move(l1);
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
              if (cmp(a0, a00) <= UINT64_C(0)) {
                _stack.emplace_back(_Resume1{std::move(a0)});
                _stack.emplace_back(_Enter{l2, std::move(*a1), f});
              } else {
                _stack.emplace_back(_Resume2{std::move(a00)});
                _stack.emplace_back(_Enter{std::move(*a10), l1, f});
              }
            }
          }
        }
      } else if (std::holds_alternative<_Resume1>(_frame)) {
        auto _f = std::move(std::get<_Resume1>(_frame));
        _result = List<uint64_t>::cons(_f.a0, _result);
      } else {
        auto _f = std::move(std::get<_Resume2>(_frame));
        _result = List<uint64_t>::cons(_f.a00, _result);
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &, uint64_t &>
  static List<uint64_t> merge_by(F0 &&cmp, const List<uint64_t> &l1,
                                 const List<uint64_t> &l2) {
    return merge_by_fuel((l1.length() + l2.length()), cmp, l1, l2);
  }

  /// max_by f l finds element with maximum f value.
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static uint64_t
  max_by(F0 &&f,
         const List<uint64_t> &l) { /// _Enter: captures varying parameters for
                                    /// each recursive call.

    struct _Enter {
      const List<uint64_t> *l;
    };

    /// _Cont_Cons: saves [a0, f], resumes after recursive call, then processes
    /// rest.
    struct _Cont_Cons {
      uint64_t a0;
      F0 f;
    };

    using _Frame = std::variant<_Enter, _Cont_Cons>;
    uint64_t _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified max_by: _Enter -> _Cont_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          auto &&_sv = *a1;
          if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
            _result = f(a0);
          } else {
            _stack.emplace_back(_Cont_Cons{a0, f});
            _stack.emplace_back(_Enter{a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Cont_Cons>(_frame));
        uint64_t a0 = _f.a0;
        F0 f = _f.f;
        uint64_t rest_max = _result;
        uint64_t fx = f(a0);
        if (rest_max <= fx) {
          _result = std::move(fx);
        } else {
          _result = std::move(rest_max);
        }
      }
    }
    return _result;
  }

  /// iterate f n x generates x, f(x), f(f(x)), ... of length n.
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static List<uint64_t>
  iterate(F0 &&f, uint64_t n,
          uint64_t x) { /// _Enter: captures varying parameters for each
                        /// recursive call.

    struct _Enter {
      uint64_t x;
      uint64_t n;
    };

    /// _Resume_m: saves [x], resumes after recursive call with _result.
    struct _Resume_m {
      uint64_t x;
    };

    using _Frame = std::variant<_Enter, _Resume_m>;
    List<uint64_t> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{x, n});
    /// Loopified iterate: _Enter -> _Resume_m.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        uint64_t x = _f.x;
        uint64_t n = _f.n;
        if (n <= 0) {
          _result = List<uint64_t>::nil();
        } else {
          uint64_t m = n - 1;
          _stack.emplace_back(_Resume_m{x});
          _stack.emplace_back(_Enter{f(x), m});
        }
      } else {
        auto _f = std::move(std::get<_Resume_m>(_frame));
        _result = List<uint64_t>::cons(_f.x, _result);
      }
    }
    return _result;
  }

  /// maximum_by cmp l finds maximum element by comparison function.
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &, uint64_t &>
  static uint64_t
  maximum_by(F0 &&cmp,
             const List<uint64_t> &l) { /// _Enter: captures varying parameters
                                        /// for each recursive call.

    struct _Enter {
      const List<uint64_t> *l;
    };

    /// _Cont_Cons: saves [a0, cmp], resumes after recursive call, then
    /// processes rest.
    struct _Cont_Cons {
      uint64_t a0;
      F0 cmp;
    };

    using _Frame = std::variant<_Enter, _Cont_Cons>;
    uint64_t _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified maximum_by: _Enter -> _Cont_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          auto &&_sv = *a1;
          if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
            _result = std::move(a0);
          } else {
            _stack.emplace_back(_Cont_Cons{a0, cmp});
            _stack.emplace_back(_Enter{a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Cont_Cons>(_frame));
        uint64_t a0 = _f.a0;
        F0 cmp = _f.cmp;
        uint64_t m = _result;
        if (UINT64_C(0) <= cmp(a0, m)) {
          _result = std::move(a0);
        } else {
          _result = std::move(m);
        }
      }
    }
    return _result;
  }

  /// fold_right f l acc folds from the right.
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &, uint64_t &>
  static uint64_t
  fold_right(F0 &&f, const List<uint64_t> &l,
             uint64_t acc) { /// _Enter: captures varying parameters for each
                             /// recursive call.

    struct _Enter {
      const List<uint64_t> *l;
    };

    /// _Resume_Cons: saves [f, a0], resumes after recursive call with _result.
    struct _Resume_Cons {
      F0 f;
      uint64_t a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    uint64_t _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified fold_right: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = std::move(acc);
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{f, a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = _f.f(_f.a0, _result);
      }
    }
    return _result;
  }

  /// partition p l partitions list into (satisfies p, doesn't satisfy p).
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static std::pair<List<uint64_t>, List<uint64_t>>
  partition(F0 &&p,
            const List<uint64_t> &l) { /// _Enter: captures varying parameters
                                       /// for each recursive call.

    struct _Enter {
      const List<uint64_t> *l;
    };

    /// _Cont_Cons: saves [a0, p], resumes after recursive call, then processes
    /// rest.
    struct _Cont_Cons {
      uint64_t a0;
      F0 p;
    };

    using _Frame = std::variant<_Enter, _Cont_Cons>;
    std::pair<List<uint64_t>, List<uint64_t>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified partition: _Enter -> _Cont_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result =
              std::make_pair(List<uint64_t>::nil(), List<uint64_t>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(_Cont_Cons{a0, p});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Cont_Cons>(_frame));
        uint64_t a0 = _f.a0;
        F0 p = _f.p;
        const List<uint64_t> &yes = _result.first;
        const List<uint64_t> &no = _result.second;
        if (p(a0)) {
          _result = std::make_pair(List<uint64_t>::cons(a0, yes), no);
        } else {
          _result = std::make_pair(yes, List<uint64_t>::cons(a0, no));
        }
      }
    }
    return _result;
  }

  /// subsequences l generates all subsequences of l: 1,2 -> [],[1],[2],[1,2].
  static List<List<uint64_t>> subsequences(const List<uint64_t> &l);
  /// Helper: pair element with all elements in list.
  static List<std::pair<uint64_t, uint64_t>>
  pair_with_all(uint64_t x, const List<uint64_t> &l);
  /// cartesian l1 l2 computes cartesian product of two lists.
  static List<std::pair<uint64_t, uint64_t>>
  cartesian(const List<uint64_t> &l1, const List<uint64_t> &l2);
  /// longest_run l finds the longest consecutive run of equal elements.
  /// Matches on recursive result to decide behavior.
  static List<uint64_t> longest_run_fuel(uint64_t fuel, List<uint64_t> l);
  static List<uint64_t> longest_run(const List<uint64_t> &l);

  /// any p l checks if any element satisfies predicate (same as exists_fn but
  /// different name).
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static bool any(F0 &&p, const List<uint64_t> &l) {
    const List<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        return false;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        if (p(a0)) {
          return true;
        } else {
          _loop_l = a1.get();
        }
      }
    }
  }

  /// all p l checks if all elements satisfy predicate (same as forall_ but
  /// different name).
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static bool all(F0 &&p, const List<uint64_t> &l) {
    const List<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        return true;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        if (p(a0)) {
          _loop_l = a1.get();
        } else {
          return false;
        }
      }
    }
  }

  /// filter_not p l filters elements that don't satisfy predicate.
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static List<uint64_t>
  filter_not(F0 &&p,
             const List<uint64_t> &l) { /// _Enter: captures varying parameters
                                        /// for each recursive call.

    struct _Enter {
      const List<uint64_t> *l;
    };

    /// _Resume1: saves [a0], resumes after recursive call with _result.
    struct _Resume1 {
      uint64_t a0;
    };

    using _Frame = std::variant<_Enter, _Resume1>;
    List<uint64_t> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified filter_not: _Enter -> _Resume1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<uint64_t>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          if (p(a0)) {
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            _stack.emplace_back(_Resume1{a0});
            _stack.emplace_back(_Enter{a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume1>(_frame));
        _result = List<uint64_t>::cons(_f.a0, _result);
      }
    }
    return _result;
  }

  /// span_split p l splits at first element that doesn't satisfy p.
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static std::pair<List<uint64_t>, List<uint64_t>>
  span_split(F0 &&p,
             const List<uint64_t> &l) { /// _Enter: captures varying parameters
                                        /// for each recursive call.

    struct _Enter {
      const List<uint64_t> *l;
    };

    /// _Cont1: saves [a0], resumes after recursive call, then processes rest.
    struct _Cont1 {
      uint64_t a0;
    };

    using _Frame = std::variant<_Enter, _Cont1>;
    std::pair<List<uint64_t>, List<uint64_t>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified span_split: _Enter -> _Cont1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result =
              std::make_pair(List<uint64_t>::nil(), List<uint64_t>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          if (p(a0)) {
            _stack.emplace_back(_Cont1{a0});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            _result = std::make_pair(List<uint64_t>::nil(),
                                     List<uint64_t>::cons(a0, *a1));
          }
        }
      } else {
        auto _f = std::move(std::get<_Cont1>(_frame));
        uint64_t a0 = _f.a0;
        const List<uint64_t> &taken = _result.first;
        const List<uint64_t> &rest = _result.second;
        _result = std::make_pair(List<uint64_t>::cons(a0, taken), rest);
      }
    }
    return _result;
  }

  /// group_by_eq eq l groups consecutive elements by equality function.
  template <typename F1>
    requires std::is_invocable_r_v<bool, F1 &, uint64_t &, uint64_t &>
  static List<List<uint64_t>> group_by_eq_fuel(uint64_t fuel, F1 &&eq,
                                               const List<uint64_t> &l) {
    if (fuel <= 0) {
      return List<List<uint64_t>>::nil();
    } else {
      uint64_t f = fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        return List<List<uint64_t>>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        auto &&_sv0 = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
          return List<List<uint64_t>>::cons(
              List<uint64_t>::cons(a0, List<uint64_t>::nil()),
              List<List<uint64_t>>::nil());
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(_sv0.v());
          if (eq(a0, a00)) {
            auto &&_sv1 = group_by_eq_fuel(f, eq, *a1);
            if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
                    _sv1.v())) {
              return List<List<uint64_t>>::cons(
                  List<uint64_t>::cons(a0, List<uint64_t>::nil()),
                  List<List<uint64_t>>::nil());
            } else {
              const auto &[a01, a11] =
                  std::get<typename List<List<uint64_t>>::Cons>(_sv1.v());
              return List<List<uint64_t>>::cons(List<uint64_t>::cons(a0, a01),
                                                *a11);
            }
          } else {
            return List<List<uint64_t>>::cons(
                List<uint64_t>::cons(a0, List<uint64_t>::nil()),
                group_by_eq_fuel(f, eq, *a1));
          }
        }
      }
    }
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &, uint64_t &>
  static List<List<uint64_t>> group_by_eq(F0 &&eq, const List<uint64_t> &l) {
    return group_by_eq_fuel(l.length(), eq, l);
  }

  /// power_set l generates all subsets.
  static List<List<uint64_t>> power_set(const List<uint64_t> &l);

  /// map_accum_l f acc l maps with accumulator threading.
  template <typename F0>
    requires std::is_invocable_r_v<std::pair<uint64_t, uint64_t>, F0 &,
                                   uint64_t &, uint64_t &>
  static std::pair<uint64_t, List<uint64_t>>
  map_accum_l(F0 &&f, uint64_t acc,
              const List<uint64_t> &l) { /// _Enter: captures varying parameters
                                         /// for each recursive call.

    struct _Enter {
      const List<uint64_t> *l;
      uint64_t acc;
    };

    /// _Cont_acc_: saves [y], resumes after recursive call, then processes
    /// rest.
    struct _Cont_acc_ {
      uint64_t y;
    };

    using _Frame = std::variant<_Enter, _Cont_acc_>;
    std::pair<uint64_t, List<uint64_t>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l, acc});
    /// Loopified map_accum_l: _Enter -> _Cont_acc_.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<uint64_t> &l = *_f.l;
        uint64_t acc = _f.acc;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = std::make_pair(std::move(acc), List<uint64_t>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          auto _cs = f(acc, a0);
          const uint64_t &acc_ = _cs.first;
          const uint64_t &y = _cs.second;
          _stack.emplace_back(_Cont_acc_{y});
          _stack.emplace_back(_Enter{a1.get(), std::move(_cs.first)});
        }
      } else {
        auto _f = std::move(std::get<_Cont_acc_>(_frame));
        uint64_t y = _f.y;
        const uint64_t &acc__ = _result.first;
        const List<uint64_t> &ys = _result.second;
        _result = std::make_pair(std::move(_result.first),
                                 List<uint64_t>::cons(y, ys));
      }
    }
    return _result;
  }
};

#endif // INCLUDED_LOOPIFY_HOFS
