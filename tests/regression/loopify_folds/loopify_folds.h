#ifndef INCLUDED_LOOPIFY_FOLDS
#define INCLUDED_LOOPIFY_FOLDS

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

  uint64_t length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (a1->length() + 1);
    }
  }
};

struct LoopifyFolds {
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &, uint64_t &>
  static uint64_t fold_left(F0 &&f, uint64_t acc, const List<uint64_t> &l) {
    const List<uint64_t> *_loop_l = &l;
    uint64_t _loop_acc = std::move(acc);
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        return _loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        _loop_l = a1.get();
        _loop_acc = f(_loop_acc, a0);
      }
    }
  }

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &, uint64_t &>
  static uint64_t
  fold_right(F0 &&f, const List<uint64_t> &l,
             uint64_t acc) { /// _Enter: captures varying parameters for each
                             /// recursive call.

    struct _Enter {
      const List<uint64_t> *l;
    };

    /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
    struct _Resume_Cons {
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
          _stack.emplace_back(_Resume_Cons{a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = f(_f.a0, std::move(_result));
      }
    }
    return _result;
  }

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
        _result = List<uint64_t>::cons(_f.acc, std::move(_result));
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &, uint64_t &>
  static List<uint64_t> scanr(F0 &&f, uint64_t acc, const List<uint64_t> &l) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
      return List<uint64_t>::cons(acc, List<uint64_t>::nil());
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
      auto &&_sv0 = scanr(f, acc, *a1);
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
        return List<uint64_t>::cons(acc, List<uint64_t>::nil());
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_sv0.v());
        return List<uint64_t>::cons(f(a0, a00), *a10);
      }
    }
  }

  template <typename F1>
    requires std::is_invocable_r_v<uint64_t, F1 &, uint64_t &, uint64_t &>
  static uint64_t foldl1_fuel(uint64_t fuel, F1 &&f, const List<uint64_t> &l) {
    List<uint64_t> _loop_l = l;
    uint64_t _loop_fuel = std::move(fuel);
    while (true) {
      if (_loop_fuel <= 0) {
        return UINT64_C(0);
      } else {
        uint64_t fuel_ = _loop_fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l.v())) {
          return UINT64_C(0);
        } else {
          const auto &[a0, a1] =
              std::get<typename List<uint64_t>::Cons>(_loop_l.v());
          auto &&_sv0 = *a1;
          if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
            return a0;
          } else {
            const auto &[a00, a10] =
                std::get<typename List<uint64_t>::Cons>(_sv0.v());
            _loop_l = List<uint64_t>::cons(f(a0, a00), *a10);
            _loop_fuel = fuel_;
          }
        }
      }
    }
  }

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &, uint64_t &>
  static uint64_t foldl1(F0 &&f, const List<uint64_t> &l) {
    return foldl1_fuel(l.length(), f, l);
  }

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &, uint64_t &>
  static uint64_t
  foldr1(F0 &&f,
         const List<uint64_t> &l) { /// _Enter: captures varying parameters for
                                    /// each recursive call.

    struct _Enter {
      const List<uint64_t> *l;
    };

    /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
    struct _Resume_Cons {
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
            _stack.emplace_back(_Resume_Cons{a0});
            _stack.emplace_back(_Enter{a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = f(_f.a0, std::move(_result));
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<std::pair<uint64_t, uint64_t>, F0 &,
                                   uint64_t &, uint64_t &>
  static std::pair<uint64_t, List<uint64_t>>
  map_accum(F0 &&f, uint64_t acc,
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
    /// Loopified map_accum: _Enter -> _Cont_acc_.
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
          uint64_t acc_ = std::move(_cs.first);
          uint64_t y = std::move(_cs.second);
          _stack.emplace_back(_Cont_acc_{y});
          _stack.emplace_back(_Enter{a1.get(), std::move(acc_)});
        }
      } else {
        auto _f = std::move(std::get<_Cont_acc_>(_frame));
        uint64_t y = _f.y;
        auto _cs1 = std::move(_result);
        uint64_t final_acc = std::move(_cs1.first);
        List<uint64_t> ys = std::move(_cs1.second);
        _result = std::make_pair(std::move(final_acc),
                                 List<uint64_t>::cons(y, std::move(ys)));
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static List<uint64_t>
  iterate_accum(F0 &&f, uint64_t n,
                uint64_t x) { /// _Enter: captures varying parameters for each
                              /// recursive call.

    struct _Enter {
      uint64_t x;
      uint64_t n;
    };

    /// _Resume_n_: saves [x], resumes after recursive call with _result.
    struct _Resume_n_ {
      uint64_t x;
    };

    using _Frame = std::variant<_Enter, _Resume_n_>;
    List<uint64_t> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{x, n});
    /// Loopified iterate_accum: _Enter -> _Resume_n_.
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
          uint64_t n_ = n - 1;
          _stack.emplace_back(_Resume_n_{x});
          _stack.emplace_back(_Enter{f(x), n_});
        }
      } else {
        auto _f = std::move(std::get<_Resume_n_>(_frame));
        _result = List<uint64_t>::cons(_f.x, std::move(_result));
      }
    }
    return _result;
  }

  template <typename F1>
    requires std::is_invocable_r_v<std::pair<uint64_t, uint64_t>, F1 &,
                                   uint64_t &>
  static List<uint64_t>
  unfold_fuel(uint64_t fuel, F1 &&f,
              uint64_t seed) { /// _Enter: captures varying parameters for each
                               /// recursive call.

    struct _Enter {
      uint64_t seed;
      uint64_t fuel;
    };

    /// _Resume_x: saves [x], resumes after recursive call with _result.
    struct _Resume_x {
      uint64_t x;
    };

    using _Frame = std::variant<_Enter, _Resume_x>;
    List<uint64_t> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{seed, fuel});
    /// Loopified unfold_fuel: _Enter -> _Resume_x.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        uint64_t seed = _f.seed;
        uint64_t fuel = _f.fuel;
        if (fuel <= 0) {
          _result = List<uint64_t>::nil();
        } else {
          uint64_t fuel_ = fuel - 1;
          auto _cs = f(seed);
          uint64_t x = std::move(_cs.first);
          uint64_t next_seed = std::move(_cs.second);
          _stack.emplace_back(_Resume_x{x});
          _stack.emplace_back(_Enter{next_seed, fuel_});
        }
      } else {
        auto _f = std::move(std::get<_Resume_x>(_frame));
        _result = List<uint64_t>::cons(_f.x, std::move(_result));
      }
    }
    return _result;
  }

  template <typename F1>
    requires std::is_invocable_r_v<std::pair<uint64_t, uint64_t>, F1 &,
                                   uint64_t &>
  static List<uint64_t> unfold(uint64_t _x0, F1 &&_x1, uint64_t _x2) {
    return unfold_fuel(_x0, _x1, _x2);
  }
};

#endif // INCLUDED_LOOPIFY_FOLDS
