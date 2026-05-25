#ifndef INCLUDED_LOOPIFY_LIST_GENERATORS
#define INCLUDED_LOOPIFY_LIST_GENERATORS

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

struct LoopifyListGenerators {
  static List<uint64_t> cycle_fuel(uint64_t fuel, uint64_t n,
                                   const List<uint64_t> &l);
  static List<uint64_t> cycle(uint64_t n, const List<uint64_t> &l);

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

    /// _Resume_n_: saves [x], resumes after recursive call with _result.
    struct _Resume_n_ {
      uint64_t x;
    };

    using _Frame = std::variant<_Enter, _Resume_n_>;
    List<uint64_t> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{x, n});
    /// Loopified iterate: _Enter -> _Resume_n_.
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
        _result = List<uint64_t>::cons(_f.x, _result);
      }
    }
    return _result;
  }

  template <typename F2>
    requires std::is_invocable_r_v<uint64_t, F2 &, uint64_t &>
  static List<uint64_t> build_list_aux(
      uint64_t n, uint64_t idx,
      F2 &&f) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      uint64_t idx;
      uint64_t n;
    };

    /// _Resume_n_: saves [idx], resumes after recursive call with _result.
    struct _Resume_n_ {
      uint64_t idx;
    };

    using _Frame = std::variant<_Enter, _Resume_n_>;
    List<uint64_t> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{idx, n});
    /// Loopified build_list_aux: _Enter -> _Resume_n_.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        uint64_t idx = _f.idx;
        uint64_t n = _f.n;
        if (n <= 0) {
          _result = List<uint64_t>::nil();
        } else {
          uint64_t n_ = n - 1;
          _stack.emplace_back(_Resume_n_{f(idx)});
          _stack.emplace_back(_Enter{(idx + UINT64_C(1)), n_});
        }
      } else {
        auto _f = std::move(std::get<_Resume_n_>(_frame));
        _result = List<uint64_t>::cons(_f.idx, _result);
      }
    }
    return _result;
  }

  template <typename F1>
    requires std::is_invocable_r_v<uint64_t, F1 &, uint64_t &>
  static List<uint64_t> build_list(uint64_t n, F1 &&f) {
    return build_list_aux(n, UINT64_C(0), f);
  }

  template <typename F1>
    requires std::is_invocable_r_v<uint64_t, F1 &, uint64_t &>
  static List<uint64_t> init_list(uint64_t n, F1 &&f) {
    if (n <= 0) {
      return List<uint64_t>::nil();
    } else {
      uint64_t n_ = n - 1;
      return List<uint64_t>::cons(f(UINT64_C(0)), [&]() {
        auto go_impl = [&](auto &_self_go, uint64_t i) -> List<uint64_t> {
          if (i <= 0) {
            return List<uint64_t>::nil();
          } else {
            uint64_t i_ = i - 1;
            return List<uint64_t>::cons(f((((n - i) > n ? 0 : (n - i)))),
                                        _self_go(_self_go, i_));
          }
        };
        auto go = [&](uint64_t i) -> List<uint64_t> {
          return go_impl(go_impl, i);
        };
        return go(n_);
      }());
    }
  }

  static List<uint64_t> range(uint64_t start, uint64_t count);
  static List<uint64_t> replicate_elem(uint64_t n, uint64_t x);
  static List<uint64_t> replicate_each(uint64_t n, const List<uint64_t> &l);

  template <typename F1>
    requires std::is_invocable_r_v<uint64_t, F1 &, uint64_t &>
  static List<uint64_t> tabulate(uint64_t n, F1 &&f) {
    if (n <= 0) {
      return List<uint64_t>::nil();
    } else {
      uint64_t n_ = n - 1;
      auto aux_impl = [&](auto &_self_aux, uint64_t idx) -> List<uint64_t> {
        if (idx <= 0) {
          return List<uint64_t>::cons(f(UINT64_C(0)), List<uint64_t>::nil());
        } else {
          uint64_t idx_ = idx - 1;
          return _self_aux(_self_aux, idx_)
              .app(List<uint64_t>::cons(f(idx), List<uint64_t>::nil()));
        }
      };
      auto aux = [&](uint64_t idx) -> List<uint64_t> {
        return aux_impl(aux_impl, idx);
      };
      return aux(n_);
    }
  }

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &, uint64_t &>
  static List<uint64_t>
  zip_with(F0 &&f, const List<uint64_t> &l1,
           const List<uint64_t> &l2) { /// _Enter: captures varying parameters
                                       /// for each recursive call.

    struct _Enter {
      const List<uint64_t> *l2;
      const List<uint64_t> *l1;
    };

    /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
    struct _Resume_Cons {
      uint64_t _s0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    List<uint64_t> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l2, &l1});
    /// Loopified zip_with: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<uint64_t> &l2 = *_f.l2;
        const List<uint64_t> &l1 = *_f.l1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l1.v())) {
          _result = List<uint64_t>::nil();
        } else {
          const auto &[a0, a1] =
              std::get<typename List<uint64_t>::Cons>(l1.v());
          if (std::holds_alternative<typename List<uint64_t>::Nil>(l2.v())) {
            _result = List<uint64_t>::nil();
          } else {
            const auto &[a00, a10] =
                std::get<typename List<uint64_t>::Cons>(l2.v());
            _stack.emplace_back(_Resume_Cons{f(a0, a00)});
            _stack.emplace_back(_Enter{a10.get(), a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = List<uint64_t>::cons(_f._s0, _result);
      }
    }
    return _result;
  }

  static List<std::pair<uint64_t, uint64_t>>
  enumerate_aux(uint64_t idx, const List<uint64_t> &l);
  static List<std::pair<uint64_t, uint64_t>> enumerate(const List<uint64_t> &l);
};

#endif // INCLUDED_LOOPIFY_LIST_GENERATORS
