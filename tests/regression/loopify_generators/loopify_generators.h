#ifndef INCLUDED_LOOPIFY_GENERATORS
#define INCLUDED_LOOPIFY_GENERATORS

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

/// Consolidated list generator functions.
struct LoopifyGenerators {
  /// cycle n l repeats the list n times: cycle 2 1,2 -> 1,2,1,2.
  static List<uint64_t> cycle(uint64_t n, const List<uint64_t> &l);

  /// iterate f n x applies f repeatedly n times: iterate (+1) 3 5 -> 5,6,7.
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
        _result = List<uint64_t>::cons(_f.x, std::move(_result));
      }
    }
    return _result;
  }

  /// zip_with f l1 l2 zips with a combining function.
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
        _result = List<uint64_t>::cons(_f._s0, std::move(_result));
      }
    }
    return _result;
  }

  /// zip_longest l1 l2 default zips, using default for missing elements.
  static List<std::pair<uint64_t, uint64_t>>
  zip_longest_aux(const List<uint64_t> &l1, const List<uint64_t> &l2,
                  uint64_t default0, uint64_t fuel);
  static uint64_t len_impl(const List<uint64_t> &l);
  static List<std::pair<uint64_t, uint64_t>>
  zip_longest(const List<uint64_t> &l1, const List<uint64_t> &l2,
              uint64_t default0);
  /// build_list n builds tree-like list structure: build_list(4) -> 2,4,2.
  static List<uint64_t> build_list_fuel(uint64_t fuel, uint64_t n);
  static List<uint64_t> build_list(uint64_t n);
  /// take n l returns first n elements.
  static List<uint64_t> take(uint64_t n, const List<uint64_t> &l);
  /// repeat x n creates list with n copies of x.
  static List<uint64_t> repeat(uint64_t x, uint64_t n);

  /// unfold f n init unfolds a list from seed value.
  template <typename F1>
    requires std::is_invocable_r_v<std::pair<uint64_t, uint64_t>, F1 &,
                                   uint64_t &>
  static List<uint64_t>
  unfold_fuel(uint64_t fuel, F1 &&f, uint64_t n,
              uint64_t seed) { /// _Enter: captures varying parameters for each
                               /// recursive call.

    struct _Enter {
      uint64_t seed;
      uint64_t n;
      uint64_t fuel;
    };

    /// _Resume_val: saves [val], resumes after recursive call with _result.
    struct _Resume_val {
      uint64_t val;
    };

    using _Frame = std::variant<_Enter, _Resume_val>;
    List<uint64_t> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{seed, n, fuel});
    /// Loopified unfold_fuel: _Enter -> _Resume_val.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        uint64_t seed = _f.seed;
        uint64_t n = _f.n;
        uint64_t fuel = _f.fuel;
        if (fuel <= 0) {
          _result = List<uint64_t>::nil();
        } else {
          uint64_t g = fuel - 1;
          if (n == UINT64_C(0)) {
            _result = List<uint64_t>::nil();
          } else {
            auto _cs = f(seed);
            uint64_t val = std::move(_cs.first);
            uint64_t next_seed = std::move(_cs.second);
            _stack.emplace_back(_Resume_val{val});
            _stack.emplace_back(
                _Enter{next_seed,
                       (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), g});
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume_val>(_frame));
        _result = List<uint64_t>::cons(_f.val, std::move(_result));
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<std::pair<uint64_t, uint64_t>, F0 &,
                                   uint64_t &>
  static List<uint64_t> unfold(F0 &&f, uint64_t n, uint64_t seed) {
    return unfold_fuel(UINT64_C(100), f, n, seed);
  }

  /// tabulate n f generates f 0, f 1, ..., f (n-1) (same as init_list but
  /// different naming).
  template <typename F1>
    requires std::is_invocable_r_v<uint64_t, F1 &, uint64_t &>
  static List<uint64_t> tabulate(uint64_t n, F1 &&f) {
    auto go_impl = [&](auto &_self_go, uint64_t i) -> List<uint64_t> {
      if (i <= 0) {
        return List<uint64_t>::nil();
      } else {
        uint64_t j = i - 1;
        return List<uint64_t>::cons(f((((n - i) > n ? 0 : (n - i)))),
                                    _self_go(_self_go, j));
      }
    };
    auto go = [&](uint64_t i) -> List<uint64_t> { return go_impl(go_impl, i); };
    return go(n);
  }

  /// Helper: replicate single element n times.
  static List<uint64_t> replicate_single(uint64_t x, uint64_t n);
  /// replicate_each n l replicates each element n times: replicate_each 2 1,2
  /// -> 1,1,2,2.
  static List<uint64_t> replicate_each(uint64_t n, const List<uint64_t> &l);
};

#endif // INCLUDED_LOOPIFY_GENERATORS
