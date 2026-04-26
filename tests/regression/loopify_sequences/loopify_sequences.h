#ifndef INCLUDED_LOOPIFY_SEQUENCES
#define INCLUDED_LOOPIFY_SEQUENCES

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> struct is_shared_ptr : std::false_type {};

template <typename T>
struct is_shared_ptr<std::shared_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> struct is_optional : std::false_type {};

template <typename T> struct is_optional<std::optional<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_shared<T>(x->clone()) : nullptr;
  } else {
    return x;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using TargetBare = std::remove_cvref_t<Target>;
  using SourceBare = std::remove_cvref_t<Source>;
  if constexpr (is_unique_ptr<TargetBare>::value) {
    using Inner = typename is_unique_ptr<TargetBare>::element_type;
    if constexpr (is_unique_ptr<SourceBare>::value) {
      using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires {
                             typename Inner::crane_element_type;
                             x->template clone_as<
                                 typename Inner::crane_element_type>();
                           }) {
        return std::make_unique<Inner>(
            x->template clone_as<typename Inner::crane_element_type>());
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x->clone());
      }
    } else {
      if constexpr (requires { x.clone(); }) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (std::is_same_v<Inner, SourceBare>) {
        if constexpr (requires { x.clone(); }) {
          return std::make_unique<Inner>(x.clone());
        } else {
          return std::make_unique<Inner>(x);
        }
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        if constexpr (requires { x.clone(); }) {
          return std::make_unique<Inner>(x.clone());
        } else {
          return std::make_unique<Inner>(x);
        }
      }
    }
  } else if constexpr (is_optional<TargetBare>::value) {
    using Inner = typename is_optional<TargetBare>::element_type;
    if constexpr (is_optional<SourceBare>::value) {
      if (!x)
        return std::nullopt;
      return Target{clone_as_value<Inner>(*x)};
    } else {
      return Target{clone_as_value<Inner>(x)};
    }
  } else if constexpr (is_shared_ptr<TargetBare>::value) {
    using Inner = typename is_shared_ptr<TargetBare>::element_type;
    if constexpr (is_shared_ptr<SourceBare>::value) {
      using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else if constexpr (is_unique_ptr<SourceBare>::value) {
      if (!x)
        return nullptr;
      if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_shared<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x.clone());
      }
    }
  } else if constexpr (std::is_same_v<TargetBare, SourceBare>) {
    return clone_value(x);
  } else if constexpr (is_unique_ptr<SourceBare>::value) {
    using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      if (!x)
        return Target{};
      if constexpr (requires { x->clone(); }) {
        return x->clone();
      } else {
        return *x;
      }
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else if constexpr (requires { x->clone(); }) {
      return x->clone();
    } else {
      return Target(*x);
    }
  } else if constexpr (is_shared_ptr<SourceBare>::value) {
    using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (requires {
                         typename TargetBare::crane_element_type;
                         x.template clone_as<
                             typename TargetBare::crane_element_type>();
                       }) {
    return x.template clone_as<typename TargetBare::crane_element_type>();
  } else if constexpr (requires { x.template clone_as<TargetBare>(); }) {
    return x.template clone_as<TargetBare>();
  } else {
    return Target(x);
  }
}

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;
  using crane_element_type = t_A;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  __attribute__((pure)) List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{clone_as_value<t_A>(d_a0),
                            clone_as_value<std::unique_ptr<List<t_A>>>(d_a1)});
    }
  }

  template <typename _CloneT0>
  __attribute__((pure)) List<_CloneT0> clone_as() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<_CloneT0>(typename List<_CloneT0>::Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<_CloneT0>(typename List<_CloneT0>::Cons{
          clone_as_value<_CloneT0>(d_a0),
          clone_as_value<std::unique_ptr<List<_CloneT0>>>(d_a1)});
    }
  }

  // CREATORS
  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1.clone())});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) unsigned int length() const {
    const List *_self = this;

    struct _Enter {
      const List *_self;
    };

    struct _Call1 {};

    using _Frame = std::variant<_Enter, _Call1>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{_self});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List *_self = _f._self;
        auto &&_sv = *(_self);
        if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
          _result = 0u;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<t_A>::Cons>(_sv.v());
          _stack.emplace_back(_Call1{});
          _stack.emplace_back(_Enter{d_a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = (_result + 1);
      }
    }
    return _result;
  }

  __attribute__((pure)) List<t_A> app(List<t_A> m) const {
    std::unique_ptr<List<t_A>> _head{};
    std::unique_ptr<List<t_A>> *_write = &_head;
    const List *_loop_self = this;
    while (true) {
      auto &&_sv = *(_loop_self);
      if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
        *(_write) = std::make_unique<List<t_A>>(m);
        break;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
        auto _cell = std::make_unique<List<t_A>>(
            typename List<t_A>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename List<t_A>::Cons>((*_write)->v_mut()).d_a1;
        _loop_self = d_a1.get();
        continue;
      }
    }
    return std::move(*(_head));
  }
};

struct LoopifySequences {
  /// alternate_sum sign acc l alternating sum with sign flip.
  __attribute__((pure)) static unsigned int
  alternate_sum(const unsigned int &sign, unsigned int acc,
                const List<unsigned int> &l);

  /// intercalate sep lists inserts sep between lists and flattens.
  template <typename T1>
  __attribute__((pure)) static List<T1>
  intercalate(const List<T1> &sep, const List<List<T1>> &lists) {
    struct _Enter {
      const List<List<T1>> lists;
    };

    struct _Call1 {
      List<T1> _s0;
      const List<T1> _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    List<T1> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{lists});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<List<T1>> lists = _f.lists;
        if (std::holds_alternative<typename List<List<T1>>::Nil>(lists.v())) {
          _result = List<T1>::nil();
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<List<T1>>::Cons>(lists.v());
          auto &&_sv = *(d_a1);
          if (std::holds_alternative<typename List<List<T1>>::Nil>(_sv.v())) {
            _result = d_a0;
          } else {
            _stack.emplace_back(_Call1{d_a0, sep});
            _stack.emplace_back(_Enter{*(d_a1)});
          }
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = _f._s0.app(_f._s1.app(_result));
      }
    }
    return _result;
  }

  /// join_with sep l joins list elements with separator.
  template <typename T1>
  __attribute__((pure)) static List<T1> join_with(const T1 sep,
                                                  const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return List<T1>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
      List<T1> d_a1_value = clone_as_value<List<T1>>(d_a1);
      std::function<List<T1>(List<T1>)> go;
      go = [&](List<T1> rest) -> List<T1> {
        struct _Enter {
          List<T1> rest;
        };
        struct _Call1 {
          decltype(sep) _s0;
          T1 _s1;
        };
        using _Frame = std::variant<_Enter, _Call1>;
        List<T1> _result{};
        std::vector<_Frame> _stack;
        _stack.reserve(16);
        _stack.emplace_back(_Enter{rest});
        while (!_stack.empty()) {
          _Frame _frame = std::move(_stack.back());
          _stack.pop_back();
          if (std::holds_alternative<_Enter>(_frame)) {
            auto _f = std::move(std::get<_Enter>(_frame));
            List<T1> rest = _f.rest;
            if (std::holds_alternative<typename List<T1>::Nil>(rest.v())) {
              _result = List<T1>::nil();
            } else {
              const auto &[d_a00, d_a10] =
                  std::get<typename List<T1>::Cons>(rest.v());
              _stack.emplace_back(_Call1{sep, d_a00});
              _stack.emplace_back(_Enter{*(d_a10)});
            }
          } else {
            auto _f = std::move(std::get<_Call1>(_frame));
            _result = List<T1>::cons(_f._s0, List<T1>::cons(_f._s1, _result));
          }
        }
        return _result;
      };
      return List<T1>::cons(d_a0, go(d_a1_value));
    }
  } /// transpose l transposes a list of lists.

  template <typename T1>
  __attribute__((pure)) static List<List<T1>>
  transpose_fuel(const unsigned int &fuel, const List<List<T1>> &ll) {
    std::unique_ptr<List<List<T1>>> _head{};
    std::unique_ptr<List<List<T1>>> *_write = &_head;
    List<List<T1>> _loop_ll = ll;
    unsigned int _loop_fuel = fuel;
    while (true) {
      if (_loop_fuel <= 0) {
        *(_write) = std::make_unique<List<List<T1>>>(List<List<T1>>::nil());
        break;
      } else {
        unsigned int f = _loop_fuel - 1;
        std::function<bool(List<List<T1>>)> all_nil;
        all_nil = [](List<List<T1>> l) -> bool {
          bool _result;
          List<List<T1>> _loop_l = std::move(l);
          while (true) {
            if (std::holds_alternative<typename List<List<T1>>::Nil>(
                    _loop_l.v())) {
              _result = true;
              break;
            } else {
              const auto &[d_a0, d_a1] =
                  std::get<typename List<List<T1>>::Cons>(_loop_l.v());
              if (std::holds_alternative<typename List<T1>::Nil>(d_a0.v())) {
                _loop_l = *(d_a1);
              } else {
                _result = false;
                break;
              }
            }
          }
          return _result;
        };
        if (all_nil(_loop_ll)) {
          *(_write) = std::make_unique<List<List<T1>>>(List<List<T1>>::nil());
          break;
        } else {
          std::function<List<T1>(List<List<T1>>)> heads;
          heads = [&](List<List<T1>> l) -> List<T1> {
            struct _Enter {
              List<List<T1>> l;
            };
            struct _Call1 {
              T1 _s0;
            };
            using _Frame = std::variant<_Enter, _Call1>;
            List<T1> _result{};
            std::vector<_Frame> _stack;
            _stack.reserve(16);
            _stack.emplace_back(_Enter{l});
            while (!_stack.empty()) {
              _Frame _frame = std::move(_stack.back());
              _stack.pop_back();
              if (std::holds_alternative<_Enter>(_frame)) {
                auto _f = std::move(std::get<_Enter>(_frame));
                List<List<T1>> l = _f.l;
                if (std::holds_alternative<typename List<List<T1>>::Nil>(
                        l.v())) {
                  _result = List<T1>::nil();
                } else {
                  const auto &[d_a00, d_a10] =
                      std::get<typename List<List<T1>>::Cons>(l.v());
                  if (std::holds_alternative<typename List<T1>::Nil>(
                          d_a00.v())) {
                    _stack.emplace_back(_Enter{*(d_a10)});
                  } else {
                    const auto &[d_a01, d_a11] =
                        std::get<typename List<T1>::Cons>(d_a00.v());
                    _stack.emplace_back(_Call1{d_a01});
                    _stack.emplace_back(_Enter{*(d_a10)});
                  }
                }
              } else {
                auto _f = std::move(std::get<_Call1>(_frame));
                _result = List<T1>::cons(_f._s0, _result);
              }
            }
            return _result;
          };
          std::function<List<List<T1>>(List<List<T1>>)> tails;
          tails = [&](List<List<T1>> l) -> List<List<T1>> {
            struct _Enter {
              List<List<T1>> l;
            };
            struct _Call1 {
              List<T1> _s0;
            };
            using _Frame = std::variant<_Enter, _Call1>;
            List<List<T1>> _result{};
            std::vector<_Frame> _stack;
            _stack.reserve(16);
            _stack.emplace_back(_Enter{l});
            while (!_stack.empty()) {
              _Frame _frame = std::move(_stack.back());
              _stack.pop_back();
              if (std::holds_alternative<_Enter>(_frame)) {
                auto _f = std::move(std::get<_Enter>(_frame));
                List<List<T1>> l = _f.l;
                if (std::holds_alternative<typename List<List<T1>>::Nil>(
                        l.v())) {
                  _result = List<List<T1>>::nil();
                } else {
                  const auto &[d_a01, d_a11] =
                      std::get<typename List<List<T1>>::Cons>(l.v());
                  if (std::holds_alternative<typename List<T1>::Nil>(
                          d_a01.v())) {
                    _stack.emplace_back(_Enter{*(d_a11)});
                  } else {
                    const auto &[d_a02, d_a12] =
                        std::get<typename List<T1>::Cons>(d_a01.v());
                    _stack.emplace_back(_Call1{*(d_a12)});
                    _stack.emplace_back(_Enter{*(d_a11)});
                  }
                }
              } else {
                auto _f = std::move(std::get<_Call1>(_frame));
                _result = List<List<T1>>::cons(_f._s0, _result);
              }
            }
            return _result;
          };
          auto _cell = std::make_unique<List<List<T1>>>(
              typename List<List<T1>>::Cons(heads(_loop_ll), nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<typename List<List<T1>>::Cons>((*_write)->v_mut()).d_a1;
          List<List<T1>> _next_ll = tails(_loop_ll);
          unsigned int _next_fuel = f;
          _loop_ll = std::move(_next_ll);
          _loop_fuel = std::move(_next_fuel);
          continue;
        }
      }
    }
    return std::move(*(_head));
  }

  template <typename T1>
  __attribute__((pure)) static List<List<T1>>
  transpose(const List<List<T1>> &ll) {
    return transpose_fuel<T1>(100u, ll);
  }

  /// collatz_list n generates collatz sequence.
  __attribute__((pure)) static List<unsigned int>
  collatz_list_fuel(const unsigned int &fuel, unsigned int n);
  __attribute__((pure)) static List<unsigned int>
  collatz_list(const unsigned int &n);
  /// run_sum l running sum (scanl for addition).
  __attribute__((pure)) static List<unsigned int>
  run_sum_aux(const unsigned int &acc, const List<unsigned int> &l);
  __attribute__((pure)) static List<unsigned int>
  run_sum(const List<unsigned int> &l);
  /// rotate_left n l rotates list left by n positions.
  __attribute__((pure)) static List<unsigned int>
  rotate_left_fuel(const unsigned int &fuel, const unsigned int &n,
                   List<unsigned int> l);
  __attribute__((pure)) static List<unsigned int>
  rotate_left(const unsigned int &n, const List<unsigned int> &l);

  /// iterate f n x generates x, f x, f (f x), ... of length n.
  template <MapsTo<unsigned int, unsigned int> F0>
  __attribute__((pure)) static List<unsigned int>
  iterate(F0 &&f, const unsigned int &n, unsigned int x) {
    std::unique_ptr<List<unsigned int>> _head{};
    std::unique_ptr<List<unsigned int>> *_write = &_head;
    unsigned int _loop_x = std::move(x);
    unsigned int _loop_n = n;
    while (true) {
      if (_loop_n <= 0) {
        *(_write) =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        unsigned int m = _loop_n - 1;
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(_loop_x, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        unsigned int _next_x = f(_loop_x);
        unsigned int _next_n = m;
        _loop_x = std::move(_next_x);
        _loop_n = std::move(_next_n);
        continue;
      }
    }
    return std::move(*(_head));
  }

  /// sum_acc acc l sum with accumulator.
  __attribute__((pure)) static unsigned int
  sum_acc(unsigned int acc, const List<unsigned int> &l);
  /// repeat_string s n repeats string n times (using list as string).
  __attribute__((pure)) static List<unsigned int>
  repeat_string(const List<unsigned int> &s, const unsigned int &n);
  /// repeat_with_sep s sep n repeats with separator.
  __attribute__((pure)) static List<unsigned int>
  repeat_with_sep(List<unsigned int> s, const List<unsigned int> &sep,
                  const unsigned int &n);
  /// string_chain s n recursive string chain: s-chain(s, n-1)-end.
  __attribute__((pure)) static List<unsigned int>
  string_chain_fuel(const unsigned int &fuel, const List<unsigned int> &s,
                    const unsigned int &n, const List<unsigned int> &sep,
                    const List<unsigned int> &end_marker);
  __attribute__((pure)) static List<unsigned int>
  string_chain(const List<unsigned int> &s, const unsigned int &n,
               const List<unsigned int> &sep,
               const List<unsigned int> &end_marker);
  /// split_by_sign l base pos neg splits list based on base threshold.
  __attribute__((pure)) static std::pair<List<unsigned int>, List<unsigned int>>
  split_by_sign(const List<unsigned int> &l, const unsigned int &base,
                List<unsigned int> pos, List<unsigned int> neg);
  /// differences l computes differences between consecutive elements.
  __attribute__((pure)) static List<unsigned int>
  differences(const List<unsigned int> &l);
  /// replace_at idx value l replaces element at index with value.
  __attribute__((pure)) static List<unsigned int>
  replace_at(const unsigned int &idx, unsigned int value,
             const List<unsigned int> &l);
  /// cycle n l repeats list n times.
  __attribute__((pure)) static List<unsigned int>
  cycle(const unsigned int &n, const List<unsigned int> &l);
  /// Helper: get first element.
  __attribute__((pure)) static unsigned int
  first_elem(const List<unsigned int> &l);
  /// Helper: get last element.
  __attribute__((pure)) static unsigned int
  last_elem(const List<unsigned int> &l);
  /// Helper: remove first element.
  __attribute__((pure)) static List<unsigned int>
  tail_list(const List<unsigned int> &l);
  /// Helper: remove last element.
  __attribute__((pure)) static List<unsigned int>
  init_list(const List<unsigned int> &l);
  /// is_palindrome s checks if list is a palindrome.
  __attribute__((pure)) static bool
  is_palindrome_fuel(const unsigned int &fuel, const List<unsigned int> &s);
  __attribute__((pure)) static bool is_palindrome(const List<unsigned int> &s);
  /// string_subsequences s generates all subsequences treating list as string.
  __attribute__((pure)) static List<List<unsigned int>>
  string_subsequences(const List<unsigned int> &s);
  /// run_length_groups l groups consecutive runs into sublist lengths.
  __attribute__((pure)) static List<unsigned int>
  run_length_groups_aux(const unsigned int &prev, unsigned int count,
                        const List<unsigned int> &l);
  __attribute__((pure)) static List<unsigned int>
  run_length_groups(const List<unsigned int> &l);
  /// is_prefix_of l1 l2 checks if l1 is a prefix of l2.
  __attribute__((pure)) static bool is_prefix_of(const List<unsigned int> &l1,
                                                 const List<unsigned int> &l2);
  /// lis l longest increasing subsequence (greedy, not optimal).
  __attribute__((pure)) static List<unsigned int> lis(List<unsigned int> l);

  /// take_while p l takes elements while predicate holds.
  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static List<unsigned int>
  take_while(F0 &&p, const List<unsigned int> &l) {
    std::unique_ptr<List<unsigned int>> _head{};
    std::unique_ptr<List<unsigned int>> *_write = &_head;
    List<unsigned int> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v())) {
        *(_write) =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l.v());
        if (p(d_a0)) {
          auto _cell = std::make_unique<List<unsigned int>>(
              typename List<unsigned int>::Cons(d_a0, nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                   .d_a1;
          _loop_l = *(d_a1);
          continue;
        } else {
          *(_write) =
              std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
          break;
        }
      }
    }
    return std::move(*(_head));
  }

  /// drop_while p l drops elements while predicate holds.
  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static List<unsigned int>
  drop_while(F0 &&p, const List<unsigned int> &l) {
    List<unsigned int> _result;
    List<unsigned int> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v())) {
        _result = List<unsigned int>::nil();
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l.v());
        if (p(d_a0)) {
          _loop_l = *(d_a1);
        } else {
          _result = List<unsigned int>::cons(d_a0, *(d_a1));
          break;
        }
      }
    }
    return _result;
  }

  /// Helper: check if element is in list.
  __attribute__((pure)) static bool elem(const unsigned int &x,
                                         const List<unsigned int> &l);
  /// Helper: filter list.
  __attribute__((pure)) static List<unsigned int>
  filter_ne(const unsigned int &x, const List<unsigned int> &l);
  /// nub l removes duplicates from list.
  __attribute__((pure)) static List<unsigned int>
  nub_fuel(const unsigned int &fuel, const List<unsigned int> &l);
  __attribute__((pure)) static List<unsigned int>
  nub(const List<unsigned int> &l);
  /// group l groups consecutive equal elements.
  __attribute__((pure)) static List<List<unsigned int>>
  group_fuel(const unsigned int &fuel, const List<unsigned int> &l);
  __attribute__((pure)) static List<List<unsigned int>>
  group(const List<unsigned int> &l);
  /// Helper: get head with default.
  __attribute__((pure)) static unsigned int
  head_or(unsigned int default0, const List<unsigned int> &l);
  /// remove_if_sum_even l removes elements where sum with next is even.
  __attribute__((pure)) static List<unsigned int>
  remove_if_sum_even(const List<unsigned int> &l);

  /// bool_all p l checks if all elements satisfy predicate (forall with &&).
  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static bool bool_all(F0 &&p,
                                             const List<unsigned int> &l) {
    struct _Enter {
      const List<unsigned int> l;
    };

    struct _Call1 {
      bool _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    bool _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<unsigned int> l = _f.l;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = true;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          _stack.emplace_back(_Call1{p(d_a0)});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = (_f._s0 && _result);
      }
    }
    return _result;
  }

  /// run_length_encode l encodes consecutive runs: 1,1,2,2,2 -> (1,2),(2,3).
  __attribute__((pure)) static List<std::pair<unsigned int, unsigned int>>
  run_length_encode_fuel(const unsigned int &fuel, const List<unsigned int> &l);
  __attribute__((pure)) static List<std::pair<unsigned int, unsigned int>>
  run_length_encode(const List<unsigned int> &l);
  /// between lo hi l filters elements in range lo, hi.
  __attribute__((pure)) static List<unsigned int>
  between(const unsigned int &lo, const unsigned int &hi,
          const List<unsigned int> &l);
};

#endif // INCLUDED_LOOPIFY_SEQUENCES
