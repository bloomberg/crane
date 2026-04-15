#ifndef INCLUDED_LOOPIFY_GENERATORS
#define INCLUDED_LOOPIFY_GENERATORS

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  std::shared_ptr<List<t_A>> app(std::shared_ptr<List<t_A>> m) const {
    std::shared_ptr<List<t_A>> _head{};
    std::shared_ptr<List<t_A>> _last{};
    const List *_loop_self = this;
    bool _continue = true;
    while (_continue) {
      if (std::holds_alternative<typename List<t_A>::Nil>(_loop_self->v())) {
        if (_last) {
          std::get<typename List<t_A>::Cons>(_last->v_mut()).d_a1 = m;
        } else {
          _head = m;
        }
        _continue = false;
      } else {
        const auto &_m =
            *std::get_if<typename List<t_A>::Cons>(&_loop_self->v());
        auto _cell = List<t_A>::cons(_m.d_a0, nullptr);
        if (_last) {
          std::get<typename List<t_A>::Cons>(_last->v_mut()).d_a1 = _cell;
        } else {
          _head = _cell;
        }
        _last = _cell;
        _loop_self = _m.d_a1.get();
        continue;
      }
    }
    return _head;
  }
};

/// Consolidated list generator functions.
struct LoopifyGenerators {
  /// cycle n l repeats the list n times: cycle 2 1,2 -> 1,2,1,2.
  static std::shared_ptr<List<unsigned int>>
  cycle(const unsigned int n, const std::shared_ptr<List<unsigned int>> &l);

  /// iterate f n x applies f repeatedly n times: iterate (+1) 3 5 -> 5,6,7.
  template <MapsTo<unsigned int, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  iterate(F0 &&f, const unsigned int n, const unsigned int x) {
    std::shared_ptr<List<unsigned int>> _head{};
    std::shared_ptr<List<unsigned int>> _last{};
    unsigned int _loop_x = x;
    unsigned int _loop_n = n;
    bool _continue = true;
    while (_continue) {
      if (_loop_n <= 0) {
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              List<unsigned int>::nil();
        } else {
          _head = List<unsigned int>::nil();
        }
        _continue = false;
      } else {
        unsigned int m = _loop_n - 1;
        auto _cell = List<unsigned int>::cons(_loop_x, nullptr);
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              _cell;
        } else {
          _head = _cell;
        }
        _last = _cell;
        unsigned int _next_x = f(_loop_x);
        unsigned int _next_n = m;
        _loop_x = std::move(_next_x);
        _loop_n = std::move(_next_n);
        continue;
      }
    }
    return _head;
  }

  /// zip_with f l1 l2 zips with a combining function.
  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  zip_with(F0 &&f, const std::shared_ptr<List<unsigned int>> &l1,
           const std::shared_ptr<List<unsigned int>> &l2) {
    std::shared_ptr<List<unsigned int>> _head{};
    std::shared_ptr<List<unsigned int>> _last{};
    std::shared_ptr<List<unsigned int>> _loop_l2 = l2;
    std::shared_ptr<List<unsigned int>> _loop_l1 = l1;
    bool _continue = true;
    while (_continue) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l1->v())) {
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              List<unsigned int>::nil();
        } else {
          _head = List<unsigned int>::nil();
        }
        _continue = false;
      } else {
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&_loop_l1->v());
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _loop_l2->v())) {
          if (_last) {
            std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                List<unsigned int>::nil();
          } else {
            _head = List<unsigned int>::nil();
          }
          _continue = false;
        } else {
          const auto &_m0 =
              *std::get_if<typename List<unsigned int>::Cons>(&_loop_l2->v());
          auto _cell = List<unsigned int>::cons(f(_m.d_a0, _m0.d_a0), nullptr);
          if (_last) {
            std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                _cell;
          } else {
            _head = _cell;
          }
          _last = _cell;
          std::shared_ptr<List<unsigned int>> _next_l2 = _m0.d_a1;
          std::shared_ptr<List<unsigned int>> _next_l1 = _m.d_a1;
          _loop_l2 = std::move(_next_l2);
          _loop_l1 = std::move(_next_l1);
          continue;
        }
      }
    }
    return _head;
  }

  /// zip_longest l1 l2 default zips, using default for missing elements.
  static std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
  zip_longest_aux(const std::shared_ptr<List<unsigned int>> &l1,
                  const std::shared_ptr<List<unsigned int>> &l2,
                  const unsigned int default0, const unsigned int fuel);
  __attribute__((pure)) static unsigned int
  len_impl(const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
  zip_longest(
      const std::shared_ptr<List<unsigned int>> &l1,
      const std::shared_ptr<List<unsigned int>> &l2,
      const unsigned int default0); /// build_list n builds tree-like list
                                    /// structure: build_list(4) -> 2,4,2.
  static std::shared_ptr<List<unsigned int>>
  build_list_fuel(const unsigned int fuel, const unsigned int n);
  static std::shared_ptr<List<unsigned int>> build_list(const unsigned int n);
  /// take n l returns first n elements.
  static std::shared_ptr<List<unsigned int>>
  take(const unsigned int n, const std::shared_ptr<List<unsigned int>> &l);
  /// repeat x n creates list with n copies of x.
  static std::shared_ptr<List<unsigned int>> repeat(const unsigned int x,
                                                    const unsigned int n);

  /// unfold f n init unfolds a list from seed value.
  template <MapsTo<std::pair<unsigned int, unsigned int>, unsigned int> F1>
  static std::shared_ptr<List<unsigned int>>
  unfold_fuel(const unsigned int fuel, F1 &&f, const unsigned int n,
              const unsigned int seed) {
    std::shared_ptr<List<unsigned int>> _head{};
    std::shared_ptr<List<unsigned int>> _last{};
    unsigned int _loop_seed = seed;
    unsigned int _loop_n = n;
    unsigned int _loop_fuel = fuel;
    bool _continue = true;
    while (_continue) {
      if (_loop_fuel <= 0) {
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              List<unsigned int>::nil();
        } else {
          _head = List<unsigned int>::nil();
        }
        _continue = false;
      } else {
        unsigned int g = _loop_fuel - 1;
        if (_loop_n == 0u) {
          if (_last) {
            std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                List<unsigned int>::nil();
          } else {
            _head = List<unsigned int>::nil();
          }
          _continue = false;
        } else {
          auto _cs = f(_loop_seed);
          const unsigned int &val = _cs.first;
          const unsigned int &next_seed = _cs.second;
          auto _cell = List<unsigned int>::cons(val, nullptr);
          if (_last) {
            std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                _cell;
          } else {
            _head = _cell;
          }
          _last = _cell;
          unsigned int _next_seed = next_seed;
          unsigned int _next_n =
              (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
          unsigned int _next_fuel = g;
          _loop_seed = std::move(_next_seed);
          _loop_n = std::move(_next_n);
          _loop_fuel = std::move(_next_fuel);
          continue;
        }
      }
    }
    return _head;
  }

  template <MapsTo<std::pair<unsigned int, unsigned int>, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  unfold(F0 &&f, const unsigned int n, const unsigned int seed) {
    return unfold_fuel(100u, f, n, seed);
  }

  /// tabulate n f generates f 0, f 1, ..., f (n-1) (same as init_list but
  /// different naming).
  template <MapsTo<unsigned int, unsigned int> F1>
  static std::shared_ptr<List<unsigned int>> tabulate(const unsigned int n,
                                                      F1 &&f) {
    std::function<std::shared_ptr<List<unsigned int>>(unsigned int)> go;
    go = [&](unsigned int i) -> std::shared_ptr<List<unsigned int>> {
      struct _Enter {
        unsigned int i;
      };
      struct _Call1 {
        decltype(f((((n - std::declval<unsigned int &>()) > n
                         ? 0
                         : (n - std::declval<unsigned int &>()))))) _s0;
      };
      using _Frame = std::variant<_Enter, _Call1>;
      std::shared_ptr<List<unsigned int>> _result{};
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{i});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          const auto &_f = std::get<_Enter>(_frame);
          unsigned int i = _f.i;
          if (i <= 0) {
            _result = List<unsigned int>::nil();
          } else {
            unsigned int j = i - 1;
            _stack.emplace_back(_Call1{f((((n - i) > n ? 0 : (n - i))))});
            _stack.emplace_back(_Enter{j});
          }
        } else {
          const auto &_f = std::get<_Call1>(_frame);
          _result = List<unsigned int>::cons(_f._s0, _result);
        }
      }
      return _result;
    };
    return go(n);
  }

  /// Helper: replicate single element n times.
  static std::shared_ptr<List<unsigned int>>
  replicate_single(const unsigned int x, const unsigned int n);
  /// replicate_each n l replicates each element n times: replicate_each 2 1,2
  /// -> 1,1,2,2.
  static std::shared_ptr<List<unsigned int>>
  replicate_each(const unsigned int n,
                 const std::shared_ptr<List<unsigned int>> &l);
};

#endif // INCLUDED_LOOPIFY_GENERATORS
