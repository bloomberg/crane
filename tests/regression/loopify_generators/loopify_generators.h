#ifndef INCLUDED_LOOPIFY_GENERATORS
#define INCLUDED_LOOPIFY_GENERATORS

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

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

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  List<t_A> clone() const {
    List<t_A> _out{};

    struct _CloneFrame {
      const List<t_A> *_src;
      List<t_A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<t_A> *_src = _frame._src;
      List<t_A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ = Cons{_alt.d_a0,
                          _alt.d_a1 ? std::make_unique<List<t_A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1) {
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  static List<t_A> nil() { return List(Nil{}); }

  static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<t_A>>> _stack{};
    auto _drain = [&](List<t_A> &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
        if (_alt.d_a1) {
          _stack.push_back(std::move(_alt.d_a1));
        }
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node) {
        _drain(*_node);
      }
    }
  }

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }

  List<t_A> app(List<t_A> m) const {
    std::unique_ptr<List<t_A>> _head{};
    std::unique_ptr<List<t_A>> *_write = &_head;
    const List *_loop_self = this;
    List<t_A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *(_loop_self);
      if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
        *(_write) = std::make_unique<List<t_A>>(std::move(_loop_m));
        break;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
        auto _cell = std::make_unique<List<t_A>>(
            typename List<t_A>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename List<t_A>::Cons>((*_write)->v_mut()).d_a1;
        const List *_next_self = d_a1.get();
        List<t_A> _next_m = std::move(_loop_m);
        _loop_self = _next_self;
        _loop_m = std::move(_next_m);
        continue;
      }
    }
    return std::move(*(_head));
  }
};

/// Consolidated list generator functions.
struct LoopifyGenerators {
  /// cycle n l repeats the list n times: cycle 2 1,2 -> 1,2,1,2.
  static List<unsigned int> cycle(const unsigned int &n,
                                  const List<unsigned int> &l);

  /// iterate f n x applies f repeatedly n times: iterate (+1) 3 5 -> 5,6,7.
  template <MapsTo<unsigned int, unsigned int> F0>
  static List<unsigned int> iterate(F0 &&f, const unsigned int &n,
                                    unsigned int x) {
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

  /// zip_with f l1 l2 zips with a combining function.
  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  static List<unsigned int> zip_with(F0 &&f, const List<unsigned int> &l1,
                                     const List<unsigned int> &l2) {
    std::unique_ptr<List<unsigned int>> _head{};
    std::unique_ptr<List<unsigned int>> *_write = &_head;
    const List<unsigned int> *_loop_l2 = &l2;
    const List<unsigned int> *_loop_l1 = &l1;
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l1->v())) {
        *(_write) =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l1->v());
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _loop_l2->v())) {
          *(_write) =
              std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
          break;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(_loop_l2->v());
          auto _cell = std::make_unique<List<unsigned int>>(
              typename List<unsigned int>::Cons(f(d_a0, d_a00), nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                   .d_a1;
          const List<unsigned int> *_next_l2 = d_a10.get();
          const List<unsigned int> *_next_l1 = d_a1.get();
          _loop_l2 = _next_l2;
          _loop_l1 = _next_l1;
          continue;
        }
      }
    }
    return std::move(*(_head));
  }

  /// zip_longest l1 l2 default zips, using default for missing elements.
  static List<std::pair<unsigned int, unsigned int>>
  zip_longest_aux(const List<unsigned int> &l1, const List<unsigned int> &l2,
                  unsigned int default0, const unsigned int &fuel);
  static unsigned int len_impl(const List<unsigned int> &l);
  static List<std::pair<unsigned int, unsigned int>>
  zip_longest(const List<unsigned int> &l1, const List<unsigned int> &l2,
              const unsigned int &default0);
  /// build_list n builds tree-like list structure: build_list(4) -> 2,4,2.
  static List<unsigned int> build_list_fuel(const unsigned int &fuel,
                                            const unsigned int &n);
  static List<unsigned int> build_list(const unsigned int &n);
  /// take n l returns first n elements.
  static List<unsigned int> take(const unsigned int &n,
                                 const List<unsigned int> &l);
  /// repeat x n creates list with n copies of x.
  static List<unsigned int> repeat(unsigned int x, const unsigned int &n);

  /// unfold f n init unfolds a list from seed value.
  template <MapsTo<std::pair<unsigned int, unsigned int>, unsigned int> F1>
  static List<unsigned int> unfold_fuel(const unsigned int &fuel, F1 &&f,
                                        const unsigned int &n,
                                        const unsigned int &seed) {
    std::unique_ptr<List<unsigned int>> _head{};
    std::unique_ptr<List<unsigned int>> *_write = &_head;
    unsigned int _loop_seed = seed;
    unsigned int _loop_n = n;
    unsigned int _loop_fuel = fuel;
    while (true) {
      if (_loop_fuel <= 0) {
        *(_write) =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        unsigned int g = _loop_fuel - 1;
        if (_loop_n == 0u) {
          *(_write) =
              std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
          break;
        } else {
          auto _cs = f(_loop_seed);
          const unsigned int &val = _cs.first;
          const unsigned int &next_seed = _cs.second;
          auto _cell = std::make_unique<List<unsigned int>>(
              typename List<unsigned int>::Cons(val, nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                   .d_a1;
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
    return std::move(*(_head));
  }

  template <MapsTo<std::pair<unsigned int, unsigned int>, unsigned int> F0>
  static List<unsigned int> unfold(F0 &&f, const unsigned int &n,
                                   const unsigned int &seed) {
    return unfold_fuel(100u, f, n, seed);
  }

  /// tabulate n f generates f 0, f 1, ..., f (n-1) (same as init_list but
  /// different naming).
  template <MapsTo<unsigned int, unsigned int> F1>
  static List<unsigned int> tabulate(unsigned int n, F1 &&f) {
    std::function<List<unsigned int>(unsigned int)> go;
    go = [&](unsigned int i) -> List<unsigned int> {
      struct _Enter {
        unsigned int i;
      };
      struct _Call1 {
        decltype(f((((n - std::declval<unsigned int &>()) > n
                         ? 0
                         : (n - std::declval<unsigned int &>()))))) _s0;
      };
      using _Frame = std::variant<_Enter, _Call1>;
      List<unsigned int> _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{i});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          unsigned int i = std::move(_f.i);
          if (i <= 0) {
            _result = List<unsigned int>::nil();
          } else {
            unsigned int j = i - 1;
            _stack.emplace_back(_Call1{f((((n - i) > n ? 0 : (n - i))))});
            _stack.emplace_back(_Enter{j});
          }
        } else {
          auto _f = std::move(std::get<_Call1>(_frame));
          _result = List<unsigned int>::cons(_f._s0, _result);
        }
      }
      return _result;
    };
    return go(n);
  }

  /// Helper: replicate single element n times.
  static List<unsigned int> replicate_single(unsigned int x,
                                             const unsigned int &n);
  /// replicate_each n l replicates each element n times: replicate_each 2 1,2
  /// -> 1,1,2,2.
  static List<unsigned int> replicate_each(const unsigned int &n,
                                           const List<unsigned int> &l);
};

#endif // INCLUDED_LOOPIFY_GENERATORS
