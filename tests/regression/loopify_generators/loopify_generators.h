#ifndef INCLUDED_LOOPIFY_GENERATORS
#define INCLUDED_LOOPIFY_GENERATORS

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a0;
    std::unique_ptr<List<A>> a1;
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

  List(const List<A> &_other) : v_(std::move(_other.clone().v_)) {}

  List(List<A> &&_other) : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  List<A> clone() const {
    List<A> _out{};

    struct _CloneFrame {
      const List<A> *_src;
      List<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<A> *_src = _frame._src;
      List<A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->v_ =
            Cons{_alt.a0, _alt.a1 ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a0, a1] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a0), a1 ? std::make_unique<List<A>>(*a1) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a0, List<A> a1) {
    return List(Cons{std::move(a0), std::make_unique<List<A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.a1) {
          _stack.push_back(std::move(_alt.a1));
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

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  List<A> app(List<A> m) const {
    std::unique_ptr<List<A>> _head{};
    std::unique_ptr<List<A>> *_write = &_head;
    const List *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = std::make_unique<List<A>>(std::move(_loop_m));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell =
            std::make_unique<List<A>>(typename List<A>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<A>::Cons>((*_write)->v_mut()).a1;
        _loop_self = a1.get();
        continue;
      }
    }
    return std::move(*_head);
  }
};

/// Consolidated list generator functions.
struct LoopifyGenerators {
  /// cycle n l repeats the list n times: cycle 2 1,2 -> 1,2,1,2.
  static List<unsigned int> cycle(unsigned int n, const List<unsigned int> &l);

  /// iterate f n x applies f repeatedly n times: iterate (+1) 3 5 -> 5,6,7.
  template <typename F0>
    requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &>
  static List<unsigned int> iterate(F0 &&f, unsigned int n, unsigned int x) {
    std::unique_ptr<List<unsigned int>> _head{};
    std::unique_ptr<List<unsigned int>> *_write = &_head;
    unsigned int _loop_x = std::move(x);
    unsigned int _loop_n = std::move(n);
    while (true) {
      if (_loop_n <= 0) {
        *_write =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        unsigned int m = _loop_n - 1;
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(_loop_x, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).a1;
        _loop_x = f(_loop_x);
        _loop_n = m;
        continue;
      }
    }
    return std::move(*_head);
  }

  /// zip_with f l1 l2 zips with a combining function.
  template <typename F0>
    requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &,
                                   unsigned int &>
  static List<unsigned int> zip_with(F0 &&f, const List<unsigned int> &l1,
                                     const List<unsigned int> &l2) {
    std::unique_ptr<List<unsigned int>> _head{};
    std::unique_ptr<List<unsigned int>> *_write = &_head;
    const List<unsigned int> *_loop_l2 = &l2;
    const List<unsigned int> *_loop_l1 = &l1;
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l1->v())) {
        *_write =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l1->v());
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _loop_l2->v())) {
          *_write =
              std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
          break;
        } else {
          const auto &[a00, a10] =
              std::get<typename List<unsigned int>::Cons>(_loop_l2->v());
          auto _cell = std::make_unique<List<unsigned int>>(
              typename List<unsigned int>::Cons(f(a0, a00), nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                   .a1;
          _loop_l2 = a10.get();
          _loop_l1 = a1.get();
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  /// zip_longest l1 l2 default zips, using default for missing elements.
  static List<std::pair<unsigned int, unsigned int>>
  zip_longest_aux(const List<unsigned int> &l1, const List<unsigned int> &l2,
                  unsigned int default0, unsigned int fuel);
  static unsigned int len_impl(const List<unsigned int> &l);
  static List<std::pair<unsigned int, unsigned int>>
  zip_longest(const List<unsigned int> &l1, const List<unsigned int> &l2,
              unsigned int default0);
  /// build_list n builds tree-like list structure: build_list(4) -> 2,4,2.
  static List<unsigned int> build_list_fuel(unsigned int fuel, unsigned int n);
  static List<unsigned int> build_list(unsigned int n);
  /// take n l returns first n elements.
  static List<unsigned int> take(unsigned int n, const List<unsigned int> &l);
  /// repeat x n creates list with n copies of x.
  static List<unsigned int> repeat(unsigned int x, unsigned int n);

  /// unfold f n init unfolds a list from seed value.
  template <typename F1>
    requires std::is_invocable_r_v<std::pair<unsigned int, unsigned int>, F1 &,
                                   unsigned int &>
  static List<unsigned int> unfold_fuel(unsigned int fuel, F1 &&f,
                                        unsigned int n, unsigned int seed) {
    std::unique_ptr<List<unsigned int>> _head{};
    std::unique_ptr<List<unsigned int>> *_write = &_head;
    unsigned int _loop_seed = std::move(seed);
    unsigned int _loop_n = std::move(n);
    unsigned int _loop_fuel = std::move(fuel);
    while (true) {
      if (_loop_fuel <= 0) {
        *_write =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        unsigned int g = _loop_fuel - 1;
        if (_loop_n == 0u) {
          *_write =
              std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
          break;
        } else {
          auto _cs = f(_loop_seed);
          const unsigned int &val = _cs.first;
          const unsigned int &next_seed = _cs.second;
          auto _cell = std::make_unique<List<unsigned int>>(
              typename List<unsigned int>::Cons(val, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                   .a1;
          _loop_seed = next_seed;
          _loop_n = (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
          _loop_fuel = g;
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  template <typename F0>
    requires std::is_invocable_r_v<std::pair<unsigned int, unsigned int>, F0 &,
                                   unsigned int &>
  static List<unsigned int> unfold(F0 &&f, unsigned int n, unsigned int seed) {
    return unfold_fuel(100u, f, n, seed);
  }

  /// tabulate n f generates f 0, f 1, ..., f (n-1) (same as init_list but
  /// different naming).
  template <typename F1>
    requires std::is_invocable_r_v<unsigned int, F1 &, unsigned int &>
  static List<unsigned int> tabulate(unsigned int n, F1 &&f) {
    auto go_impl = [&](auto &_self_go, unsigned int i) -> List<unsigned int> {
      if (i <= 0) {
        return List<unsigned int>::nil();
      } else {
        unsigned int j = i - 1;
        return List<unsigned int>::cons(f((((n - i) > n ? 0 : (n - i)))),
                                        _self_go(_self_go, j));
      }
    };
    auto go = [&](unsigned int i) -> List<unsigned int> {
      return go_impl(go_impl, i);
    };
    return go(n);
  }

  /// Helper: replicate single element n times.
  static List<unsigned int> replicate_single(unsigned int x, unsigned int n);
  /// replicate_each n l replicates each element n times: replicate_each 2 1,2
  /// -> 1,1,2,2.
  static List<unsigned int> replicate_each(unsigned int n,
                                           const List<unsigned int> &l);
};

#endif // INCLUDED_LOOPIFY_GENERATORS
