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
    A a;
    std::unique_ptr<List<A>> l;
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

  List(List<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) noexcept {
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
        _dst->v_ = Cons{_alt.a, _alt.l ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.l) {
          _stack.push_back({_alt.l.get(), _dst_alt.l.get()});
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
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a), l ? std::make_unique<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_unique<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.l) {
          _stack.push_back(std::move(_alt.l));
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
        _write = &std::get<typename List<A>::Cons>((*_write)->v_mut()).l;
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
  static List<uint64_t> cycle(uint64_t n, const List<uint64_t> &l);

  /// iterate f n x applies f repeatedly n times: iterate (+1) 3 5 -> 5,6,7.
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static List<uint64_t> iterate(F0 &&f, uint64_t n, uint64_t x) {
    std::unique_ptr<List<uint64_t>> _head{};
    std::unique_ptr<List<uint64_t>> *_write = &_head;
    uint64_t _loop_x = std::move(x);
    uint64_t _loop_n = std::move(n);
    while (true) {
      if (_loop_n <= 0) {
        *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        uint64_t m = _loop_n - 1;
        auto _cell = std::make_unique<List<uint64_t>>(
            typename List<uint64_t>::Cons(_loop_x, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
        _loop_x = f(_loop_x);
        _loop_n = m;
        continue;
      }
    }
    return std::move(*_head);
  }

  /// zip_with f l1 l2 zips with a combining function.
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &, uint64_t &>
  static List<uint64_t> zip_with(F0 &&f, const List<uint64_t> &l1,
                                 const List<uint64_t> &l2) {
    std::unique_ptr<List<uint64_t>> _head{};
    std::unique_ptr<List<uint64_t>> *_write = &_head;
    const List<uint64_t> *_loop_l2 = &l2;
    const List<uint64_t> *_loop_l1 = &l1;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l1->v())) {
        *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l1->v());
        if (std::holds_alternative<typename List<uint64_t>::Nil>(
                _loop_l2->v())) {
          *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
          break;
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(_loop_l2->v());
          auto _cell = std::make_unique<List<uint64_t>>(
              typename List<uint64_t>::Cons(f(a0, a00), nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
          _loop_l2 = a10.get();
          _loop_l1 = a1.get();
          continue;
        }
      }
    }
    return std::move(*_head);
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
  static List<uint64_t> unfold_fuel(uint64_t fuel, F1 &&f, uint64_t n,
                                    uint64_t seed) {
    std::unique_ptr<List<uint64_t>> _head{};
    std::unique_ptr<List<uint64_t>> *_write = &_head;
    uint64_t _loop_seed = std::move(seed);
    uint64_t _loop_n = std::move(n);
    uint64_t _loop_fuel = std::move(fuel);
    while (true) {
      if (_loop_fuel <= 0) {
        *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        uint64_t g = _loop_fuel - 1;
        if (_loop_n == UINT64_C(0)) {
          *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
          break;
        } else {
          auto _cs = f(_loop_seed);
          const uint64_t &val = _cs.first;
          const uint64_t &next_seed = _cs.second;
          auto _cell = std::make_unique<List<uint64_t>>(
              typename List<uint64_t>::Cons(val, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
          _loop_seed = next_seed;
          _loop_n = ((
              (_loop_n - UINT64_C(1)) > _loop_n ? 0 : (_loop_n - UINT64_C(1))));
          _loop_fuel = g;
          continue;
        }
      }
    }
    return std::move(*_head);
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
