#ifndef INCLUDED_LOOPIFY_FOLDS
#define INCLUDED_LOOPIFY_FOLDS

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

  uint64_t length() const {
    const List *_self = this;

    /// _Enter: captures varying parameters for each recursive call.
    struct _Enter {
      const List *_self;
    };

    /// _Resume_Cons: resumes after recursive call with _result.
    struct _Resume_Cons {};

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    uint64_t _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{_self});
    /// Loopified length: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_Resume_Cons{});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = (_result + 1);
      }
    }
    return _result;
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

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &, uint64_t &>
  static List<uint64_t> scanl(F0 &&f, uint64_t acc, const List<uint64_t> &l) {
    std::unique_ptr<List<uint64_t>> _head{};
    std::unique_ptr<List<uint64_t>> *_write = &_head;
    const List<uint64_t> *_loop_l = &l;
    uint64_t _loop_acc = std::move(acc);
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        *_write = std::make_unique<List<uint64_t>>(
            List<uint64_t>::cons(_loop_acc, List<uint64_t>::nil()));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        auto _cell = std::make_unique<List<uint64_t>>(
            typename List<uint64_t>::Cons(_loop_acc, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
        _loop_l = a1.get();
        _loop_acc = f(_loop_acc, a0);
        continue;
      }
    }
    return std::move(*_head);
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
          const uint64_t &acc_ = _cs.first;
          const uint64_t &y = _cs.second;
          _stack.emplace_back(_Cont_acc_{y});
          _stack.emplace_back(_Enter{a1.get(), std::move(_cs.first)});
        }
      } else {
        auto _f = std::move(std::get<_Cont_acc_>(_frame));
        uint64_t y = _f.y;
        const uint64_t &final_acc = _result.first;
        const List<uint64_t> &ys = _result.second;
        _result = std::make_pair(std::move(_result.first),
                                 List<uint64_t>::cons(y, ys));
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static List<uint64_t> iterate_accum(F0 &&f, uint64_t n, uint64_t x) {
    std::unique_ptr<List<uint64_t>> _head{};
    std::unique_ptr<List<uint64_t>> *_write = &_head;
    uint64_t _loop_x = std::move(x);
    uint64_t _loop_n = std::move(n);
    while (true) {
      if (_loop_n <= 0) {
        *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        uint64_t n_ = _loop_n - 1;
        auto _cell = std::make_unique<List<uint64_t>>(
            typename List<uint64_t>::Cons(_loop_x, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
        _loop_x = f(_loop_x);
        _loop_n = n_;
        continue;
      }
    }
    return std::move(*_head);
  }

  template <typename F1>
    requires std::is_invocable_r_v<std::pair<uint64_t, uint64_t>, F1 &,
                                   uint64_t &>
  static List<uint64_t> unfold_fuel(uint64_t fuel, F1 &&f, uint64_t seed) {
    std::unique_ptr<List<uint64_t>> _head{};
    std::unique_ptr<List<uint64_t>> *_write = &_head;
    uint64_t _loop_seed = std::move(seed);
    uint64_t _loop_fuel = std::move(fuel);
    while (true) {
      if (_loop_fuel <= 0) {
        *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        uint64_t fuel_ = _loop_fuel - 1;
        auto _cs = f(_loop_seed);
        const uint64_t &x = _cs.first;
        const uint64_t &next_seed = _cs.second;
        auto _cell = std::make_unique<List<uint64_t>>(
            typename List<uint64_t>::Cons(x, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
        _loop_seed = next_seed;
        _loop_fuel = fuel_;
        continue;
      }
    }
    return std::move(*_head);
  }

  template <typename F1>
    requires std::is_invocable_r_v<std::pair<uint64_t, uint64_t>, F1 &,
                                   uint64_t &>
  static List<uint64_t> unfold(uint64_t _x0, F1 &&_x1, uint64_t _x2) {
    return unfold_fuel(_x0, _x1, _x2);
  }
};

#endif // INCLUDED_LOOPIFY_FOLDS
