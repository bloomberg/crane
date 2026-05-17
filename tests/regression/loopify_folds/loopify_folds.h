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

  unsigned int length() const {
    const List *_self = this;

    /// _Enter: captures varying parameters for each recursive call.
    struct _Enter {
      const List *_self;
    };

    /// _Resume_Cons: resumes after recursive call with _result.
    struct _Resume_Cons {};

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    unsigned int _result{};
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
          _result = 0u;
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
    requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &,
                                   unsigned int &>
  static unsigned int fold_left(F0 &&f, unsigned int acc,
                                const List<unsigned int> &l) {
    unsigned int _result;
    const List<unsigned int> *_loop_l = &l;
    unsigned int _loop_acc = std::move(acc);
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        _result = std::move(_loop_acc);
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l->v());
        _loop_l = a1.get();
        _loop_acc = f(_loop_acc, a0);
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &,
                                   unsigned int &>
  static unsigned int
  fold_right(F0 &&f, const List<unsigned int> &l,
             unsigned int acc) { /// _Enter: captures varying parameters for
                                 /// each recursive call.

    struct _Enter {
      const List<unsigned int> *l;
    };

    /// _Resume_Cons: saves [f, a0], resumes after recursive call with _result.
    struct _Resume_Cons {
      F0 f;
      unsigned int a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified fold_right: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<unsigned int> &l = *_f.l;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = std::move(acc);
        } else {
          const auto &[a0, a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
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
    requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &,
                                   unsigned int &>
  static List<unsigned int> scanl(F0 &&f, unsigned int acc,
                                  const List<unsigned int> &l) {
    std::unique_ptr<List<unsigned int>> _head{};
    std::unique_ptr<List<unsigned int>> *_write = &_head;
    const List<unsigned int> *_loop_l = &l;
    unsigned int _loop_acc = std::move(acc);
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        *_write = std::make_unique<List<unsigned int>>(
            List<unsigned int>::cons(_loop_acc, List<unsigned int>::nil()));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l->v());
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(_loop_acc, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).a1;
        _loop_l = a1.get();
        _loop_acc = f(_loop_acc, a0);
        continue;
      }
    }
    return std::move(*_head);
  }

  template <typename F0>
    requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &,
                                   unsigned int &>
  static List<unsigned int> scanr(F0 &&f, unsigned int acc,
                                  const List<unsigned int> &l) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
      return List<unsigned int>::cons(acc, List<unsigned int>::nil());
    } else {
      const auto &[a0, a1] = std::get<typename List<unsigned int>::Cons>(l.v());
      auto &&_sv0 = scanr(f, acc, *a1);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0.v())) {
        return List<unsigned int>::cons(acc, List<unsigned int>::nil());
      } else {
        const auto &[a00, a10] =
            std::get<typename List<unsigned int>::Cons>(_sv0.v());
        return List<unsigned int>::cons(f(a0, a00), *a10);
      }
    }
  }

  template <typename F1>
    requires std::is_invocable_r_v<unsigned int, F1 &, unsigned int &,
                                   unsigned int &>
  static unsigned int foldl1_fuel(unsigned int fuel, F1 &&f,
                                  const List<unsigned int> &l) {
    unsigned int _result;
    List<unsigned int> _loop_l = l;
    unsigned int _loop_fuel = std::move(fuel);
    while (true) {
      if (_loop_fuel <= 0) {
        _result = 0u;
        break;
      } else {
        unsigned int fuel_ = _loop_fuel - 1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _loop_l.v())) {
          _result = 0u;
          break;
        } else {
          const auto &[a0, a1] =
              std::get<typename List<unsigned int>::Cons>(_loop_l.v());
          auto &&_sv0 = *a1;
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  _sv0.v())) {
            _result = std::move(a0);
            break;
          } else {
            const auto &[a00, a10] =
                std::get<typename List<unsigned int>::Cons>(_sv0.v());
            _loop_l = List<unsigned int>::cons(f(a0, a00), *a10);
            _loop_fuel = fuel_;
          }
        }
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &,
                                   unsigned int &>
  static unsigned int foldl1(F0 &&f, const List<unsigned int> &l) {
    return foldl1_fuel(l.length(), f, l);
  }

  template <typename F0>
    requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &,
                                   unsigned int &>
  static unsigned int
  foldr1(F0 &&f,
         const List<unsigned int> &l) { /// _Enter: captures varying parameters
                                        /// for each recursive call.

    struct _Enter {
      const List<unsigned int> *l;
    };

    /// _Resume_Cons: saves [f, a0], resumes after recursive call with _result.
    struct _Resume_Cons {
      F0 f;
      unsigned int a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified foldr1: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<unsigned int> &l = *_f.l;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = 0u;
        } else {
          const auto &[a0, a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          auto &&_sv = *a1;
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  _sv.v())) {
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
    requires std::is_invocable_r_v<std::pair<unsigned int, unsigned int>, F0 &,
                                   unsigned int &, unsigned int &>
  static std::pair<unsigned int, List<unsigned int>> map_accum(
      F0 &&f, unsigned int acc,
      const List<unsigned int>
          &l) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      const List<unsigned int> *l;
      unsigned int acc;
    };

    /// _Cont_acc_: saves [y], resumes after recursive call, then processes
    /// rest.
    struct _Cont_acc_ {
      unsigned int y;
    };

    using _Frame = std::variant<_Enter, _Cont_acc_>;
    std::pair<unsigned int, List<unsigned int>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l, acc});
    /// Loopified map_accum: _Enter -> _Cont_acc_.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<unsigned int> &l = *_f.l;
        unsigned int acc = _f.acc;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = std::make_pair(std::move(acc), List<unsigned int>::nil());
        } else {
          const auto &[a0, a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          auto _cs = f(acc, a0);
          const unsigned int &acc_ = _cs.first;
          const unsigned int &y = _cs.second;
          _stack.emplace_back(_Cont_acc_{y});
          _stack.emplace_back(_Enter{a1.get(), std::move(_cs.first)});
        }
      } else {
        auto _f = std::move(std::get<_Cont_acc_>(_frame));
        unsigned int y = _f.y;
        const unsigned int &final_acc = _result.first;
        const List<unsigned int> &ys = _result.second;
        _result = std::make_pair(std::move(_result.first),
                                 List<unsigned int>::cons(y, ys));
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &>
  static List<unsigned int> iterate_accum(F0 &&f, unsigned int n,
                                          unsigned int x) {
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
        unsigned int n_ = _loop_n - 1;
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(_loop_x, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).a1;
        _loop_x = f(_loop_x);
        _loop_n = n_;
        continue;
      }
    }
    return std::move(*_head);
  }

  template <typename F1>
    requires std::is_invocable_r_v<std::pair<unsigned int, unsigned int>, F1 &,
                                   unsigned int &>
  static List<unsigned int> unfold_fuel(unsigned int fuel, F1 &&f,
                                        unsigned int seed) {
    std::unique_ptr<List<unsigned int>> _head{};
    std::unique_ptr<List<unsigned int>> *_write = &_head;
    unsigned int _loop_seed = std::move(seed);
    unsigned int _loop_fuel = std::move(fuel);
    while (true) {
      if (_loop_fuel <= 0) {
        *_write =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        unsigned int fuel_ = _loop_fuel - 1;
        auto _cs = f(_loop_seed);
        const unsigned int &x = _cs.first;
        const unsigned int &next_seed = _cs.second;
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(x, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).a1;
        _loop_seed = next_seed;
        _loop_fuel = fuel_;
        continue;
      }
    }
    return std::move(*_head);
  }

  template <typename F1>
    requires std::is_invocable_r_v<std::pair<unsigned int, unsigned int>, F1 &,
                                   unsigned int &>
  static List<unsigned int> unfold(unsigned int _x0, F1 &&_x1,
                                   unsigned int _x2) {
    return unfold_fuel(_x0, _x1, _x2);
  }
};

#endif // INCLUDED_LOOPIFY_FOLDS
