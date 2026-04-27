#ifndef INCLUDED_LOOPIFY_FOLDS
#define INCLUDED_LOOPIFY_FOLDS

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
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
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

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

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
};

struct LoopifyFolds {
  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  fold_left(F0 &&f, unsigned int acc, const List<unsigned int> &l) {
    unsigned int _result;
    List<unsigned int> _loop_l = l;
    unsigned int _loop_acc = std::move(acc);
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v())) {
        _result = _loop_acc;
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l.v());
        List<unsigned int> _next_l = *(d_a1);
        unsigned int _next_acc = f(_loop_acc, d_a0);
        _loop_l = std::move(_next_l);
        _loop_acc = std::move(_next_acc);
      }
    }
    return _result;
  }

  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  fold_right(F0 &&f, const List<unsigned int> &l, unsigned int acc) {
    struct _Enter {
      const List<unsigned int> l;
    };

    struct _Call1 {
      unsigned int _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    unsigned int _result{};
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
          _result = acc;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          _stack.emplace_back(_Call1{d_a0});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = f(_f._s0, _result);
      }
    }
    return _result;
  }

  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  __attribute__((pure)) static List<unsigned int>
  scanl(F0 &&f, unsigned int acc, const List<unsigned int> &l) {
    std::unique_ptr<List<unsigned int>> _head{};
    std::unique_ptr<List<unsigned int>> *_write = &_head;
    List<unsigned int> _loop_l = l;
    unsigned int _loop_acc = std::move(acc);
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v())) {
        *(_write) = std::make_unique<List<unsigned int>>(
            List<unsigned int>::cons(_loop_acc, List<unsigned int>::nil()));
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l.v());
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(_loop_acc, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        List<unsigned int> _next_l = *(d_a1);
        unsigned int _next_acc = f(_loop_acc, d_a0);
        _loop_l = std::move(_next_l);
        _loop_acc = std::move(_next_acc);
        continue;
      }
    }
    return std::move(*(_head));
  }

  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  __attribute__((pure)) static List<unsigned int>
  scanr(F0 &&f, unsigned int acc, const List<unsigned int> &l) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
      return List<unsigned int>::cons(acc, List<unsigned int>::nil());
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(l.v());
      auto &&_sv0 = scanr(f, acc, *(d_a1));
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0.v())) {
        return List<unsigned int>::cons(acc, List<unsigned int>::nil());
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(_sv0.v());
        return List<unsigned int>::cons(f(d_a0, d_a00), *(d_a10));
      }
    }
  }

  template <MapsTo<unsigned int, unsigned int, unsigned int> F1>
  __attribute__((pure)) static unsigned int
  foldl1_fuel(const unsigned int &fuel, F1 &&f, const List<unsigned int> &l) {
    unsigned int _result;
    List<unsigned int> _loop_l = l;
    unsigned int _loop_fuel = fuel;
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
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(_loop_l.v());
          auto &&_sv0 = *(d_a1);
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  _sv0.v())) {
            _result = d_a0;
            break;
          } else {
            const auto &[d_a00, d_a10] =
                std::get<typename List<unsigned int>::Cons>(_sv0.v());
            List<unsigned int> _next_l =
                List<unsigned int>::cons(f(d_a0, d_a00), *(d_a10));
            unsigned int _next_fuel = fuel_;
            _loop_l = std::move(_next_l);
            _loop_fuel = std::move(_next_fuel);
          }
        }
      }
    }
    return _result;
  }

  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  foldl1(F0 &&f, const List<unsigned int> &l) {
    return foldl1_fuel(l.length(), f, l);
  }

  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  foldr1(F0 &&f, const List<unsigned int> &l) {
    struct _Enter {
      const List<unsigned int> l;
    };

    struct _Call1 {
      unsigned int _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    unsigned int _result{};
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
          _result = 0u;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          auto &&_sv = *(d_a1);
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  _sv.v())) {
            _result = d_a0;
          } else {
            _stack.emplace_back(_Call1{d_a0});
            _stack.emplace_back(_Enter{*(d_a1)});
          }
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = f(_f._s0, _result);
      }
    }
    return _result;
  }

  template <
      MapsTo<std::pair<unsigned int, unsigned int>, unsigned int, unsigned int>
          F0>
  __attribute__((pure)) static std::pair<unsigned int, List<unsigned int>>
  map_accum(F0 &&f, unsigned int acc, const List<unsigned int> &l) {
    struct _Enter {
      const List<unsigned int> l;
      unsigned int acc;
    };

    struct _Call1 {
      unsigned int _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<unsigned int, List<unsigned int>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l, acc});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<unsigned int> l = _f.l;
        unsigned int acc = _f.acc;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = std::make_pair(acc, List<unsigned int>::nil());
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          auto _cs = f(acc, d_a0);
          const unsigned int &acc_ = _cs.first;
          const unsigned int &y = _cs.second;
          _stack.emplace_back(_Call1{y});
          _stack.emplace_back(_Enter{*(d_a1), acc_});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        unsigned int y = _f._s0;
        const unsigned int &final_acc = _result.first;
        const List<unsigned int> &ys = _result.second;
        _result = std::make_pair(final_acc, List<unsigned int>::cons(y, ys));
      }
    }
    return _result;
  }

  template <MapsTo<unsigned int, unsigned int> F0>
  __attribute__((pure)) static List<unsigned int>
  iterate_accum(F0 &&f, const unsigned int &n, unsigned int x) {
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
        unsigned int n_ = _loop_n - 1;
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(_loop_x, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        unsigned int _next_x = f(_loop_x);
        unsigned int _next_n = n_;
        _loop_x = std::move(_next_x);
        _loop_n = std::move(_next_n);
        continue;
      }
    }
    return std::move(*(_head));
  }

  template <MapsTo<std::pair<unsigned int, unsigned int>, unsigned int> F1>
  __attribute__((pure)) static List<unsigned int>
  unfold_fuel(const unsigned int &fuel, F1 &&f, const unsigned int &seed) {
    std::unique_ptr<List<unsigned int>> _head{};
    std::unique_ptr<List<unsigned int>> *_write = &_head;
    unsigned int _loop_seed = seed;
    unsigned int _loop_fuel = fuel;
    while (true) {
      if (_loop_fuel <= 0) {
        *(_write) =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        unsigned int fuel_ = _loop_fuel - 1;
        auto _cs = f(_loop_seed);
        const unsigned int &x = _cs.first;
        const unsigned int &next_seed = _cs.second;
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(x, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        unsigned int _next_seed = next_seed;
        unsigned int _next_fuel = fuel_;
        _loop_seed = std::move(_next_seed);
        _loop_fuel = std::move(_next_fuel);
        continue;
      }
    }
    return std::move(*(_head));
  }

  template <MapsTo<std::pair<unsigned int, unsigned int>, unsigned int> F1>
  __attribute__((pure)) static List<unsigned int>
  unfold(const unsigned int &_x0, F1 &&_x1, const unsigned int &_x2) {
    return unfold_fuel(_x0, _x1, _x2);
  }
};

#endif // INCLUDED_LOOPIFY_FOLDS
