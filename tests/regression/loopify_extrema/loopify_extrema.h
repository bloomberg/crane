#ifndef INCLUDED_LOOPIFY_EXTREMA
#define INCLUDED_LOOPIFY_EXTREMA

#include <algorithm>
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

  __attribute__((pure)) static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List>> _stack;
    auto _drain = [&](List &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
        if (_alt.d_a1)
          _stack.push_back(std::move(_alt.d_a1));
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node)
        _drain(*_node);
    }
  }

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct LoopifyExtrema {
  __attribute__((pure)) static unsigned int
  maximum(const List<unsigned int> &l);
  __attribute__((pure)) static unsigned int
  minimum(const List<unsigned int> &l);
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  minmax(const List<unsigned int> &l);

  template <MapsTo<unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  max_by(F0 &&f, const List<unsigned int> &l) {
    struct _Enter {
      const List<unsigned int> l;
    };

    struct _Call1 {
      unsigned int _s0;
      F0 _s1;
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
            _result = f(d_a0);
          } else {
            _stack.emplace_back(_Call1{d_a0, f});
            _stack.emplace_back(_Enter{*(d_a1)});
          }
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        unsigned int d_a0 = _f._s0;
        F0 f = _f._s1;
        unsigned int rest_max = _result;
        unsigned int fx = f(d_a0);
        if (rest_max < fx) {
          _result = fx;
        } else {
          _result = rest_max;
        }
      }
    }
    return _result;
  }

  template <MapsTo<unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  min_by(F0 &&f, const List<unsigned int> &l) {
    struct _Enter {
      const List<unsigned int> l;
    };

    struct _Call1 {
      unsigned int _s0;
      F0 _s1;
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
            _result = f(d_a0);
          } else {
            _stack.emplace_back(_Call1{d_a0, f});
            _stack.emplace_back(_Enter{*(d_a1)});
          }
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        unsigned int d_a0 = _f._s0;
        F0 f = _f._s1;
        unsigned int rest_min = _result;
        unsigned int fx = f(d_a0);
        if (fx < rest_min) {
          _result = fx;
        } else {
          _result = rest_min;
        }
      }
    }
    return _result;
  }

  template <MapsTo<unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  argmax(F0 &&f, const List<unsigned int> &l) {
    struct _Enter {
      const List<unsigned int> l;
    };

    struct _Call1 {
      unsigned int _s0;
      F0 _s1;
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
            _stack.emplace_back(_Call1{d_a0, f});
            _stack.emplace_back(_Enter{*(d_a1)});
          }
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        unsigned int d_a0 = _f._s0;
        F0 f = _f._s1;
        unsigned int rest_best = _result;
        unsigned int fx = f(d_a0);
        unsigned int f_rest = f(rest_best);
        if (f_rest < fx) {
          _result = d_a0;
        } else {
          _result = rest_best;
        }
      }
    }
    return _result;
  }

  template <MapsTo<unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  argmin(F0 &&f, const List<unsigned int> &l) {
    struct _Enter {
      const List<unsigned int> l;
    };

    struct _Call1 {
      unsigned int _s0;
      F0 _s1;
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
            _stack.emplace_back(_Call1{d_a0, f});
            _stack.emplace_back(_Enter{*(d_a1)});
          }
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        unsigned int d_a0 = _f._s0;
        F0 f = _f._s1;
        unsigned int rest_best = _result;
        unsigned int fx = f(d_a0);
        unsigned int f_rest = f(rest_best);
        if (fx < f_rest) {
          _result = d_a0;
        } else {
          _result = rest_best;
        }
      }
    }
    return _result;
  }

  __attribute__((pure)) static unsigned int
  lex_compare(const List<unsigned int> &l1, const List<unsigned int> &l2);
  __attribute__((pure)) static bool all_equal(const List<unsigned int> &l);
  __attribute__((pure)) static bool is_sorted(const List<unsigned int> &l);

  template <MapsTo<bool, unsigned int, unsigned int> F0>
  __attribute__((pure)) static bool adjacent_all(F0 &&p,
                                                 const List<unsigned int> &l) {
    bool _result;
    List<unsigned int> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v())) {
        _result = true;
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l.v());
        auto &&_sv0 = *(d_a1);
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _sv0.v())) {
          _result = true;
          break;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(_sv0.v());
          if (p(d_a0, d_a00)) {
            _loop_l = *(d_a1);
          } else {
            _result = false;
            break;
          }
        }
      }
    }
    return _result;
  }
};

#endif // INCLUDED_LOOPIFY_EXTREMA
