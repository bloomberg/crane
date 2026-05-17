#ifndef INCLUDED_LOOPIFY_EXTREMA
#define INCLUDED_LOOPIFY_EXTREMA

#include <algorithm>
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
};

struct LoopifyExtrema {
  static unsigned int maximum(const List<unsigned int> &l);
  static unsigned int minimum(const List<unsigned int> &l);
  static std::pair<unsigned int, unsigned int>
  minmax(const List<unsigned int> &l);

  template <typename F0>
    requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &>
  static unsigned int
  max_by(F0 &&f,
         const List<unsigned int> &l) { /// _Enter: captures varying parameters
                                        /// for each recursive call.

    struct _Enter {
      const List<unsigned int> *l;
    };

    /// _Cont_Cons: saves [a0, f], resumes after recursive call, then processes
    /// rest.
    struct _Cont_Cons {
      unsigned int a0;
      F0 f;
    };

    using _Frame = std::variant<_Enter, _Cont_Cons>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified max_by: _Enter -> _Cont_Cons.
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
            _result = f(a0);
          } else {
            _stack.emplace_back(_Cont_Cons{a0, f});
            _stack.emplace_back(_Enter{a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Cont_Cons>(_frame));
        unsigned int a0 = _f.a0;
        F0 f = _f.f;
        unsigned int rest_max = _result;
        unsigned int fx = f(a0);
        if (rest_max < fx) {
          _result = fx;
        } else {
          _result = rest_max;
        }
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &>
  static unsigned int
  min_by(F0 &&f,
         const List<unsigned int> &l) { /// _Enter: captures varying parameters
                                        /// for each recursive call.

    struct _Enter {
      const List<unsigned int> *l;
    };

    /// _Cont_Cons: saves [a0, f], resumes after recursive call, then processes
    /// rest.
    struct _Cont_Cons {
      unsigned int a0;
      F0 f;
    };

    using _Frame = std::variant<_Enter, _Cont_Cons>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified min_by: _Enter -> _Cont_Cons.
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
            _result = f(a0);
          } else {
            _stack.emplace_back(_Cont_Cons{a0, f});
            _stack.emplace_back(_Enter{a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Cont_Cons>(_frame));
        unsigned int a0 = _f.a0;
        F0 f = _f.f;
        unsigned int rest_min = _result;
        unsigned int fx = f(a0);
        if (fx < rest_min) {
          _result = fx;
        } else {
          _result = rest_min;
        }
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &>
  static unsigned int
  argmax(F0 &&f,
         const List<unsigned int> &l) { /// _Enter: captures varying parameters
                                        /// for each recursive call.

    struct _Enter {
      const List<unsigned int> *l;
    };

    /// _Cont_Cons: saves [a0, f], resumes after recursive call, then processes
    /// rest.
    struct _Cont_Cons {
      unsigned int a0;
      F0 f;
    };

    using _Frame = std::variant<_Enter, _Cont_Cons>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified argmax: _Enter -> _Cont_Cons.
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
            _result = a0;
          } else {
            _stack.emplace_back(_Cont_Cons{a0, f});
            _stack.emplace_back(_Enter{a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Cont_Cons>(_frame));
        unsigned int a0 = _f.a0;
        F0 f = _f.f;
        unsigned int rest_best = _result;
        unsigned int fx = f(a0);
        unsigned int f_rest = f(rest_best);
        if (f_rest < fx) {
          _result = a0;
        } else {
          _result = rest_best;
        }
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &>
  static unsigned int
  argmin(F0 &&f,
         const List<unsigned int> &l) { /// _Enter: captures varying parameters
                                        /// for each recursive call.

    struct _Enter {
      const List<unsigned int> *l;
    };

    /// _Cont_Cons: saves [a0, f], resumes after recursive call, then processes
    /// rest.
    struct _Cont_Cons {
      unsigned int a0;
      F0 f;
    };

    using _Frame = std::variant<_Enter, _Cont_Cons>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified argmin: _Enter -> _Cont_Cons.
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
            _result = a0;
          } else {
            _stack.emplace_back(_Cont_Cons{a0, f});
            _stack.emplace_back(_Enter{a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Cont_Cons>(_frame));
        unsigned int a0 = _f.a0;
        F0 f = _f.f;
        unsigned int rest_best = _result;
        unsigned int fx = f(a0);
        unsigned int f_rest = f(rest_best);
        if (fx < f_rest) {
          _result = a0;
        } else {
          _result = rest_best;
        }
      }
    }
    return _result;
  }

  static unsigned int lex_compare(const List<unsigned int> &l1,
                                  const List<unsigned int> &l2);
  static bool all_equal(const List<unsigned int> &l);
  static bool is_sorted(const List<unsigned int> &l);

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &, unsigned int &>
  static bool adjacent_all(F0 &&p, const List<unsigned int> &l) {
    bool _result;
    const List<unsigned int> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        _result = true;
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l->v());
        auto &&_sv0 = *a1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _sv0.v())) {
          _result = true;
          break;
        } else {
          const auto &[a00, a10] =
              std::get<typename List<unsigned int>::Cons>(_sv0.v());
          if (p(a0, a00)) {
            _loop_l = a1.get();
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
