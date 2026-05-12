#ifndef INCLUDED_LOOPIFY_TAIL
#define INCLUDED_LOOPIFY_TAIL

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct LoopifyTail {
  template <typename t_A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      t_A d_a0;
      std::unique_ptr<list<t_A>> d_a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    list() {}

    explicit list(Nil _v) : d_v_(_v) {}

    explicit list(Cons _v) : d_v_(std::move(_v)) {}

    list(const list<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    list(list<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    list<t_A> &operator=(const list<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    list<t_A> &operator=(list<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    list<t_A> clone() const {
      list<t_A> _out{};

      struct _CloneFrame {
        const list<t_A> *_src;
        list<t_A> *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const list<t_A> *_src = _frame._src;
        list<t_A> *_dst = _frame._dst;
        if (std::holds_alternative<Nil>(_src->v())) {
          _dst->d_v_ = Nil();
        } else {
          const auto &_alt = std::get<Cons>(_src->v());
          _dst->d_v_ = Cons(_alt.d_a0, _alt.d_a1 ? std::make_unique<list<t_A>>()
                                                 : nullptr);
          auto &_dst_alt = std::get<Cons>(_dst->d_v_);
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    template <typename _U> explicit list(const list<_U> &_other) {
      if (std::holds_alternative<typename list<_U>::Nil>(_other.v())) {
        this->d_v_ = Nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<_U>::Cons>(_other.v());
        this->d_v_ = Cons(t_A(d_a0),
                          d_a1 ? std::make_unique<list<t_A>>(*d_a1) : nullptr);
      }
    }

    static list<t_A> nil() { return list(Nil()); }

    static list<t_A> cons(t_A a0, list<t_A> a1) {
      return list(
          Cons(std::move(a0), std::make_unique<list<t_A>>(std::move(a1))));
    }

    // MANIPULATORS
    ~list() {
      std::vector<std::unique_ptr<list<t_A>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](list<t_A> &_node) {
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
  };

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, list<T1> &, T2 &>
  static T2
  list_rect(const T2 f, F1 &&f0,
            const list<T1> &l) { /// _Enter: captures varying parameters for
                                 /// each recursive call.

    struct _Enter {
      const list<T1> *l;
    };

    /// _Resume_Cons: saves [f0, d_a1, d_a0], resumes after recursive call with
    /// _result.
    struct _Resume_Cons {
      F1 f0;
      list<T1> d_a1;
      T1 d_a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter(&l));
    /// Loopified list_rect: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> &l = *(_f.l);
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = f;
        } else {
          const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons(f0, *(d_a1), d_a0));
          _stack.emplace_back(_Enter(d_a1.get()));
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = _f.f0(_f.d_a0, _f.d_a1, _result);
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, list<T1> &, T2 &>
  static T2
  list_rec(const T2 f, F1 &&f0,
           const list<T1> &l) { /// _Enter: captures varying parameters for each
                                /// recursive call.

    struct _Enter {
      const list<T1> *l;
    };

    /// _Resume_Cons: saves [f0, d_a1, d_a0], resumes after recursive call with
    /// _result.
    struct _Resume_Cons {
      F1 f0;
      list<T1> d_a1;
      T1 d_a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter(&l));
    /// Loopified list_rec: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> &l = *(_f.l);
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = f;
        } else {
          const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons(f0, *(d_a1), d_a0));
          _stack.emplace_back(_Enter(d_a1.get()));
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = _f.f0(_f.d_a0, _f.d_a1, _result);
      }
    }
    return _result;
  } /// Tail-recursive: last element of a list

  template <typename T1> static T1 last(const T1 x, const list<T1> &l) {
    T1 _result;
    const list<T1> *_loop_l = &l;
    T1 _loop_x = x;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        _result = _loop_x;
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<T1>::Cons>(_loop_l->v());
        _loop_l = d_a1.get();
        _loop_x = d_a0;
      }
    }
    return _result;
  } /// Tail-recursive: length with accumulator

  template <typename T1>
  static unsigned int length_acc(const unsigned int acc, const list<T1> &l) {
    unsigned int _result;
    const list<T1> *_loop_l = &l;
    unsigned int _loop_acc = acc;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        _result = _loop_acc;
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<T1>::Cons>(_loop_l->v());
        _loop_l = d_a1.get();
        _loop_acc = (_loop_acc + 1);
      }
    }
    return _result;
  }

  template <typename T1> static unsigned int length(const list<T1> &l) {
    return length_acc<T1>(0u, l);
  }

  /// Tail-recursive: membership test
  static bool member(const unsigned int x, const list<unsigned int> &l);
  /// Tail-recursive: nth element
  static unsigned int
  nth(const unsigned int n, const list<unsigned int> &l,
      const unsigned int default0); /// Tail-recursive: fold_left

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T2 &, T1 &>
  static T2 fold_left(F0 &&f, const T2 acc, const list<T1> &l) {
    T2 _result;
    const list<T1> *_loop_l = &l;
    T2 _loop_acc = acc;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        _result = _loop_acc;
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<T1>::Cons>(_loop_l->v());
        _loop_l = d_a1.get();
        _loop_acc = f(_loop_acc, d_a0);
      }
    }
    return _result;
  }

  /// Tail-recursive: lookup in association list
  static unsigned int
  lookup(const unsigned int key,
         const list<std::pair<unsigned int, unsigned int>> &l);
};

#endif // INCLUDED_LOOPIFY_TAIL
