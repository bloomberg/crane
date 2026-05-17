#ifndef INCLUDED_LOOPIFY_TAIL
#define INCLUDED_LOOPIFY_TAIL

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct LoopifyTail {
  template <typename A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      A a0;
      std::unique_ptr<list<A>> a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    list() {}

    explicit list(Nil _v) : v_(_v) {}

    explicit list(Cons _v) : v_(std::move(_v)) {}

    list(const list<A> &_other) : v_(std::move(_other.clone().v_)) {}

    list(list<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

    list<A> &operator=(const list<A> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    list<A> &operator=(list<A> &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    list<A> clone() const {
      list<A> _out{};

      struct _CloneFrame {
        const list<A> *_src;
        list<A> *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const list<A> *_src = _frame._src;
        list<A> *_dst = _frame._dst;
        if (std::holds_alternative<Nil>(_src->v())) {
          _dst->v_ = Nil{};
        } else {
          const auto &_alt = std::get<Cons>(_src->v());
          _dst->v_ =
              Cons{_alt.a0, _alt.a1 ? std::make_unique<list<A>>() : nullptr};
          auto &_dst_alt = std::get<Cons>(_dst->v_);
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    template <typename _U> explicit list(const list<_U> &_other) {
      if (std::holds_alternative<typename list<_U>::Nil>(_other.v())) {
        this->v_ = Nil{};
      } else {
        const auto &[a0, a1] = std::get<typename list<_U>::Cons>(_other.v());
        this->v_ = Cons{A(a0), a1 ? std::make_unique<list<A>>(*a1) : nullptr};
      }
    }

    static list<A> nil() { return list(Nil{}); }

    static list<A> cons(A a0, list<A> a1) {
      return list(
          Cons{std::move(a0), std::make_unique<list<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~list() {
      std::vector<std::unique_ptr<list<A>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](list<A> &_node) {
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

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, list<T1> &, T2 &>
  static T2
  list_rect(T2 f, F1 &&f0,
            const list<T1> &l) { /// _Enter: captures varying parameters for
                                 /// each recursive call.

    struct _Enter {
      const list<T1> *l;
    };

    /// _Resume_Cons: saves [f0, a1, a0], resumes after recursive call with
    /// _result.
    struct _Resume_Cons {
      F1 f0;
      list<T1> a1;
      T1 a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified list_rect: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> &l = *_f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = std::move(f);
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{f0, *a1, a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = _f.f0(_f.a0, _f.a1, _result);
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, list<T1> &, T2 &>
  static T2
  list_rec(T2 f, F1 &&f0,
           const list<T1> &l) { /// _Enter: captures varying parameters for each
                                /// recursive call.

    struct _Enter {
      const list<T1> *l;
    };

    /// _Resume_Cons: saves [f0, a1, a0], resumes after recursive call with
    /// _result.
    struct _Resume_Cons {
      F1 f0;
      list<T1> a1;
      T1 a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified list_rec: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> &l = *_f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = std::move(f);
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{f0, *a1, a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = _f.f0(_f.a0, _f.a1, _result);
      }
    }
    return _result;
  } /// Tail-recursive: last element of a list

  template <typename T1> static T1 last(T1 x, const list<T1> &l) {
    T1 _result;
    const list<T1> *_loop_l = &l;
    T1 _loop_x = std::move(x);
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        _result = std::move(_loop_x);
        break;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        _loop_l = a1.get();
        _loop_x = a0;
      }
    }
    return _result;
  } /// Tail-recursive: length with accumulator

  template <typename T1>
  static uint64_t length_acc(uint64_t acc, const list<T1> &l) {
    uint64_t _result;
    const list<T1> *_loop_l = &l;
    uint64_t _loop_acc = std::move(acc);
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        _result = std::move(_loop_acc);
        break;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        _loop_l = a1.get();
        _loop_acc = (_loop_acc + 1);
      }
    }
    return _result;
  }

  template <typename T1> static uint64_t length(const list<T1> &l) {
    return length_acc<T1>(UINT64_C(0), l);
  } /// Tail-recursive: membership test

  static bool member(uint64_t x, const list<uint64_t> &l);
  /// Tail-recursive: nth element
  static uint64_t nth(uint64_t n, const list<uint64_t> &l, uint64_t default0);

  /// Tail-recursive: fold_left
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T2 &, T1 &>
  static T2 fold_left(F0 &&f, T2 acc, const list<T1> &l) {
    T2 _result;
    const list<T1> *_loop_l = &l;
    T2 _loop_acc = std::move(acc);
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        _result = std::move(_loop_acc);
        break;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        _loop_l = a1.get();
        _loop_acc = f(_loop_acc, a0);
      }
    }
    return _result;
  }

  /// Tail-recursive: lookup in association list
  static uint64_t lookup(uint64_t key,
                         const list<std::pair<uint64_t, uint64_t>> &l);
};

#endif // INCLUDED_LOOPIFY_TAIL
