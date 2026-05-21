#ifndef INCLUDED_LOOPIFY_OPTION
#define INCLUDED_LOOPIFY_OPTION

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct LoopifyOption {
  template <typename A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      A a;
      std::shared_ptr<list<A>> l;
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
              Cons{_alt.a, _alt.l ? std::make_shared<list<A>>() : nullptr};
          auto &_dst_alt = std::get<Cons>(_dst->v_);
          if (_alt.l) {
            _stack.push_back({_alt.l.get(), _dst_alt.l.get()});
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
        const auto &[a, l] = std::get<typename list<_U>::Cons>(_other.v());
        this->v_ = Cons{A(a), l ? std::make_shared<list<A>>(*l) : nullptr};
      }
    }

    static list<A> nil() { return list(Nil{}); }

    static list<A> cons(A a, list<A> l) {
      return list(Cons{std::move(a), std::make_shared<list<A>>(std::move(l))});
    }

    // MANIPULATORS
    ~list() {
      std::vector<std::shared_ptr<list<A>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](list<A> &_node) {
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
  }

  /// find_opt p l returns the first element satisfying p, or None.
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &>
  static std::optional<T1> find_opt(F0 &&p, const list<T1> &l) {
    const list<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        return std::optional<T1>();
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        if (p(a0)) {
          return std::make_optional<T1>(a0);
        } else {
          _loop_l = a1.get();
        }
      }
    }
  }

  /// last_opt l returns the last element, or None for empty.
  template <typename T1> static std::optional<T1> last_opt(const list<T1> &l) {
    const list<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        return std::optional<T1>();
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename list<T1>::Nil>(_sv.v())) {
          return std::make_optional<T1>(a0);
        } else {
          _loop_l = a1.get();
        }
      }
    }
  }

  /// nth_opt n l returns the nth element, or None for out of bounds.
  template <typename T1>
  static std::optional<T1> nth_opt(uint64_t n, const list<T1> &l) {
    const list<T1> *_loop_l = &l;
    uint64_t _loop_n = std::move(n);
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        return std::optional<T1>();
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        if (_loop_n == UINT64_C(0)) {
          return std::make_optional<T1>(a0);
        } else {
          _loop_l = a1.get();
          _loop_n = ((
              (_loop_n - UINT64_C(1)) > _loop_n ? 0 : (_loop_n - UINT64_C(1))));
        }
      }
    }
  }

  /// lookup_opt key l looks up key in an association list.
  static std::optional<uint64_t>
  lookup_opt(uint64_t key, const list<std::pair<uint64_t, uint64_t>> &l);

  /// map_opt f l applies f and keeps only Some results.
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<std::optional<T2>, F0 &, T1 &>
  static list<T2> map_opt(F0 &&f, const list<T1> &l) {
    std::shared_ptr<list<T2>> _head{};
    std::shared_ptr<list<T2>> *_write = &_head;
    const list<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        *_write = std::make_shared<list<T2>>(list<T2>::nil());
        break;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        auto _cs = f(a0);
        if (_cs.has_value()) {
          const T2 &y = *_cs;
          auto _cell =
              std::make_shared<list<T2>>(typename list<T2>::Cons(y, nullptr));
          *_write = std::move(_cell);
          _write = &std::get<typename list<T2>::Cons>((*_write)->v_mut()).l;
          _loop_l = a1.get();
          continue;
        } else {
          _loop_l = a1.get();
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  /// find_index p l returns the index of the first match, or None.
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &>
  static std::optional<uint64_t> find_index_aux(F0 &&p, const list<T1> &l,
                                                uint64_t i) {
    uint64_t _loop_i = std::move(i);
    const list<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        return std::optional<uint64_t>();
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        if (p(a0)) {
          return std::make_optional<uint64_t>(_loop_i);
        } else {
          _loop_i = (_loop_i + 1);
          _loop_l = a1.get();
        }
      }
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &>
  static std::optional<uint64_t> find_index(F0 &&p, const list<T1> &l) {
    return find_index_aux<T1>(p, l, UINT64_C(0));
  }
};

#endif // INCLUDED_LOOPIFY_OPTION
