#ifndef INCLUDED_LOOPIFY_OPTION
#define INCLUDED_LOOPIFY_OPTION

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct LoopifyOption {
  template <typename t_A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      t_A d_a0;
      std::unique_ptr<list<t_A>> d_a1;
    };

    using variant_t = std::variant<Nil, Cons>;
    using crane_element_type = t_A;

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

    __attribute__((pure)) list<t_A> &operator=(const list<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) list<t_A> &operator=(list<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) list<t_A> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Nil>(_sv.v())) {
        return list<t_A>(Nil{});
      } else {
        const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
        t_A __c0;
        if constexpr (
            requires { d_a0 ? 0 : 0; } && requires { *d_a0; } &&
            requires { d_a0->clone(); } && requires { d_a0.get(); }) {
          using _E = std::remove_cvref_t<decltype(*d_a0)>;
          __c0 = d_a0 ? std::make_unique<_E>(d_a0->clone()) : nullptr;
        } else if constexpr (requires { d_a0.clone(); }) {
          __c0 = d_a0.clone();
        } else {
          __c0 = d_a0;
        }
        return list<t_A>(Cons{
            std::move(__c0),
            d_a1 ? std::make_unique<LoopifyOption::list<t_A>>(d_a1->clone())
                 : nullptr});
      }
    }

    // CREATORS
    template <typename _U> explicit list(const list<_U> &_other) {
      if (std::holds_alternative<typename list<_U>::Nil>(_other.v())) {
        d_v_ = Nil{};
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<_U>::Cons>(_other.v());
        d_v_ = Cons{[&]<typename _DstT = t_A>(auto &&__v) -> _DstT {
                      if constexpr (
                          requires { *__v; } &&
                          !requires { std::declval<_DstT>().get(); })
                        return _DstT(*__v);
                      else if constexpr (
                          !requires { *__v; } &&
                          requires { std::declval<_DstT>().get(); }) {
                        using _E = std::remove_pointer_t<
                            decltype(std::declval<_DstT>().get())>;
                        return std::make_unique<_E>(std::move(__v));
                      } else
                        return _DstT(__v);
                    }(d_a0),
                    d_a1 ? std::make_unique<list<t_A>>(*d_a1) : nullptr};
      }
    }

    __attribute__((pure)) static list<t_A> nil() { return list(Nil{}); }

    __attribute__((pure)) static list<t_A> cons(t_A a0, const list<t_A> &a1) {
      return list(Cons{std::move(a0), std::make_unique<list<t_A>>(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) list<t_A> *operator->() { return this; }

    __attribute__((pure)) const list<t_A> *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = list<t_A>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, T1, list<T1>, T2> F1>
  static T2 list_rect(const T2 f, F1 &&f0, const list<T1> &l) {
    struct _Enter {
      const list<T1> l;
    };

    struct _Call1 {
      list<T1> _s0;
      T1 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> l = _f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = f;
        } else {
          const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(_Call1{*(d_a1), d_a0});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = f0(_f._s1, _f._s0, _result);
      }
    }
    return _result;
  }

  template <typename T1, typename T2, MapsTo<T2, T1, list<T1>, T2> F1>
  static T2 list_rec(const T2 f, F1 &&f0, const list<T1> &l) {
    struct _Enter {
      const list<T1> l;
    };

    struct _Call1 {
      list<T1> _s0;
      T1 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> l = _f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = f;
        } else {
          const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(_Call1{*(d_a1), d_a0});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = f0(_f._s1, _f._s0, _result);
      }
    }
    return _result;
  }

  /// find_opt p l returns the first element satisfying p, or None.
  template <typename T1, MapsTo<bool, T1> F0>
  __attribute__((pure)) static std::optional<T1> find_opt(F0 &&p,
                                                          const list<T1> &l) {
    std::optional<T1> _result;
    list<T1> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l.v())) {
        _result = std::optional<T1>();
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<T1>::Cons>(_loop_l.v());
        if (p(d_a0)) {
          _result = std::make_optional<T1>(d_a0);
          break;
        } else {
          _loop_l = *(d_a1);
        }
      }
    }
    return _result;
  }

  /// last_opt l returns the last element, or None for empty.
  template <typename T1>
  __attribute__((pure)) static std::optional<T1> last_opt(const list<T1> &l) {
    std::optional<T1> _result;
    list<T1> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l.v())) {
        _result = std::optional<T1>();
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<T1>::Cons>(_loop_l.v());
        auto &&_sv = *(d_a1);
        if (std::holds_alternative<typename list<T1>::Nil>(_sv.v())) {
          _result = std::make_optional<T1>(d_a0);
          break;
        } else {
          _loop_l = *(d_a1);
        }
      }
    }
    return _result;
  }

  /// nth_opt n l returns the nth element, or None for out of bounds.
  template <typename T1>
  __attribute__((pure)) static std::optional<T1> nth_opt(const unsigned int &n,
                                                         const list<T1> &l) {
    std::optional<T1> _result;
    list<T1> _loop_l = l;
    unsigned int _loop_n = n;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l.v())) {
        _result = std::optional<T1>();
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<T1>::Cons>(_loop_l.v());
        if (_loop_n == 0u) {
          _result = std::make_optional<T1>(d_a0);
          break;
        } else {
          list<T1> _next_l = *(d_a1);
          unsigned int _next_n =
              (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
          _loop_l = std::move(_next_l);
          _loop_n = std::move(_next_n);
        }
      }
    }
    return _result;
  }

  /// lookup_opt key l looks up key in an association list.
  __attribute__((pure)) static std::optional<unsigned int>
  lookup_opt(const unsigned int &key,
             const list<std::pair<unsigned int, unsigned int>> &l);

  /// map_opt f l applies f and keeps only Some results.
  template <typename T1, typename T2, MapsTo<std::optional<T2>, T1> F0>
  __attribute__((pure)) static list<T2> map_opt(F0 &&f, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return list<T2>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
      auto _cs = f(d_a0);
      if (_cs.has_value()) {
        const T2 &y = *_cs;
        return list<T2>::cons(y, map_opt<T1, T2>(f, *(d_a1)));
      } else {
        return map_opt<T1, T2>(f, *(d_a1));
      }
    }
  }

  /// find_index p l returns the index of the first match, or None.
  template <typename T1, MapsTo<bool, T1> F0>
  __attribute__((pure)) static std::optional<unsigned int>
  find_index_aux(F0 &&p, const list<T1> &l, unsigned int i) {
    std::optional<unsigned int> _result;
    unsigned int _loop_i = std::move(i);
    list<T1> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l.v())) {
        _result = std::optional<unsigned int>();
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<T1>::Cons>(_loop_l.v());
        if (p(d_a0)) {
          _result = std::make_optional<unsigned int>(_loop_i);
          break;
        } else {
          unsigned int _next_i = (_loop_i + 1);
          list<T1> _next_l = *(d_a1);
          _loop_i = std::move(_next_i);
          _loop_l = std::move(_next_l);
        }
      }
    }
    return _result;
  }

  template <typename T1, MapsTo<bool, T1> F0>
  __attribute__((pure)) static std::optional<unsigned int>
  find_index(F0 &&p, const list<T1> &l) {
    return find_index_aux<T1>(p, l, 0u);
  }
};

#endif // INCLUDED_LOOPIFY_OPTION
