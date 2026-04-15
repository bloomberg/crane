#ifndef INCLUDED_LOOPIFY_OPTION
#define INCLUDED_LOOPIFY_OPTION

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct LoopifyOption {
  template <typename t_A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      t_A d_a0;
      std::shared_ptr<list<t_A>> d_a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit list(Nil _v) : d_v_(_v) {}

    explicit list(Cons _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<list<t_A>> nil() {
      return std::make_shared<list<t_A>>(Nil{});
    }

    static std::shared_ptr<list<t_A>>
    cons(t_A a0, const std::shared_ptr<list<t_A>> &a1) {
      return std::make_shared<list<t_A>>(Cons{std::move(a0), a1});
    }

    static std::shared_ptr<list<t_A>> cons(t_A a0,
                                           std::shared_ptr<list<t_A>> &&a1) {
      return std::make_shared<list<t_A>>(Cons{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rect(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    struct _Enter {
      const std::shared_ptr<list<T1>> l;
    };

    struct _Call1 {
      decltype(std::declval<typename list<T1>::Cons &>().d_a1) _s0;
      decltype(std::declval<typename list<T1>::Cons &>().d_a0) _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<list<T1>> l = _f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l->v())) {
          _result = f;
        } else {
          const auto &_m = *std::get_if<typename list<T1>::Cons>(&l->v());
          _stack.emplace_back(_Call1{_m.d_a1, _m.d_a0});
          _stack.emplace_back(_Enter{_m.d_a1});
        }
      } else {
        const auto &_f = std::get<_Call1>(_frame);
        _result = f0(_f._s1, _f._s0, _result);
      }
    }
    return _result;
  }

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rec(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    struct _Enter {
      const std::shared_ptr<list<T1>> l;
    };

    struct _Call1 {
      decltype(std::declval<typename list<T1>::Cons &>().d_a1) _s0;
      decltype(std::declval<typename list<T1>::Cons &>().d_a0) _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<list<T1>> l = _f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l->v())) {
          _result = f;
        } else {
          const auto &_m = *std::get_if<typename list<T1>::Cons>(&l->v());
          _stack.emplace_back(_Call1{_m.d_a1, _m.d_a0});
          _stack.emplace_back(_Enter{_m.d_a1});
        }
      } else {
        const auto &_f = std::get<_Call1>(_frame);
        _result = f0(_f._s1, _f._s0, _result);
      }
    }
    return _result;
  }

  /// find_opt p l returns the first element satisfying p, or None.
  template <typename T1, MapsTo<bool, T1> F0>
  __attribute__((pure)) static std::optional<T1>
  find_opt(F0 &&p, const std::shared_ptr<list<T1>> &l) {
    std::optional<T1> _result;
    std::shared_ptr<list<T1>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        _result = std::optional<T1>();
        _continue = false;
      } else {
        const auto &_m = *std::get_if<typename list<T1>::Cons>(&_loop_l->v());
        if (p(_m.d_a0)) {
          _result = std::make_optional<T1>(_m.d_a0);
          _continue = false;
        } else {
          _loop_l = _m.d_a1;
        }
      }
    }
    return _result;
  }

  /// last_opt l returns the last element, or None for empty.
  template <typename T1>
  __attribute__((pure)) static std::optional<T1>
  last_opt(const std::shared_ptr<list<T1>> &l) {
    std::optional<T1> _result;
    std::shared_ptr<list<T1>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        _result = std::optional<T1>();
        _continue = false;
      } else {
        const auto &_m = *std::get_if<typename list<T1>::Cons>(&_loop_l->v());
        auto &&_sv = _m.d_a1;
        if (std::holds_alternative<typename list<T1>::Nil>(_sv->v())) {
          _result = std::make_optional<T1>(_m.d_a0);
          _continue = false;
        } else {
          _loop_l = _m.d_a1;
        }
      }
    }
    return _result;
  }

  /// nth_opt n l returns the nth element, or None for out of bounds.
  template <typename T1>
  __attribute__((pure)) static std::optional<T1>
  nth_opt(const unsigned int n, const std::shared_ptr<list<T1>> &l) {
    std::optional<T1> _result;
    std::shared_ptr<list<T1>> _loop_l = l;
    unsigned int _loop_n = n;
    bool _continue = true;
    while (_continue) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        _result = std::optional<T1>();
        _continue = false;
      } else {
        const auto &_m = *std::get_if<typename list<T1>::Cons>(&_loop_l->v());
        if (_loop_n == 0u) {
          _result = std::make_optional<T1>(_m.d_a0);
          _continue = false;
        } else {
          std::shared_ptr<list<T1>> _next_l = _m.d_a1;
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
  __attribute__((pure)) static std::optional<unsigned int> lookup_opt(
      const unsigned int key,
      const std::shared_ptr<list<std::pair<unsigned int, unsigned int>>> &l);

  /// map_opt f l applies f and keeps only Some results.
  template <typename T1, typename T2, MapsTo<std::optional<T2>, T1> F0>
  static std::shared_ptr<list<T2>> map_opt(F0 &&f,
                                           const std::shared_ptr<list<T1>> &l) {
    std::shared_ptr<list<T2>> _head{};
    std::shared_ptr<list<T2>> _last{};
    std::shared_ptr<list<T1>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        if (_last) {
          std::get<typename list<T2>::Cons>(_last->v_mut()).d_a1 =
              list<T2>::nil();
        } else {
          _head = list<T2>::nil();
        }
        _continue = false;
      } else {
        const auto &_m = *std::get_if<typename list<T1>::Cons>(&_loop_l->v());
        auto _cs = f(_m.d_a0);
        if (_cs.has_value()) {
          const T2 &y = *_cs;
          auto _cell = list<T2>::cons(y, nullptr);
          if (_last) {
            std::get<typename list<T2>::Cons>(_last->v_mut()).d_a1 = _cell;
          } else {
            _head = _cell;
          }
          _last = _cell;
          _loop_l = _m.d_a1;
          continue;
        } else {
          _loop_l = _m.d_a1;
          continue;
        }
      }
    }
    return _head;
  }

  /// find_index p l returns the index of the first match, or None.
  template <typename T1, MapsTo<bool, T1> F0>
  __attribute__((pure)) static std::optional<unsigned int>
  find_index_aux(F0 &&p, const std::shared_ptr<list<T1>> &l,
                 const unsigned int i) {
    std::optional<unsigned int> _result;
    unsigned int _loop_i = i;
    std::shared_ptr<list<T1>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        _result = std::optional<unsigned int>();
        _continue = false;
      } else {
        const auto &_m = *std::get_if<typename list<T1>::Cons>(&_loop_l->v());
        if (p(_m.d_a0)) {
          _result = std::make_optional<unsigned int>(_loop_i);
          _continue = false;
        } else {
          unsigned int _next_i = (_loop_i + 1);
          std::shared_ptr<list<T1>> _next_l = _m.d_a1;
          _loop_i = std::move(_next_i);
          _loop_l = std::move(_next_l);
        }
      }
    }
    return _result;
  }

  template <typename T1, MapsTo<bool, T1> F0>
  __attribute__((pure)) static std::optional<unsigned int>
  find_index(F0 &&p, const std::shared_ptr<list<T1>> &l) {
    return find_index_aux<T1>(p, l, 0u);
  }
};

#endif // INCLUDED_LOOPIFY_OPTION
