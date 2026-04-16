#ifndef INCLUDED_LOOPIFY_POLYMORPHIC
#define INCLUDED_LOOPIFY_POLYMORPHIC

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  std::shared_ptr<List<t_A>> app(std::shared_ptr<List<t_A>> m) const {
    std::shared_ptr<List<t_A>> _head{};
    std::shared_ptr<List<t_A>> *_write = &_head;
    const List *_loop_self = this;
    while (true) {
      if (std::holds_alternative<typename List<t_A>::Nil>(_loop_self->v())) {
        *_write = m;
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<t_A>::Cons>(_loop_self->v());
        auto _cell = List<t_A>::cons(d_a0, nullptr);
        *_write = _cell;
        _write = &std::get<typename List<t_A>::Cons>(_cell->v_mut()).d_a1;
        _loop_self = d_a1.get();
        continue;
      }
    }
    return _head;
  }
};

struct LoopifyPolymorphic {
  template <typename T1>
  __attribute__((pure)) static unsigned int
  poly_length(const std::shared_ptr<List<T1>> &l) {
    struct _Enter {
      const std::shared_ptr<List<T1>> l;
    };

    struct _Call1 {
      decltype(1u) _s0;
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
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<List<T1>> l = _f.l;
        if (std::holds_alternative<typename List<T1>::Nil>(l->v())) {
          _result = 0u;
        } else {
          const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l->v());
          _stack.emplace_back(_Call1{1u});
          _stack.emplace_back(_Enter{d_a1});
        }
      } else {
        const auto &_f = std::get<_Call1>(_frame);
        _result = (_f._s0 + _result);
      }
    }
    return _result;
  }

  template <typename T1>
  static std::shared_ptr<List<T1>>
  poly_reverse(const std::shared_ptr<List<T1>> &l) {
    struct _Enter {
      const std::shared_ptr<List<T1>> l;
    };

    struct _Call1 {
      decltype(List<T1>::cons(std::declval<T1 &>(), List<T1>::nil())) _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::shared_ptr<List<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<List<T1>> l = _f.l;
        if (std::holds_alternative<typename List<T1>::Nil>(l->v())) {
          _result = List<T1>::nil();
        } else {
          const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l->v());
          _stack.emplace_back(_Call1{List<T1>::cons(d_a0, List<T1>::nil())});
          _stack.emplace_back(_Enter{d_a1});
        }
      } else {
        const auto &_f = std::get<_Call1>(_frame);
        _result = _result->app(_f._s0);
      }
    }
    return _result;
  }

  template <typename T1>
  static std::shared_ptr<List<T1>>
  poly_append(const std::shared_ptr<List<T1>> &l1,
              std::shared_ptr<List<T1>> l2) {
    std::shared_ptr<List<T1>> _head{};
    std::shared_ptr<List<T1>> *_write = &_head;
    std::shared_ptr<List<T1>> _loop_l1 = l1;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l1->v())) {
        *_write = std::move(l2);
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<T1>::Cons>(_loop_l1->v());
        auto _cell = List<T1>::cons(d_a0, nullptr);
        *_write = _cell;
        _write = &std::get<typename List<T1>::Cons>(_cell->v_mut()).d_a1;
        _loop_l1 = d_a1;
        continue;
      }
    }
    return _head;
  }

  template <typename T1>
  __attribute__((pure)) static std::optional<T1>
  poly_last(const std::shared_ptr<List<T1>> &l) {
    std::optional<T1> _result;
    std::shared_ptr<List<T1>> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
        _result = std::optional<T1>();
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<T1>::Cons>(_loop_l->v());
        if (std::holds_alternative<typename List<T1>::Nil>(d_a1->v())) {
          _result = std::make_optional<T1>(d_a0);
          break;
        } else {
          _loop_l = d_a1;
        }
      }
    }
    return _result;
  }

  template <typename T1>
  static std::shared_ptr<List<T1>>
  poly_take(const unsigned int n, const std::shared_ptr<List<T1>> &l) {
    std::shared_ptr<List<T1>> _head{};
    std::shared_ptr<List<T1>> *_write = &_head;
    std::shared_ptr<List<T1>> _loop_l = l;
    unsigned int _loop_n = n;
    while (true) {
      if (_loop_n <= 0) {
        *_write = List<T1>::nil();
        break;
      } else {
        unsigned int n_ = _loop_n - 1;
        if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
          *_write = List<T1>::nil();
          break;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<T1>::Cons>(_loop_l->v());
          auto _cell = List<T1>::cons(d_a0, nullptr);
          *_write = _cell;
          _write = &std::get<typename List<T1>::Cons>(_cell->v_mut()).d_a1;
          std::shared_ptr<List<T1>> _next_l = d_a1;
          unsigned int _next_n = n_;
          _loop_l = std::move(_next_l);
          _loop_n = std::move(_next_n);
          continue;
        }
      }
    }
    return _head;
  }

  template <typename T1>
  static std::shared_ptr<List<T1>> poly_drop(const unsigned int n,
                                             std::shared_ptr<List<T1>> l) {
    std::shared_ptr<List<T1>> _result;
    std::shared_ptr<List<T1>> _loop_l = std::move(l);
    unsigned int _loop_n = n;
    while (true) {
      if (_loop_n <= 0) {
        _result = std::move(_loop_l);
        break;
      } else {
        unsigned int n_ = _loop_n - 1;
        if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
          _result = List<T1>::nil();
          break;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<T1>::Cons>(_loop_l->v());
          std::shared_ptr<List<T1>> _next_l = d_a1;
          unsigned int _next_n = n_;
          _loop_l = std::move(_next_l);
          _loop_n = std::move(_next_n);
        }
      }
    }
    return _result;
  }

  template <typename T1>
  __attribute__((pure)) static std::optional<T1>
  poly_nth(const unsigned int n, const std::shared_ptr<List<T1>> &l) {
    std::optional<T1> _result;
    std::shared_ptr<List<T1>> _loop_l = l;
    unsigned int _loop_n = n;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
        _result = std::optional<T1>();
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<T1>::Cons>(_loop_l->v());
        if (_loop_n == 0u) {
          _result = std::make_optional<T1>(d_a0);
          break;
        } else {
          std::shared_ptr<List<T1>> _next_l = d_a1;
          unsigned int _next_n =
              (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
          _loop_l = std::move(_next_l);
          _loop_n = std::move(_next_n);
        }
      }
    }
    return _result;
  }

  template <typename T1, MapsTo<bool, T1> F0>
  static std::shared_ptr<List<T1>>
  poly_filter(F0 &&p, const std::shared_ptr<List<T1>> &l) {
    std::shared_ptr<List<T1>> _head{};
    std::shared_ptr<List<T1>> *_write = &_head;
    std::shared_ptr<List<T1>> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
        *_write = List<T1>::nil();
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<T1>::Cons>(_loop_l->v());
        if (p(d_a0)) {
          auto _cell = List<T1>::cons(d_a0, nullptr);
          *_write = _cell;
          _write = &std::get<typename List<T1>::Cons>(_cell->v_mut()).d_a1;
          _loop_l = d_a1;
          continue;
        } else {
          _loop_l = d_a1;
          continue;
        }
      }
    }
    return _head;
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::shared_ptr<List<T2>>
  poly_map(F0 &&f, const std::shared_ptr<List<T1>> &l) {
    std::shared_ptr<List<T2>> _head{};
    std::shared_ptr<List<T2>> *_write = &_head;
    std::shared_ptr<List<T1>> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
        *_write = List<T2>::nil();
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<T1>::Cons>(_loop_l->v());
        auto _cell = List<T2>::cons(f(d_a0), nullptr);
        *_write = _cell;
        _write = &std::get<typename List<T2>::Cons>(_cell->v_mut()).d_a1;
        _loop_l = d_a1;
        continue;
      }
    }
    return _head;
  }

  template <typename T1, typename T2>
  static std::shared_ptr<List<std::pair<T1, T2>>>
  poly_zip(const std::shared_ptr<List<T1>> &l1,
           const std::shared_ptr<List<T2>> &l2) {
    std::shared_ptr<List<std::pair<T1, T2>>> _head{};
    std::shared_ptr<List<std::pair<T1, T2>>> *_write = &_head;
    std::shared_ptr<List<T2>> _loop_l2 = l2;
    std::shared_ptr<List<T1>> _loop_l1 = l1;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l1->v())) {
        *_write = List<std::pair<T1, T2>>::nil();
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<T1>::Cons>(_loop_l1->v());
        if (std::holds_alternative<typename List<T2>::Nil>(_loop_l2->v())) {
          *_write = List<std::pair<T1, T2>>::nil();
          break;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<T2>::Cons>(_loop_l2->v());
          auto _cell = List<std::pair<T1, T2>>::cons(
              std::make_pair(d_a0, d_a00), nullptr);
          *_write = _cell;
          _write =
              &std::get<typename List<std::pair<T1, T2>>::Cons>(_cell->v_mut())
                   .d_a1;
          std::shared_ptr<List<T2>> _next_l2 = d_a10;
          std::shared_ptr<List<T1>> _next_l1 = d_a1;
          _loop_l2 = std::move(_next_l2);
          _loop_l1 = std::move(_next_l1);
          continue;
        }
      }
    }
    return _head;
  }

  template <typename T1, typename T2>
  __attribute__((pure)) static std::pair<std::shared_ptr<List<T1>>,
                                         std::shared_ptr<List<T2>>>
  poly_unzip(const std::shared_ptr<List<std::pair<T1, T2>>> &l) {
    struct _Enter {
      const std::shared_ptr<List<std::pair<T1, T2>>> l;
    };

    struct _Call1 {
      T2 _s0;
      T1 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<std::shared_ptr<List<T1>>, std::shared_ptr<List<T2>>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<List<std::pair<T1, T2>>> l = _f.l;
        if (std::holds_alternative<typename List<std::pair<T1, T2>>::Nil>(
                l->v())) {
          _result = std::make_pair(List<T1>::nil(), List<T2>::nil());
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<std::pair<T1, T2>>::Cons>(l->v());
          const T1 &a = d_a0.first;
          const T2 &b = d_a0.second;
          _stack.emplace_back(_Call1{b, a});
          _stack.emplace_back(_Enter{d_a1});
        }
      } else {
        const auto &_f = std::get<_Call1>(_frame);
        T2 b = _f._s0;
        T1 a = _f._s1;
        const std::shared_ptr<List<T1>> &as_ = _result.first;
        const std::shared_ptr<List<T2>> &bs = _result.second;
        _result = std::make_pair(List<T1>::cons(a, as_), List<T2>::cons(b, bs));
      }
    }
    return _result;
  }

  template <typename T1, MapsTo<bool, T1> F0>
  __attribute__((pure)) static std::pair<std::shared_ptr<List<T1>>,
                                         std::shared_ptr<List<T1>>>
  poly_partition(F0 &&p, const std::shared_ptr<List<T1>> &l) {
    struct _Enter {
      const std::shared_ptr<List<T1>> l;
    };

    struct _Call1 {
      F0 _s0;
      T1 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<std::shared_ptr<List<T1>>, std::shared_ptr<List<T1>>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<List<T1>> l = _f.l;
        if (std::holds_alternative<typename List<T1>::Nil>(l->v())) {
          _result = std::make_pair(List<T1>::nil(), List<T1>::nil());
        } else {
          const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l->v());
          _stack.emplace_back(_Call1{p, d_a0});
          _stack.emplace_back(_Enter{d_a1});
        }
      } else {
        const auto &_f = std::get<_Call1>(_frame);
        F0 p = _f._s0;
        T1 d_a0 = _f._s1;
        const std::shared_ptr<List<T1>> &trues = _result.first;
        const std::shared_ptr<List<T1>> &falses = _result.second;
        if (p(d_a0)) {
          _result = std::make_pair(List<T1>::cons(d_a0, trues), falses);
        } else {
          _result = std::make_pair(trues, List<T1>::cons(d_a0, falses));
        }
      }
    }
    return _result;
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static bool
  poly_member(F0 &&eq, const T1 x, const std::shared_ptr<List<T1>> &l) {
    bool _result;
    std::shared_ptr<List<T1>> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
        _result = false;
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<T1>::Cons>(_loop_l->v());
        if (eq(x, d_a0)) {
          _result = true;
          break;
        } else {
          _loop_l = d_a1;
        }
      }
    }
    return _result;
  }

  template <typename T1>
  static std::shared_ptr<List<T1>> poly_replicate(const unsigned int n,
                                                  const T1 x) {
    std::shared_ptr<List<T1>> _head{};
    std::shared_ptr<List<T1>> *_write = &_head;
    unsigned int _loop_n = n;
    while (true) {
      if (_loop_n <= 0) {
        *_write = List<T1>::nil();
        break;
      } else {
        unsigned int n_ = _loop_n - 1;
        auto _cell = List<T1>::cons(x, nullptr);
        *_write = _cell;
        _write = &std::get<typename List<T1>::Cons>(_cell->v_mut()).d_a1;
        _loop_n = n_;
        continue;
      }
    }
    return _head;
  }

  __attribute__((pure)) static unsigned int
  nat_length(const std::shared_ptr<List<unsigned int>> &_x0);
  static std::shared_ptr<List<unsigned int>>
  nat_reverse(const std::shared_ptr<List<unsigned int>> &_x0);
  static std::shared_ptr<List<unsigned int>>
  nat_append(const std::shared_ptr<List<unsigned int>> &_x0,
             const std::shared_ptr<List<unsigned int>> &_x1);
  __attribute__((pure)) static std::optional<unsigned int>
  nat_last(const std::shared_ptr<List<unsigned int>> &_x0);
  static std::shared_ptr<List<unsigned int>>
  nat_take(const unsigned int _x0,
           const std::shared_ptr<List<unsigned int>> &_x1);
  static std::shared_ptr<List<unsigned int>>
  nat_drop(const unsigned int _x0,
           const std::shared_ptr<List<unsigned int>> &_x1);
  __attribute__((pure)) static std::optional<unsigned int>
  nat_nth(const unsigned int _x0,
          const std::shared_ptr<List<unsigned int>> &_x1);
  __attribute__((pure)) static bool nat_eq(const unsigned int _x0,
                                           const unsigned int _x1);
  __attribute__((pure)) static bool is_even(const unsigned int x);

  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  nat_filter(F0 &&_x0, const std::shared_ptr<List<unsigned int>> &_x1) {
    return poly_filter<unsigned int>(_x0, _x1);
  }

  template <MapsTo<unsigned int, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  nat_map(F0 &&_x0, const std::shared_ptr<List<unsigned int>> &_x1) {
    return poly_map<unsigned int, unsigned int>(_x0, _x1);
  }

  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static std::pair<std::shared_ptr<List<unsigned int>>,
                                         std::shared_ptr<List<unsigned int>>>
  nat_partition(F0 &&_x0, const std::shared_ptr<List<unsigned int>> &_x1) {
    return poly_partition<unsigned int>(_x0, _x1);
  }

  __attribute__((pure)) static bool
  nat_member(const unsigned int _x0,
             const std::shared_ptr<List<unsigned int>> &_x1);
  static std::shared_ptr<List<unsigned int>>
  nat_replicate(const unsigned int _x0, const unsigned int _x1);
};

#endif // INCLUDED_LOOPIFY_POLYMORPHIC
