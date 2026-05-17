#ifndef INCLUDED_LOOPIFY_LISTS
#define INCLUDED_LOOPIFY_LISTS

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

/// Consolidated UNIQUE list operations - no stdlib duplicates.
/// Tests loopification on domain-specific list algorithms.
struct LoopifyLists {
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

    list(list<A> &&_other) : v_(std::move(_other.v_)) {}

    list<A> &operator=(const list<A> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    list<A> &operator=(list<A> &&_other) {
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
          _result = f;
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
          _result = f;
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

  /// stutter l duplicates each element: 1,2 -> 1,1,2,2.
  template <typename T1> static list<T1> stutter(const list<T1> &l) {
    std::unique_ptr<list<T1>> _head{};
    std::unique_ptr<list<T1>> *_write = &_head;
    const list<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        *_write = std::make_unique<list<T1>>(list<T1>::nil());
        break;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        auto _cell =
            std::make_unique<list<T1>>(typename list<T1>::Cons(a0, nullptr));
        auto _cell1 =
            std::make_unique<list<T1>>(typename list<T1>::Cons(a0, nullptr));
        std::get<typename list<T1>::Cons>(_cell->v_mut()).a1 =
            std::move(_cell1);
        *_write = std::move(_cell);
        _write = &std::get<typename list<T1>::Cons>(
                      std::get<typename list<T1>::Cons>((*_write)->v_mut())
                          .a1->v_mut())
                      .a1;
        _loop_l = a1.get();
        continue;
      }
    }
    return std::move(*_head);
  }

  /// snoc l x appends x at the end (reverse cons).
  template <typename T1> static list<T1> snoc(const list<T1> &l, T1 x) {
    std::unique_ptr<list<T1>> _head{};
    std::unique_ptr<list<T1>> *_write = &_head;
    const list<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        *_write =
            std::make_unique<list<T1>>(list<T1>::cons(x, list<T1>::nil()));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        auto _cell =
            std::make_unique<list<T1>>(typename list<T1>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename list<T1>::Cons>((*_write)->v_mut()).a1;
        _loop_l = a1.get();
        continue;
      }
    }
    return std::move(*_head);
  }

  /// intersperse sep l inserts separator between elements.
  template <typename T1>
  static list<T1> intersperse(T1 sep, const list<T1> &l) {
    std::unique_ptr<list<T1>> _head{};
    std::unique_ptr<list<T1>> *_write = &_head;
    const list<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        *_write = std::make_unique<list<T1>>(list<T1>::nil());
        break;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename list<T1>::Nil>(_sv.v())) {
          *_write =
              std::make_unique<list<T1>>(list<T1>::cons(a0, list<T1>::nil()));
          break;
        } else {
          auto _cell =
              std::make_unique<list<T1>>(typename list<T1>::Cons(a0, nullptr));
          auto _cell1 =
              std::make_unique<list<T1>>(typename list<T1>::Cons(sep, nullptr));
          std::get<typename list<T1>::Cons>(_cell->v_mut()).a1 =
              std::move(_cell1);
          *_write = std::move(_cell);
          _write = &std::get<typename list<T1>::Cons>(
                        std::get<typename list<T1>::Cons>((*_write)->v_mut())
                            .a1->v_mut())
                        .a1;
          _loop_l = a1.get();
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  /// replicate n x creates n copies of x.
  template <typename T1> static list<T1> replicate(unsigned int n, T1 x) {
    std::unique_ptr<list<T1>> _head{};
    std::unique_ptr<list<T1>> *_write = &_head;
    unsigned int _loop_n = std::move(n);
    while (true) {
      if (_loop_n <= 0) {
        *_write = std::make_unique<list<T1>>(list<T1>::nil());
        break;
      } else {
        unsigned int m = _loop_n - 1;
        auto _cell =
            std::make_unique<list<T1>>(typename list<T1>::Cons(x, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename list<T1>::Cons>((*_write)->v_mut()).a1;
        _loop_n = m;
        continue;
      }
    }
    return std::move(*_head);
  }

  /// replicate_list n l repeats list l n times.
  template <typename T1>
  static list<T1>
  replicate_list(unsigned int n,
                 const list<T1> &l) { /// _Enter: captures varying parameters
                                      /// for each recursive call.

    struct _Enter {
      unsigned int n;
    };

    /// _Resume_m: saves [app, l], resumes after recursive call with _result.
    struct _Resume_m {
      std::function<list<T1>(list<T1>, list<T1>)> app;
      list<T1> l;
    };

    using _Frame = std::variant<_Enter, _Resume_m>;
    list<T1> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{n});
    /// Loopified replicate_list: _Enter -> _Resume_m.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        unsigned int n = _f.n;
        auto app_impl = [](auto &_self_app, const list<T1> &l1,
                           list<T1> l2) -> list<T1> {
          if (std::holds_alternative<typename list<T1>::Nil>(l1.v())) {
            return l2;
          } else {
            const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l1.v());
            return list<T1>::cons(a0, _self_app(_self_app, *a1, std::move(l2)));
          }
        };
        auto app = [&](const list<T1> &l1, list<T1> l2) -> list<T1> {
          return app_impl(app_impl, l1, l2);
        };
        if (n <= 0) {
          _result = list<T1>::nil();
        } else {
          unsigned int m = n - 1;
          _stack.emplace_back(_Resume_m{std::move(app), l});
          _stack.emplace_back(_Enter{m});
        }
      } else {
        auto _f = std::move(std::get<_Resume_m>(_frame));
        _result = _f.app(_f.l, _result);
      }
    }
    return _result;
  }

  /// init_list n f generates f 0, f 1, ..., f (n-1).
  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, unsigned int &>
  static list<T1> init_list(unsigned int n, F1 &&f) {
    auto go_impl = [&](auto &_self_go, unsigned int i) -> list<T1> {
      if (i <= 0) {
        return list<T1>::nil();
      } else {
        unsigned int j = i - 1;
        return list<T1>::cons(f((((n - i) > n ? 0 : (n - i)))),
                              _self_go(_self_go, j));
      }
    };
    auto go = [&](unsigned int i) -> list<T1> { return go_impl(go_impl, i); };
    return go(n);
  }

  /// range start count generates start, start+1, ..., start+count-1.
  static list<unsigned int> range(unsigned int start, unsigned int count0);

  /// tails l returns all suffixes.
  template <typename T1> static list<list<T1>> tails(list<T1> l) {
    std::unique_ptr<list<list<T1>>> _head{};
    std::unique_ptr<list<list<T1>>> *_write = &_head;
    list<T1> _loop_l = std::move(l);
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l.v_mut())) {
        *_write = std::make_unique<list<list<T1>>>(
            list<list<T1>>::cons(list<T1>::nil(), list<list<T1>>::nil()));
        break;
      } else {
        auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l.v_mut());
        auto _cell = std::make_unique<list<list<T1>>>(
            typename list<list<T1>>::Cons(_loop_l, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename list<list<T1>>::Cons>((*_write)->v_mut()).a1;
        _loop_l = std::move(*a1);
        continue;
      }
    }
    return std::move(*_head);
  }

  /// inits l returns all prefixes (complex recursion pattern).
  template <typename T1>
  static list<list<T1>>
  inits(const list<T1> &l) { /// _Enter: captures varying parameters for each
                             /// recursive call.

    struct _Enter {
      const list<T1> *l;
    };

    /// _Resume_Cons: saves [_s0, map_cons], resumes after recursive call with
    /// _result.
    struct _Resume_Cons {
      decltype(list<T1>::nil()) _s0;
      std::function<list<list<T1>>(list<list<T1>>)> map_cons;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    list<list<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified inits: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> &l = *_f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result =
              list<list<T1>>::cons(list<T1>::nil(), list<list<T1>>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          auto map_cons_impl = [](auto &_self_map_cons,
                                  const list<list<T1>> &ys) -> list<list<T1>> {
            if (std::holds_alternative<typename list<list<T1>>::Nil>(ys.v())) {
              return list<list<T1>>::nil();
            } else {
              const auto &[a0, a1] =
                  std::get<typename list<list<T1>>::Cons>(ys.v());
              return list<list<T1>>::cons(list<T1>::cons(a0, a0),
                                          _self_map_cons(_self_map_cons, *a1));
            }
          };
          auto map_cons = [&](const list<list<T1>> &ys) -> list<list<T1>> {
            return map_cons_impl(map_cons_impl, ys);
          };
          _stack.emplace_back(
              _Resume_Cons{list<T1>::nil(), std::move(map_cons)});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = list<list<T1>>::cons(_f._s0, _f.map_cons(_result));
      }
    }
    return _result;
  }

  /// scanl f acc l returns intermediate fold results.
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T2 &, T1 &>
  static list<T2> scanl(F0 &&f, T2 acc, const list<T1> &l) {
    std::unique_ptr<list<T2>> _head{};
    std::unique_ptr<list<T2>> *_write = &_head;
    const list<T1> *_loop_l = &l;
    T2 _loop_acc = std::move(acc);
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        *_write = std::make_unique<list<T2>>(
            list<T2>::cons(_loop_acc, list<T2>::nil()));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        T2 new_acc = f(_loop_acc, a0);
        auto _cell = std::make_unique<list<T2>>(
            typename list<T2>::Cons(_loop_acc, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename list<T2>::Cons>((*_write)->v_mut()).a1;
        _loop_l = a1.get();
        _loop_acc = new_acc;
        continue;
      }
    }
    return std::move(*_head);
  }

  /// group_by eq l groups consecutive equal elements.
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static list<list<T1>> group_by_aux(F0 &&eq, const T1 &prev, list<T1> acc,
                                     const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return list<list<T1>>::cons(std::move(acc), list<list<T1>>::nil());
    } else {
      const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
      if (eq(prev, a0)) {
        return group_by_aux<T1>(eq, a0, list<T1>::cons(a0, std::move(acc)),
                                *a1);
      } else {
        return list<list<T1>>::cons(
            std::move(acc),
            group_by_aux<T1>(eq, a0, list<T1>::cons(a0, list<T1>::nil()), *a1));
      }
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static list<list<T1>> group_by(F0 &&eq, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return list<list<T1>>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
      return group_by_aux<T1>(eq, a0, list<T1>::cons(a0, list<T1>::nil()), *a1);
    }
  } /// chunks_of n l splits into chunks of size n.

  template <typename T1>
  static list<list<T1>> chunks_of_aux(unsigned int n, const list<T1> &l,
                                      unsigned int fuel) {
    std::unique_ptr<list<list<T1>>> _head{};
    std::unique_ptr<list<list<T1>>> *_write = &_head;
    unsigned int _loop_fuel = std::move(fuel);
    list<T1> _loop_l = l;
    while (true) {
      if (_loop_fuel <= 0) {
        *_write = std::make_unique<list<list<T1>>>(list<list<T1>>::nil());
        break;
      } else {
        unsigned int f = _loop_fuel - 1;
        auto take_impl = [](auto &_self_take, unsigned int k,
                            const list<T1> &lst) -> list<T1> {
          if (k <= 0) {
            return list<T1>::nil();
          } else {
            unsigned int m = k - 1;
            if (std::holds_alternative<typename list<T1>::Nil>(lst.v())) {
              return list<T1>::nil();
            } else {
              const auto &[a0, a1] = std::get<typename list<T1>::Cons>(lst.v());
              return list<T1>::cons(a0, _self_take(_self_take, m, *a1));
            }
          }
        };
        auto take = [&](unsigned int k, const list<T1> &lst) -> list<T1> {
          return take_impl(take_impl, k, lst);
        };
        auto drop0_impl = [](auto &_self_drop0, unsigned int k,
                             list<T1> lst) -> list<T1> {
          if (k <= 0) {
            return lst;
          } else {
            unsigned int m = k - 1;
            if (std::holds_alternative<typename list<T1>::Nil>(lst.v_mut())) {
              return list<T1>::nil();
            } else {
              auto &[a00, a10] = std::get<typename list<T1>::Cons>(lst.v_mut());
              return _self_drop0(_self_drop0, m, *a10);
            }
          }
        };
        auto drop0 = [&](unsigned int k, list<T1> lst) -> list<T1> {
          return drop0_impl(drop0_impl, k, lst);
        };
        if (std::holds_alternative<typename list<T1>::Nil>(_loop_l.v())) {
          *_write = std::make_unique<list<list<T1>>>(list<list<T1>>::nil());
          break;
        } else {
          list<T1> chunk = take(n, _loop_l);
          list<T1> rest = drop0(n, _loop_l);
          if (std::holds_alternative<typename list<T1>::Nil>(chunk.v_mut())) {
            *_write = std::make_unique<list<list<T1>>>(list<list<T1>>::nil());
            break;
          } else {
            auto _cell = std::make_unique<list<list<T1>>>(
                typename list<list<T1>>::Cons(chunk, nullptr));
            *_write = std::move(_cell);
            _write =
                &std::get<typename list<list<T1>>::Cons>((*_write)->v_mut()).a1;
            _loop_fuel = f;
            _loop_l = std::move(rest);
            continue;
          }
        }
      }
    }
    return std::move(*_head);
  }

  template <typename T1>
  static list<list<T1>> chunks_of(unsigned int n, const list<T1> &l) {
    auto length_impl = [](auto &_self_length,
                          const list<T1> &l0) -> unsigned int {
      if (std::holds_alternative<typename list<T1>::Nil>(l0.v())) {
        return 0u;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l0.v());
        return (_self_length(_self_length, *a1) + 1);
      }
    };
    auto length = [&](const list<T1> &l0) -> unsigned int {
      return length_impl(length_impl, l0);
    };
    return chunks_of_aux<T1>(n, l, (length(l) + 1));
  }

  /// step_sum l sums with conditional contributions: even values as-is, odd
  /// doubled.
  static unsigned int step_sum(const list<unsigned int> &l);
  /// sum_abs l sums absolute values (using monus for nat).
  static unsigned int sum_abs(const list<unsigned int> &l, unsigned int base);
  /// four_elem l multi-case pattern matching on list structure.
  static unsigned int four_elem(const list<unsigned int> &l);
  /// between lo hi l filters elements in range lo, hi.
  static list<unsigned int> between(unsigned int lo, unsigned int hi,
                                    const list<unsigned int> &l);

  /// count_matching p l counts elements satisfying predicate.
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &>
  static unsigned int count_matching(F0 &&p, const list<unsigned int> &l) {
    if (std::holds_alternative<typename list<unsigned int>::Nil>(l.v())) {
      return 0u;
    } else {
      const auto &[a0, a1] = std::get<typename list<unsigned int>::Cons>(l.v());
      if (p(a0)) {
        return (count_matching(p, *a1) + 1);
      } else {
        return count_matching(p, *a1);
      }
    }
  }

  /// categorize k l categorizes elements: 1 for <k, 2 for =k, 3 for >k.
  static unsigned int categorize(unsigned int k, const list<unsigned int> &l);
  /// max_prefix_sum l maximum prefix sum (Kadane-like).
  static unsigned int max_prefix_sum(const list<unsigned int> &l);
  /// pairwise_sum l sums consecutive pairs: 1,2,3,4 -> 3,7.
  static list<unsigned int> pairwise_sum(const list<unsigned int> &l);
  /// weighted_sum i l weighted sum with increasing weights.
  static unsigned int weighted_sum(unsigned int i, const list<unsigned int> &l);

  /// zip_with f l1 l2 zips two lists with a function.
  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T1 &, T2 &>
  static list<T3> zip_with(F0 &&f, const list<T1> &l1, const list<T2> &l2) {
    std::unique_ptr<list<T3>> _head{};
    std::unique_ptr<list<T3>> *_write = &_head;
    const list<T2> *_loop_l2 = &l2;
    const list<T1> *_loop_l1 = &l1;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l1->v())) {
        *_write = std::make_unique<list<T3>>(list<T3>::nil());
        break;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l1->v());
        if (std::holds_alternative<typename list<T2>::Nil>(_loop_l2->v())) {
          *_write = std::make_unique<list<T3>>(list<T3>::nil());
          break;
        } else {
          const auto &[a00, a10] =
              std::get<typename list<T2>::Cons>(_loop_l2->v());
          auto _cell = std::make_unique<list<T3>>(
              typename list<T3>::Cons(f(a0, a00), nullptr));
          *_write = std::move(_cell);
          _write = &std::get<typename list<T3>::Cons>((*_write)->v_mut()).a1;
          _loop_l2 = a10.get();
          _loop_l1 = a1.get();
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  /// zip_longest l1 l2 def zips with default for mismatched lengths.
  template <typename T1>
  static list<std::pair<T1, T1>>
  zip_longest_aux(unsigned int fuel, const list<T1> &l1, const list<T1> &l2,
                  T1 default0) {
    std::unique_ptr<list<std::pair<T1, T1>>> _head{};
    std::unique_ptr<list<std::pair<T1, T1>>> *_write = &_head;
    list<T1> _loop_l2 = l2;
    list<T1> _loop_l1 = l1;
    unsigned int _loop_fuel = std::move(fuel);
    while (true) {
      if (_loop_fuel <= 0) {
        *_write = std::make_unique<list<std::pair<T1, T1>>>(
            list<std::pair<T1, T1>>::nil());
        break;
      } else {
        unsigned int f = _loop_fuel - 1;
        if (std::holds_alternative<typename list<T1>::Nil>(_loop_l1.v())) {
          if (std::holds_alternative<typename list<T1>::Nil>(_loop_l2.v())) {
            *_write = std::make_unique<list<std::pair<T1, T1>>>(
                list<std::pair<T1, T1>>::nil());
            break;
          } else {
            const auto &[a00, a10] =
                std::get<typename list<T1>::Cons>(_loop_l2.v());
            auto _cell = std::make_unique<list<std::pair<T1, T1>>>(
                typename list<std::pair<T1, T1>>::Cons(
                    std::make_pair(default0, a00), nullptr));
            *_write = std::move(_cell);
            _write = &std::get<typename list<std::pair<T1, T1>>::Cons>(
                          (*_write)->v_mut())
                          .a1;
            _loop_l2 = std::move(*a10);
            _loop_l1 = list<T1>::nil();
            _loop_fuel = f;
            continue;
          }
        } else {
          const auto &[a0, a1] =
              std::get<typename list<T1>::Cons>(_loop_l1.v());
          if (std::holds_alternative<typename list<T1>::Nil>(_loop_l2.v())) {
            auto _cell = std::make_unique<list<std::pair<T1, T1>>>(
                typename list<std::pair<T1, T1>>::Cons(
                    std::make_pair(a0, default0), nullptr));
            *_write = std::move(_cell);
            _write = &std::get<typename list<std::pair<T1, T1>>::Cons>(
                          (*_write)->v_mut())
                          .a1;
            _loop_l2 = list<T1>::nil();
            _loop_l1 = std::move(*a1);
            _loop_fuel = f;
            continue;
          } else {
            const auto &[a00, a10] =
                std::get<typename list<T1>::Cons>(_loop_l2.v());
            auto _cell = std::make_unique<list<std::pair<T1, T1>>>(
                typename list<std::pair<T1, T1>>::Cons(std::make_pair(a0, a00),
                                                       nullptr));
            *_write = std::move(_cell);
            _write = &std::get<typename list<std::pair<T1, T1>>::Cons>(
                          (*_write)->v_mut())
                          .a1;
            _loop_l2 = std::move(*a10);
            _loop_l1 = std::move(*a1);
            _loop_fuel = f;
            continue;
          }
        }
      }
    }
    return std::move(*_head);
  }

  template <typename T1>
  static list<std::pair<T1, T1>>
  zip_longest(const list<T1> &l1, const list<T1> &l2, const T1 &default0) {
    auto length_impl = [](auto &_self_length,
                          const list<T1> &l) -> unsigned int {
      if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
        return 0u;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
        return (_self_length(_self_length, *a1) + 1);
      }
    };
    auto length = [&](const list<T1> &l) -> unsigned int {
      return length_impl(length_impl, l);
    };
    unsigned int len = (length(l1) + length(l2));
    return zip_longest_aux<T1>((len + 1), l1, l2, default0);
  }

  /// sliding_pairs l returns consecutive pairs: 1,2,3 -> (1,2),(2,3).
  template <typename T1>
  static list<std::pair<T1, T1>> sliding_pairs(const list<T1> &l) {
    std::unique_ptr<list<std::pair<T1, T1>>> _head{};
    std::unique_ptr<list<std::pair<T1, T1>>> *_write = &_head;
    const list<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        *_write = std::make_unique<list<std::pair<T1, T1>>>(
            list<std::pair<T1, T1>>::nil());
        break;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        auto &&_sv0 = *a1;
        if (std::holds_alternative<typename list<T1>::Nil>(_sv0.v())) {
          *_write = std::make_unique<list<std::pair<T1, T1>>>(
              list<std::pair<T1, T1>>::nil());
          break;
        } else {
          const auto &[a00, a10] = std::get<typename list<T1>::Cons>(_sv0.v());
          auto _cell = std::make_unique<list<std::pair<T1, T1>>>(
              typename list<std::pair<T1, T1>>::Cons(std::make_pair(a0, a00),
                                                     nullptr));
          *_write = std::move(_cell);
          _write = &std::get<typename list<std::pair<T1, T1>>::Cons>(
                        (*_write)->v_mut())
                        .a1;
          _loop_l = a1.get();
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  /// partition3 p q l partitions into 3 groups based on 2 predicates.
  template <typename F0, typename F1>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &> &&
             std::is_invocable_r_v<bool, F1 &, unsigned int &>
  static std::pair<std::pair<list<unsigned int>, list<unsigned int>>,
                   list<unsigned int>>
  partition3(
      F0 &&p, F1 &&q,
      const list<unsigned int>
          &l) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      const list<unsigned int> *l;
    };

    /// _Cont_Cons: saves [a0, p, q], resumes after recursive call, then
    /// processes rest.
    struct _Cont_Cons {
      unsigned int a0;
      F0 p;
      F1 q;
    };

    using _Frame = std::variant<_Enter, _Cont_Cons>;
    std::pair<std::pair<list<unsigned int>, list<unsigned int>>,
              list<unsigned int>>
        _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified partition3: _Enter -> _Cont_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<unsigned int> &l = *_f.l;
        if (std::holds_alternative<typename list<unsigned int>::Nil>(l.v())) {
          _result = std::make_pair(std::make_pair(list<unsigned int>::nil(),
                                                  list<unsigned int>::nil()),
                                   list<unsigned int>::nil());
        } else {
          const auto &[a0, a1] =
              std::get<typename list<unsigned int>::Cons>(l.v());
          _stack.emplace_back(_Cont_Cons{a0, p, q});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Cont_Cons>(_frame));
        unsigned int a0 = _f.a0;
        F0 p = _f.p;
        F1 q = _f.q;
        const std::pair<list<unsigned int>, list<unsigned int>> &p0 =
            _result.first;
        const list<unsigned int> &cs = _result.second;
        const list<unsigned int> &as_ = p0.first;
        const list<unsigned int> &bs = p0.second;
        if (p(a0)) {
          _result = std::make_pair(
              std::make_pair(list<unsigned int>::cons(a0, as_), bs), cs);
        } else {
          if (q(a0)) {
            _result = std::make_pair(
                std::make_pair(as_, list<unsigned int>::cons(a0, bs)), cs);
          } else {
            _result = std::make_pair(std::make_pair(as_, bs),
                                     list<unsigned int>::cons(a0, cs));
          }
        }
      }
    }
    return _result;
  }

  /// transpose m transposes a matrix (list of lists).
  template <typename T1>
  static list<list<T1>> transpose_fuel(unsigned int fuel,
                                       const list<list<T1>> &m) {
    std::unique_ptr<list<list<T1>>> _head{};
    std::unique_ptr<list<list<T1>>> *_write = &_head;
    list<list<T1>> _loop_m = m;
    unsigned int _loop_fuel = std::move(fuel);
    while (true) {
      if (_loop_fuel <= 0) {
        *_write = std::make_unique<list<list<T1>>>(list<list<T1>>::nil());
        break;
      } else {
        unsigned int f = _loop_fuel - 1;
        auto map_head_impl = [](auto &_self_map_head,
                                const list<list<T1>> &l) -> list<T1> {
          if (std::holds_alternative<typename list<list<T1>>::Nil>(l.v())) {
            return list<T1>::nil();
          } else {
            const auto &[a0, a1] =
                std::get<typename list<list<T1>>::Cons>(l.v());
            if (std::holds_alternative<typename list<T1>::Nil>(a0.v())) {
              return list<T1>::nil();
            } else {
              const auto &[a00, a10] =
                  std::get<typename list<T1>::Cons>(a0.v());
              return list<T1>::cons(a00, _self_map_head(_self_map_head, *a1));
            }
          }
        };
        auto map_head = [&](const list<list<T1>> &l) -> list<T1> {
          return map_head_impl(map_head_impl, l);
        };
        auto map_tail_impl = [](auto &_self_map_tail,
                                const list<list<T1>> &l) -> list<list<T1>> {
          if (std::holds_alternative<typename list<list<T1>>::Nil>(l.v())) {
            return list<list<T1>>::nil();
          } else {
            const auto &[a00, a10] =
                std::get<typename list<list<T1>>::Cons>(l.v());
            if (std::holds_alternative<typename list<T1>::Nil>(a00.v())) {
              return list<list<T1>>::nil();
            } else {
              const auto &[a01, a11] =
                  std::get<typename list<T1>::Cons>(a00.v());
              return list<list<T1>>::cons(*a11,
                                          _self_map_tail(_self_map_tail, *a10));
            }
          }
        };
        auto map_tail = [&](const list<list<T1>> &l) -> list<list<T1>> {
          return map_tail_impl(map_tail_impl, l);
        };
        if (std::holds_alternative<typename list<list<T1>>::Nil>(_loop_m.v())) {
          *_write = std::make_unique<list<list<T1>>>(list<list<T1>>::nil());
          break;
        } else {
          const auto &[a01, a11] =
              std::get<typename list<list<T1>>::Cons>(_loop_m.v());
          if (std::holds_alternative<typename list<T1>::Nil>(a01.v())) {
            *_write = std::make_unique<list<list<T1>>>(list<list<T1>>::nil());
            break;
          } else {
            list<T1> heads = map_head(_loop_m);
            list<list<T1>> tails0 = map_tail(_loop_m);
            if (std::holds_alternative<typename list<T1>::Nil>(heads.v_mut())) {
              *_write = std::make_unique<list<list<T1>>>(list<list<T1>>::nil());
              break;
            } else {
              auto _cell = std::make_unique<list<list<T1>>>(
                  typename list<list<T1>>::Cons(heads, nullptr));
              *_write = std::move(_cell);
              _write =
                  &std::get<typename list<list<T1>>::Cons>((*_write)->v_mut())
                       .a1;
              _loop_m = std::move(tails0);
              _loop_fuel = f;
              continue;
            }
          }
        }
      }
    }
    return std::move(*_head);
  }

  template <typename T1>
  static list<list<T1>> transpose(const list<list<T1>> &m) {
    return transpose_fuel<T1>(100u, m);
  }

  /// map_accum_l f acc l maps with accumulator from left.
  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<std::pair<T3, T2>, F0 &, T3 &, T1 &>
  static std::pair<T3, list<T2>>
  map_accum_l(F0 &&f, T3 acc,
              const list<T1> &l) { /// _Enter: captures varying parameters for
                                   /// each recursive call.

    struct _Enter {
      const list<T1> *l;
      T3 acc;
    };

    /// _Cont_acc_: saves [y], resumes after recursive call, then processes
    /// rest.
    struct _Cont_acc_ {
      T2 y;
    };

    using _Frame = std::variant<_Enter, _Cont_acc_>;
    std::pair<T3, list<T2>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l, acc});
    /// Loopified map_accum_l: _Enter -> _Cont_acc_.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> &l = *_f.l;
        T3 acc = _f.acc;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = std::make_pair(std::move(acc), list<T2>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          auto _cs = f(acc, a0);
          const T3 &acc_ = _cs.first;
          const T2 &y = _cs.second;
          _stack.emplace_back(_Cont_acc_{y});
          _stack.emplace_back(_Enter{a1.get(), std::move(_cs.first)});
        }
      } else {
        auto _f = std::move(std::get<_Cont_acc_>(_frame));
        T2 y = _f.y;
        const T3 &acc__ = _result.first;
        const list<T2> &ys = _result.second;
        _result =
            std::make_pair(std::move(_result.first), list<T2>::cons(y, ys));
      }
    }
    return _result;
  }

  /// prefix_sums acc l returns all prefix sums: 1,2,3 -> 0,1,3,6.
  static list<unsigned int> prefix_sums(unsigned int acc,
                                        const list<unsigned int> &l);
  /// uniq_sorted l removes consecutive duplicates from sorted list.
  static list<unsigned int> uniq_sorted(const list<unsigned int> &l);
  /// Helper: take first n elements.
  static list<unsigned int> take_n(unsigned int n, const list<unsigned int> &l);
  /// Helper: list length.
  static unsigned int len_list(const list<unsigned int> &l);
  /// windows n l returns all sliding windows of size n.
  static list<list<unsigned int>> windows_aux(unsigned int fuel, unsigned int n,
                                              const list<unsigned int> &l);
  static list<list<unsigned int>> windows(unsigned int n,
                                          const list<unsigned int> &l);
  /// is_prefix_of l1 l2 checks if l1 is a prefix of l2.
  static bool is_prefix_of(const list<unsigned int> &l1,
                           const list<unsigned int> &l2);
  /// lookup_all key l finds all values for key in association list.
  static list<unsigned int>
  lookup_all(unsigned int key,
             const list<std::pair<unsigned int, unsigned int>> &l);

  /// delete_by eq x l deletes first element equal to x by custom equality.
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &, unsigned int &>
  static list<unsigned int> delete_by(F0 &&eq, unsigned int x,
                                      const list<unsigned int> &l) {
    std::unique_ptr<list<unsigned int>> _head{};
    std::unique_ptr<list<unsigned int>> *_write = &_head;
    const list<unsigned int> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename list<unsigned int>::Nil>(
              _loop_l->v())) {
        *_write =
            std::make_unique<list<unsigned int>>(list<unsigned int>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename list<unsigned int>::Cons>(_loop_l->v());
        if (eq(x, a0)) {
          *_write = std::make_unique<list<unsigned int>>(*a1);
          break;
        } else {
          auto _cell = std::make_unique<list<unsigned int>>(
              typename list<unsigned int>::Cons(a0, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut())
                   .a1;
          _loop_l = a1.get();
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  /// find_indices p l returns list of indices where predicate holds.
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &>
  static list<unsigned int>
  find_indices_aux(F0 &&p, const list<unsigned int> &l, unsigned int i) {
    if (std::holds_alternative<typename list<unsigned int>::Nil>(l.v())) {
      return list<unsigned int>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename list<unsigned int>::Cons>(l.v());
      if (p(a0)) {
        return list<unsigned int>::cons(i, find_indices_aux(p, *a1, (i + 1)));
      } else {
        return find_indices_aux(p, *a1, (i + 1));
      }
    }
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &>
  static list<unsigned int> find_indices(F0 &&p, const list<unsigned int> &l) {
    return find_indices_aux(p, l, 0u);
  }

  /// member x l checks if x is in the list.
  static bool member(unsigned int x, const list<unsigned int> &l);
  /// product l multiplies all elements in the list.
  static unsigned int product(const list<unsigned int> &l);
  /// sum_list l sums all elements in the list.
  static unsigned int sum_list(const list<unsigned int> &l);

  /// flatten l flattens a list of lists.
  template <typename T1>
  static list<T1>
  flatten(const list<list<T1>> &l) { /// _Enter: captures varying parameters for
                                     /// each recursive call.

    struct _Enter {
      const list<list<T1>> *l;
    };

    /// _Resume_Cons: saves [app, a0], resumes after recursive call with
    /// _result.
    struct _Resume_Cons {
      std::function<list<T1>(list<T1>, list<T1>)> app;
      list<T1> a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    list<T1> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified flatten: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<list<T1>> &l = *_f.l;
        if (std::holds_alternative<typename list<list<T1>>::Nil>(l.v())) {
          _result = list<T1>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename list<list<T1>>::Cons>(l.v());
          auto app_impl = [](auto &_self_app, const list<T1> &l1,
                             list<T1> l2) -> list<T1> {
            if (std::holds_alternative<typename list<T1>::Nil>(l1.v())) {
              return l2;
            } else {
              const auto &[a00, a10] =
                  std::get<typename list<T1>::Cons>(l1.v());
              return list<T1>::cons(a00,
                                    _self_app(_self_app, *a10, std::move(l2)));
            }
          };
          auto app = [&](const list<T1> &l1, list<T1> l2) -> list<T1> {
            return app_impl(app_impl, l1, l2);
          };
          _stack.emplace_back(_Resume_Cons{std::move(app), a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = _f.app(_f.a0, _result);
      }
    }
    return _result;
  }

  /// flatten_nested l alternative flatten with different pattern: flattens one
  /// level at a time. Pattern:  :: rest -> flatten rest, (x :: xs) :: rest -> x
  /// :: flatten (xs :: rest).
  static list<unsigned int>
  flatten_nested_fuel(unsigned int fuel, const list<list<unsigned int>> &l);
  static unsigned int sum_list_lengths(const list<list<unsigned int>> &l);
  static list<unsigned int> flatten_nested(const list<list<unsigned int>> &l);
  /// compress l removes consecutive duplicates: 1,1,2,2,2,3 -> 1,2,3.
  static list<unsigned int> compress(const list<unsigned int> &l);
  /// group_pairs l groups consecutive elements into pairs: 1,2,3,4 ->
  /// (1,2),(3,4).
  static list<std::pair<unsigned int, unsigned int>>
  group_pairs(const list<unsigned int> &l);
  /// swizzle l separates elements by position: 1,2,3,4 -> (1,3,2,4).
  static std::pair<list<unsigned int>, list<unsigned int>>
  swizzle(const list<unsigned int> &l);
  /// index_of_aux x l i finds first index of x in l starting from i.
  static unsigned int index_of_aux(unsigned int x, const list<unsigned int> &l,
                                   unsigned int i);
  static unsigned int index_of(unsigned int x, const list<unsigned int> &l);
  /// interleave l1 l2 interleaves two lists: 1,2 3,4 -> 1,3,2,4.
  static list<unsigned int> interleave(list<unsigned int> l1,
                                       list<unsigned int> l2);
  /// lookup key l finds value for key in association list.
  static unsigned int
  lookup(unsigned int key,
         const list<std::pair<unsigned int, unsigned int>> &l);
  /// group l groups consecutive equal elements: 1,1,2,2,2,3 ->
  /// [1,1],[2,2,2],[3].
  static list<list<unsigned int>> group_fuel(unsigned int fuel,
                                             const list<unsigned int> &l);
  static list<list<unsigned int>> group(const list<unsigned int> &l);
  /// Internal helper: reverse a list.
  static list<unsigned int> rev_helper(list<unsigned int> acc,
                                       const list<unsigned int> &l);
  /// reverse_insert x l inserts x and reverses at each step.
  static list<unsigned int> reverse_insert(unsigned int x,
                                           const list<unsigned int> &l);
  /// Internal helper: append lists.
  static list<unsigned int> app_helper(const list<unsigned int> &l1,
                                       list<unsigned int> l2);
  /// double_append l1 l2 appends with doubling: 1,2 3 -> 1,3,3,3,3.
  static list<unsigned int> double_append(const list<unsigned int> &l1,
                                          list<unsigned int> l2);
  /// remove_if_sum_even l removes element if sum with next is even.
  static list<unsigned int> remove_if_sum_even(const list<unsigned int> &l);
  /// split_at n l splits list at index n into (prefix, suffix).
  static std::pair<list<unsigned int>, list<unsigned int>>
  split_at(unsigned int n, list<unsigned int> l);

  /// span p l splits list at first element not satisfying p.
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &>
  static std::pair<list<unsigned int>, list<unsigned int>>
  span(F0 &&p,
       list<unsigned int>
           l) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      list<unsigned int> l;
    };

    /// _Cont1: saves [a0], resumes after recursive call, then processes rest.
    struct _Cont1 {
      unsigned int a0;
    };

    using _Frame = std::variant<_Enter, _Cont1>;
    std::pair<list<unsigned int>, list<unsigned int>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{l});
    /// Loopified span: _Enter -> _Cont1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        list<unsigned int> l = std::move(_f.l);
        if (std::holds_alternative<typename list<unsigned int>::Nil>(
                l.v_mut())) {
          _result = std::make_pair(list<unsigned int>::nil(),
                                   list<unsigned int>::nil());
        } else {
          auto &[a0, a1] =
              std::get<typename list<unsigned int>::Cons>(l.v_mut());
          if (p(a0)) {
            _stack.emplace_back(_Cont1{a0});
            _stack.emplace_back(_Enter{std::move(*a1)});
          } else {
            _result = std::make_pair(list<unsigned int>::nil(), l);
          }
        }
      } else {
        auto _f = std::move(std::get<_Cont1>(_frame));
        unsigned int a0 = _f.a0;
        const list<unsigned int> &a = _result.first;
        const list<unsigned int> &b = _result.second;
        _result = std::make_pair(list<unsigned int>::cons(std::move(a0), a), b);
      }
    }
    return _result;
  }

  /// unzip l splits list of pairs into two lists.
  static std::pair<list<unsigned int>, list<unsigned int>>
  unzip(const list<std::pair<unsigned int, unsigned int>> &l);
  /// nth n l default returns nth element or default if out of bounds.
  static unsigned int nth(unsigned int n, const list<unsigned int> &l,
                          unsigned int default0);
  /// last l default returns last element or default if empty.
  static unsigned int last(const list<unsigned int> &l, unsigned int default0);
  /// drop n l drops first n elements.
  static list<unsigned int> drop(unsigned int n, list<unsigned int> l);
  /// init l returns all but last element.
  static list<unsigned int> init(const list<unsigned int> &l);
  /// count x l counts occurrences of x in l.
  static unsigned int count(unsigned int x, const list<unsigned int> &l);
  /// maximum l finds maximum element (returns 0 for empty list).
  static unsigned int maximum(const list<unsigned int> &l);
  /// minmax l finds both minimum and maximum in one pass.
  static std::pair<unsigned int, unsigned int>
  minmax(const list<unsigned int> &l);
  /// Helper for rotate_left.
  static list<unsigned int> rotate_left_fuel(unsigned int fuel, unsigned int n,
                                             list<unsigned int> l);
  /// rotate_left n l rotates list left by n positions: rotate 2 1,2,3,4 ->
  /// 3,4,1,2.
  static list<unsigned int> rotate_left(unsigned int n,
                                        const list<unsigned int> &l);
  /// intercalate sep lists joins lists with separator: intercalate 0
  /// [1,2],[3,4] -> 1,2,0,3,4.
  static list<unsigned int> intercalate(const list<unsigned int> &sep,
                                        const list<list<unsigned int>> &lists);
  /// majority l finds majority element using Boyer-Moore voting algorithm.
  /// Returns (candidate, count).
  static std::pair<unsigned int, unsigned int>
  majority(const list<unsigned int> &l);
  /// zip3 l1 l2 l3 zips three lists into triples.
  static list<std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>
  zip3(const list<unsigned int> &l1, const list<unsigned int> &l2,
       const list<unsigned int> &l3);
  /// sum_and_count l returns both sum and count in one pass.
  static std::pair<unsigned int, unsigned int>
  sum_and_count(const list<unsigned int> &l);
  /// elem_at n l returns element at index n (like nth but with different name).
  static std::optional<unsigned int> elem_at(unsigned int n,
                                             const list<unsigned int> &l);
};

#endif // INCLUDED_LOOPIFY_LISTS
