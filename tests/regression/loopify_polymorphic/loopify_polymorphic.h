#ifndef INCLUDED_LOOPIFY_POLYMORPHIC
#define INCLUDED_LOOPIFY_POLYMORPHIC

#include <memory>
#include <optional>
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

  List(List<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) noexcept {
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

  List<A> app(List<A> m) const {
    std::unique_ptr<List<A>> _head{};
    std::unique_ptr<List<A>> *_write = &_head;
    const List *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = std::make_unique<List<A>>(std::move(_loop_m));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell =
            std::make_unique<List<A>>(typename List<A>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<A>::Cons>((*_write)->v_mut()).a1;
        _loop_self = a1.get();
        continue;
      }
    }
    return std::move(*_head);
  }
};

struct LoopifyPolymorphic {
  template <typename T1>
  static unsigned int
  poly_length(const List<T1> &l) { /// _Enter: captures varying parameters for
                                   /// each recursive call.

    struct _Enter {
      const List<T1> *l;
    };

    /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
    struct _Resume_Cons {
      decltype(1u) _s0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified poly_length: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<T1> &l = *_f.l;
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          _result = 0u;
        } else {
          const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{1u});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = (_f._s0 + _result);
      }
    }
    return _result;
  }

  template <typename T1>
  static List<T1>
  poly_reverse(const List<T1> &l) { /// _Enter: captures varying parameters for
                                    /// each recursive call.

    struct _Enter {
      const List<T1> *l;
    };

    /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
    struct _Resume_Cons {
      decltype(List<T1>::cons(std::declval<T1 &>(), List<T1>::nil())) _s0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    List<T1> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified poly_reverse: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<T1> &l = *_f.l;
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          _result = List<T1>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
          _stack.emplace_back(
              _Resume_Cons{List<T1>::cons(a0, List<T1>::nil())});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = _result.app(_f._s0);
      }
    }
    return _result;
  }

  template <typename T1>
  static List<T1> poly_append(const List<T1> &l1, List<T1> l2) {
    std::unique_ptr<List<T1>> _head{};
    std::unique_ptr<List<T1>> *_write = &_head;
    List<T1> _loop_l2 = std::move(l2);
    const List<T1> *_loop_l1 = &l1;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l1->v())) {
        *_write = std::make_unique<List<T1>>(std::move(_loop_l2));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(_loop_l1->v());
        auto _cell =
            std::make_unique<List<T1>>(typename List<T1>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<T1>::Cons>((*_write)->v_mut()).a1;
        _loop_l1 = a1.get();
        continue;
      }
    }
    return std::move(*_head);
  }

  template <typename T1> static std::optional<T1> poly_last(const List<T1> &l) {
    std::optional<T1> _result;
    const List<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
        _result = std::optional<T1>();
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(_loop_l->v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename List<T1>::Nil>(_sv.v())) {
          _result = std::make_optional<T1>(a0);
          break;
        } else {
          _loop_l = a1.get();
        }
      }
    }
    return _result;
  }

  template <typename T1>
  static List<T1> poly_take(unsigned int n, const List<T1> &l) {
    std::unique_ptr<List<T1>> _head{};
    std::unique_ptr<List<T1>> *_write = &_head;
    const List<T1> *_loop_l = &l;
    unsigned int _loop_n = std::move(n);
    while (true) {
      if (_loop_n <= 0) {
        *_write = std::make_unique<List<T1>>(List<T1>::nil());
        break;
      } else {
        unsigned int n_ = _loop_n - 1;
        if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
          *_write = std::make_unique<List<T1>>(List<T1>::nil());
          break;
        } else {
          const auto &[a0, a1] =
              std::get<typename List<T1>::Cons>(_loop_l->v());
          auto _cell =
              std::make_unique<List<T1>>(typename List<T1>::Cons(a0, nullptr));
          *_write = std::move(_cell);
          _write = &std::get<typename List<T1>::Cons>((*_write)->v_mut()).a1;
          _loop_l = a1.get();
          _loop_n = n_;
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  template <typename T1> static List<T1> poly_drop(unsigned int n, List<T1> l) {
    List<T1> _result;
    List<T1> _loop_l = std::move(l);
    unsigned int _loop_n = std::move(n);
    while (true) {
      if (_loop_n <= 0) {
        _result = std::move(_loop_l);
        break;
      } else {
        unsigned int n_ = _loop_n - 1;
        if (std::holds_alternative<typename List<T1>::Nil>(_loop_l.v_mut())) {
          _result = List<T1>::nil();
          break;
        } else {
          auto &[a0, a1] = std::get<typename List<T1>::Cons>(_loop_l.v_mut());
          _loop_l = std::move(*a1);
          _loop_n = n_;
        }
      }
    }
    return _result;
  }

  template <typename T1>
  static std::optional<T1> poly_nth(unsigned int n, const List<T1> &l) {
    std::optional<T1> _result;
    const List<T1> *_loop_l = &l;
    unsigned int _loop_n = std::move(n);
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
        _result = std::optional<T1>();
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(_loop_l->v());
        if (_loop_n == 0u) {
          _result = std::make_optional<T1>(a0);
          break;
        } else {
          _loop_l = a1.get();
          _loop_n = (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
        }
      }
    }
    return _result;
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &>
  static List<T1> poly_filter(F0 &&p, const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return List<T1>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      if (p(a0)) {
        return List<T1>::cons(a0, poly_filter<T1>(p, *a1));
      } else {
        return poly_filter<T1>(p, *a1);
      }
    }
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static List<T2> poly_map(F0 &&f, const List<T1> &l) {
    std::unique_ptr<List<T2>> _head{};
    std::unique_ptr<List<T2>> *_write = &_head;
    const List<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
        *_write = std::make_unique<List<T2>>(List<T2>::nil());
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(_loop_l->v());
        auto _cell =
            std::make_unique<List<T2>>(typename List<T2>::Cons(f(a0), nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<T2>::Cons>((*_write)->v_mut()).a1;
        _loop_l = a1.get();
        continue;
      }
    }
    return std::move(*_head);
  }

  template <typename T1, typename T2>
  static List<std::pair<T1, T2>> poly_zip(const List<T1> &l1,
                                          const List<T2> &l2) {
    std::unique_ptr<List<std::pair<T1, T2>>> _head{};
    std::unique_ptr<List<std::pair<T1, T2>>> *_write = &_head;
    const List<T2> *_loop_l2 = &l2;
    const List<T1> *_loop_l1 = &l1;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l1->v())) {
        *_write = std::make_unique<List<std::pair<T1, T2>>>(
            List<std::pair<T1, T2>>::nil());
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(_loop_l1->v());
        if (std::holds_alternative<typename List<T2>::Nil>(_loop_l2->v())) {
          *_write = std::make_unique<List<std::pair<T1, T2>>>(
              List<std::pair<T1, T2>>::nil());
          break;
        } else {
          const auto &[a00, a10] =
              std::get<typename List<T2>::Cons>(_loop_l2->v());
          auto _cell = std::make_unique<List<std::pair<T1, T2>>>(
              typename List<std::pair<T1, T2>>::Cons(std::make_pair(a0, a00),
                                                     nullptr));
          *_write = std::move(_cell);
          _write = &std::get<typename List<std::pair<T1, T2>>::Cons>(
                        (*_write)->v_mut())
                        .a1;
          _loop_l2 = a10.get();
          _loop_l1 = a1.get();
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  template <typename T1, typename T2>
  static std::pair<List<T1>, List<T2>> poly_unzip(
      const List<std::pair<T1, T2>>
          &l) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      const List<std::pair<T1, T2>> *l;
    };

    /// _Cont_a: saves [a, b], resumes after recursive call, then processes
    /// rest.
    struct _Cont_a {
      T1 a;
      T2 b;
    };

    using _Frame = std::variant<_Enter, _Cont_a>;
    std::pair<List<T1>, List<T2>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified poly_unzip: _Enter -> _Cont_a.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<std::pair<T1, T2>> &l = *_f.l;
        if (std::holds_alternative<typename List<std::pair<T1, T2>>::Nil>(
                l.v())) {
          _result = std::make_pair(List<T1>::nil(), List<T2>::nil());
        } else {
          const auto &[a0, a1] =
              std::get<typename List<std::pair<T1, T2>>::Cons>(l.v());
          const T1 &a = a0.first;
          const T2 &b = a0.second;
          _stack.emplace_back(_Cont_a{a, b});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Cont_a>(_frame));
        T1 a = _f.a;
        T2 b = _f.b;
        const List<T1> &as_ = _result.first;
        const List<T2> &bs = _result.second;
        _result = std::make_pair(List<T1>::cons(a, as_), List<T2>::cons(b, bs));
      }
    }
    return _result;
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &>
  static std::pair<List<T1>, List<T1>>
  poly_partition(F0 &&p,
                 const List<T1> &l) { /// _Enter: captures varying parameters
                                      /// for each recursive call.

    struct _Enter {
      const List<T1> *l;
    };

    /// _Cont_Cons: saves [a0, p], resumes after recursive call, then processes
    /// rest.
    struct _Cont_Cons {
      T1 a0;
      F0 p;
    };

    using _Frame = std::variant<_Enter, _Cont_Cons>;
    std::pair<List<T1>, List<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified poly_partition: _Enter -> _Cont_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<T1> &l = *_f.l;
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          _result = std::make_pair(List<T1>::nil(), List<T1>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
          _stack.emplace_back(_Cont_Cons{a0, p});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Cont_Cons>(_frame));
        T1 a0 = _f.a0;
        F0 p = _f.p;
        const List<T1> &trues = _result.first;
        const List<T1> &falses = _result.second;
        if (p(a0)) {
          _result = std::make_pair(List<T1>::cons(a0, trues), falses);
        } else {
          _result = std::make_pair(trues, List<T1>::cons(a0, falses));
        }
      }
    }
    return _result;
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static bool poly_member(F0 &&eq, const T1 &x, const List<T1> &l) {
    bool _result;
    const List<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
        _result = false;
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(_loop_l->v());
        if (eq(x, a0)) {
          _result = true;
          break;
        } else {
          _loop_l = a1.get();
        }
      }
    }
    return _result;
  }

  template <typename T1> static List<T1> poly_replicate(unsigned int n, T1 x) {
    std::unique_ptr<List<T1>> _head{};
    std::unique_ptr<List<T1>> *_write = &_head;
    unsigned int _loop_n = std::move(n);
    while (true) {
      if (_loop_n <= 0) {
        *_write = std::make_unique<List<T1>>(List<T1>::nil());
        break;
      } else {
        unsigned int n_ = _loop_n - 1;
        auto _cell =
            std::make_unique<List<T1>>(typename List<T1>::Cons(x, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<T1>::Cons>((*_write)->v_mut()).a1;
        _loop_n = n_;
        continue;
      }
    }
    return std::move(*_head);
  }

  static unsigned int nat_length(const List<unsigned int> &_x0);
  static List<unsigned int> nat_reverse(const List<unsigned int> &_x0);
  static List<unsigned int> nat_append(const List<unsigned int> &_x0,
                                       const List<unsigned int> &_x1);
  static std::optional<unsigned int> nat_last(const List<unsigned int> &_x0);
  static List<unsigned int> nat_take(unsigned int _x0,
                                     const List<unsigned int> &_x1);
  static List<unsigned int> nat_drop(unsigned int _x0,
                                     const List<unsigned int> &_x1);
  static std::optional<unsigned int> nat_nth(unsigned int _x0,
                                             const List<unsigned int> &_x1);
  static bool nat_eq(unsigned int _x0, unsigned int _x1);
  static bool is_even(unsigned int x);

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &>
  static List<unsigned int> nat_filter(F0 &&_x0,
                                       const List<unsigned int> &_x1) {
    return poly_filter<unsigned int>(_x0, _x1);
  }

  template <typename F0>
    requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &>
  static List<unsigned int> nat_map(F0 &&_x0, const List<unsigned int> &_x1) {
    return poly_map<unsigned int, unsigned int>(_x0, _x1);
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &>
  static std::pair<List<unsigned int>, List<unsigned int>>
  nat_partition(F0 &&_x0, const List<unsigned int> &_x1) {
    return poly_partition<unsigned int>(_x0, _x1);
  }

  static bool nat_member(unsigned int _x0, const List<unsigned int> &_x1);
  static List<unsigned int> nat_replicate(unsigned int _x0, unsigned int _x1);
};

#endif // INCLUDED_LOOPIFY_POLYMORPHIC
