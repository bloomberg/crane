#ifndef INCLUDED_LOOPIFY_POLYMORPHIC
#define INCLUDED_LOOPIFY_POLYMORPHIC

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
  List clone() const {
    List _out{};

    struct _CloneFrame {
      const List *_src;
      List *_dst;
    };

    std::vector<_CloneFrame> _stack;
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List *_src = _frame._src;
      List *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        const auto &_alt = std::get<Nil>(_src->v());
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ =
            Cons{_alt.d_a0, _alt.d_a1 ? std::make_unique<List>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1)
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
      }
    }
    return _out;
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

  static List<t_A> nil() { return List(Nil{}); }

  static List<t_A> cons(t_A a0, List<t_A> a1) {
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
  const variant_t &v() const { return d_v_; }

  List<t_A> app(List<t_A> m) const {
    std::unique_ptr<List<t_A>> _head{};
    std::unique_ptr<List<t_A>> *_write = &_head;
    const List *_loop_self = this;
    List<t_A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *(_loop_self);
      if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
        *(_write) = std::make_unique<List<t_A>>(std::move(_loop_m));
        break;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
        auto _cell = std::make_unique<List<t_A>>(
            typename List<t_A>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename List<t_A>::Cons>((*_write)->v_mut()).d_a1;
        const List *_next_self = d_a1.get();
        List<t_A> _next_m = std::move(_loop_m);
        _loop_self = _next_self;
        _loop_m = std::move(_next_m);
        continue;
      }
    }
    return std::move(*(_head));
  }
};

struct LoopifyPolymorphic {
  template <typename T1> static unsigned int poly_length(const List<T1> &l) {
    struct _Enter {
      const List<T1> *l;
    };

    struct _Call1 {
      decltype(1u) _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{&l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<T1> &l = *(_f.l);
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          _result = 0u;
        } else {
          const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
          _stack.emplace_back(_Call1{1u});
          _stack.emplace_back(_Enter{d_a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = (_f._s0 + _result);
      }
    }
    return _result;
  }

  template <typename T1> static List<T1> poly_reverse(const List<T1> &l) {
    struct _Enter {
      const List<T1> *l;
    };

    struct _Call1 {
      decltype(List<T1>::cons(std::declval<T1 &>(), List<T1>::nil())) _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    List<T1> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{&l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<T1> &l = *(_f.l);
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          _result = List<T1>::nil();
        } else {
          const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
          _stack.emplace_back(_Call1{List<T1>::cons(d_a0, List<T1>::nil())});
          _stack.emplace_back(_Enter{d_a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
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
        *(_write) = std::make_unique<List<T1>>(std::move(_loop_l2));
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<T1>::Cons>(_loop_l1->v());
        auto _cell =
            std::make_unique<List<T1>>(typename List<T1>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename List<T1>::Cons>((*_write)->v_mut()).d_a1;
        List<T1> _next_l2 = std::move(_loop_l2);
        const List<T1> *_next_l1 = d_a1.get();
        _loop_l2 = std::move(_next_l2);
        _loop_l1 = _next_l1;
        continue;
      }
    }
    return std::move(*(_head));
  }

  template <typename T1> static std::optional<T1> poly_last(const List<T1> &l) {
    std::optional<T1> _result;
    const List<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
        _result = std::optional<T1>();
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<T1>::Cons>(_loop_l->v());
        auto &&_sv = *(d_a1);
        if (std::holds_alternative<typename List<T1>::Nil>(_sv.v())) {
          _result = std::make_optional<T1>(d_a0);
          break;
        } else {
          _loop_l = d_a1.get();
        }
      }
    }
    return _result;
  }

  template <typename T1>
  static List<T1> poly_take(const unsigned int &n, const List<T1> &l) {
    std::unique_ptr<List<T1>> _head{};
    std::unique_ptr<List<T1>> *_write = &_head;
    const List<T1> *_loop_l = &l;
    unsigned int _loop_n = n;
    while (true) {
      if (_loop_n <= 0) {
        *(_write) = std::make_unique<List<T1>>(List<T1>::nil());
        break;
      } else {
        unsigned int n_ = _loop_n - 1;
        if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
          *(_write) = std::make_unique<List<T1>>(List<T1>::nil());
          break;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<T1>::Cons>(_loop_l->v());
          auto _cell = std::make_unique<List<T1>>(
              typename List<T1>::Cons(d_a0, nullptr));
          *(_write) = std::move(_cell);
          _write = &std::get<typename List<T1>::Cons>((*_write)->v_mut()).d_a1;
          const List<T1> *_next_l = d_a1.get();
          unsigned int _next_n = n_;
          _loop_l = _next_l;
          _loop_n = std::move(_next_n);
          continue;
        }
      }
    }
    return std::move(*(_head));
  }

  template <typename T1>
  static List<T1> poly_drop(const unsigned int &n, List<T1> l) {
    List<T1> _result;
    List<T1> _loop_l = std::move(l);
    unsigned int _loop_n = n;
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
          auto &[d_a0, d_a1] =
              std::get<typename List<T1>::Cons>(_loop_l.v_mut());
          List<T1> _next_l = std::move(*(d_a1));
          unsigned int _next_n = n_;
          _loop_l = std::move(_next_l);
          _loop_n = std::move(_next_n);
        }
      }
    }
    return _result;
  }

  template <typename T1>
  static std::optional<T1> poly_nth(const unsigned int &n, const List<T1> &l) {
    std::optional<T1> _result;
    const List<T1> *_loop_l = &l;
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
          const List<T1> *_next_l = d_a1.get();
          unsigned int _next_n =
              (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
          _loop_l = _next_l;
          _loop_n = std::move(_next_n);
        }
      }
    }
    return _result;
  }

  template <typename T1, MapsTo<bool, T1> F0>
  static List<T1> poly_filter(F0 &&p, const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return List<T1>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
      if (p(d_a0)) {
        return List<T1>::cons(d_a0, poly_filter<T1>(p, *(d_a1)));
      } else {
        return poly_filter<T1>(p, *(d_a1));
      }
    }
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static List<T2> poly_map(F0 &&f, const List<T1> &l) {
    std::unique_ptr<List<T2>> _head{};
    std::unique_ptr<List<T2>> *_write = &_head;
    const List<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
        *(_write) = std::make_unique<List<T2>>(List<T2>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<T1>::Cons>(_loop_l->v());
        auto _cell = std::make_unique<List<T2>>(
            typename List<T2>::Cons(f(d_a0), nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename List<T2>::Cons>((*_write)->v_mut()).d_a1;
        _loop_l = d_a1.get();
        continue;
      }
    }
    return std::move(*(_head));
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
        *(_write) = std::make_unique<List<std::pair<T1, T2>>>(
            List<std::pair<T1, T2>>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<T1>::Cons>(_loop_l1->v());
        if (std::holds_alternative<typename List<T2>::Nil>(_loop_l2->v())) {
          *(_write) = std::make_unique<List<std::pair<T1, T2>>>(
              List<std::pair<T1, T2>>::nil());
          break;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<T2>::Cons>(_loop_l2->v());
          auto _cell = std::make_unique<List<std::pair<T1, T2>>>(
              typename List<std::pair<T1, T2>>::Cons(
                  std::make_pair(d_a0, d_a00), nullptr));
          *(_write) = std::move(_cell);
          _write = &std::get<typename List<std::pair<T1, T2>>::Cons>(
                        (*_write)->v_mut())
                        .d_a1;
          const List<T2> *_next_l2 = d_a10.get();
          const List<T1> *_next_l1 = d_a1.get();
          _loop_l2 = _next_l2;
          _loop_l1 = _next_l1;
          continue;
        }
      }
    }
    return std::move(*(_head));
  }

  template <typename T1, typename T2>
  static std::pair<List<T1>, List<T2>>
  poly_unzip(const List<std::pair<T1, T2>> &l) {
    struct _Enter {
      const List<std::pair<T1, T2>> *l;
    };

    struct _Call1 {
      T1 _s0;
      T2 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<List<T1>, List<T2>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{&l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<std::pair<T1, T2>> &l = *(_f.l);
        if (std::holds_alternative<typename List<std::pair<T1, T2>>::Nil>(
                l.v())) {
          _result = std::make_pair(List<T1>::nil(), List<T2>::nil());
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<std::pair<T1, T2>>::Cons>(l.v());
          const T1 &a = d_a0.first;
          const T2 &b = d_a0.second;
          _stack.emplace_back(_Call1{a, b});
          _stack.emplace_back(_Enter{d_a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        T1 a = _f._s0;
        T2 b = _f._s1;
        const List<T1> &as_ = _result.first;
        const List<T2> &bs = _result.second;
        _result = std::make_pair(List<T1>::cons(a, as_), List<T2>::cons(b, bs));
      }
    }
    return _result;
  }

  template <typename T1, MapsTo<bool, T1> F0>
  static std::pair<List<T1>, List<T1>> poly_partition(F0 &&p,
                                                      const List<T1> &l) {
    struct _Enter {
      const List<T1> *l;
    };

    struct _Call1 {
      T1 _s0;
      F0 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<List<T1>, List<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{&l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<T1> &l = *(_f.l);
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          _result = std::make_pair(List<T1>::nil(), List<T1>::nil());
        } else {
          const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
          _stack.emplace_back(_Call1{d_a0, p});
          _stack.emplace_back(_Enter{d_a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        T1 d_a0 = _f._s0;
        F0 p = _f._s1;
        const List<T1> &trues = _result.first;
        const List<T1> &falses = _result.second;
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
  static bool poly_member(F0 &&eq, const T1 x, const List<T1> &l) {
    bool _result;
    const List<T1> *_loop_l = &l;
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
          _loop_l = d_a1.get();
        }
      }
    }
    return _result;
  }

  template <typename T1>
  static List<T1> poly_replicate(const unsigned int &n, const T1 x) {
    std::unique_ptr<List<T1>> _head{};
    std::unique_ptr<List<T1>> *_write = &_head;
    unsigned int _loop_n = n;
    while (true) {
      if (_loop_n <= 0) {
        *(_write) = std::make_unique<List<T1>>(List<T1>::nil());
        break;
      } else {
        unsigned int n_ = _loop_n - 1;
        auto _cell =
            std::make_unique<List<T1>>(typename List<T1>::Cons(x, nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename List<T1>::Cons>((*_write)->v_mut()).d_a1;
        _loop_n = n_;
        continue;
      }
    }
    return std::move(*(_head));
  }

  static unsigned int nat_length(const List<unsigned int> &_x0);
  static List<unsigned int> nat_reverse(const List<unsigned int> &_x0);
  static List<unsigned int> nat_append(const List<unsigned int> &_x0,
                                       const List<unsigned int> &_x1);
  static std::optional<unsigned int> nat_last(const List<unsigned int> &_x0);
  static List<unsigned int> nat_take(const unsigned int &_x0,
                                     const List<unsigned int> &_x1);
  static List<unsigned int> nat_drop(const unsigned int &_x0,
                                     const List<unsigned int> &_x1);
  static std::optional<unsigned int> nat_nth(const unsigned int &_x0,
                                             const List<unsigned int> &_x1);
  static bool nat_eq(const unsigned int &_x0, const unsigned int &_x1);
  static bool is_even(const unsigned int &x);

  template <MapsTo<bool, unsigned int> F0>
  static List<unsigned int> nat_filter(F0 &&_x0,
                                       const List<unsigned int> &_x1) {
    return poly_filter<unsigned int>(_x0, _x1);
  }

  template <MapsTo<unsigned int, unsigned int> F0>
  static List<unsigned int> nat_map(F0 &&_x0, const List<unsigned int> &_x1) {
    return poly_map<unsigned int, unsigned int>(_x0, _x1);
  }

  template <MapsTo<bool, unsigned int> F0>
  static std::pair<List<unsigned int>, List<unsigned int>>
  nat_partition(F0 &&_x0, const List<unsigned int> &_x1) {
    return poly_partition<unsigned int>(_x0, _x1);
  }

  static bool nat_member(const unsigned int &_x0,
                         const List<unsigned int> &_x1);
  static List<unsigned int> nat_replicate(const unsigned int &_x0,
                                          const unsigned int &_x1);
};

#endif // INCLUDED_LOOPIFY_POLYMORPHIC
