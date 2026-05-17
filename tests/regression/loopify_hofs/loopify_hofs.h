#ifndef INCLUDED_LOOPIFY_HOFS
#define INCLUDED_LOOPIFY_HOFS

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

  unsigned int length() const {
    const List *_self = this;

    /// _Enter: captures varying parameters for each recursive call.
    struct _Enter {
      const List *_self;
    };

    /// _Resume_Cons: resumes after recursive call with _result.
    struct _Resume_Cons {};

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{_self});
    /// Loopified length: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = 0u;
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_Resume_Cons{});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = (_result + 1);
      }
    }
    return _result;
  }

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

struct LoopifyHofs {
  /// foldl1 f l folds from left with no initial value. Returns 0 for empty
  /// list.
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &, T1 &>
  static T1 foldl1_aux(F0 &&f, T1 acc, const List<T1> &l) {
    T1 _result;
    const List<T1> *_loop_l = &l;
    T1 _loop_acc = std::move(acc);
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
        _result = _loop_acc;
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(_loop_l->v());
        _loop_l = a1.get();
        _loop_acc = f(_loop_acc, a0);
      }
    }
    return _result;
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &, T1 &>
  static T1 foldl1(F0 &&f, T1 default0, const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      return foldl1_aux<T1>(f, a0, *a1);
    }
  }

  /// forall_ p l checks if all elements satisfy predicate p.
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &>
  static bool forall_(F0 &&p, const List<T1> &l) {
    bool _result;
    const List<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
        _result = true;
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(_loop_l->v());
        if (p(a0)) {
          _loop_l = a1.get();
        } else {
          _result = false;
          break;
        }
      }
    }
    return _result;
  }

  /// exists_fn p l checks if any element satisfies predicate p.
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &>
  static bool exists_fn(F0 &&p, const List<T1> &l) {
    bool _result;
    const List<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
        _result = false;
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(_loop_l->v());
        if (p(a0)) {
          _result = true;
          break;
        } else {
          _loop_l = a1.get();
        }
      }
    }
    return _result;
  }

  /// drop_while p l drops elements while predicate holds.
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &>
  static List<T1> drop_while(F0 &&p, const List<T1> &l) {
    List<T1> _result;
    const List<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
        _result = List<T1>::nil();
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(_loop_l->v());
        if (p(a0)) {
          _loop_l = a1.get();
        } else {
          _result = List<T1>::cons(a0, *a1);
          break;
        }
      }
    }
    return _result;
  }

  /// take_while p l takes elements while predicate holds.
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &>
  static List<T1> take_while(F0 &&p, const List<T1> &l) {
    std::unique_ptr<List<T1>> _head{};
    std::unique_ptr<List<T1>> *_write = &_head;
    const List<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
        *_write = std::make_unique<List<T1>>(List<T1>::nil());
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(_loop_l->v());
        if (p(a0)) {
          auto _cell =
              std::make_unique<List<T1>>(typename List<T1>::Cons(a0, nullptr));
          *_write = std::move(_cell);
          _write = &std::get<typename List<T1>::Cons>((*_write)->v_mut()).a1;
          _loop_l = a1.get();
          continue;
        } else {
          *_write = std::make_unique<List<T1>>(List<T1>::nil());
          break;
        }
      }
    }
    return std::move(*_head);
  }

  /// flat_map f l maps f and flattens results.
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<List<T2>, F0 &, T1 &>
  static List<T2>
  flat_map(F0 &&f,
           const List<T1> &l) { /// _Enter: captures varying parameters for each
                                /// recursive call.

    struct _Enter {
      const List<T1> *l;
    };

    /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
    struct _Resume_Cons {
      List<T2> a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    List<T2> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified flat_map: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<T1> &l = *_f.l;
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          _result = List<T2>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{f(a0)});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = _f.a0.app(_result);
      }
    }
    return _result;
  }

  /// all_pairs l1 l2 returns all pairs from two lists.
  template <typename T1, typename T2>
  static List<std::pair<T1, T2>>
  all_pairs(const List<T1> &l1,
            const List<T2> &l2) { /// _Enter: captures varying parameters for
                                  /// each recursive call.

    struct _Enter {
      const List<T1> *l1;
    };

    /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
    struct _Resume_Cons {
      List<std::pair<T1, T2>> _s0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    List<std::pair<T1, T2>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l1});
    /// Loopified all_pairs: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<T1> &l1 = *_f.l1;
        auto pair_with_impl = [](auto &_self_pair_with, T1 x,
                                 const List<T2> &l) -> List<std::pair<T1, T2>> {
          if (std::holds_alternative<typename List<T2>::Nil>(l.v())) {
            return List<std::pair<T1, T2>>::nil();
          } else {
            const auto &[a0, a1] = std::get<typename List<T2>::Cons>(l.v());
            return List<std::pair<T1, T2>>::cons(
                std::make_pair(x, a0),
                _self_pair_with(_self_pair_with, x, *a1));
          }
        };
        auto pair_with = [&](T1 x,
                             const List<T2> &l) -> List<std::pair<T1, T2>> {
          return pair_with_impl(pair_with_impl, x, l);
        };
        if (std::holds_alternative<typename List<T1>::Nil>(l1.v())) {
          _result = List<std::pair<T1, T2>>::nil();
        } else {
          const auto &[a00, a10] = std::get<typename List<T1>::Cons>(l1.v());
          _stack.emplace_back(_Resume_Cons{pair_with(a00, l2)});
          _stack.emplace_back(_Enter{a10.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = _f._s0.app(_result);
      }
    }
    return _result;
  }

  /// find_indices p l finds all indices where p is true.
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &>
  static List<unsigned int>
  find_indices_aux(F0 &&p, const List<unsigned int> &l, unsigned int i) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
      return List<unsigned int>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<unsigned int>::Cons>(l.v());
      if (p(a0)) {
        return List<unsigned int>::cons(i, find_indices_aux(p, *a1, (i + 1)));
      } else {
        return find_indices_aux(p, *a1, (i + 1));
      }
    }
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &>
  static List<unsigned int> find_indices(F0 &&p, const List<unsigned int> &l) {
    return find_indices_aux(p, l, 0u);
  }

  /// delete_by eq x l deletes first element equal to x.
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &, unsigned int &>
  static List<unsigned int> delete_by(F0 &&eq, unsigned int x,
                                      const List<unsigned int> &l) {
    std::unique_ptr<List<unsigned int>> _head{};
    std::unique_ptr<List<unsigned int>> *_write = &_head;
    const List<unsigned int> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        *_write =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l->v());
        if (eq(x, a0)) {
          *_write = std::make_unique<List<unsigned int>>(*a1);
          break;
        } else {
          auto _cell = std::make_unique<List<unsigned int>>(
              typename List<unsigned int>::Cons(a0, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                   .a1;
          _loop_l = a1.get();
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  /// is_prefix_of l1 l2 checks if l1 is a prefix of l2.
  static bool is_prefix_of(const List<unsigned int> &l1,
                           const List<unsigned int> &l2);
  /// lookup_all key l finds all values associated with key in association list.
  static List<unsigned int>
  lookup_all(unsigned int key,
             const List<std::pair<unsigned int, unsigned int>> &l);

  /// scanl f acc l scan from left with accumulator.
  template <typename F0>
    requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &,
                                   unsigned int &>
  static List<unsigned int> scanl(F0 &&f, unsigned int acc,
                                  const List<unsigned int> &l) {
    std::unique_ptr<List<unsigned int>> _head{};
    std::unique_ptr<List<unsigned int>> *_write = &_head;
    const List<unsigned int> *_loop_l = &l;
    unsigned int _loop_acc = std::move(acc);
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        *_write = std::make_unique<List<unsigned int>>(
            List<unsigned int>::cons(_loop_acc, List<unsigned int>::nil()));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l->v());
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(_loop_acc, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).a1;
        _loop_l = a1.get();
        _loop_acc = f(_loop_acc, a0);
        continue;
      }
    }
    return std::move(*_head);
  }

  /// scanl1 f l like scanl but no initial value, uses first element.
  template <typename F1>
    requires std::is_invocable_r_v<unsigned int, F1 &, unsigned int &,
                                   unsigned int &>
  static List<unsigned int> scanl1_fuel(unsigned int fuel, F1 &&f,
                                        List<unsigned int> l) {
    std::unique_ptr<List<unsigned int>> _head{};
    std::unique_ptr<List<unsigned int>> *_write = &_head;
    List<unsigned int> _loop_l = std::move(l);
    unsigned int _loop_fuel = std::move(fuel);
    while (true) {
      if (_loop_fuel <= 0) {
        *_write = std::make_unique<List<unsigned int>>(std::move(_loop_l));
        break;
      } else {
        unsigned int g = _loop_fuel - 1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _loop_l.v_mut())) {
          *_write =
              std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
          break;
        } else {
          auto &[a0, a1] =
              std::get<typename List<unsigned int>::Cons>(_loop_l.v_mut());
          auto &&_sv0 = *a1;
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  _sv0.v())) {
            *_write =
                std::make_unique<List<unsigned int>>(List<unsigned int>::cons(
                    std::move(a0), List<unsigned int>::nil()));
            break;
          } else {
            const auto &[a00, a10] =
                std::get<typename List<unsigned int>::Cons>(_sv0.v());
            auto _cell = std::make_unique<List<unsigned int>>(
                typename List<unsigned int>::Cons(a0, nullptr));
            *_write = std::move(_cell);
            _write =
                &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                     .a1;
            _loop_l = List<unsigned int>::cons(f(a0, a00), *a10);
            _loop_fuel = g;
            continue;
          }
        }
      }
    }
    return std::move(*_head);
  }

  template <typename F0>
    requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &,
                                   unsigned int &>
  static List<unsigned int> scanl1(F0 &&f, const List<unsigned int> &l) {
    return scanl1_fuel(l.length(), f, l);
  }

  /// foldr1 f l fold right with no initial value.
  template <typename F0>
    requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &,
                                   unsigned int &>
  static unsigned int
  foldr1(F0 &&f,
         const List<unsigned int> &l) { /// _Enter: captures varying parameters
                                        /// for each recursive call.

    struct _Enter {
      const List<unsigned int> *l;
    };

    /// _Resume_Cons: saves [f, a0], resumes after recursive call with _result.
    struct _Resume_Cons {
      F0 f;
      unsigned int a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified foldr1: _Enter -> _Resume_Cons.
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
            _stack.emplace_back(_Resume_Cons{f, a0});
            _stack.emplace_back(_Enter{a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = _f.f(_f.a0, _result);
      }
    }
    return _result;
  }

  /// Helper: get head of list with default.
  static unsigned int head_default(unsigned int default0,
                                   const List<unsigned int> &l);

  /// scanr f acc l scan from right.
  template <typename F0>
    requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &,
                                   unsigned int &>
  static List<unsigned int>
  scanr(F0 &&f, unsigned int acc,
        const List<unsigned int> &l) { /// _Enter: captures varying parameters
                                       /// for each recursive call.

    struct _Enter {
      const List<unsigned int> *l;
    };

    /// _Cont_Cons: saves [a0, acc, f], resumes after recursive call, then
    /// processes rest.
    struct _Cont_Cons {
      unsigned int a0;
      unsigned int acc;
      F0 f;
    };

    using _Frame = std::variant<_Enter, _Cont_Cons>;
    List<unsigned int> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified scanr: _Enter -> _Cont_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<unsigned int> &l = *_f.l;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = List<unsigned int>::cons(acc, List<unsigned int>::nil());
        } else {
          const auto &[a0, a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          _stack.emplace_back(_Cont_Cons{a0, acc, f});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Cont_Cons>(_frame));
        unsigned int a0 = _f.a0;
        unsigned int acc = _f.acc;
        F0 f = _f.f;
        List<unsigned int> rest = _result;
        unsigned int h = head_default(acc, rest);
        _result = List<unsigned int>::cons(f(a0, h), std::move(rest));
      }
    }
    return _result;
  } /// scanr1 f l scanr with no initial value.

  template <typename F0>
    requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &,
                                   unsigned int &>
  static List<unsigned int>
  scanr1(F0 &&f,
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
    List<unsigned int> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified scanr1: _Enter -> _Cont_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<unsigned int> &l = *_f.l;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = List<unsigned int>::nil();
        } else {
          const auto &[a0, a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          auto &&_sv = *a1;
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  _sv.v())) {
            _result = List<unsigned int>::cons(a0, List<unsigned int>::nil());
          } else {
            _stack.emplace_back(_Cont_Cons{a0, f});
            _stack.emplace_back(_Enter{a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Cont_Cons>(_frame));
        unsigned int a0 = _f.a0;
        F0 f = _f.f;
        List<unsigned int> rest = _result;
        unsigned int h = head_default(a0, rest);
        _result = List<unsigned int>::cons(f(a0, h), std::move(rest));
      }
    }
    return _result;
  }

  /// mapcat f l maps f and concatenates results (concat_map).
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<List<T1>, F0 &, unsigned int &>
  static List<T1>
  mapcat(F0 &&f,
         const List<unsigned int> &l) { /// _Enter: captures varying parameters
                                        /// for each recursive call.

    struct _Enter {
      const List<unsigned int> *l;
    };

    /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
    struct _Resume_Cons {
      List<T1> a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    List<T1> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified mapcat: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<unsigned int> &l = *_f.l;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = List<T1>::nil();
        } else {
          const auto &[a0, a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{f(a0)});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = _f.a0.app(_result);
      }
    }
    return _result;
  }

  /// map_maybe f l maps f and filters out None results.
  template <typename F0>
    requires std::is_invocable_r_v<std::optional<unsigned int>, F0 &,
                                   unsigned int &>
  static List<unsigned int> map_maybe(
      F0 &&f,
      const List<unsigned int>
          &l) { /// _Enter: captures varying parameters for each recursive call.

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
    List<unsigned int> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified map_maybe: _Enter -> _Cont_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<unsigned int> &l = *_f.l;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = List<unsigned int>::nil();
        } else {
          const auto &[a0, a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          _stack.emplace_back(_Cont_Cons{a0, f});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Cont_Cons>(_frame));
        unsigned int a0 = _f.a0;
        F0 f = _f.f;
        List<unsigned int> rest = _result;
        auto _cs = f(a0);
        if (_cs.has_value()) {
          const unsigned int &y = *_cs;
          _result = List<unsigned int>::cons(y, std::move(rest));
        } else {
          _result = std::move(rest);
        }
      }
    }
    return _result;
  }

  /// bool_all p l checks if all elements satisfy p (same as forall_).
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &>
  static bool bool_all(
      F0 &&p,
      const List<unsigned int>
          &l) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      const List<unsigned int> *l;
    };

    /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
    struct _Resume_Cons {
      bool a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    bool _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified bool_all: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<unsigned int> &l = *_f.l;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = true;
        } else {
          const auto &[a0, a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{p(a0)});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = (_f.a0 && _result);
      }
    }
    return _result;
  }

  /// merge_by cmp l1 l2 merges two lists using comparison function.
  template <typename F1>
    requires std::is_invocable_r_v<unsigned int, F1 &, unsigned int &,
                                   unsigned int &>
  static List<unsigned int> merge_by_fuel(unsigned int fuel, F1 &&cmp,
                                          List<unsigned int> l1,
                                          List<unsigned int> l2) {
    if (fuel <= 0) {
      return l1;
    } else {
      unsigned int f = fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              l1.v_mut())) {
        return l2;
      } else {
        auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(l1.v_mut());
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                l2.v_mut())) {
          return l1;
        } else {
          auto &[a00, a10] =
              std::get<typename List<unsigned int>::Cons>(l2.v_mut());
          if (cmp(a0, a00) <= 0u) {
            return List<unsigned int>::cons(std::move(a0),
                                            merge_by_fuel(f, cmp, *a1, l2));
          } else {
            return List<unsigned int>::cons(std::move(a00),
                                            merge_by_fuel(f, cmp, l1, *a10));
          }
        }
      }
    }
  }

  template <typename F0>
    requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &,
                                   unsigned int &>
  static List<unsigned int> merge_by(F0 &&cmp, const List<unsigned int> &l1,
                                     const List<unsigned int> &l2) {
    return merge_by_fuel((l1.length() + l2.length()), cmp, l1, l2);
  }

  /// max_by f l finds element with maximum f value.
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
        if (rest_max <= fx) {
          _result = fx;
        } else {
          _result = rest_max;
        }
      }
    }
    return _result;
  }

  /// iterate f n x generates x, f(x), f(f(x)), ... of length n.
  template <typename F0>
    requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &>
  static List<unsigned int> iterate(F0 &&f, unsigned int n, unsigned int x) {
    std::unique_ptr<List<unsigned int>> _head{};
    std::unique_ptr<List<unsigned int>> *_write = &_head;
    unsigned int _loop_x = std::move(x);
    unsigned int _loop_n = std::move(n);
    while (true) {
      if (_loop_n <= 0) {
        *_write =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        unsigned int m = _loop_n - 1;
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(_loop_x, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).a1;
        _loop_x = f(_loop_x);
        _loop_n = m;
        continue;
      }
    }
    return std::move(*_head);
  }

  /// maximum_by cmp l finds maximum element by comparison function.
  template <typename F0>
    requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &,
                                   unsigned int &>
  static unsigned int maximum_by(
      F0 &&cmp,
      const List<unsigned int>
          &l) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      const List<unsigned int> *l;
    };

    /// _Cont_Cons: saves [a0, cmp], resumes after recursive call, then
    /// processes rest.
    struct _Cont_Cons {
      unsigned int a0;
      F0 cmp;
    };

    using _Frame = std::variant<_Enter, _Cont_Cons>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified maximum_by: _Enter -> _Cont_Cons.
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
            _stack.emplace_back(_Cont_Cons{a0, cmp});
            _stack.emplace_back(_Enter{a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Cont_Cons>(_frame));
        unsigned int a0 = _f.a0;
        F0 cmp = _f.cmp;
        unsigned int m = _result;
        if (0u <= cmp(a0, m)) {
          _result = a0;
        } else {
          _result = m;
        }
      }
    }
    return _result;
  }

  /// fold_right f l acc folds from the right.
  template <typename F0>
    requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &,
                                   unsigned int &>
  static unsigned int
  fold_right(F0 &&f, const List<unsigned int> &l,
             unsigned int acc) { /// _Enter: captures varying parameters for
                                 /// each recursive call.

    struct _Enter {
      const List<unsigned int> *l;
    };

    /// _Resume_Cons: saves [f, a0], resumes after recursive call with _result.
    struct _Resume_Cons {
      F0 f;
      unsigned int a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified fold_right: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<unsigned int> &l = *_f.l;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = acc;
        } else {
          const auto &[a0, a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{f, a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = _f.f(_f.a0, _result);
      }
    }
    return _result;
  }

  /// partition p l partitions list into (satisfies p, doesn't satisfy p).
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &>
  static std::pair<List<unsigned int>, List<unsigned int>> partition(
      F0 &&p,
      const List<unsigned int>
          &l) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      const List<unsigned int> *l;
    };

    /// _Cont_Cons: saves [a0, p], resumes after recursive call, then processes
    /// rest.
    struct _Cont_Cons {
      unsigned int a0;
      F0 p;
    };

    using _Frame = std::variant<_Enter, _Cont_Cons>;
    std::pair<List<unsigned int>, List<unsigned int>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified partition: _Enter -> _Cont_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<unsigned int> &l = *_f.l;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = std::make_pair(List<unsigned int>::nil(),
                                   List<unsigned int>::nil());
        } else {
          const auto &[a0, a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          _stack.emplace_back(_Cont_Cons{a0, p});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Cont_Cons>(_frame));
        unsigned int a0 = _f.a0;
        F0 p = _f.p;
        const List<unsigned int> &yes = _result.first;
        const List<unsigned int> &no = _result.second;
        if (p(a0)) {
          _result = std::make_pair(List<unsigned int>::cons(a0, yes), no);
        } else {
          _result = std::make_pair(yes, List<unsigned int>::cons(a0, no));
        }
      }
    }
    return _result;
  }

  /// subsequences l generates all subsequences of l: 1,2 -> [],[1],[2],[1,2].
  static List<List<unsigned int>> subsequences(const List<unsigned int> &l);
  /// Helper: pair element with all elements in list.
  static List<std::pair<unsigned int, unsigned int>>
  pair_with_all(unsigned int x, const List<unsigned int> &l);
  /// cartesian l1 l2 computes cartesian product of two lists.
  static List<std::pair<unsigned int, unsigned int>>
  cartesian(const List<unsigned int> &l1, const List<unsigned int> &l2);
  /// longest_run l finds the longest consecutive run of equal elements.
  /// Matches on recursive result to decide behavior.
  static List<unsigned int> longest_run_fuel(unsigned int fuel,
                                             List<unsigned int> l);
  static List<unsigned int> longest_run(const List<unsigned int> &l);

  /// any p l checks if any element satisfies predicate (same as exists_fn but
  /// different name).
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &>
  static bool any(F0 &&p, const List<unsigned int> &l) {
    bool _result;
    const List<unsigned int> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        _result = false;
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l->v());
        if (p(a0)) {
          _result = true;
          break;
        } else {
          _loop_l = a1.get();
        }
      }
    }
    return _result;
  }

  /// all p l checks if all elements satisfy predicate (same as forall_ but
  /// different name).
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &>
  static bool all(F0 &&p, const List<unsigned int> &l) {
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
        if (p(a0)) {
          _loop_l = a1.get();
        } else {
          _result = false;
          break;
        }
      }
    }
    return _result;
  }

  /// filter_not p l filters elements that don't satisfy predicate.
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &>
  static List<unsigned int> filter_not(F0 &&p, const List<unsigned int> &l) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
      return List<unsigned int>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<unsigned int>::Cons>(l.v());
      if (p(a0)) {
        return filter_not(p, *a1);
      } else {
        return List<unsigned int>::cons(a0, filter_not(p, *a1));
      }
    }
  }

  /// span_split p l splits at first element that doesn't satisfy p.
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &>
  static std::pair<List<unsigned int>, List<unsigned int>> span_split(
      F0 &&p,
      const List<unsigned int>
          &l) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      const List<unsigned int> *l;
    };

    /// _Cont1: saves [a0], resumes after recursive call, then processes rest.
    struct _Cont1 {
      unsigned int a0;
    };

    using _Frame = std::variant<_Enter, _Cont1>;
    std::pair<List<unsigned int>, List<unsigned int>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified span_split: _Enter -> _Cont1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<unsigned int> &l = *_f.l;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = std::make_pair(List<unsigned int>::nil(),
                                   List<unsigned int>::nil());
        } else {
          const auto &[a0, a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          if (p(a0)) {
            _stack.emplace_back(_Cont1{a0});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            _result = std::make_pair(List<unsigned int>::nil(),
                                     List<unsigned int>::cons(a0, *a1));
          }
        }
      } else {
        auto _f = std::move(std::get<_Cont1>(_frame));
        unsigned int a0 = _f.a0;
        const List<unsigned int> &taken = _result.first;
        const List<unsigned int> &rest = _result.second;
        _result = std::make_pair(List<unsigned int>::cons(a0, taken), rest);
      }
    }
    return _result;
  }

  /// group_by_eq eq l groups consecutive elements by equality function.
  template <typename F1>
    requires std::is_invocable_r_v<bool, F1 &, unsigned int &, unsigned int &>
  static List<List<unsigned int>>
  group_by_eq_fuel(unsigned int fuel, F1 &&eq, const List<unsigned int> &l) {
    if (fuel <= 0) {
      return List<List<unsigned int>>::nil();
    } else {
      unsigned int f = fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        return List<List<unsigned int>>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        auto &&_sv0 = *a1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _sv0.v())) {
          return List<List<unsigned int>>::cons(
              List<unsigned int>::cons(a0, List<unsigned int>::nil()),
              List<List<unsigned int>>::nil());
        } else {
          const auto &[a00, a10] =
              std::get<typename List<unsigned int>::Cons>(_sv0.v());
          if (eq(a0, a00)) {
            auto &&_sv1 = group_by_eq_fuel(f, eq, *a1);
            if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
                    _sv1.v())) {
              return List<List<unsigned int>>::cons(
                  List<unsigned int>::cons(a0, List<unsigned int>::nil()),
                  List<List<unsigned int>>::nil());
            } else {
              const auto &[a01, a11] =
                  std::get<typename List<List<unsigned int>>::Cons>(_sv1.v());
              return List<List<unsigned int>>::cons(
                  List<unsigned int>::cons(a0, a01), *a11);
            }
          } else {
            return List<List<unsigned int>>::cons(
                List<unsigned int>::cons(a0, List<unsigned int>::nil()),
                group_by_eq_fuel(f, eq, *a1));
          }
        }
      }
    }
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &, unsigned int &>
  static List<List<unsigned int>> group_by_eq(F0 &&eq,
                                              const List<unsigned int> &l) {
    return group_by_eq_fuel(l.length(), eq, l);
  }

  /// power_set l generates all subsets.
  static List<List<unsigned int>> power_set(const List<unsigned int> &l);

  /// map_accum_l f acc l maps with accumulator threading.
  template <typename F0>
    requires std::is_invocable_r_v<std::pair<unsigned int, unsigned int>, F0 &,
                                   unsigned int &, unsigned int &>
  static std::pair<unsigned int, List<unsigned int>> map_accum_l(
      F0 &&f, unsigned int acc,
      const List<unsigned int>
          &l) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      const List<unsigned int> *l;
      unsigned int acc;
    };

    /// _Cont_acc_: saves [y], resumes after recursive call, then processes
    /// rest.
    struct _Cont_acc_ {
      unsigned int y;
    };

    using _Frame = std::variant<_Enter, _Cont_acc_>;
    std::pair<unsigned int, List<unsigned int>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l, acc});
    /// Loopified map_accum_l: _Enter -> _Cont_acc_.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<unsigned int> &l = *_f.l;
        unsigned int acc = _f.acc;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = std::make_pair(std::move(acc), List<unsigned int>::nil());
        } else {
          const auto &[a0, a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          auto _cs = f(acc, a0);
          const unsigned int &acc_ = _cs.first;
          const unsigned int &y = _cs.second;
          _stack.emplace_back(_Cont_acc_{y});
          _stack.emplace_back(_Enter{a1.get(), std::move(_cs.first)});
        }
      } else {
        auto _f = std::move(std::get<_Cont_acc_>(_frame));
        unsigned int y = _f.y;
        const unsigned int &acc__ = _result.first;
        const List<unsigned int> &ys = _result.second;
        _result = std::make_pair(std::move(_result.first),
                                 List<unsigned int>::cons(y, ys));
      }
    }
    return _result;
  }
};

#endif // INCLUDED_LOOPIFY_HOFS
