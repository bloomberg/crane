#ifndef INCLUDED_LOOPIFY_HOFS
#define INCLUDED_LOOPIFY_HOFS

#include <functional>
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
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
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

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) unsigned int length() const {
    const List *_self = this;

    struct _Enter {
      const List *_self;
    };

    struct _Call1 {};

    using _Frame = std::variant<_Enter, _Call1>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{_self});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List *_self = _f._self;
        auto &&_sv = *(_self);
        if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
          _result = 0u;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<t_A>::Cons>(_sv.v());
          _stack.emplace_back(_Call1{});
          _stack.emplace_back(_Enter{d_a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = (_result + 1);
      }
    }
    return _result;
  }

  __attribute__((pure)) List<t_A> app(List<t_A> m) const {
    std::unique_ptr<List<t_A>> _head{};
    std::unique_ptr<List<t_A>> *_write = &_head;
    const List *_loop_self = this;
    while (true) {
      auto &&_sv = *(_loop_self);
      if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
        *(_write) = std::make_unique<List<t_A>>(m);
        break;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
        auto _cell = std::make_unique<List<t_A>>(
            typename List<t_A>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename List<t_A>::Cons>((*_write)->v_mut()).d_a1;
        _loop_self = d_a1.get();
        continue;
      }
    }
    return std::move(*(_head));
  }
};

struct LoopifyHofs {
  /// foldl1 f l folds from left with no initial value. Returns 0 for empty
  /// list.
  template <typename T1, MapsTo<T1, T1, T1> F0>
  static T1 foldl1_aux(F0 &&f, const T1 acc, const List<T1> &l) {
    T1 _result;
    List<T1> _loop_l = l;
    T1 _loop_acc = acc;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l.v())) {
        _result = _loop_acc;
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<T1>::Cons>(_loop_l.v());
        List<T1> _next_l = *(d_a1);
        T1 _next_acc = f(_loop_acc, d_a0);
        _loop_l = std::move(_next_l);
        _loop_acc = std::move(_next_acc);
      }
    }
    return _result;
  }

  template <typename T1, MapsTo<T1, T1, T1> F0>
  static T1 foldl1(F0 &&f, const T1 default0, const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
      return foldl1_aux<T1>(f, d_a0, *(d_a1));
    }
  }

  /// forall_ p l checks if all elements satisfy predicate p.
  template <typename T1, MapsTo<bool, T1> F0>
  __attribute__((pure)) static bool forall_(F0 &&p, const List<T1> &l) {
    bool _result;
    List<T1> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l.v())) {
        _result = true;
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<T1>::Cons>(_loop_l.v());
        if (p(d_a0)) {
          _loop_l = *(d_a1);
        } else {
          _result = false;
          break;
        }
      }
    }
    return _result;
  }

  /// exists_fn p l checks if any element satisfies predicate p.
  template <typename T1, MapsTo<bool, T1> F0>
  __attribute__((pure)) static bool exists_fn(F0 &&p, const List<T1> &l) {
    bool _result;
    List<T1> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l.v())) {
        _result = false;
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<T1>::Cons>(_loop_l.v());
        if (p(d_a0)) {
          _result = true;
          break;
        } else {
          _loop_l = *(d_a1);
        }
      }
    }
    return _result;
  }

  /// drop_while p l drops elements while predicate holds.
  template <typename T1, MapsTo<bool, T1> F0>
  __attribute__((pure)) static List<T1> drop_while(F0 &&p, const List<T1> &l) {
    List<T1> _result;
    List<T1> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l.v())) {
        _result = List<T1>::nil();
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<T1>::Cons>(_loop_l.v());
        if (p(d_a0)) {
          _loop_l = *(d_a1);
        } else {
          _result = List<T1>::cons(d_a0, *(d_a1));
          break;
        }
      }
    }
    return _result;
  }

  /// take_while p l takes elements while predicate holds.
  template <typename T1, MapsTo<bool, T1> F0>
  __attribute__((pure)) static List<T1> take_while(F0 &&p, const List<T1> &l) {
    std::unique_ptr<List<T1>> _head{};
    std::unique_ptr<List<T1>> *_write = &_head;
    List<T1> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l.v())) {
        *(_write) = std::make_unique<List<T1>>(List<T1>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<T1>::Cons>(_loop_l.v());
        if (p(d_a0)) {
          auto _cell = std::make_unique<List<T1>>(
              typename List<T1>::Cons(d_a0, nullptr));
          *(_write) = std::move(_cell);
          _write = &std::get<typename List<T1>::Cons>((*_write)->v_mut()).d_a1;
          _loop_l = *(d_a1);
          continue;
        } else {
          *(_write) = std::make_unique<List<T1>>(List<T1>::nil());
          break;
        }
      }
    }
    return std::move(*(_head));
  }

  /// flat_map f l maps f and flattens results.
  template <typename T1, typename T2, MapsTo<List<T2>, T1> F0>
  __attribute__((pure)) static List<T2> flat_map(F0 &&f, const List<T1> &l) {
    struct _Enter {
      const List<T1> l;
    };

    struct _Call1 {
      List<T2> _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    List<T2> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<T1> l = _f.l;
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          _result = List<T2>::nil();
        } else {
          const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
          _stack.emplace_back(_Call1{f(d_a0)});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = _f._s0.app(_result);
      }
    }
    return _result;
  }

  /// all_pairs l1 l2 returns all pairs from two lists.
  template <typename T1, typename T2>
  __attribute__((pure)) static List<std::pair<T1, T2>>
  all_pairs(const List<T1> &l1, const List<T2> &l2) {
    struct _Enter {
      const List<T1> l1;
    };

    struct _Call1 {
      List<std::pair<T1, T2>> _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    List<std::pair<T1, T2>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l1});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<T1> l1 = _f.l1;
        std::function<List<std::pair<T1, T2>>(T1, List<T2>)> pair_with;
        pair_with = [&](T1 x, List<T2> l) -> List<std::pair<T1, T2>> {
          struct _Enter {
            List<T2> l;
          };
          struct _Call1 {
            decltype(std::make_pair(std::declval<T1 &>(),
                                    std::declval<T2 &>())) _s0;
          };
          using _Frame = std::variant<_Enter, _Call1>;
          List<std::pair<T1, T2>> _result{};
          std::vector<_Frame> _stack;
          _stack.reserve(16);
          _stack.emplace_back(_Enter{l});
          while (!_stack.empty()) {
            _Frame _frame = std::move(_stack.back());
            _stack.pop_back();
            if (std::holds_alternative<_Enter>(_frame)) {
              auto _f = std::move(std::get<_Enter>(_frame));
              List<T2> l = _f.l;
              if (std::holds_alternative<typename List<T2>::Nil>(l.v())) {
                _result = List<std::pair<T1, T2>>::nil();
              } else {
                const auto &[d_a0, d_a1] =
                    std::get<typename List<T2>::Cons>(l.v());
                _stack.emplace_back(_Call1{std::make_pair(x, d_a0)});
                _stack.emplace_back(_Enter{*(d_a1)});
              }
            } else {
              auto _f = std::move(std::get<_Call1>(_frame));
              _result = List<std::pair<T1, T2>>::cons(_f._s0, _result);
            }
          }
          return _result;
        };
        if (std::holds_alternative<typename List<T1>::Nil>(l1.v())) {
          _result = List<std::pair<T1, T2>>::nil();
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<T1>::Cons>(l1.v());
          _stack.emplace_back(_Call1{pair_with(d_a00, l2)});
          _stack.emplace_back(_Enter{*(d_a10)});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = _f._s0.app(_result);
      }
    }
    return _result;
  }

  /// find_indices p l finds all indices where p is true.
  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static List<unsigned int>
  find_indices_aux(F0 &&p, const List<unsigned int> &l, unsigned int i) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
      return List<unsigned int>::nil();
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(l.v());
      if (p(d_a0)) {
        return List<unsigned int>::cons(i,
                                        find_indices_aux(p, *(d_a1), (i + 1)));
      } else {
        return find_indices_aux(p, *(d_a1), (i + 1));
      }
    }
  }

  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static List<unsigned int>
  find_indices(F0 &&p, const List<unsigned int> &l) {
    return find_indices_aux(p, l, 0u);
  }

  /// delete_by eq x l deletes first element equal to x.
  template <MapsTo<bool, unsigned int, unsigned int> F0>
  __attribute__((pure)) static List<unsigned int>
  delete_by(F0 &&eq, const unsigned int &x, const List<unsigned int> &l) {
    std::unique_ptr<List<unsigned int>> _head{};
    std::unique_ptr<List<unsigned int>> *_write = &_head;
    List<unsigned int> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v())) {
        *(_write) =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l.v());
        if (eq(x, d_a0)) {
          *(_write) = std::make_unique<List<unsigned int>>(*(d_a1));
          break;
        } else {
          auto _cell = std::make_unique<List<unsigned int>>(
              typename List<unsigned int>::Cons(d_a0, nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                   .d_a1;
          _loop_l = *(d_a1);
          continue;
        }
      }
    }
    return std::move(*(_head));
  }

  /// is_prefix_of l1 l2 checks if l1 is a prefix of l2.
  __attribute__((pure)) static bool is_prefix_of(const List<unsigned int> &l1,
                                                 const List<unsigned int> &l2);
  /// lookup_all key l finds all values associated with key in association list.
  __attribute__((pure)) static List<unsigned int>
  lookup_all(const unsigned int &key,
             const List<std::pair<unsigned int, unsigned int>> &l);

  /// scanl f acc l scan from left with accumulator.
  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  __attribute__((pure)) static List<unsigned int>
  scanl(F0 &&f, unsigned int acc, const List<unsigned int> &l) {
    std::unique_ptr<List<unsigned int>> _head{};
    std::unique_ptr<List<unsigned int>> *_write = &_head;
    List<unsigned int> _loop_l = l;
    unsigned int _loop_acc = std::move(acc);
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v())) {
        *(_write) = std::make_unique<List<unsigned int>>(
            List<unsigned int>::cons(_loop_acc, List<unsigned int>::nil()));
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l.v());
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(_loop_acc, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        List<unsigned int> _next_l = *(d_a1);
        unsigned int _next_acc = f(_loop_acc, d_a0);
        _loop_l = std::move(_next_l);
        _loop_acc = std::move(_next_acc);
        continue;
      }
    }
    return std::move(*(_head));
  }

  /// scanl1 f l like scanl but no initial value, uses first element.
  template <MapsTo<unsigned int, unsigned int, unsigned int> F1>
  __attribute__((pure)) static List<unsigned int>
  scanl1_fuel(const unsigned int &fuel, F1 &&f, List<unsigned int> l) {
    std::unique_ptr<List<unsigned int>> _head{};
    std::unique_ptr<List<unsigned int>> *_write = &_head;
    List<unsigned int> _loop_l = std::move(l);
    unsigned int _loop_fuel = fuel;
    while (true) {
      if (_loop_fuel <= 0) {
        *(_write) = std::make_unique<List<unsigned int>>(_loop_l);
        break;
      } else {
        unsigned int g = _loop_fuel - 1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _loop_l.v())) {
          *(_write) =
              std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
          break;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(_loop_l.v());
          auto &&_sv0 = *(d_a1);
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  _sv0.v())) {
            *(_write) = std::make_unique<List<unsigned int>>(
                List<unsigned int>::cons(d_a0, List<unsigned int>::nil()));
            break;
          } else {
            const auto &[d_a00, d_a10] =
                std::get<typename List<unsigned int>::Cons>(_sv0.v());
            auto _cell = std::make_unique<List<unsigned int>>(
                typename List<unsigned int>::Cons(d_a0, nullptr));
            *(_write) = std::move(_cell);
            _write =
                &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                     .d_a1;
            List<unsigned int> _next_l =
                List<unsigned int>::cons(f(d_a0, d_a00), *(d_a10));
            unsigned int _next_fuel = g;
            _loop_l = std::move(_next_l);
            _loop_fuel = std::move(_next_fuel);
            continue;
          }
        }
      }
    }
    return std::move(*(_head));
  }

  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  __attribute__((pure)) static List<unsigned int>
  scanl1(F0 &&f, const List<unsigned int> &l) {
    return scanl1_fuel(l.length(), f, l);
  }

  /// foldr1 f l fold right with no initial value.
  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  foldr1(F0 &&f, const List<unsigned int> &l) {
    struct _Enter {
      const List<unsigned int> l;
    };

    struct _Call1 {
      unsigned int _s0;
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
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<unsigned int> l = _f.l;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = 0u;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          auto &&_sv = *(d_a1);
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  _sv.v())) {
            _result = d_a0;
          } else {
            _stack.emplace_back(_Call1{d_a0});
            _stack.emplace_back(_Enter{*(d_a1)});
          }
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = f(_f._s0, _result);
      }
    }
    return _result;
  }

  /// Helper: get head of list with default.
  __attribute__((pure)) static unsigned int
  head_default(unsigned int default0, const List<unsigned int> &l);

  /// scanr f acc l scan from right.
  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  __attribute__((pure)) static List<unsigned int>
  scanr(F0 &&f, unsigned int acc, const List<unsigned int> &l) {
    struct _Enter {
      const List<unsigned int> l;
    };

    struct _Call1 {
      unsigned int _s0;
      unsigned int _s1;
      F0 _s2;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    List<unsigned int> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<unsigned int> l = _f.l;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = List<unsigned int>::cons(acc, List<unsigned int>::nil());
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          _stack.emplace_back(_Call1{acc, d_a0, f});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        unsigned int acc = _f._s0;
        unsigned int d_a0 = _f._s1;
        F0 f = _f._s2;
        List<unsigned int> rest = _result;
        unsigned int h = head_default(acc, rest);
        _result = List<unsigned int>::cons(f(d_a0, h), rest);
      }
    }
    return _result;
  }

  /// scanr1 f l scanr with no initial value.
  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  __attribute__((pure)) static List<unsigned int>
  scanr1(F0 &&f, const List<unsigned int> &l) {
    struct _Enter {
      const List<unsigned int> l;
    };

    struct _Call1 {
      unsigned int _s0;
      F0 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    List<unsigned int> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<unsigned int> l = _f.l;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = List<unsigned int>::nil();
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          auto &&_sv = *(d_a1);
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  _sv.v())) {
            _result = List<unsigned int>::cons(d_a0, List<unsigned int>::nil());
          } else {
            _stack.emplace_back(_Call1{d_a0, f});
            _stack.emplace_back(_Enter{*(d_a1)});
          }
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        unsigned int d_a0 = _f._s0;
        F0 f = _f._s1;
        List<unsigned int> rest = _result;
        unsigned int h = head_default(d_a0, rest);
        _result = List<unsigned int>::cons(f(d_a0, h), rest);
      }
    }
    return _result;
  }

  /// mapcat f l maps f and concatenates results (concat_map).
  template <typename T1, MapsTo<List<T1>, unsigned int> F0>
  __attribute__((pure)) static List<T1> mapcat(F0 &&f,
                                               const List<unsigned int> &l) {
    struct _Enter {
      const List<unsigned int> l;
    };

    struct _Call1 {
      List<T1> _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    List<T1> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<unsigned int> l = _f.l;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = List<T1>::nil();
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          _stack.emplace_back(_Call1{f(d_a0)});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = _f._s0.app(_result);
      }
    }
    return _result;
  }

  /// map_maybe f l maps f and filters out None results.
  template <MapsTo<std::optional<unsigned int>, unsigned int> F0>
  __attribute__((pure)) static List<unsigned int>
  map_maybe(F0 &&f, const List<unsigned int> &l) {
    struct _Enter {
      const List<unsigned int> l;
    };

    struct _Call1 {
      unsigned int _s0;
      F0 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    List<unsigned int> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<unsigned int> l = _f.l;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = List<unsigned int>::nil();
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          _stack.emplace_back(_Call1{d_a0, f});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        unsigned int d_a0 = _f._s0;
        F0 f = _f._s1;
        List<unsigned int> rest = _result;
        auto _cs = f(d_a0);
        if (_cs.has_value()) {
          const unsigned int &y = *_cs;
          _result = List<unsigned int>::cons(y, rest);
        } else {
          _result = rest;
        }
      }
    }
    return _result;
  }

  /// bool_all p l checks if all elements satisfy p (same as forall_).
  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static bool bool_all(F0 &&p,
                                             const List<unsigned int> &l) {
    struct _Enter {
      const List<unsigned int> l;
    };

    struct _Call1 {
      bool _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    bool _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<unsigned int> l = _f.l;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = true;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          _stack.emplace_back(_Call1{p(d_a0)});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = (_f._s0 && _result);
      }
    }
    return _result;
  }

  /// merge_by cmp l1 l2 merges two lists using comparison function.
  template <MapsTo<unsigned int, unsigned int, unsigned int> F1>
  __attribute__((pure)) static List<unsigned int>
  merge_by_fuel(const unsigned int &fuel, F1 &&cmp, List<unsigned int> l1,
                List<unsigned int> l2) {
    if (fuel <= 0) {
      return l1;
    } else {
      unsigned int f = fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l1.v())) {
        return l2;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l1.v());
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l2.v())) {
          return l1;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(l2.v());
          if (cmp(d_a0, d_a00) <= 0u) {
            return List<unsigned int>::cons(d_a0,
                                            merge_by_fuel(f, cmp, *(d_a1), l2));
          } else {
            return List<unsigned int>::cons(
                d_a00, merge_by_fuel(f, cmp, l1, *(d_a10)));
          }
        }
      }
    }
  }

  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  __attribute__((pure)) static List<unsigned int>
  merge_by(F0 &&cmp, const List<unsigned int> &l1,
           const List<unsigned int> &l2) {
    return merge_by_fuel((l1.length() + l2.length()), cmp, l1, l2);
  }

  /// max_by f l finds element with maximum f value.
  template <MapsTo<unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  max_by(F0 &&f, const List<unsigned int> &l) {
    struct _Enter {
      const List<unsigned int> l;
    };

    struct _Call1 {
      unsigned int _s0;
      F0 _s1;
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
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<unsigned int> l = _f.l;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = 0u;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          auto &&_sv = *(d_a1);
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  _sv.v())) {
            _result = f(d_a0);
          } else {
            _stack.emplace_back(_Call1{d_a0, f});
            _stack.emplace_back(_Enter{*(d_a1)});
          }
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        unsigned int d_a0 = _f._s0;
        F0 f = _f._s1;
        unsigned int rest_max = _result;
        unsigned int fx = f(d_a0);
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
  template <MapsTo<unsigned int, unsigned int> F0>
  __attribute__((pure)) static List<unsigned int>
  iterate(F0 &&f, const unsigned int &n, unsigned int x) {
    std::unique_ptr<List<unsigned int>> _head{};
    std::unique_ptr<List<unsigned int>> *_write = &_head;
    unsigned int _loop_x = std::move(x);
    unsigned int _loop_n = n;
    while (true) {
      if (_loop_n <= 0) {
        *(_write) =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        unsigned int m = _loop_n - 1;
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(_loop_x, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        unsigned int _next_x = f(_loop_x);
        unsigned int _next_n = m;
        _loop_x = std::move(_next_x);
        _loop_n = std::move(_next_n);
        continue;
      }
    }
    return std::move(*(_head));
  }

  /// maximum_by cmp l finds maximum element by comparison function.
  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  maximum_by(F0 &&cmp, const List<unsigned int> &l) {
    struct _Enter {
      const List<unsigned int> l;
    };

    struct _Call1 {
      F0 _s0;
      unsigned int _s1;
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
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<unsigned int> l = _f.l;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = 0u;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          auto &&_sv = *(d_a1);
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  _sv.v())) {
            _result = d_a0;
          } else {
            _stack.emplace_back(_Call1{cmp, d_a0});
            _stack.emplace_back(_Enter{*(d_a1)});
          }
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        F0 cmp = _f._s0;
        unsigned int d_a0 = _f._s1;
        unsigned int m = _result;
        if (0u <= cmp(d_a0, m)) {
          _result = d_a0;
        } else {
          _result = m;
        }
      }
    }
    return _result;
  }

  /// fold_right f l acc folds from the right.
  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  fold_right(F0 &&f, const List<unsigned int> &l, unsigned int acc) {
    struct _Enter {
      const List<unsigned int> l;
    };

    struct _Call1 {
      unsigned int _s0;
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
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<unsigned int> l = _f.l;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = acc;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          _stack.emplace_back(_Call1{d_a0});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = f(_f._s0, _result);
      }
    }
    return _result;
  }

  /// partition p l partitions list into (satisfies p, doesn't satisfy p).
  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static std::pair<List<unsigned int>, List<unsigned int>>
  partition(F0 &&p, const List<unsigned int> &l) {
    struct _Enter {
      const List<unsigned int> l;
    };

    struct _Call1 {
      unsigned int _s0;
      F0 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<List<unsigned int>, List<unsigned int>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<unsigned int> l = _f.l;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = std::make_pair(List<unsigned int>::nil(),
                                   List<unsigned int>::nil());
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          _stack.emplace_back(_Call1{d_a0, p});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        unsigned int d_a0 = _f._s0;
        F0 p = _f._s1;
        const List<unsigned int> &yes = _result.first;
        const List<unsigned int> &no = _result.second;
        if (p(d_a0)) {
          _result = std::make_pair(List<unsigned int>::cons(d_a0, yes), no);
        } else {
          _result = std::make_pair(yes, List<unsigned int>::cons(d_a0, no));
        }
      }
    }
    return _result;
  }

  /// subsequences l generates all subsequences of l: 1,2 -> [],[1],[2],[1,2].
  __attribute__((pure)) static List<List<unsigned int>>
  subsequences(const List<unsigned int> &l);
  /// Helper: pair element with all elements in list.
  __attribute__((pure)) static List<std::pair<unsigned int, unsigned int>>
  pair_with_all(unsigned int x, const List<unsigned int> &l);
  /// cartesian l1 l2 computes cartesian product of two lists.
  __attribute__((pure)) static List<std::pair<unsigned int, unsigned int>>
  cartesian(const List<unsigned int> &l1, const List<unsigned int> &l2);
  /// longest_run l finds the longest consecutive run of equal elements.
  /// Matches on recursive result to decide behavior.
  __attribute__((pure)) static List<unsigned int>
  longest_run_fuel(const unsigned int &fuel, List<unsigned int> l);
  __attribute__((pure)) static List<unsigned int>
  longest_run(const List<unsigned int> &l);

  /// any p l checks if any element satisfies predicate (same as exists_fn but
  /// different name).
  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static bool any(F0 &&p, const List<unsigned int> &l) {
    bool _result;
    List<unsigned int> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v())) {
        _result = false;
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l.v());
        if (p(d_a0)) {
          _result = true;
          break;
        } else {
          _loop_l = *(d_a1);
        }
      }
    }
    return _result;
  }

  /// all p l checks if all elements satisfy predicate (same as forall_ but
  /// different name).
  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static bool all(F0 &&p, const List<unsigned int> &l) {
    bool _result;
    List<unsigned int> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v())) {
        _result = true;
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l.v());
        if (p(d_a0)) {
          _loop_l = *(d_a1);
        } else {
          _result = false;
          break;
        }
      }
    }
    return _result;
  }

  /// filter_not p l filters elements that don't satisfy predicate.
  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static List<unsigned int>
  filter_not(F0 &&p, const List<unsigned int> &l) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
      return List<unsigned int>::nil();
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(l.v());
      if (p(d_a0)) {
        return filter_not(p, *(d_a1));
      } else {
        return List<unsigned int>::cons(d_a0, filter_not(p, *(d_a1)));
      }
    }
  }

  /// span_split p l splits at first element that doesn't satisfy p.
  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static std::pair<List<unsigned int>, List<unsigned int>>
  span_split(F0 &&p, const List<unsigned int> &l) {
    struct _Enter {
      const List<unsigned int> l;
    };

    struct _Call1 {
      unsigned int _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<List<unsigned int>, List<unsigned int>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<unsigned int> l = _f.l;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = std::make_pair(List<unsigned int>::nil(),
                                   List<unsigned int>::nil());
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          if (p(d_a0)) {
            _stack.emplace_back(_Call1{d_a0});
            _stack.emplace_back(_Enter{*(d_a1)});
          } else {
            _result = std::make_pair(List<unsigned int>::nil(),
                                     List<unsigned int>::cons(d_a0, *(d_a1)));
          }
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        unsigned int d_a0 = _f._s0;
        const List<unsigned int> &taken = _result.first;
        const List<unsigned int> &rest = _result.second;
        _result = std::make_pair(List<unsigned int>::cons(d_a0, taken), rest);
      }
    }
    return _result;
  }

  /// group_by_eq eq l groups consecutive elements by equality function.
  template <MapsTo<bool, unsigned int, unsigned int> F1>
  __attribute__((pure)) static List<List<unsigned int>>
  group_by_eq_fuel(const unsigned int &fuel, F1 &&eq,
                   const List<unsigned int> &l) {
    if (fuel <= 0) {
      return List<List<unsigned int>>::nil();
    } else {
      unsigned int f = fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        return List<List<unsigned int>>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        auto &&_sv0 = *(d_a1);
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _sv0.v())) {
          return List<List<unsigned int>>::cons(
              List<unsigned int>::cons(d_a0, List<unsigned int>::nil()),
              List<List<unsigned int>>::nil());
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(_sv0.v());
          if (eq(d_a0, d_a00)) {
            auto &&_sv1 = group_by_eq_fuel(f, eq, *(d_a1));
            if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
                    _sv1.v())) {
              return List<List<unsigned int>>::cons(
                  List<unsigned int>::cons(d_a0, List<unsigned int>::nil()),
                  List<List<unsigned int>>::nil());
            } else {
              const auto &[d_a01, d_a11] =
                  std::get<typename List<List<unsigned int>>::Cons>(_sv1.v());
              return List<List<unsigned int>>::cons(
                  List<unsigned int>::cons(d_a0, d_a01), *(d_a11));
            }
          } else {
            return List<List<unsigned int>>::cons(
                List<unsigned int>::cons(d_a0, List<unsigned int>::nil()),
                group_by_eq_fuel(f, eq, *(d_a1)));
          }
        }
      }
    }
  }

  template <MapsTo<bool, unsigned int, unsigned int> F0>
  __attribute__((pure)) static List<List<unsigned int>>
  group_by_eq(F0 &&eq, const List<unsigned int> &l) {
    return group_by_eq_fuel(l.length(), eq, l);
  }

  /// power_set l generates all subsets.
  __attribute__((pure)) static List<List<unsigned int>>
  power_set(const List<unsigned int> &l);

  /// map_accum_l f acc l maps with accumulator threading.
  template <
      MapsTo<std::pair<unsigned int, unsigned int>, unsigned int, unsigned int>
          F0>
  __attribute__((pure)) static std::pair<unsigned int, List<unsigned int>>
  map_accum_l(F0 &&f, unsigned int acc, const List<unsigned int> &l) {
    struct _Enter {
      const List<unsigned int> l;
      unsigned int acc;
    };

    struct _Call1 {
      unsigned int _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<unsigned int, List<unsigned int>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l, acc});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<unsigned int> l = _f.l;
        unsigned int acc = _f.acc;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = std::make_pair(acc, List<unsigned int>::nil());
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          auto _cs = f(acc, d_a0);
          const unsigned int &acc_ = _cs.first;
          const unsigned int &y = _cs.second;
          _stack.emplace_back(_Call1{y});
          _stack.emplace_back(_Enter{*(d_a1), acc_});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        unsigned int y = _f._s0;
        const unsigned int &acc__ = _result.first;
        const List<unsigned int> &ys = _result.second;
        _result = std::make_pair(acc__, List<unsigned int>::cons(y, ys));
      }
    }
    return _result;
  }
};

#endif // INCLUDED_LOOPIFY_HOFS
