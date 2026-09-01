#ifndef INCLUDED_LOOPIFY_PREDICATES
#define INCLUDED_LOOPIFY_PREDICATES

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
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

  template <typename _U> List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    crane::small_vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        std::atomic_thread_fence(std::memory_order_acquire);
        _drain(_cur->v_mut());
      }
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct LoopifyPredicates {
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static List<uint64_t> take_while(F0 &&p, const List<uint64_t> &l) {
    std::shared_ptr<List<uint64_t>> _head{};
    std::shared_ptr<List<uint64_t>> *_write = &_head;
    const List<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        if (p(a0)) {
          auto _cell = std::make_shared<List<uint64_t>>(
              typename List<uint64_t>::Cons(a0, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
          _loop_l = crane_raw(a1);
          continue;
        } else {
          *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
          break;
        }
      }
    }
    return std::move(*_head);
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static List<uint64_t> drop_while(F0 &&p, List<uint64_t> l) {
    List<uint64_t> _loop_l = std::move(l);
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              _loop_l.v_mut())) {
        return List<uint64_t>::nil();
      } else {
        auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l.v_mut());
        if (p(a0)) {
          _loop_l = List<uint64_t>(*a1);
        } else {
          return _loop_l;
        }
      }
    }
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static std::pair<List<uint64_t>, List<uint64_t>>
  span(F0 &&p,
       List<uint64_t>
           l) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      List<uint64_t> l;
    };

    /// _Cont1: saves [a0], resumes after recursive call, then processes rest.
    struct _Cont1 {
      uint64_t a0;
    };

    using _Frame = std::variant<_Enter, _Cont1>;
    std::pair<List<uint64_t>, List<uint64_t>> _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{std::move(l)});
    /// Loopified span: _Enter -> _Cont1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        List<uint64_t> l = std::move(_f.l);
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v_mut())) {
          _result =
              std::make_pair(List<uint64_t>::nil(), List<uint64_t>::nil());
        } else {
          auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v_mut());
          if (p(a0)) {
            _stack.emplace_back(_Cont1{a0});
            _stack.emplace_back(_Enter{*a1});
          } else {
            _result = std::make_pair(List<uint64_t>::nil(), l);
          }
        }
      } else {
        auto _f = std::move(std::get<_Cont1>(_frame));
        uint64_t a0 = _f.a0;
        std::pair<List<uint64_t>, List<uint64_t>> _rc1 = std::move(_result);
        auto [yes, no] = _rc1;
        _result = std::make_pair(List<uint64_t>::cons(a0, std::move(yes)),
                                 std::move(no));
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static std::pair<List<uint64_t>, List<uint64_t>>
  break_at(F0 &&p,
           List<uint64_t> l) { /// _Enter: captures varying parameters for each
                               /// recursive call.

    struct _Enter {
      List<uint64_t> l;
    };

    /// _Cont1: saves [a0], resumes after recursive call, then processes rest.
    struct _Cont1 {
      uint64_t a0;
    };

    using _Frame = std::variant<_Enter, _Cont1>;
    std::pair<List<uint64_t>, List<uint64_t>> _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{std::move(l)});
    /// Loopified break_at: _Enter -> _Cont1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        List<uint64_t> l = std::move(_f.l);
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v_mut())) {
          _result =
              std::make_pair(List<uint64_t>::nil(), List<uint64_t>::nil());
        } else {
          auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v_mut());
          if (p(a0)) {
            _result = std::make_pair(List<uint64_t>::nil(), l);
          } else {
            _stack.emplace_back(_Cont1{a0});
            _stack.emplace_back(_Enter{*a1});
          }
        }
      } else {
        auto _f = std::move(std::get<_Cont1>(_frame));
        uint64_t a0 = _f.a0;
        std::pair<List<uint64_t>, List<uint64_t>> _rc1 = std::move(_result);
        auto [before, after] = _rc1;
        _result = std::make_pair(List<uint64_t>::cons(a0, std::move(before)),
                                 std::move(after));
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static List<uint64_t> filter(F0 &&p, const List<uint64_t> &l) {
    std::shared_ptr<List<uint64_t>> _head{};
    std::shared_ptr<List<uint64_t>> *_write = &_head;
    const List<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        if (p(a0)) {
          auto _cell = std::make_shared<List<uint64_t>>(
              typename List<uint64_t>::Cons(a0, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
          _loop_l = crane_raw(a1);
          continue;
        } else {
          _loop_l = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static List<uint64_t> reject(F0 &&p, const List<uint64_t> &l) {
    std::shared_ptr<List<uint64_t>> _head{};
    std::shared_ptr<List<uint64_t>> *_write = &_head;
    const List<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        if (p(a0)) {
          _loop_l = crane_raw(a1);
          continue;
        } else {
          auto _cell = std::make_shared<List<uint64_t>>(
              typename List<uint64_t>::Cons(a0, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
          _loop_l = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static bool
  forall_pred(F0 &&p,
              const List<uint64_t> &l) { /// _Enter: captures varying parameters
                                         /// for each recursive call.

    struct _Enter {
      const List<uint64_t> *l;
    };

    /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
    struct _Resume_Cons {
      bool a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    bool _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&l});
    /// Loopified forall_pred: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = true;
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{p(a0)});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = (_f.a0 && std::move(_result));
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static bool
  exists_pred(F0 &&p,
              const List<uint64_t> &l) { /// _Enter: captures varying parameters
                                         /// for each recursive call.

    struct _Enter {
      const List<uint64_t> *l;
    };

    /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
    struct _Resume_Cons {
      bool a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    bool _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&l});
    /// Loopified exists_pred: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = false;
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{p(a0)});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = (_f.a0 || std::move(_result));
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static std::optional<uint64_t> find_index_aux(F0 &&p, const List<uint64_t> &l,
                                                uint64_t idx) {
    uint64_t _loop_idx = std::move(idx);
    const List<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        return std::optional<uint64_t>();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        if (p(a0)) {
          return std::make_optional<uint64_t>(_loop_idx);
        } else {
          _loop_idx = (_loop_idx + UINT64_C(1));
          _loop_l = crane_raw(a1);
        }
      }
    }
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static std::optional<uint64_t> find_index(F0 &&p, const List<uint64_t> &l) {
    return find_index_aux(p, l, UINT64_C(0));
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static List<uint64_t> find_indices_aux(F0 &&p, const List<uint64_t> &l,
                                         uint64_t idx) {
    std::shared_ptr<List<uint64_t>> _head{};
    std::shared_ptr<List<uint64_t>> *_write = &_head;
    uint64_t _loop_idx = std::move(idx);
    const List<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        if (p(a0)) {
          auto _cell = std::make_shared<List<uint64_t>>(
              typename List<uint64_t>::Cons(_loop_idx, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
          _loop_idx = (_loop_idx + UINT64_C(1));
          _loop_l = crane_raw(a1);
          continue;
        } else {
          _loop_idx = (_loop_idx + UINT64_C(1));
          _loop_l = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static List<uint64_t> find_indices(F0 &&p, const List<uint64_t> &l) {
    return find_indices_aux(p, l, UINT64_C(0));
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &, uint64_t &>
  static List<uint64_t> delete_by(F0 &&eq, uint64_t x,
                                  const List<uint64_t> &l) {
    std::shared_ptr<List<uint64_t>> _head{};
    std::shared_ptr<List<uint64_t>> *_write = &_head;
    const List<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        if (eq(x, a0)) {
          *_write = std::make_shared<List<uint64_t>>(*a1);
          break;
        } else {
          auto _cell = std::make_shared<List<uint64_t>>(
              typename List<uint64_t>::Cons(a0, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
          _loop_l = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  static List<uint64_t> remove_all(uint64_t x, const List<uint64_t> &l);
};

#endif // INCLUDED_LOOPIFY_PREDICATES
