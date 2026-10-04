#ifndef INCLUDED_LOOPIFY_PREDICATES
#define INCLUDED_LOOPIFY_PREDICATES

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
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

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct LoopifyPredicates {
  template <typename F0>
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
  static std::pair<List<uint64_t>, List<uint64_t>>
  span(F0 &&p,
       const List<uint64_t> &l) { /// CraneEnter: captures varying parameters
                                  /// for each recursive call.

    struct CraneEnter {
      const List<uint64_t> *l;
    };

    /// CraneCont1: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont1 {
      uint64_t a0;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont1>;
    std::pair<List<uint64_t>, List<uint64_t>> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified span: CraneEnter -> CraneCont1.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result =
              std::make_pair(List<uint64_t>::nil(), List<uint64_t>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          if (p(a0)) {
            _stack.emplace_back(CraneCont1{a0});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          } else {
            _result = std::make_pair(List<uint64_t>::nil(), l);
          }
        }
      } else {
        auto _f = std::move(std::get<CraneCont1>(_frame));
        uint64_t a0 = _f.a0;
        auto [yes, no] = std::move(_result);
        _result = std::make_pair(List<uint64_t>::cons(a0, std::move(yes)),
                                 std::move(no));
      }
    }
    return _result;
  }

  template <typename F0>
  static std::pair<List<uint64_t>, List<uint64_t>>
  break_at(F0 &&p,
           const List<uint64_t> &l) { /// CraneEnter: captures varying
                                      /// parameters for each recursive call.

    struct CraneEnter {
      const List<uint64_t> *l;
    };

    /// CraneCont1: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont1 {
      uint64_t a0;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont1>;
    std::pair<List<uint64_t>, List<uint64_t>> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified break_at: CraneEnter -> CraneCont1.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result =
              std::make_pair(List<uint64_t>::nil(), List<uint64_t>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          if (p(a0)) {
            _result = std::make_pair(List<uint64_t>::nil(), l);
          } else {
            _stack.emplace_back(CraneCont1{a0});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        }
      } else {
        auto _f = std::move(std::get<CraneCont1>(_frame));
        uint64_t a0 = _f.a0;
        auto [before, after] = std::move(_result);
        _result = std::make_pair(List<uint64_t>::cons(a0, std::move(before)),
                                 std::move(after));
      }
    }
    return _result;
  }

  template <typename F0>
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
              const List<uint64_t> &l) { /// CraneEnter: captures varying
                                         /// parameters for each recursive call.

    struct CraneEnter {
      const List<uint64_t> *l;
    };

    /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_Cons {
      uint64_t a0;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    bool _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified forall_pred: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = true;
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(CraneCont_Cons{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        uint64_t a0 = _f.a0;
        _result = (p(a0) && std::move(_result));
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static bool
  exists_pred(F0 &&p,
              const List<uint64_t> &l) { /// CraneEnter: captures varying
                                         /// parameters for each recursive call.

    struct CraneEnter {
      const List<uint64_t> *l;
    };

    /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_Cons {
      uint64_t a0;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    bool _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified exists_pred: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = false;
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(CraneCont_Cons{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        uint64_t a0 = _f.a0;
        _result = (p(a0) || std::move(_result));
      }
    }
    return _result;
  }

  template <typename F0>
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
  static std::optional<uint64_t> find_index(F0 &&p, const List<uint64_t> &l) {
    return find_index_aux(p, l, UINT64_C(0));
  }

  template <typename F0>
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
  static List<uint64_t> find_indices(F0 &&p, const List<uint64_t> &l) {
    return find_indices_aux(p, l, UINT64_C(0));
  }

  template <typename F0>
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
