#ifndef INCLUDED_LOOPIFY_POLYMORPHIC
#define INCLUDED_LOOPIFY_POLYMORPHIC

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

  List<A> app(List<A> m) const {
    std::optional<List<A>> _root{};
    std::shared_ptr<List<A>> *_write = nullptr;
    const List<A> *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = std::move(_loop_m);
        (_write ? *(*_write = std::make_shared<List<A>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<A>::Cons(a0, nullptr);
        List<A> &_node =
            (_write ? *(*_write = std::make_shared<List<A>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<A>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

struct LoopifyPolymorphic {
  template <typename T1>
  static uint64_t
  poly_length(const List<T1> &l) { /// CraneEnter: captures varying parameters
                                   /// for each recursive call.

    struct CraneEnter {
      const List<T1> *l;
    };

    /// CraneCont_Cons: resumes after recursive call, then processes rest.
    struct CraneCont_Cons {};

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    uint64_t _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified poly_length: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<T1> &l = *_f.l;
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
          _stack.emplace_back(CraneCont_Cons{});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        _result = (UINT64_C(1) + std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1>
  static List<T1>
  poly_reverse(const List<T1> &l) { /// CraneEnter: captures varying parameters
                                    /// for each recursive call.

    struct CraneEnter {
      const List<T1> *l;
    };

    /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_Cons {
      T1 a0;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    List<T1> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified poly_reverse: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<T1> &l = *_f.l;
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          _result = List<T1>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
          _stack.emplace_back(CraneCont_Cons{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        auto a0 = std::move(_f.a0);
        _result = std::move(_result).app(List<T1>::cons(a0, List<T1>::nil()));
      }
    }
    return _result;
  }

  template <typename T1>
  static List<T1> poly_append(const List<T1> &l1, List<T1> l2) {
    std::optional<List<T1>> _root{};
    std::shared_ptr<List<T1>> *_write = nullptr;
    List<T1> _loop_l2 = std::move(l2);
    const List<T1> *_loop_l1 = &l1;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l1->v())) {
        auto _value = std::move(_loop_l2);
        (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(_loop_l1->v());
        auto _cell = typename List<T1>::Cons(a0, nullptr);
        List<T1> &_node =
            (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<T1>::Cons>(_node.v_mut()).l;
        _loop_l1 = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }

  template <typename T1> static std::optional<T1> poly_last(const List<T1> &l) {
    const List<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
        return std::optional<T1>();
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(_loop_l->v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename List<T1>::Nil>(_sv.v())) {
          return std::make_optional<T1>(a0);
        } else {
          _loop_l = crane_raw(a1);
        }
      }
    }
  }

  template <typename T1>
  static List<T1> poly_take(uint64_t n, const List<T1> &l) {
    std::optional<List<T1>> _root{};
    std::shared_ptr<List<T1>> *_write = nullptr;
    const List<T1> *_loop_l = &l;
    uint64_t _loop_n = n;
    while (true) {
      if (_loop_n <= 0) {
        auto _value = List<T1>::nil();
        (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        uint64_t n_ = _loop_n - 1;
        if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
          auto _value = List<T1>::nil();
          (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          const auto &[a0, a1] =
              std::get<typename List<T1>::Cons>(_loop_l->v());
          auto _cell = typename List<T1>::Cons(a0, nullptr);
          List<T1> &_node =
              (_write
                   ? *(*_write = std::make_shared<List<T1>>(std::move(_cell)))
                   : _root.emplace(std::move(_cell)));
          _write = &std::get<typename List<T1>::Cons>(_node.v_mut()).l;
          _loop_l = crane_raw(a1);
          _loop_n = n_;
          continue;
        }
      }
    }
    return std::move(*_root);
  }

  template <typename T1> static List<T1> poly_drop(uint64_t n, List<T1> l) {
    List<T1> _loop_l = std::move(l);
    uint64_t _loop_n = n;
    while (true) {
      if (_loop_n <= 0) {
        return _loop_l;
      } else {
        uint64_t n_ = _loop_n - 1;
        if (std::holds_alternative<typename List<T1>::Nil>(_loop_l.v_mut())) {
          return List<T1>::nil();
        } else {
          auto &[a0, a1] = std::get<typename List<T1>::Cons>(_loop_l.v_mut());
          _loop_l = List<T1>(*a1);
          _loop_n = n_;
        }
      }
    }
  }

  template <typename T1>
  static std::optional<T1> poly_nth(uint64_t n, const List<T1> &l) {
    const List<T1> *_loop_l = &l;
    uint64_t _loop_n = n;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
        return std::optional<T1>();
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(_loop_l->v());
        if (_loop_n == UINT64_C(0)) {
          return std::make_optional<T1>(a0);
        } else {
          _loop_l = crane_raw(a1);
          _loop_n = ((
              (_loop_n - UINT64_C(1)) > _loop_n ? 0 : (_loop_n - UINT64_C(1))));
        }
      }
    }
  }

  template <typename T1, typename F0>
  static List<T1> poly_filter(F0 &&p, const List<T1> &l) {
    std::optional<List<T1>> _root{};
    std::shared_ptr<List<T1>> *_write = nullptr;
    const List<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
        auto _value = List<T1>::nil();
        (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(_loop_l->v());
        if (p(a0)) {
          auto _cell = typename List<T1>::Cons(a0, nullptr);
          List<T1> &_node =
              (_write
                   ? *(*_write = std::make_shared<List<T1>>(std::move(_cell)))
                   : _root.emplace(std::move(_cell)));
          _write = &std::get<typename List<T1>::Cons>(_node.v_mut()).l;
          _loop_l = crane_raw(a1);
          continue;
        } else {
          _loop_l = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_root);
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, const T1 &>
  static List<T2> poly_map(F0 &&f, const List<T1> &l) {
    std::optional<List<T2>> _root{};
    std::shared_ptr<List<T2>> *_write = nullptr;
    const List<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
        auto _value = List<T2>::nil();
        (_write ? *(*_write = std::make_shared<List<T2>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(_loop_l->v());
        auto _cell = typename List<T2>::Cons(f(a0), nullptr);
        List<T2> &_node =
            (_write ? *(*_write = std::make_shared<List<T2>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<T2>::Cons>(_node.v_mut()).l;
        _loop_l = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }

  template <typename T1, typename T2>
  static List<std::pair<T1, T2>> poly_zip(const List<T1> &l1,
                                          const List<T2> &l2) {
    std::optional<List<std::pair<T1, T2>>> _root{};
    std::shared_ptr<List<std::pair<T1, T2>>> *_write = nullptr;
    const List<T2> *_loop_l2 = &l2;
    const List<T1> *_loop_l1 = &l1;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l1->v())) {
        auto _value = List<std::pair<T1, T2>>::nil();
        (_write ? *(*_write = std::make_shared<List<std::pair<T1, T2>>>(
                        std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(_loop_l1->v());
        if (std::holds_alternative<typename List<T2>::Nil>(_loop_l2->v())) {
          auto _value = List<std::pair<T1, T2>>::nil();
          (_write ? *(*_write = std::make_shared<List<std::pair<T1, T2>>>(
                          std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          const auto &[a00, a10] =
              std::get<typename List<T2>::Cons>(_loop_l2->v());
          auto _cell = typename List<std::pair<T1, T2>>::Cons(
              std::make_pair(a0, a00), nullptr);
          List<std::pair<T1, T2>> &_node =
              (_write ? *(*_write = std::make_shared<List<std::pair<T1, T2>>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write =
              &std::get<typename List<std::pair<T1, T2>>::Cons>(_node.v_mut())
                   .l;
          _loop_l2 = crane_raw(a10);
          _loop_l1 = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_root);
  }

  template <typename T1, typename T2>
  static std::pair<List<T1>, List<T2>>
  poly_unzip(const List<std::pair<T1, T2>>
                 &l) { /// CraneEnter: captures varying parameters for each
                       /// recursive call.

    struct CraneEnter {
      const List<std::pair<T1, T2>> *l;
    };

    /// CraneCont_a: saves [a, b], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_a {
      T1 a;
      T2 b;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_a>;
    std::pair<List<T1>, List<T2>> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified poly_unzip: CraneEnter -> CraneCont_a.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<std::pair<T1, T2>> &l = *_f.l;
        if (std::holds_alternative<typename List<std::pair<T1, T2>>::Nil>(
                l.v())) {
          _result = std::make_pair(List<T1>::nil(), List<T2>::nil());
        } else {
          const auto &[a0, a1] =
              std::get<typename List<std::pair<T1, T2>>::Cons>(l.v());
          const auto &[a, b] = a0;
          _stack.emplace_back(CraneCont_a{a, b});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_a>(_frame));
        auto a = std::move(_f.a);
        auto b = std::move(_f.b);
        auto [as_, bs] = std::move(_result);
        _result = std::make_pair(List<T1>::cons(a, std::move(as_)),
                                 List<T2>::cons(b, std::move(bs)));
      }
    }
    return _result;
  }

  template <typename T1, typename F0>
  static std::pair<List<T1>, List<T1>>
  poly_partition(F0 &&p,
                 const List<T1> &l) { /// CraneEnter: captures varying
                                      /// parameters for each recursive call.

    struct CraneEnter {
      const List<T1> *l;
    };

    /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_Cons {
      T1 a0;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    std::pair<List<T1>, List<T1>> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified poly_partition: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<T1> &l = *_f.l;
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          _result = std::make_pair(List<T1>::nil(), List<T1>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
          _stack.emplace_back(CraneCont_Cons{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        auto a0 = std::move(_f.a0);
        auto [trues, falses] = std::move(_result);
        if (p(a0)) {
          _result = std::make_pair(List<T1>::cons(a0, std::move(trues)),
                                   std::move(falses));
        } else {
          _result = std::make_pair(std::move(trues),
                                   List<T1>::cons(a0, std::move(falses)));
        }
      }
    }
    return _result;
  }

  template <typename T1, typename F0>
  static bool poly_member(F0 &&eq, const T1 &x, const List<T1> &l) {
    const List<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
        return false;
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(_loop_l->v());
        if (eq(x, a0)) {
          return true;
        } else {
          _loop_l = crane_raw(a1);
        }
      }
    }
  }

  template <typename T1>
  static List<T1> poly_replicate(uint64_t n, const T1 &x) {
    std::optional<List<T1>> _root{};
    std::shared_ptr<List<T1>> *_write = nullptr;
    uint64_t _loop_n = n;
    while (true) {
      if (_loop_n <= 0) {
        auto _value = List<T1>::nil();
        (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        uint64_t n_ = _loop_n - 1;
        auto _cell = typename List<T1>::Cons(x, nullptr);
        List<T1> &_node =
            (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<T1>::Cons>(_node.v_mut()).l;
        _loop_n = n_;
        continue;
      }
    }
    return std::move(*_root);
  }

  static uint64_t nat_length(const List<uint64_t> &x0_);
  static List<uint64_t> nat_reverse(const List<uint64_t> &x0_);
  static List<uint64_t> nat_append(const List<uint64_t> &x0_,
                                   const List<uint64_t> &x1_);
  static std::optional<uint64_t> nat_last(const List<uint64_t> &x0_);
  static List<uint64_t> nat_take(uint64_t x0_, const List<uint64_t> &x1_);
  static List<uint64_t> nat_drop(uint64_t x0_, const List<uint64_t> &x1_);
  static std::optional<uint64_t> nat_nth(uint64_t x0_,
                                         const List<uint64_t> &x1_);
  static bool nat_eq(uint64_t x0_, uint64_t x1_);
  static bool is_even(uint64_t x);

  template <typename F0>
  static List<uint64_t> nat_filter(F0 &&x0_, const List<uint64_t> &x1_) {
    return poly_filter<uint64_t>(x0_, x1_);
  }

  template <typename F0>
  static List<uint64_t> nat_map(F0 &&x0_, const List<uint64_t> &x1_) {
    return poly_map<uint64_t, uint64_t>(x0_, x1_);
  }

  template <typename F0>
  static std::pair<List<uint64_t>, List<uint64_t>>
  nat_partition(F0 &&x0_, const List<uint64_t> &x1_) {
    return poly_partition<uint64_t>(x0_, x1_);
  }

  static bool nat_member(uint64_t x0_, const List<uint64_t> &x1_);
  static List<uint64_t> nat_replicate(uint64_t x0_, uint64_t x1_);
};

#endif // INCLUDED_LOOPIFY_POLYMORPHIC
