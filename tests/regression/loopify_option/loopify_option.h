#ifndef INCLUDED_LOOPIFY_OPTION
#define INCLUDED_LOOPIFY_OPTION

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

struct LoopifyOption {
  template <typename A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      A a;
      std::shared_ptr<list<A>> l;
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

    template <typename CraneU>
    list(const list<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename list<CraneU>::Nil>(
                    _other.v())) {
              return Nil{};
            } else {
              const auto &[a, l] =
                  std::get<typename list<CraneU>::Cons>(_other.v());
              return Cons{
                  [&]() -> A {
                    if constexpr (crane_convertible<A, const CraneU &>) {
                      return crane_convert<A>(a);
                    } else {
                      throw std::logic_error(
                          "unreachable: inactive constructor field at this "
                          "instantiation");
                    }
                  }(),
                  (l ? std::make_shared<list<A>>(crane_convert<list<A>>(*l))
                     : nullptr)};
            }
          }()) {}

    static list<A> nil() { return list<A>(Nil{}); }

    static list<A> cons(A a, list<A> l) {
      return list<A>(
          Cons{std::move(a), std::make_shared<list<A>>(std::move(l))});
    }

    // MANIPULATORS
    ~list() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<list<A>> {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
          if (_alt->l && _alt->l.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->l);
          }
        }
        return nullptr;
      };
      std::shared_ptr<list<A>> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    list(const list &) = default;
    list &operator=(const list &) = default;
    list(list &&) = default;
    list &operator=(list &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
  static T2
  list_rect(T2 f, F1 &&f0,
            const list<T1> &l) { /// CraneEnter: captures varying parameters for
                                 /// each recursive call.

    struct CraneEnter {
      const list<T1> *l;
    };

    /// CraneCont_Cons: saves [a0, a1], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Cons {
      T1 a0;
      std::shared_ptr<list<T1>> a1;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    T2 _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified list_rect: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const list<T1> &l = *_f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = f;
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(CraneCont_Cons{a0, a1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        auto a0 = std::move(_f.a0);
        std::shared_ptr<list<T1>> a1 = std::move(_f.a1);
        _result = f0(a0, *a1, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename F1>
  static T2 list_rec(const T2 &f, F1 &&f0, const list<T1> &l) {
    return list_rect<T1, T2>(f, f0, l);
  }

  /// find_opt p l returns the first element satisfying p, or None.
  template <typename T1, typename F0>
  static std::optional<T1> find_opt(F0 &&p, const list<T1> &l) {
    const list<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        return std::optional<T1>();
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        if (p(a0)) {
          return std::make_optional<T1>(a0);
        } else {
          _loop_l = crane_raw(a1);
        }
      }
    }
  }

  /// last_opt l returns the last element, or None for empty.
  template <typename T1> static std::optional<T1> last_opt(const list<T1> &l) {
    const list<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        return std::optional<T1>();
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename list<T1>::Nil>(_sv.v())) {
          return std::make_optional<T1>(a0);
        } else {
          _loop_l = crane_raw(a1);
        }
      }
    }
  }

  /// nth_opt n l returns the nth element, or None for out of bounds.
  template <typename T1>
  static std::optional<T1> nth_opt(uint64_t n, const list<T1> &l) {
    const list<T1> *_loop_l = &l;
    uint64_t _loop_n = n;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        return std::optional<T1>();
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
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

  /// lookup_opt key l looks up key in an association list.
  static std::optional<uint64_t>
  lookup_opt(uint64_t key, const list<std::pair<uint64_t, uint64_t>> &l);

  /// map_opt f l applies f and keeps only Some results.
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<std::optional<T2>, F0 &, const T1 &>
  static list<T2> map_opt(F0 &&f, const list<T1> &l) {
    std::optional<list<T2>> _root{};
    std::shared_ptr<list<T2>> *_write = nullptr;
    const list<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        auto _value = list<T2>::nil();
        (_write ? *(*_write = std::make_shared<list<T2>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        auto _cs = f(a0);
        if (_cs.has_value()) {
          const T2 &y = *_cs;
          auto _cell = typename list<T2>::Cons(y, nullptr);
          list<T2> &_node =
              (_write
                   ? *(*_write = std::make_shared<list<T2>>(std::move(_cell)))
                   : _root.emplace(std::move(_cell)));
          _write = &std::get<typename list<T2>::Cons>(_node.v_mut()).l;
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

  /// find_index p l returns the index of the first match, or None.
  template <typename T1, typename F0>
  static std::optional<uint64_t> find_index_aux(F0 &&p, const list<T1> &l,
                                                uint64_t i) {
    uint64_t _loop_i = i;
    const list<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        return std::optional<uint64_t>();
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        if (p(a0)) {
          return std::make_optional<uint64_t>(_loop_i);
        } else {
          _loop_i = (_loop_i + 1);
          _loop_l = crane_raw(a1);
        }
      }
    }
  }

  template <typename T1, typename F0>
  static std::optional<uint64_t> find_index(F0 &&p, const list<T1> &l) {
    return find_index_aux<T1>(p, l, UINT64_C(0));
  }
};

#endif // INCLUDED_LOOPIFY_OPTION
