#ifndef INCLUDED_LOOPIFY_LIST_GENERATORS
#define INCLUDED_LOOPIFY_LIST_GENERATORS

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

  uint64_t length() const {
    const List<A> *_self = this;

    /// CraneEnter: captures varying parameters for each recursive call.
    struct CraneEnter {
      const List<A> *_self;
    };

    /// CraneCont_Cons: resumes after recursive call, then processes rest.
    struct CraneCont_Cons {};

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    uint64_t _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{_self});
    /// Loopified length: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(CraneCont_Cons{});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }

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

struct LoopifyListGenerators {
  static List<uint64_t> cycle_fuel(uint64_t fuel, uint64_t n,
                                   const List<uint64_t> &l);
  static List<uint64_t> cycle(uint64_t n, const List<uint64_t> &l);

  template <typename F0>
  static List<uint64_t> iterate(F0 &&f, uint64_t n, uint64_t x) {
    std::optional<List<uint64_t>> _root{};
    std::shared_ptr<List<uint64_t>> *_write = nullptr;
    uint64_t _loop_x = std::move(x);
    uint64_t _loop_n = std::move(n);
    while (true) {
      if (_loop_n <= 0) {
        auto _value = List<uint64_t>::nil();
        (_write
             ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        uint64_t n_ = _loop_n - 1;
        auto _cell = typename List<uint64_t>::Cons(_loop_x, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_x = f(_loop_x);
        _loop_n = n_;
        continue;
      }
    }
    return std::move(*_root);
  }

  template <typename F2>
  static List<uint64_t> build_list_aux(uint64_t n, uint64_t idx, F2 &&f) {
    std::optional<List<uint64_t>> _root{};
    std::shared_ptr<List<uint64_t>> *_write = nullptr;
    uint64_t _loop_idx = std::move(idx);
    uint64_t _loop_n = std::move(n);
    while (true) {
      if (_loop_n <= 0) {
        auto _value = List<uint64_t>::nil();
        (_write
             ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        uint64_t n_ = _loop_n - 1;
        auto _cell = typename List<uint64_t>::Cons(f(_loop_idx), nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_idx = (_loop_idx + UINT64_C(1));
        _loop_n = n_;
        continue;
      }
    }
    return std::move(*_root);
  }

  template <typename F1> static List<uint64_t> build_list(uint64_t n, F1 &&f) {
    return build_list_aux(n, UINT64_C(0), f);
  }

  template <typename F1> static List<uint64_t> init_list(uint64_t n, F1 &&f) {
    if (n <= 0) {
      return List<uint64_t>::nil();
    } else {
      uint64_t n_ = n - 1;
      return List<uint64_t>::cons(f(UINT64_C(0)), [&]() {
        auto go_impl = [&](auto &, uint64_t i) -> List<uint64_t> {
          /// CraneEnter: captures varying parameters for each recursive call.
          struct CraneEnter {
            uint64_t i;
          };
          /// CraneCont_i_: saves [f, i, n], resumes after recursive call, then
          /// processes rest.
          struct CraneCont_i_ {
            std::decay_t<F1> f;
            uint64_t i;
            uint64_t n;
          };
          using CraneFrame = std::variant<CraneEnter, CraneCont_i_>;
          List<uint64_t> _result{};
          crane::small_vector<CraneFrame> _stack;
          _stack.emplace_back(CraneEnter{i});
          /// Loopified go: CraneEnter -> CraneCont_i_.
          while (!_stack.empty()) {
            CraneFrame _frame = std::move(_stack.back());
            _stack.pop_back();
            if (std::holds_alternative<CraneEnter>(_frame)) {
              auto _f = std::move(std::get<CraneEnter>(_frame));
              uint64_t i = _f.i;
              if (i <= 0) {
                _result = List<uint64_t>::nil();
              } else {
                uint64_t i_ = i - 1;
                _stack.emplace_back(CraneCont_i_{f, i, n});
                _stack.emplace_back(CraneEnter{i_});
              }
            } else {
              auto _f = std::move(std::get<CraneCont_i_>(_frame));
              std::decay_t<F1> f = std::move(_f.f);
              uint64_t i = _f.i;
              uint64_t n = _f.n;
              _result = List<uint64_t>::cons(f((((n - i) > n ? 0 : (n - i)))),
                                             std::move(_result));
            }
          }
          return _result;
        };
        auto go = [&](uint64_t i) -> List<uint64_t> {
          return go_impl(go_impl, i);
        };
        return go(n_);
      }());
    }
  }

  static List<uint64_t> range(uint64_t start, uint64_t count);
  static List<uint64_t> replicate_elem(uint64_t n, uint64_t x);
  static List<uint64_t> replicate_each(uint64_t n, const List<uint64_t> &l);

  template <typename F1> static List<uint64_t> tabulate(uint64_t n, F1 &&f) {
    if (n <= 0) {
      return List<uint64_t>::nil();
    } else {
      uint64_t n_ = n - 1;
      auto aux_impl = [&](auto &, uint64_t idx) -> List<uint64_t> {
        /// CraneEnter: captures varying parameters for each recursive call.
        struct CraneEnter {
          uint64_t idx;
        };
        /// CraneCont_idx_: saves [f, idx], resumes after recursive call, then
        /// processes rest.
        struct CraneCont_idx_ {
          std::decay_t<F1> f;
          uint64_t idx;
        };
        using CraneFrame = std::variant<CraneEnter, CraneCont_idx_>;
        List<uint64_t> _result{};
        crane::small_vector<CraneFrame> _stack;
        _stack.emplace_back(CraneEnter{idx});
        /// Loopified aux: CraneEnter -> CraneCont_idx_.
        while (!_stack.empty()) {
          CraneFrame _frame = std::move(_stack.back());
          _stack.pop_back();
          if (std::holds_alternative<CraneEnter>(_frame)) {
            auto _f = std::move(std::get<CraneEnter>(_frame));
            uint64_t idx = _f.idx;
            if (idx <= 0) {
              _result =
                  List<uint64_t>::cons(f(UINT64_C(0)), List<uint64_t>::nil());
            } else {
              uint64_t idx_ = idx - 1;
              _stack.emplace_back(CraneCont_idx_{f, idx});
              _stack.emplace_back(CraneEnter{idx_});
            }
          } else {
            auto _f = std::move(std::get<CraneCont_idx_>(_frame));
            std::decay_t<F1> f = std::move(_f.f);
            uint64_t idx = _f.idx;
            _result = std::move(_result).app(
                List<uint64_t>::cons(f(idx), List<uint64_t>::nil()));
          }
        }
        return _result;
      };
      auto aux = [&](uint64_t idx) -> List<uint64_t> {
        return aux_impl(aux_impl, idx);
      };
      return aux(n_);
    }
  }

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, const uint64_t &,
                                   const uint64_t &>
  static List<uint64_t> zip_with(F0 &&f, const List<uint64_t> &l1,
                                 const List<uint64_t> &l2) {
    std::optional<List<uint64_t>> _root{};
    std::shared_ptr<List<uint64_t>> *_write = nullptr;
    const List<uint64_t> *_loop_l2 = &l2;
    const List<uint64_t> *_loop_l1 = &l1;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l1->v())) {
        auto _value = List<uint64_t>::nil();
        (_write
             ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l1->v());
        if (std::holds_alternative<typename List<uint64_t>::Nil>(
                _loop_l2->v())) {
          auto _value = List<uint64_t>::nil();
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(_loop_l2->v());
          auto _cell = typename List<uint64_t>::Cons(f(a0, a00), nullptr);
          List<uint64_t> &_node =
              (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
          _loop_l2 = crane_raw(a10);
          _loop_l1 = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_root);
  }

  static List<std::pair<uint64_t, uint64_t>>
  enumerate_aux(uint64_t idx, const List<uint64_t> &l);

  static List<std::pair<uint64_t, uint64_t>> enumerate(const List<uint64_t> &l);
};

#endif // INCLUDED_LOOPIFY_LIST_GENERATORS
