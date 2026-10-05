#ifndef INCLUDED_LOOPIFY_ADVANCED_LISTS
#define INCLUDED_LOOPIFY_ADVANCED_LISTS

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
      : v_(crane_convert_spine(
            _other, std::shared_ptr<List<A>>(nullptr),
            [](const List<CraneU> &_cell) -> const List<CraneU> * {
              if (std::holds_alternative<typename List<CraneU>::Cons>(
                      _cell.v())) {
                return std::get<typename List<CraneU>::Cons>(_cell.v()).l.get();
              } else {
                return nullptr;
              }
            },
            [&](const List<CraneU> &_other,
                std::shared_ptr<List<A>> _below) -> variant_t {
              if (std::holds_alternative<typename List<CraneU>::Nil>(
                      _other.v())) {
                return Nil{};
              } else {
                const auto &[a, l] =
                    std::get<typename List<CraneU>::Cons>(_other.v());
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
                    std::move(_below)};
              }
            },
            [](auto &&_alt) {
              return std::make_shared<List<A>>(std::move(_alt));
            })) {}

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

struct LoopifyAdvancedLists {
  static uint64_t product(const List<uint64_t> &l);
  static List<uint64_t> compress(const List<uint64_t> &l);
  static List<uint64_t> pairwise_sum(const List<uint64_t> &l);
  static List<std::pair<uint64_t, uint64_t>>
  group_pairs(const List<uint64_t> &l);
  static List<uint64_t> interleave(List<uint64_t> l1, List<uint64_t> l2);
  static List<uint64_t> concat_lists(const List<List<uint64_t>> &ll);

  template <typename F0>
    requires std::is_invocable_r_v<List<uint64_t>, F0 &, uint64_t &>
  static List<uint64_t>
  flat_map(F0 &&f,
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
    List<uint64_t> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified flat_map: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<uint64_t>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(CraneCont_Cons{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        uint64_t a0 = _f.a0;
        _result = f(a0).app(std::move(_result));
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static bool
  all_satisfy(F0 &&p,
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
    /// Loopified all_satisfy: CraneEnter -> CraneCont_Cons.
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
  any_satisfy(F0 &&p,
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
    /// Loopified any_satisfy: CraneEnter -> CraneCont_Cons.
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
  static std::optional<uint64_t> find_first(F0 &&p, const List<uint64_t> &l) {
    const List<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        return std::optional<uint64_t>();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        if (p(a0)) {
          return std::make_optional<uint64_t>(a0);
        } else {
          _loop_l = crane_raw(a1);
        }
      }
    }
  }
};

#endif // INCLUDED_LOOPIFY_ADVANCED_LISTS
