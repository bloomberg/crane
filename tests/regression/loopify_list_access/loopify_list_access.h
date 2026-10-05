#ifndef INCLUDED_LOOPIFY_LIST_ACCESS
#define INCLUDED_LOOPIFY_LIST_ACCESS

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
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
};

struct LoopifyListAccess {
  static uint64_t nth(uint64_t n, const List<uint64_t> &l);
  static uint64_t last(const List<uint64_t> &l);
  static uint64_t index_of_aux(uint64_t x, const List<uint64_t> &l,
                               uint64_t idx);
  static uint64_t index_of(uint64_t x, const List<uint64_t> &l);
  static bool member(uint64_t x, const List<uint64_t> &l);
  static uint64_t lookup(uint64_t key,
                         const List<std::pair<uint64_t, uint64_t>> &l);
  static List<uint64_t>
  lookup_all(uint64_t key, const List<std::pair<uint64_t, uint64_t>> &l);

  template <typename F0> static uint64_t find(F0 &&p, const List<uint64_t> &l) {
    const List<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        if (p(a0)) {
          return a0;
        } else {
          _loop_l = crane_raw(a1);
        }
      }
    }
  }

  static uint64_t count(uint64_t x, const List<uint64_t> &l);

  template <typename F0>
  static uint64_t count_matching(
      F0 &&p, const List<uint64_t> &l) { /// CraneEnter: captures varying
                                         /// parameters for each recursive call.

    struct CraneEnter {
      const List<uint64_t> *l;
    };

    /// CraneCont1: resumes after recursive call, then processes rest.
    struct CraneCont1 {};

    using CraneFrame = std::variant<CraneEnter, CraneCont1>;
    uint64_t _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified count_matching: CraneEnter -> CraneCont1.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          if (p(a0)) {
            _stack.emplace_back(CraneCont1{});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          } else {
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        }
      } else {
        auto _f = std::move(std::get<CraneCont1>(_frame));
        _result = (UINT64_C(1) + std::move(_result));
      }
    }
    return _result;
  }

  static bool elem_at_eq(uint64_t idx, uint64_t val, const List<uint64_t> &l);
  static uint64_t nth_default(uint64_t n, uint64_t default0,
                              const List<uint64_t> &l);
};

#endif // INCLUDED_LOOPIFY_LIST_ACCESS
