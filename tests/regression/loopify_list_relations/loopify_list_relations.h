#ifndef INCLUDED_LOOPIFY_LIST_RELATIONS
#define INCLUDED_LOOPIFY_LIST_RELATIONS

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

struct LoopifyListRelations {
  static bool is_prefix_of(const List<uint64_t> &l1, const List<uint64_t> &l2);
  static bool is_suffix_of(const List<uint64_t> &l1, const List<uint64_t> &l2);
  static bool is_infix_of_aux(const List<uint64_t> &needle,
                              const List<uint64_t> &haystack);
  static bool is_infix_of(const List<uint64_t> &x0_, const List<uint64_t> &x1_);
  static List<uint64_t> find_sublists_aux(const List<uint64_t> &needle,
                                          const List<uint64_t> &haystack,
                                          uint64_t idx);
  static List<uint64_t> find_sublists(const List<uint64_t> &needle,
                                      const List<uint64_t> &haystack);
  static bool list_eq(const List<uint64_t> &l1, const List<uint64_t> &l2);
  static uint64_t list_compare(const List<uint64_t> &l1,
                               const List<uint64_t> &l2);
  static List<std::pair<uint64_t, uint64_t>> zip(const List<uint64_t> &l1,
                                                 const List<uint64_t> &l2);
  static List<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>
  zip3(const List<uint64_t> &l1, const List<uint64_t> &l2,
       const List<uint64_t> &l3);
  static List<uint64_t> interleave(const List<uint64_t> &l1,
                                   const List<uint64_t> &l2);
  static List<uint64_t> merge_fuel(uint64_t fuel, const List<uint64_t> &l1,
                                   const List<uint64_t> &l2);
  static List<uint64_t> merge(const List<uint64_t> &l1,
                              const List<uint64_t> &l2);
  static List<uint64_t> union_(const List<uint64_t> &l1, List<uint64_t> l2);
  static List<uint64_t> intersection(const List<uint64_t> &l1,
                                     const List<uint64_t> &l2);
};

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
};

#endif // INCLUDED_LOOPIFY_LIST_RELATIONS
