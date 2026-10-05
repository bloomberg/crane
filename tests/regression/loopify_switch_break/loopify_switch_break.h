#ifndef INCLUDED_LOOPIFY_SWITCH_BREAK
#define INCLUDED_LOOPIFY_SWITCH_BREAK

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

struct LoopifySwitchBreak {
  enum class Tag { ADD, MUL, KEEP };

  template <typename T1> static T1 tag_rect(T1 f, T1 f0, T1 f1, Tag t) {
    switch (t) {
    case Tag::ADD: {
      return f;
    }
    case Tag::MUL: {
      return f0;
    }
    case Tag::KEEP: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 tag_rec(const T1 &f, const T1 &f0, const T1 &f1, Tag t) {
    return tag_rect<T1>(f, f0, f1, t);
  }

  /// eval_ops ops acc folds a list of (tag, value) pairs into an accumulator.
  /// Each tag selects a different operation:
  /// Add  -> acc + value
  /// Mul  -> acc * value
  /// Keep -> acc  (ignore value)
  /// The function is structurally recursive on the list, and pattern-matches
  /// on the tag inside the Cons branch.  Crane extracts the tag match as a
  /// switch statement; loopification must emit break after each case.
  static uint64_t eval_ops(const List<std::pair<Tag, uint64_t>> &ops,
                           uint64_t acc);
  /// A variant that builds a result list, so the recursive calls are
  /// non-tail — this forces loopification to use continuation frames
  /// (not just tail-call optimisation), exercising the break path in
  /// non-tail switch branches.
  static List<uint64_t> collect_ops(const List<std::pair<Tag, uint64_t>> &ops,
                                    uint64_t acc);
  /// count_tags tag ops counts how many times a given tag appears.
  /// All three branches of the switch recurse; without break, EQ would
  /// fall through to the next case and produce an incorrect count.
  static uint64_t count_tag(Tag t, const List<std::pair<Tag, uint64_t>> &ops);
};

#endif // INCLUDED_LOOPIFY_SWITCH_BREAK
