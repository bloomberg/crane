#ifndef INCLUDED_LOOPIFY_SWITCH_BREAK
#define INCLUDED_LOOPIFY_SWITCH_BREAK

#include <any>
#include <memory>
#include <utility>
#include <variant>
#include <vector>

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

  template <typename _U> explicit List(const List<_U> &_other) {
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

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack = {};
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
        _drain(_cur->v_mut());
      }
    }
  }

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

  template <typename T1> static T1 tag_rec(T1 f, T1 f0, T1 f1, Tag t) {
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
