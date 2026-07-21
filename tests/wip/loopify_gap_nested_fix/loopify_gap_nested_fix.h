#ifndef INCLUDED_LOOPIFY_GAP_NESTED_FIX
#define INCLUDED_LOOPIFY_GAP_NESTED_FIX

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

struct LoopifyGapNestedFix {
  struct rose {
    // TYPES
    struct Rose0 {
      uint64_t a0;
      std::shared_ptr<List<rose>> a1;
    };

    using variant_t = std::variant<Rose0>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    rose() {}

    explicit rose(Rose0 _v) : v_(std::move(_v)) {}

    static rose rose0(uint64_t a0, List<rose> a1) {
      return rose(Rose0{a0, std::make_shared<List<rose>>(std::move(a1))});
    }

    // MANIPULATORS
    ~rose() {
      std::vector<std::shared_ptr<rose>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Rose0>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            auto *_lp = _alt->a1.get();
            while (
                std::holds_alternative<typename List<rose>::Cons>(_lp->v())) {
              auto &_lc = std::get<typename List<rose>::Cons>(_lp->v_mut());
              _stack.push_back(std::make_shared<rose>(std::move(_lc.a)));
              if (_lc.l) {
                _lp = _lc.l.get();
              } else {
                break;
              }
            }
            _alt->a1.reset();
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

  static uint64_t rose_sum(const rose &r);
  /// A fixed sample tree so the test driver need not build list rose in C++.
  /// Sum of all labels: 1 + 2 + 3 + 4 = 10.
  static inline const rose sample_tree = rose::rose0(
      UINT64_C(1),
      List<rose>::cons(
          rose::rose0(UINT64_C(2), List<rose>::nil()),
          List<rose>::cons(
              rose::rose0(
                  UINT64_C(3),
                  List<rose>::cons(rose::rose0(UINT64_C(4), List<rose>::nil()),
                                   List<rose>::nil())),
              List<rose>::nil())));

  static uint64_t rose_sum_sample(std::monostate _x);
};

#endif // INCLUDED_LOOPIFY_GAP_NESTED_FIX
