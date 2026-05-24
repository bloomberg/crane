#ifndef INCLUDED_LOOPIFY_MATCH_ARG
#define INCLUDED_LOOPIFY_MATCH_ARG

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
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct LoopifyMatchArg {
  enum class Cell { WALL, EMPTY, DOT };

  template <typename T1> static T1 cell_rect(T1 f, T1 f0, T1 f1, Cell c) {
    switch (c) {
    case Cell::WALL: {
      return f;
    }
    case Cell::EMPTY: {
      return f0;
    }
    case Cell::DOT: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 cell_rec(T1 f, T1 f0, T1 f1, Cell c) {
    switch (c) {
    case Cell::WALL: {
      return f;
    }
    case Cell::EMPTY: {
      return f0;
    }
    case Cell::DOT: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  /// Count the number of Dot cells in a list.
  /// The match on c inside the Cons branch triggers bug 2.
  static uint64_t count_dots(const List<Cell> &xs);
  /// A plain recursive length — triggers bug 1 (missing <vector>)
  /// when loopify converts it to an explicit-stack loop.
  static uint64_t my_length(const List<Cell> &xs);
};

#endif // INCLUDED_LOOPIFY_MATCH_ARG
