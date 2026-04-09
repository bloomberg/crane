#ifndef INCLUDED_LOOPIFY_MATCH_ARG
#define INCLUDED_LOOPIFY_MATCH_ARG

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct LoopifyMatchArg {
  enum class Cell { e_WALL, e_EMPTY, e_DOT };

  template <typename T1>
  static T1 cell_rect(const T1 f, const T1 f0, const T1 f1, const Cell c) {
    switch (c) {
    case Cell::e_WALL: {
      return f;
    }
    case Cell::e_EMPTY: {
      return f0;
    }
    case Cell::e_DOT: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 cell_rec(const T1 f, const T1 f0, const T1 f1, const Cell c) {
    switch (c) {
    case Cell::e_WALL: {
      return f;
    }
    case Cell::e_EMPTY: {
      return f0;
    }
    case Cell::e_DOT: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  /// Count the number of Dot cells in a list.
  /// The match on c inside the Cons branch triggers bug 2.
  __attribute__((pure)) static unsigned int
  count_dots(const std::shared_ptr<List<Cell>> &xs);

  /// A plain recursive length — triggers bug 1 (missing <vector>)
  /// when loopify converts it to an explicit-stack loop.
  __attribute__((pure)) static unsigned int
  my_length(const std::shared_ptr<List<Cell>> &xs);
};

#endif // INCLUDED_LOOPIFY_MATCH_ARG
