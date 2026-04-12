#ifndef INCLUDED_VISIT_MATCH_BUG
#define INCLUDED_VISIT_MATCH_BUG

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

struct VisitMatchBug {
  struct Tree {
    // TYPES
    struct Leaf {
      unsigned int d_a0;
    };

    struct Node {
      std::shared_ptr<Tree> d_a0;
      unsigned int d_a1;
      std::shared_ptr<Tree> d_a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit Tree(Leaf _v) : d_v_(std::move(_v)) {}

    explicit Tree(Node _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<Tree> leaf(unsigned int a0) {
      return std::make_shared<Tree>(Leaf{std::move(a0)});
    }

    static std::shared_ptr<Tree> node(const std::shared_ptr<Tree> &a0,
                                      unsigned int a1,
                                      const std::shared_ptr<Tree> &a2) {
      return std::make_shared<Tree>(Node{a0, std::move(a1), a2});
    }

    static std::shared_ptr<Tree> node(std::shared_ptr<Tree> &&a0,
                                      unsigned int a1,
                                      std::shared_ptr<Tree> &&a2) {
      return std::make_shared<Tree>(
          Node{std::move(a0), std::move(a1), std::move(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, std::shared_ptr<Tree>, T1, unsigned int,
                   std::shared_ptr<Tree>, T1>
                F1>
  static T1 Tree_rect(F0 &&f, F1 &&f0, const std::shared_ptr<Tree> &t) {
    return std::visit(Overloaded{[&](const typename Tree::Leaf &_args) -> T1 {
                                   return f(_args.d_a0);
                                 },
                                 [&](const typename Tree::Node &_args) -> T1 {
                                   return f0(_args.d_a0,
                                             Tree_rect<T1>(f, f0, _args.d_a0),
                                             _args.d_a1, _args.d_a2,
                                             Tree_rect<T1>(f, f0, _args.d_a2));
                                 }},
                      t->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, std::shared_ptr<Tree>, T1, unsigned int,
                   std::shared_ptr<Tree>, T1>
                F1>
  static T1 Tree_rec(F0 &&f, F1 &&f0, const std::shared_ptr<Tree> &t) {
    return std::visit(Overloaded{[&](const typename Tree::Leaf &_args) -> T1 {
                                   return f(_args.d_a0);
                                 },
                                 [&](const typename Tree::Node &_args) -> T1 {
                                   return f0(_args.d_a0,
                                             Tree_rec<T1>(f, f0, _args.d_a0),
                                             _args.d_a1, _args.d_a2,
                                             Tree_rec<T1>(f, f0, _args.d_a2));
                                 }},
                      t->v());
  }

  static std::shared_ptr<Tree> consume(std::shared_ptr<Tree> t);
  __attribute__((pure)) static unsigned int
  match_after_consume(const std::shared_ptr<Tree> &t);
  __attribute__((pure)) static unsigned int
  match_last_use(const std::shared_ptr<Tree> &t);
  __attribute__((pure)) static unsigned int
  nested_match_consume(const std::shared_ptr<Tree> &t);
  __attribute__((pure)) static unsigned int
  chain_then_match(const std::shared_ptr<Tree> &t1);

  struct State {
    unsigned int value;
    unsigned int data;
  };

  __attribute__((pure)) static unsigned int
  match_extract_field(const std::shared_ptr<State> &s);
  __attribute__((pure)) static unsigned int
  match_extract_two(const std::shared_ptr<State> &s);
  __attribute__((pure)) static unsigned int
  match_nested(const std::shared_ptr<State> &s);
  __attribute__((pure)) static unsigned int
  match_in_tail(const std::shared_ptr<State> &s);
  __attribute__((pure)) static unsigned int
  match_in_expr(const std::shared_ptr<State> &s);
};

#endif // INCLUDED_VISIT_MATCH_BUG
