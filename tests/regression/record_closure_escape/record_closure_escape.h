#ifndef INCLUDED_RECORD_CLOSURE_ESCAPE
#define INCLUDED_RECORD_CLOSURE_ESCAPE

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct RecordClosureEscape {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::unique_ptr<tree> d_a0;
      unsigned int d_a1;
      std::unique_ptr<tree> d_a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : d_v_(_v) {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

    tree(const tree &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    tree(tree &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) tree &operator=(const tree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) tree &operator=(tree &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) tree clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Leaf>(_sv.v())) {
        return tree(Leaf{});
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<Node>(_sv.v());
        return tree(Node{
            d_a0 ? std::make_unique<RecordClosureEscape::tree>(d_a0->clone())
                 : nullptr,
            [](auto &&__v) -> unsigned int {
              if constexpr (
                  requires { __v ? 0 : 0; } && requires { *__v; } &&
                  requires { __v->clone(); } && requires { __v.get(); }) {
                using _E = std::remove_cvref_t<decltype(*__v)>;
                return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
              } else if constexpr (requires { __v.clone(); }) {
                return __v.clone();
              } else {
                return __v;
              }
            }(d_a1),
            d_a2 ? std::make_unique<RecordClosureEscape::tree>(d_a2->clone())
                 : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static tree leaf() { return tree(Leaf{}); }

    __attribute__((pure)) static tree node(const tree &a0, unsigned int a1,
                                           const tree &a2) {
      return tree(Node{std::make_unique<tree>(a0), std::move(a1),
                       std::make_unique<tree>(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) tree *operator->() { return this; }

    __attribute__((pure)) const tree *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = tree(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, tree, T1, unsigned int, tree, T1> F1>
  static T1 tree_rect(const T1 f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t.v());
      return f0(*(d_a0), tree_rect<T1>(f, f0, *(d_a0)), d_a1, *(d_a2),
                tree_rect<T1>(f, f0, *(d_a2)));
    }
  }

  template <typename T1, MapsTo<T1, tree, T1, unsigned int, tree, T1> F1>
  static T1 tree_rec(const T1 f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t.v());
      return f0(*(d_a0), tree_rec<T1>(f, f0, *(d_a0)), d_a1, *(d_a2),
                tree_rec<T1>(f, f0, *(d_a2)));
    }
  }

  __attribute__((pure)) static unsigned int sum_values(const tree &t,
                                                       unsigned int x);

  /// A record holding a closure and a value. Records are single-constructor
  /// inductives and get special treatment in Crane's translation.
  struct fn_record {
    std::function<unsigned int(unsigned int)> fn_field;
    unsigned int val_field;

    __attribute__((pure)) fn_record *operator->() { return this; }

    __attribute__((pure)) const fn_record *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) fn_record clone() const {
      return fn_record{
          (*(this)).fn_field, [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).val_field)};
    }
  };

  /// BUG: Partial application stored in a record field.
  /// The record constructor mk_fn_record stores the & lambda.
  /// return_captures_by_value doesn't handle lambdas inside
  /// record constructor arguments.
  __attribute__((pure)) static fn_record record_escape(tree t);
  __attribute__((pure)) static unsigned int use_record(const fn_record &r);
  /// Clobber stack after record_escape returns.
  static inline const unsigned int bug_record_escape = []() {
    tree t1 = tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                         tree::node(tree::leaf(), 30u, tree::leaf()));
    fn_record r1 = record_escape(t1);
    return use_record(r1);
  }();
};

#endif // INCLUDED_RECORD_CLOSURE_ESCAPE
