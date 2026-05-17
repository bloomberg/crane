#ifndef INCLUDED_COINDUCTIVE
#define INCLUDED_COINDUCTIVE

#include "lazy.h"
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct Coinductive {
  struct stream {
    // TYPES
    struct Cons {
      unsigned int a0;
      std::shared_ptr<stream> a1;
    };

    using variant_t = std::variant<Cons>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    explicit stream(Cons _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit stream(std::function<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static stream cons(unsigned int a0, const stream &a1) {
      return stream(Cons{a0, std::make_shared<stream>(a1)});
    }

    static stream lazy_(std::function<stream()> thunk) {
      return stream(std::function<variant_t()>([=]() mutable -> variant_t {
        stream _tmp = thunk();
        return _tmp.v();
      }));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }
  };

  static stream zeros();
  static stream count_from(unsigned int n);
  static unsigned int hd(stream s);
  static stream tl(stream s);

  template <typename F0>
    requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &>
  static stream smap(F0 &&f, stream s) {
    const auto &[a0, a1] = std::get<typename stream::Cons>(s.v());
    return stream::lazy_(
        [=]() mutable -> stream { return stream::cons(f(a0), smap(f, *a1)); });
  }

  static stream interleave(stream s1, stream s2);
  static inline const stream get_zeros = zeros();
  static inline const stream get_count = count_from(0u);
  static inline const unsigned int test_hd = hd(get_zeros);
  static inline const stream test_count = get_count;

  struct tree {
    // TYPES
    struct Leaf {
      unsigned int a0;
    };

    struct Node {
      unsigned int a0;
      std::shared_ptr<tree> a1;
      std::shared_ptr<tree> a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    explicit tree(Leaf _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit tree(Node _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit tree(std::function<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static tree leaf(unsigned int a0) { return tree(Leaf{a0}); }

    static tree node(unsigned int a0, const tree &a1, const tree &a2) {
      return tree(
          Node{a0, std::make_shared<tree>(a1), std::make_shared<tree>(a2)});
    }

    static tree lazy_(std::function<tree()> thunk) {
      return tree(std::function<variant_t()>([=]() mutable -> variant_t {
        tree _tmp = thunk();
        return _tmp.v();
      }));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }
  };

  static tree infinite_tree(unsigned int n);
};

#endif // INCLUDED_COINDUCTIVE
