#ifndef INCLUDED_COINDUCTIVE
#define INCLUDED_COINDUCTIVE

#include "lazy.h"
#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct Coinductive {
  struct stream {
    // TYPES
    struct Cons {
      unsigned int d_a0;
      std::shared_ptr<stream> d_a1;
    };

    using variant_t = std::variant<Cons>;

  private:
    // DATA
    crane::lazy<variant_t> d_lazyV_;

  public:
    // CREATORS
    explicit stream(Cons _v)
        : d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit stream(std::function<variant_t()> _thunk)
        : d_lazyV_(crane::lazy<variant_t>(std::move(_thunk))) {}

    __attribute__((pure)) static stream cons(unsigned int a0,
                                             const stream &a1) {
      return stream(Cons{std::move(a0), std::make_shared<stream>(a1)});
    }

    __attribute__((pure)) static stream lazy_(std::function<stream()> thunk) {
      return stream(std::function<variant_t()>([=]() mutable -> variant_t {
        stream _tmp = thunk();
        return _tmp.v();
      }));
    }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const {
      return d_lazyV_.force();
    }
  };

  __attribute__((pure)) static stream zeros();
  __attribute__((pure)) static stream count_from(unsigned int n);
  __attribute__((pure)) static unsigned int hd(const stream s);
  __attribute__((pure)) static stream tl(const stream s);

  template <MapsTo<unsigned int, unsigned int> F0>
  __attribute__((pure)) static stream smap(F0 &&f, const stream s) {
    const auto &[d_a0, d_a1] = std::get<typename stream::Cons>(s.v());
    return stream::lazy_([=]() mutable -> stream {
      return stream::cons(f(d_a0), smap(f, *(d_a1)));
    });
  }

  __attribute__((pure)) static stream interleave(const stream s1,
                                                 const stream s2);
  static inline const stream get_zeros = zeros();
  static inline const stream get_count = count_from(0u);
  static inline const unsigned int test_hd = hd(get_zeros);
  static inline const stream test_count = get_count;

  struct tree {
    // TYPES
    struct Leaf {
      unsigned int d_a0;
    };

    struct Node {
      unsigned int d_a0;
      std::shared_ptr<tree> d_a1;
      std::shared_ptr<tree> d_a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    crane::lazy<variant_t> d_lazyV_;

  public:
    // CREATORS
    explicit tree(Leaf _v)
        : d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit tree(Node _v)
        : d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit tree(std::function<variant_t()> _thunk)
        : d_lazyV_(crane::lazy<variant_t>(std::move(_thunk))) {}

    __attribute__((pure)) static tree leaf(unsigned int a0) {
      return tree(Leaf{std::move(a0)});
    }

    __attribute__((pure)) static tree node(unsigned int a0, const tree &a1,
                                           const tree &a2) {
      return tree(Node{std::move(a0), std::make_shared<tree>(a1),
                       std::make_shared<tree>(a2)});
    }

    __attribute__((pure)) static tree lazy_(std::function<tree()> thunk) {
      return tree(std::function<variant_t()>([=]() mutable -> variant_t {
        tree _tmp = thunk();
        return _tmp.v();
      }));
    }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const {
      return d_lazyV_.force();
    }
  };

  __attribute__((pure)) static tree infinite_tree(unsigned int n);
};

#endif // INCLUDED_COINDUCTIVE
