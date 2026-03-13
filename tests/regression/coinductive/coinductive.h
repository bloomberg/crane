#ifndef INCLUDED_COINDUCTIVE
#define INCLUDED_COINDUCTIVE

#include "lazy.h"
#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

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

    // CREATORS
    explicit stream(Cons _v)
        : d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit stream(std::function<variant_t()> _thunk)
        : d_lazyV_(crane::lazy<variant_t>(std::move(_thunk))) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<stream> Cons_(unsigned int a0,
                                           const std::shared_ptr<stream> &a1) {
        return std::shared_ptr<stream>(new stream(Cons{a0, a1}));
      }

      static std::unique_ptr<stream>
      Cons_uptr(unsigned int a0, const std::shared_ptr<stream> &a1) {
        return std::unique_ptr<stream>(new stream(Cons{a0, a1}));
      }

      static std::shared_ptr<stream>
      lazy_(std::function<std::shared_ptr<stream>()> thunk) {
        return std::shared_ptr<stream>(new stream(
            std::function<variant_t()>([=](void) mutable -> variant_t {
              std::shared_ptr<stream> _tmp = thunk();
              return _tmp->v();
            })));
      }
    };

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const {
      return d_lazyV_.force();
    }
  };

  static std::shared_ptr<stream> zeros();
  static std::shared_ptr<stream> count_from(const unsigned int n);
  __attribute__((pure)) static unsigned int
  hd(const std::shared_ptr<stream> &s);
  static std::shared_ptr<stream> tl(const std::shared_ptr<stream> &s);

  template <MapsTo<unsigned int, unsigned int> F0>
  static std::shared_ptr<stream> smap(F0 &&f,
                                      const std::shared_ptr<stream> &s) {
    return stream::ctor::lazy_([=](void) mutable -> std::shared_ptr<stream> {
      return std::visit(Overloaded{[&](const typename stream::Cons _args)
                                       -> std::shared_ptr<stream> {
                          unsigned int x = _args.d_a0;
                          std::shared_ptr<stream> xs = _args.d_a1;
                          return stream::ctor::Cons_(f(std::move(x)),
                                                     smap(f, xs));
                        }},
                        s->v());
    });
  }

  static std::shared_ptr<stream> interleave(const std::shared_ptr<stream> &s1,
                                            std::shared_ptr<stream> s2);
  static inline const std::shared_ptr<stream> get_zeros = zeros();
  static inline const std::shared_ptr<stream> get_count = count_from(0u);
  static inline const unsigned int test_hd = hd(get_zeros);
  static inline const std::shared_ptr<stream> test_count = get_count;

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

    // CREATORS
    explicit tree(Leaf _v)
        : d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit tree(Node _v)
        : d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit tree(std::function<variant_t()> _thunk)
        : d_lazyV_(crane::lazy<variant_t>(std::move(_thunk))) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<tree> Leaf_(unsigned int a0) {
        return std::shared_ptr<tree>(new tree(Leaf{a0}));
      }

      static std::shared_ptr<tree> Node_(unsigned int a0,
                                         const std::shared_ptr<tree> &a1,
                                         const std::shared_ptr<tree> &a2) {
        return std::shared_ptr<tree>(new tree(Node{a0, a1, a2}));
      }

      static std::unique_ptr<tree> Leaf_uptr(unsigned int a0) {
        return std::unique_ptr<tree>(new tree(Leaf{a0}));
      }

      static std::unique_ptr<tree> Node_uptr(unsigned int a0,
                                             const std::shared_ptr<tree> &a1,
                                             const std::shared_ptr<tree> &a2) {
        return std::unique_ptr<tree>(new tree(Node{a0, a1, a2}));
      }

      static std::shared_ptr<tree>
      lazy_(std::function<std::shared_ptr<tree>()> thunk) {
        return std::shared_ptr<tree>(
            new tree(std::function<variant_t()>([=](void) mutable -> variant_t {
              std::shared_ptr<tree> _tmp = thunk();
              return _tmp->v();
            })));
      }
    };

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const {
      return d_lazyV_.force();
    }
  };

  static std::shared_ptr<tree> infinite_tree(const unsigned int n);
};

#endif // INCLUDED_COINDUCTIVE
