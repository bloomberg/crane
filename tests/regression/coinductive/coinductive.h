#ifndef INCLUDED_COINDUCTIVE
#define INCLUDED_COINDUCTIVE

#include "fn.h"
#include "lazy.h"
#include <cstdint>
#include <utility>
#include <variant>

struct Coinductive {
  struct stream {
    // TYPES
    template <typename CraneS0 = stream> struct Cons_ {
      uint64_t a0;
      CraneS0 a1;
    };

    using Cons = Cons_<>;
    using variant_t = std::variant<Cons>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    stream() {}

    explicit stream(Cons _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit stream(crane::fn<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static stream cons(uint64_t a0, stream a1) {
      return stream(crane::lazy<variant_t>(
          std::in_place, std::in_place_index<0>, a0, std::move(a1)));
    }

    explicit stream(crane::lazy<variant_t> _cell) : lazy_v_(std::move(_cell)) {}

    template <typename F> static stream lazy_(F &&thunk) {
      return stream(crane::lazy<variant_t>::delegate(std::forward<F>(thunk)));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }

    const crane::lazy<variant_t> &lazy_cell() const { return lazy_v_; }
  };

  static stream zeros();
  static stream count_from(uint64_t n);
  static uint64_t hd(stream s);
  static stream tl(stream s);

  static stream smap(crane::fn<uint64_t(uint64_t)> f, stream s) {
    const auto &[a0, a1] = std::get<typename stream::Cons>(s.v());
    return stream::lazy_(
        [=]() -> stream { return stream::cons(f(a0), smap(f, a1)); });
  }

  static stream interleave(stream s1, stream s2);
  static inline const stream get_zeros = zeros();
  static inline const stream get_count = count_from(UINT64_C(0));
  static inline const uint64_t test_hd = hd(get_zeros);
  static inline const stream test_count = get_count;

  struct tree {
    // TYPES
    struct Leaf {
      uint64_t a0;
    };

    template <typename CraneS0 = tree> struct Node_ {
      uint64_t a0;
      CraneS0 a1;
      CraneS0 a2;
    };

    using Node = Node_<>;
    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit tree(Node _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit tree(crane::fn<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static tree leaf(uint64_t a0) {
      return tree(
          crane::lazy<variant_t>(std::in_place, std::in_place_index<0>, a0));
    }

    static tree node(uint64_t a0, tree a1, tree a2) {
      return tree(crane::lazy<variant_t>(std::in_place, std::in_place_index<1>,
                                         a0, std::move(a1), std::move(a2)));
    }

    explicit tree(crane::lazy<variant_t> _cell) : lazy_v_(std::move(_cell)) {}

    template <typename F> static tree lazy_(F &&thunk) {
      return tree(crane::lazy<variant_t>::delegate(std::forward<F>(thunk)));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }

    const crane::lazy<variant_t> &lazy_cell() const { return lazy_v_; }
  };

  static tree infinite_tree(uint64_t n);
};

#endif // INCLUDED_COINDUCTIVE
