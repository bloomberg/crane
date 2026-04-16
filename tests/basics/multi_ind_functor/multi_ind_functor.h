#ifndef INCLUDED_MULTI_IND_FUNCTOR
#define INCLUDED_MULTI_IND_FUNCTOR

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <typename M>
concept Elem = requires {
  typename M::t;
  requires(
      requires {
        { M::dflt } -> std::convertible_to<typename M::t>;
      } ||
      requires {
        { M::dflt() } -> std::convertible_to<typename M::t>;
      });
};

template <Elem E> struct Container {
  struct maybe {
    // TYPES
    struct Nothing {};

    struct Just {
      unsigned int d_a0;
    };

    using variant_t = std::variant<Nothing, Just>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit maybe(Nothing _v) : d_v_(_v) {}

    explicit maybe(Just _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<maybe> nothing() {
      return std::make_shared<maybe>(Nothing{});
    }

    static std::shared_ptr<maybe> just(unsigned int a0) {
      return std::make_shared<maybe>(Just{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 maybe_rect(const T1 f, F1 &&f0, const std::shared_ptr<maybe> &m) {
    if (std::holds_alternative<typename maybe::Nothing>(m->v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename maybe::Just>(m->v());
      return f0(d_a0);
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 maybe_rec(const T1 f, F1 &&f0, const std::shared_ptr<maybe> &m) {
    if (std::holds_alternative<typename maybe::Nothing>(m->v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename maybe::Just>(m->v());
      return f0(d_a0);
    }
  }

  struct mlist {
    // TYPES
    struct MNil {};

    struct MCons {
      std::shared_ptr<maybe> d_a0;
      std::shared_ptr<mlist> d_a1;
    };

    using variant_t = std::variant<MNil, MCons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit mlist(MNil _v) : d_v_(_v) {}

    explicit mlist(MCons _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<mlist> mnil() {
      return std::make_shared<mlist>(MNil{});
    }

    static std::shared_ptr<mlist> mcons(const std::shared_ptr<maybe> &a0,
                                        const std::shared_ptr<mlist> &a1) {
      return std::make_shared<mlist>(MCons{a0, a1});
    }

    static std::shared_ptr<mlist> mcons(std::shared_ptr<maybe> &&a0,
                                        std::shared_ptr<mlist> &&a1) {
      return std::make_shared<mlist>(MCons{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1,
            MapsTo<T1, std::shared_ptr<maybe>, std::shared_ptr<mlist>, T1> F1>
  static T1 mlist_rect(const T1 f, F1 &&f0, const std::shared_ptr<mlist> &m) {
    if (std::holds_alternative<typename mlist::MNil>(m->v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename mlist::MCons>(m->v());
      return f0(d_a0, d_a1, mlist_rect<T1>(f, f0, d_a1));
    }
  }

  template <typename T1,
            MapsTo<T1, std::shared_ptr<maybe>, std::shared_ptr<mlist>, T1> F1>
  static T1 mlist_rec(const T1 f, F1 &&f0, const std::shared_ptr<mlist> &m) {
    if (std::holds_alternative<typename mlist::MNil>(m->v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename mlist::MCons>(m->v());
      return f0(d_a0, d_a1, mlist_rec<T1>(f, f0, d_a1));
    }
  }

  struct mtree {
    // TYPES
    struct Leaf {
      std::shared_ptr<maybe> d_a0;
    };

    struct Node {
      std::shared_ptr<mlist> d_a0;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit mtree(Leaf _v) : d_v_(std::move(_v)) {}

    explicit mtree(Node _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<mtree> leaf(const std::shared_ptr<maybe> &a0) {
      return std::make_shared<mtree>(Leaf{a0});
    }

    static std::shared_ptr<mtree> leaf(std::shared_ptr<maybe> &&a0) {
      return std::make_shared<mtree>(Leaf{std::move(a0)});
    }

    static std::shared_ptr<mtree> node(const std::shared_ptr<mlist> &a0) {
      return std::make_shared<mtree>(Node{a0});
    }

    static std::shared_ptr<mtree> node(std::shared_ptr<mlist> &&a0) {
      return std::make_shared<mtree>(Node{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, std::shared_ptr<maybe>> F0,
            MapsTo<T1, std::shared_ptr<mlist>> F1>
  static T1 mtree_rect(F0 &&f, F1 &&f0, const std::shared_ptr<mtree> &m) {
    if (std::holds_alternative<typename mtree::Leaf>(m->v())) {
      const auto &[d_a0] = std::get<typename mtree::Leaf>(m->v());
      return f(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename mtree::Node>(m->v());
      return f0(d_a0);
    }
  }

  template <typename T1, MapsTo<T1, std::shared_ptr<maybe>> F0,
            MapsTo<T1, std::shared_ptr<mlist>> F1>
  static T1 mtree_rec(F0 &&f, F1 &&f0, const std::shared_ptr<mtree> &m) {
    if (std::holds_alternative<typename mtree::Leaf>(m->v())) {
      const auto &[d_a0] = std::get<typename mtree::Leaf>(m->v());
      return f(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename mtree::Node>(m->v());
      return f0(d_a0);
    }
  }

  __attribute__((pure)) static bool
  is_nothing(const std::shared_ptr<maybe> &m) {
    if (std::holds_alternative<typename maybe::Nothing>(m->v())) {
      return true;
    } else {
      return false;
    }
  }

  __attribute__((pure)) static unsigned int
  mlist_length(const std::shared_ptr<mlist> &l) {
    if (std::holds_alternative<typename mlist::MNil>(l->v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename mlist::MCons>(l->v());
      return (mlist_length(d_a1) + 1);
    }
  }

  __attribute__((pure)) static unsigned int
  tree_size(const std::shared_ptr<mtree> &t0) {
    if (std::holds_alternative<typename mtree::Leaf>(t0->v())) {
      const auto &[d_a0] = std::get<typename mtree::Leaf>(t0->v());
      if (is_nothing(d_a0)) {
        return 0u;
      } else {
        return 1u;
      }
    } else {
      const auto &[d_a0] = std::get<typename mtree::Node>(t0->v());
      return mlist_length(d_a0);
    }
  }

  static const std::shared_ptr<maybe> &empty_maybe() {
    static const std::shared_ptr<maybe> v = maybe::nothing();
    return v;
  }

  static const std::shared_ptr<maybe> &some_val() {
    static const std::shared_ptr<maybe> v = maybe::just(42u);
    return v;
  }

  static const std::shared_ptr<mlist> &sample_list() {
    static const std::shared_ptr<mlist> v = mlist::mcons(
        maybe::just(42u), mlist::mcons(maybe::nothing(), mlist::mnil()));
    return v;
  }

  static const std::shared_ptr<mtree> &sample_tree() {
    static const std::shared_ptr<mtree> v = mtree::node(sample_list());
    return v;
  }
};

struct NatElem {
  using t = unsigned int;
  static inline const unsigned int dflt = 42u;
};

static_assert(Elem<NatElem>);
using NatContainer = Container<NatElem>;
const bool test_is_nothing =
    NatContainer::is_nothing(NatContainer::empty_maybe());
const unsigned int test_list_len =
    NatContainer::mlist_length(NatContainer::sample_list());
const unsigned int test_tree_size =
    NatContainer::tree_size(NatContainer::sample_tree());

#endif // INCLUDED_MULTI_IND_FUNCTOR
