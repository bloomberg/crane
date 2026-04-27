#ifndef INCLUDED_MULTI_IND_FUNCTOR
#define INCLUDED_MULTI_IND_FUNCTOR

#include <concepts>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

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
    maybe() {}

    explicit maybe(Nothing _v) : d_v_(_v) {}

    explicit maybe(Just _v) : d_v_(std::move(_v)) {}

    maybe(const maybe &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    maybe(maybe &&_other) : d_v_(std::move(_other.d_v_)) {}

    maybe &operator=(const maybe &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    maybe &operator=(maybe &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) maybe clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Nothing>(_sv.v())) {
        return maybe(Nothing{});
      } else {
        const auto &[d_a0] = std::get<Just>(_sv.v());
        return maybe(Just{d_a0});
      }
    }

    // CREATORS
    constexpr static maybe nothing() { return maybe(Nothing{}); }

    __attribute__((pure)) static maybe just(unsigned int a0) {
      return maybe(Just{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) maybe *operator->() { return this; }

    __attribute__((pure)) const maybe *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = maybe(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 maybe_rect(const T1 f, F1 &&f0, const maybe &m) {
    if (std::holds_alternative<typename maybe::Nothing>(m.v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename maybe::Just>(m.v());
      return f0(d_a0);
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 maybe_rec(const T1 f, F1 &&f0, const maybe &m) {
    if (std::holds_alternative<typename maybe::Nothing>(m.v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename maybe::Just>(m.v());
      return f0(d_a0);
    }
  }

  struct mlist {
    // TYPES
    struct MNil {};

    struct MCons {
      maybe d_a0;
      std::unique_ptr<mlist> d_a1;
    };

    using variant_t = std::variant<MNil, MCons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    mlist() {}

    explicit mlist(MNil _v) : d_v_(_v) {}

    explicit mlist(MCons _v) : d_v_(std::move(_v)) {}

    mlist(const mlist &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    mlist(mlist &&_other) : d_v_(std::move(_other.d_v_)) {}

    mlist &operator=(const mlist &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    mlist &operator=(mlist &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) mlist clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<MNil>(_sv.v())) {
        return mlist(MNil{});
      } else {
        const auto &[d_a0, d_a1] = std::get<MCons>(_sv.v());
        return mlist(
            MCons{d_a0.clone(),
                  d_a1 ? std::make_unique<Container::mlist>(d_a1->clone())
                       : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static mlist mnil() { return mlist(MNil{}); }

    __attribute__((pure)) static mlist mcons(maybe a0, const mlist &a1) {
      return mlist(MCons{std::move(a0), std::make_unique<mlist>(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) mlist *operator->() { return this; }

    __attribute__((pure)) const mlist *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = mlist(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, maybe, mlist, T1> F1>
  static T1 mlist_rect(const T1 f, F1 &&f0, const mlist &m) {
    if (std::holds_alternative<typename mlist::MNil>(m.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename mlist::MCons>(m.v());
      return f0(d_a0, *(d_a1), mlist_rect<T1>(f, f0, *(d_a1)));
    }
  }

  template <typename T1, MapsTo<T1, maybe, mlist, T1> F1>
  static T1 mlist_rec(const T1 f, F1 &&f0, const mlist &m) {
    if (std::holds_alternative<typename mlist::MNil>(m.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename mlist::MCons>(m.v());
      return f0(d_a0, *(d_a1), mlist_rec<T1>(f, f0, *(d_a1)));
    }
  }

  struct mtree {
    // TYPES
    struct Leaf {
      maybe d_a0;
    };

    struct Node {
      mlist d_a0;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    mtree() {}

    explicit mtree(Leaf _v) : d_v_(std::move(_v)) {}

    explicit mtree(Node _v) : d_v_(std::move(_v)) {}

    mtree(const mtree &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    mtree(mtree &&_other) : d_v_(std::move(_other.d_v_)) {}

    mtree &operator=(const mtree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    mtree &operator=(mtree &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) mtree clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Leaf>(_sv.v())) {
        const auto &[d_a0] = std::get<Leaf>(_sv.v());
        return mtree(Leaf{d_a0.clone()});
      } else {
        const auto &[d_a0] = std::get<Node>(_sv.v());
        return mtree(Node{d_a0.clone()});
      }
    }

    // CREATORS
    constexpr static mtree leaf(maybe a0) { return mtree(Leaf{std::move(a0)}); }

    __attribute__((pure)) static mtree node(mlist a0) {
      return mtree(Node{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) mtree *operator->() { return this; }

    __attribute__((pure)) const mtree *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = mtree(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, maybe> F0, MapsTo<T1, mlist> F1>
  static T1 mtree_rect(F0 &&f, F1 &&f0, const mtree &m) {
    if (std::holds_alternative<typename mtree::Leaf>(m.v())) {
      const auto &[d_a0] = std::get<typename mtree::Leaf>(m.v());
      return f(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename mtree::Node>(m.v());
      return f0(d_a0);
    }
  }

  template <typename T1, MapsTo<T1, maybe> F0, MapsTo<T1, mlist> F1>
  static T1 mtree_rec(F0 &&f, F1 &&f0, const mtree &m) {
    if (std::holds_alternative<typename mtree::Leaf>(m.v())) {
      const auto &[d_a0] = std::get<typename mtree::Leaf>(m.v());
      return f(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename mtree::Node>(m.v());
      return f0(d_a0);
    }
  }

  constexpr static bool is_nothing(const maybe &m) {
    if (std::holds_alternative<typename maybe::Nothing>(m.v())) {
      return true;
    } else {
      return false;
    }
  }

  __attribute__((pure)) static unsigned int mlist_length(const mlist &l) {
    if (std::holds_alternative<typename mlist::MNil>(l.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename mlist::MCons>(l.v());
      return (mlist_length(*(d_a1)) + 1);
    }
  }

  __attribute__((pure)) static unsigned int tree_size(const mtree &t0) {
    if (std::holds_alternative<typename mtree::Leaf>(t0.v())) {
      const auto &[d_a0] = std::get<typename mtree::Leaf>(t0.v());
      if (is_nothing(d_a0)) {
        return 0u;
      } else {
        return 1u;
      }
    } else {
      const auto &[d_a0] = std::get<typename mtree::Node>(t0.v());
      return mlist_length(d_a0);
    }
  }

  static const maybe &empty_maybe() {
    static const maybe v = maybe::nothing();
    return v;
  }

  static const maybe &some_val() {
    static const maybe v = maybe::just(42u);
    return v;
  }

  static const mlist &sample_list() {
    static const mlist v = mlist::mcons(
        maybe::just(42u), mlist::mcons(maybe::nothing(), mlist::mnil()));
    return v;
  }

  static const mtree &sample_tree() {
    static const mtree v = mtree::node(sample_list());
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
