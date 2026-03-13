#ifndef INCLUDED_MULTI_IND_FUNCTOR
#define INCLUDED_MULTI_IND_FUNCTOR

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

    // CREATORS
    explicit maybe(Nothing _v) : d_v_(std::move(_v)) {}

    explicit maybe(Just _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<maybe> Nothing_() {
        return std::shared_ptr<maybe>(new maybe(Nothing{}));
      }

      static std::shared_ptr<maybe> Just_(unsigned int a0) {
        return std::shared_ptr<maybe>(new maybe(Just{a0}));
      }

      static std::unique_ptr<maybe> Nothing_uptr() {
        return std::unique_ptr<maybe>(new maybe(Nothing{}));
      }

      static std::unique_ptr<maybe> Just_uptr(unsigned int a0) {
        return std::unique_ptr<maybe>(new maybe(Just{a0}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 maybe_rect(const T1 f, F1 &&f0, const std::shared_ptr<maybe> &m) {
    return std::visit(
        Overloaded{[&](const typename maybe::Nothing _args) -> T1 { return f; },
                   [&](const typename maybe::Just _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     return f0(std::move(n));
                   }},
        m->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 maybe_rec(const T1 f, F1 &&f0, const std::shared_ptr<maybe> &m) {
    return std::visit(
        Overloaded{[&](const typename maybe::Nothing _args) -> T1 { return f; },
                   [&](const typename maybe::Just _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     return f0(std::move(n));
                   }},
        m->v());
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

    // CREATORS
    explicit mlist(MNil _v) : d_v_(std::move(_v)) {}

    explicit mlist(MCons _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<mlist> MNil_() {
        return std::shared_ptr<mlist>(new mlist(MNil{}));
      }

      static std::shared_ptr<mlist> MCons_(const std::shared_ptr<maybe> &a0,
                                           const std::shared_ptr<mlist> &a1) {
        return std::shared_ptr<mlist>(new mlist(MCons{a0, a1}));
      }

      static std::unique_ptr<mlist> MNil_uptr() {
        return std::unique_ptr<mlist>(new mlist(MNil{}));
      }

      static std::unique_ptr<mlist>
      MCons_uptr(const std::shared_ptr<maybe> &a0,
                 const std::shared_ptr<mlist> &a1) {
        return std::unique_ptr<mlist>(new mlist(MCons{a0, a1}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1,
            MapsTo<T1, std::shared_ptr<maybe>, std::shared_ptr<mlist>, T1> F1>
  static T1 mlist_rect(const T1 f, F1 &&f0, const std::shared_ptr<mlist> &m) {
    return std::visit(
        Overloaded{[&](const typename mlist::MNil _args) -> T1 { return f; },
                   [&](const typename mlist::MCons _args) -> T1 {
                     std::shared_ptr<maybe> m0 = _args.d_a0;
                     std::shared_ptr<mlist> m1 = _args.d_a1;
                     return f0(std::move(m0), m1, mlist_rect<T1>(f, f0, m1));
                   }},
        m->v());
  }

  template <typename T1,
            MapsTo<T1, std::shared_ptr<maybe>, std::shared_ptr<mlist>, T1> F1>
  static T1 mlist_rec(const T1 f, F1 &&f0, const std::shared_ptr<mlist> &m) {
    return std::visit(
        Overloaded{[&](const typename mlist::MNil _args) -> T1 { return f; },
                   [&](const typename mlist::MCons _args) -> T1 {
                     std::shared_ptr<maybe> m0 = _args.d_a0;
                     std::shared_ptr<mlist> m1 = _args.d_a1;
                     return f0(std::move(m0), m1, mlist_rec<T1>(f, f0, m1));
                   }},
        m->v());
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

    // CREATORS
    explicit mtree(Leaf _v) : d_v_(std::move(_v)) {}

    explicit mtree(Node _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<mtree> Leaf_(const std::shared_ptr<maybe> &a0) {
        return std::shared_ptr<mtree>(new mtree(Leaf{a0}));
      }

      static std::shared_ptr<mtree> Node_(const std::shared_ptr<mlist> &a0) {
        return std::shared_ptr<mtree>(new mtree(Node{a0}));
      }

      static std::unique_ptr<mtree>
      Leaf_uptr(const std::shared_ptr<maybe> &a0) {
        return std::unique_ptr<mtree>(new mtree(Leaf{a0}));
      }

      static std::unique_ptr<mtree>
      Node_uptr(const std::shared_ptr<mlist> &a0) {
        return std::unique_ptr<mtree>(new mtree(Node{a0}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, std::shared_ptr<maybe>> F0,
            MapsTo<T1, std::shared_ptr<mlist>> F1>
  static T1 mtree_rect(F0 &&f, F1 &&f0, const std::shared_ptr<mtree> &m) {
    return std::visit(Overloaded{[&](const typename mtree::Leaf _args) -> T1 {
                                   std::shared_ptr<maybe> m0 = _args.d_a0;
                                   return f(std::move(m0));
                                 },
                                 [&](const typename mtree::Node _args) -> T1 {
                                   std::shared_ptr<mlist> m0 = _args.d_a0;
                                   return f0(std::move(m0));
                                 }},
                      m->v());
  }

  template <typename T1, MapsTo<T1, std::shared_ptr<maybe>> F0,
            MapsTo<T1, std::shared_ptr<mlist>> F1>
  static T1 mtree_rec(F0 &&f, F1 &&f0, const std::shared_ptr<mtree> &m) {
    return std::visit(Overloaded{[&](const typename mtree::Leaf _args) -> T1 {
                                   std::shared_ptr<maybe> m0 = _args.d_a0;
                                   return f(std::move(m0));
                                 },
                                 [&](const typename mtree::Node _args) -> T1 {
                                   std::shared_ptr<mlist> m0 = _args.d_a0;
                                   return f0(std::move(m0));
                                 }},
                      m->v());
  }

  __attribute__((pure)) static bool
  is_nothing(const std::shared_ptr<maybe> &m) {
    return std::visit(
        Overloaded{
            [](const typename maybe::Nothing _args) -> bool { return true; },
            [](const typename maybe::Just _args) -> bool { return false; }},
        m->v());
  }

  __attribute__((pure)) static unsigned int
  mlist_length(const std::shared_ptr<mlist> &l) {
    return std::visit(
        Overloaded{
            [](const typename mlist::MNil _args) -> unsigned int { return 0u; },
            [](const typename mlist::MCons _args) -> unsigned int {
              std::shared_ptr<mlist> rest = _args.d_a1;
              return (mlist_length(std::move(rest)) + 1);
            }},
        l->v());
  }

  __attribute__((pure)) static unsigned int
  tree_size(const std::shared_ptr<mtree> &t0) {
    return std::visit(
        Overloaded{[](const typename mtree::Leaf _args) -> unsigned int {
                     std::shared_ptr<maybe> m = _args.d_a0;
                     if (is_nothing(std::move(m))) {
                       return 0u;
                     } else {
                       return 1u;
                     }
                   },
                   [](const typename mtree::Node _args) -> unsigned int {
                     std::shared_ptr<mlist> children = _args.d_a0;
                     return mlist_length(std::move(children));
                   }},
        t0->v());
  }

  static const std::shared_ptr<maybe> &empty_maybe() {
    static const std::shared_ptr<maybe> v = maybe::ctor::Nothing_();
    return v;
  }

  static const std::shared_ptr<maybe> &some_val() {
    static const std::shared_ptr<maybe> v = maybe::ctor::Just_(42u);
    return v;
  }

  static const std::shared_ptr<mlist> &sample_list() {
    static const std::shared_ptr<mlist> v = mlist::ctor::MCons_(
        maybe::ctor::Just_(42u),
        mlist::ctor::MCons_(maybe::ctor::Nothing_(), mlist::ctor::MNil_()));
    return v;
  }

  static const std::shared_ptr<mtree> &sample_tree() {
    static const std::shared_ptr<mtree> v = mtree::ctor::Node_(sample_list());
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
