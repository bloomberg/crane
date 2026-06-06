#ifndef INCLUDED_MULTI_IND_FUNCTOR
#define INCLUDED_MULTI_IND_FUNCTOR

#include <concepts>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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
      uint64_t a0;
    };

    using variant_t = std::variant<Nothing, Just>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    maybe() {}

    explicit maybe(Nothing _v) : v_(_v) {}

    explicit maybe(Just _v) : v_(std::move(_v)) {}

    static maybe nothing() { return maybe(Nothing{}); }

    static maybe just(uint64_t a0) { return maybe(Just{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &>
  static T1 maybe_rect(T1 f, F1 &&f0, const maybe &m) {
    if (std::holds_alternative<typename maybe::Nothing>(m.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename maybe::Just>(m.v());
      return f0(a0);
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &>
  static T1 maybe_rec(T1 f, F1 &&f0, const maybe &m) {
    if (std::holds_alternative<typename maybe::Nothing>(m.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename maybe::Just>(m.v());
      return f0(a0);
    }
  }

  struct mlist {
    // TYPES
    struct MNil {};

    struct MCons {
      maybe a0;
      std::shared_ptr<mlist> a1;
    };

    using variant_t = std::variant<MNil, MCons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    mlist() {}

    explicit mlist(MNil _v) : v_(_v) {}

    explicit mlist(MCons _v) : v_(std::move(_v)) {}

    static mlist mnil() { return mlist(MNil{}); }

    static mlist mcons(maybe a0, mlist a1) {
      return mlist(
          MCons{std::move(a0), std::make_shared<mlist>(std::move(a1))});
    }

    // MANIPULATORS
    ~mlist() {
      std::vector<std::shared_ptr<mlist>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<MCons>(&_v)) {
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          _drain(_cur->v_mut());
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, maybe &, mlist &, T1 &>
  static T1 mlist_rect(T1 f, F1 &&f0, const mlist &m) {
    if (std::holds_alternative<typename mlist::MNil>(m.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename mlist::MCons>(m.v());
      return f0(a0, *a1, mlist_rect<T1>(f, f0, *a1));
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, maybe &, mlist &, T1 &>
  static T1 mlist_rec(T1 f, F1 &&f0, const mlist &m) {
    if (std::holds_alternative<typename mlist::MNil>(m.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename mlist::MCons>(m.v());
      return f0(a0, *a1, mlist_rec<T1>(f, f0, *a1));
    }
  }

  struct mtree {
    // TYPES
    struct Leaf {
      maybe a0;
    };

    struct Node {
      mlist a0;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    mtree() {}

    explicit mtree(Leaf _v) : v_(std::move(_v)) {}

    explicit mtree(Node _v) : v_(std::move(_v)) {}

    static mtree leaf(maybe a0) { return mtree(Leaf{std::move(a0)}); }

    static mtree node(mlist a0) { return mtree(Node{std::move(a0)}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, maybe &> &&
             std::is_invocable_r_v<T1, F1 &, mlist &>
  static T1 mtree_rect(F0 &&f, F1 &&f0, const mtree &m) {
    if (std::holds_alternative<typename mtree::Leaf>(m.v())) {
      const auto &[a0] = std::get<typename mtree::Leaf>(m.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename mtree::Node>(m.v());
      return f0(a0);
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, maybe &> &&
             std::is_invocable_r_v<T1, F1 &, mlist &>
  static T1 mtree_rec(F0 &&f, F1 &&f0, const mtree &m) {
    if (std::holds_alternative<typename mtree::Leaf>(m.v())) {
      const auto &[a0] = std::get<typename mtree::Leaf>(m.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename mtree::Node>(m.v());
      return f0(a0);
    }
  }

  static bool is_nothing(const maybe &m) {
    if (std::holds_alternative<typename maybe::Nothing>(m.v())) {
      return true;
    } else {
      return false;
    }
  }

  static uint64_t mlist_length(const mlist &l) {
    if (std::holds_alternative<typename mlist::MNil>(l.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename mlist::MCons>(l.v());
      return (mlist_length(*a1) + 1);
    }
  }

  static uint64_t tree_size(const mtree &t0) {
    if (std::holds_alternative<typename mtree::Leaf>(t0.v())) {
      const auto &[a0] = std::get<typename mtree::Leaf>(t0.v());
      if (is_nothing(a0)) {
        return UINT64_C(0);
      } else {
        return UINT64_C(1);
      }
    } else {
      const auto &[a0] = std::get<typename mtree::Node>(t0.v());
      return mlist_length(a0);
    }
  }

  static const maybe &empty_maybe() {
    static const maybe v = maybe::nothing();
    return v;
  }

  static const maybe &some_val() {
    static const maybe v = maybe::just(UINT64_C(42));
    return v;
  }

  static const mlist &sample_list() {
    static const mlist v =
        mlist::mcons(maybe::just(UINT64_C(42)),
                     mlist::mcons(maybe::nothing(), mlist::mnil()));
    return v;
  }

  static const mtree &sample_tree() {
    static const mtree v = mtree::node(sample_list());
    return v;
  }
};

struct NatElem {
  using t = uint64_t;
  static inline const uint64_t dflt = UINT64_C(42);
};

static_assert(Elem<NatElem>);
using NatContainer = Container<NatElem>;
const bool test_is_nothing =
    NatContainer::is_nothing(NatContainer::empty_maybe());
const uint64_t test_list_len =
    NatContainer::mlist_length(NatContainer::sample_list());
const uint64_t test_tree_size =
    NatContainer::tree_size(NatContainer::sample_tree());

#endif // INCLUDED_MULTI_IND_FUNCTOR
