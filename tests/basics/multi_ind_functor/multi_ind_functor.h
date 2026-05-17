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

    maybe(const maybe &_other) : v_(std::move(_other.clone().v_)) {}

    maybe(maybe &&_other) noexcept : v_(std::move(_other.v_)) {}

    maybe &operator=(const maybe &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    maybe &operator=(maybe &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    maybe clone() const {
      if (std::holds_alternative<Nothing>(this->v())) {
        return maybe(Nothing{});
      } else {
        const auto &[a0] = std::get<Just>(this->v());
        return maybe(Just{a0});
      }
    }

    // CREATORS
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
      std::unique_ptr<mlist> a1;
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

    mlist(const mlist &_other) : v_(std::move(_other.clone().v_)) {}

    mlist(mlist &&_other) noexcept : v_(std::move(_other.v_)) {}

    mlist &operator=(const mlist &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    mlist &operator=(mlist &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    mlist clone() const {
      mlist _out{};

      struct _CloneFrame {
        const mlist *_src;
        mlist *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const mlist *_src = _frame._src;
        mlist *_dst = _frame._dst;
        if (std::holds_alternative<MNil>(_src->v())) {
          _dst->v_ = MNil{};
        } else {
          const auto &_alt = std::get<MCons>(_src->v());
          _dst->v_ = MCons{_alt.a0.clone(),
                           _alt.a1 ? std::make_unique<mlist>() : nullptr};
          auto &_dst_alt = std::get<MCons>(_dst->v_);
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static mlist mnil() { return mlist(MNil{}); }

    static mlist mcons(maybe a0, mlist a1) {
      return mlist(
          MCons{std::move(a0), std::make_unique<mlist>(std::move(a1))});
    }

    // MANIPULATORS
    ~mlist() {
      std::vector<std::unique_ptr<mlist>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](mlist &_node) {
        if (std::holds_alternative<MCons>(_node.v_)) {
          auto &_alt = std::get<MCons>(_node.v_);
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
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

    mtree(const mtree &_other) : v_(std::move(_other.clone().v_)) {}

    mtree(mtree &&_other) noexcept : v_(std::move(_other.v_)) {}

    mtree &operator=(const mtree &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    mtree &operator=(mtree &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    mtree clone() const {
      if (std::holds_alternative<Leaf>(this->v())) {
        const auto &[a0] = std::get<Leaf>(this->v());
        return mtree(Leaf{a0.clone()});
      } else {
        const auto &[a0] = std::get<Node>(this->v());
        return mtree(Node{a0.clone()});
      }
    }

    // CREATORS
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
