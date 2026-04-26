#ifndef INCLUDED_MUTUAL_INDEXED
#define INCLUDED_MUTUAL_INDEXED

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> struct is_shared_ptr : std::false_type {};

template <typename T>
struct is_shared_ptr<std::shared_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> struct is_optional : std::false_type {};

template <typename T> struct is_optional<std::optional<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_shared<T>(x->clone()) : nullptr;
  } else {
    return x;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using TargetBare = std::remove_cvref_t<Target>;
  using SourceBare = std::remove_cvref_t<Source>;
  if constexpr (is_unique_ptr<TargetBare>::value) {
    using Inner = typename is_unique_ptr<TargetBare>::element_type;
    if constexpr (is_unique_ptr<SourceBare>::value) {
      using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires {
                             typename Inner::crane_element_type;
                             x->template clone_as<
                                 typename Inner::crane_element_type>();
                           }) {
        return std::make_unique<Inner>(
            x->template clone_as<typename Inner::crane_element_type>());
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x->clone());
      }
    } else {
      if constexpr (requires { x.clone(); }) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (std::is_same_v<Inner, SourceBare>) {
        if constexpr (requires { x.clone(); }) {
          return std::make_unique<Inner>(x.clone());
        } else {
          return std::make_unique<Inner>(x);
        }
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        if constexpr (requires { x.clone(); }) {
          return std::make_unique<Inner>(x.clone());
        } else {
          return std::make_unique<Inner>(x);
        }
      }
    }
  } else if constexpr (is_optional<TargetBare>::value) {
    using Inner = typename is_optional<TargetBare>::element_type;
    if constexpr (is_optional<SourceBare>::value) {
      if (!x)
        return std::nullopt;
      return Target{clone_as_value<Inner>(*x)};
    } else {
      return Target{clone_as_value<Inner>(x)};
    }
  } else if constexpr (is_shared_ptr<TargetBare>::value) {
    using Inner = typename is_shared_ptr<TargetBare>::element_type;
    if constexpr (is_shared_ptr<SourceBare>::value) {
      using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else if constexpr (is_unique_ptr<SourceBare>::value) {
      if (!x)
        return nullptr;
      if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_shared<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x.clone());
      }
    }
  } else if constexpr (std::is_same_v<TargetBare, SourceBare>) {
    return clone_value(x);
  } else if constexpr (is_unique_ptr<SourceBare>::value) {
    using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      if (!x)
        return Target{};
      if constexpr (requires { x->clone(); }) {
        return x->clone();
      } else {
        return *x;
      }
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else if constexpr (requires { x->clone(); }) {
      return x->clone();
    } else {
      return Target(*x);
    }
  } else if constexpr (is_shared_ptr<SourceBare>::value) {
    using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (requires {
                         typename TargetBare::crane_element_type;
                         x.template clone_as<
                             typename TargetBare::crane_element_type>();
                       }) {
    return x.template clone_as<typename TargetBare::crane_element_type>();
  } else if constexpr (requires { x.template clone_as<TargetBare>(); }) {
    return x.template clone_as<TargetBare>();
  } else {
    return Target(x);
  }
}

struct MutualIndexed {
  struct EvenTree;
  struct OddTree;

  struct EvenTree {
    // TYPES
    struct ELeaf {};

    struct ENode {
      unsigned int d_n;
      unsigned int d_a1;
      std::unique_ptr<OddTree> d_a2;
    };

    using variant_t = std::variant<ELeaf, ENode>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    EvenTree() {}

    explicit EvenTree(ELeaf _v) : d_v_(_v) {}

    explicit EvenTree(ENode _v) : d_v_(std::move(_v)) {}

    EvenTree(const EvenTree &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    EvenTree(EvenTree &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) EvenTree &operator=(const EvenTree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) EvenTree &operator=(EvenTree &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) EvenTree clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<ELeaf>(_sv.v())) {
        return EvenTree(ELeaf{});
      } else {
        const auto &[d_n, d_a1, d_a2] = std::get<ENode>(_sv.v());
        return EvenTree(
            ENode{d_n, d_a1, clone_as_value<std::unique_ptr<OddTree>>(d_a2)});
      }
    }

    // CREATORS
    __attribute__((pure)) static EvenTree eleaf() { return EvenTree(ELeaf{}); }

    __attribute__((pure)) static EvenTree enode(unsigned int n, unsigned int a1,
                                                const OddTree &a2) {
      return EvenTree(ENode{std::move(n), std::move(a1),
                            std::make_unique<OddTree>(a2.clone())});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) EvenTree *operator->() { return this; }

    __attribute__((pure)) const EvenTree *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = EvenTree(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  struct OddTree {
    // TYPES
    struct ONode {
      unsigned int d_n;
      unsigned int d_a1;
      std::unique_ptr<EvenTree> d_a2;
    };

    using variant_t = std::variant<ONode>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    OddTree() {}

    explicit OddTree(ONode _v) : d_v_(std::move(_v)) {}

    OddTree(const OddTree &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    OddTree(OddTree &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) OddTree &operator=(const OddTree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) OddTree &operator=(OddTree &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) OddTree clone() const {
      auto &&_sv = *(this);
      const auto &[d_n, d_a1, d_a2] = std::get<ONode>(_sv.v());
      return OddTree(
          ONode{d_n, d_a1, clone_as_value<std::unique_ptr<EvenTree>>(d_a2)});
    }

    // CREATORS
    __attribute__((pure)) static OddTree onode(unsigned int n, unsigned int a1,
                                               const EvenTree &a2) {
      return OddTree(ONode{std::move(n), std::move(a1),
                           std::make_unique<EvenTree>(a2.clone())});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) OddTree *operator->() { return this; }

    __attribute__((pure)) const OddTree *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = OddTree(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int, unsigned int, OddTree> F1>
  static T1 EvenTree_rect(const T1 f, F1 &&f0, const unsigned int &,
                          const EvenTree &e) {
    if (std::holds_alternative<typename EvenTree::ELeaf>(e.v())) {
      return f;
    } else {
      const auto &[d_n, d_a1, d_a2] = std::get<typename EvenTree::ENode>(e.v());
      return f0(d_n, d_a1, *(d_a2));
    }
  }

  template <typename T1, MapsTo<T1, unsigned int, unsigned int, OddTree> F1>
  static T1 EvenTree_rec(const T1 f, F1 &&f0, const unsigned int &,
                         const EvenTree &e) {
    if (std::holds_alternative<typename EvenTree::ELeaf>(e.v())) {
      return f;
    } else {
      const auto &[d_n, d_a1, d_a2] = std::get<typename EvenTree::ENode>(e.v());
      return f0(d_n, d_a1, *(d_a2));
    }
  }

  template <typename T1, MapsTo<T1, unsigned int, unsigned int, EvenTree> F0>
  static T1 OddTree_rect(F0 &&f, const unsigned int &, const OddTree &o) {
    const auto &[d_n, d_a1, d_a2] = std::get<typename OddTree::ONode>(o.v());
    return f(d_n, d_a1, *(d_a2));
  }

  template <typename T1, MapsTo<T1, unsigned int, unsigned int, EvenTree> F0>
  static T1 OddTree_rec(F0 &&f, const unsigned int &, const OddTree &o) {
    const auto &[d_n, d_a1, d_a2] = std::get<typename OddTree::ONode>(o.v());
    return f(d_n, d_a1, *(d_a2));
  }

  __attribute__((pure)) static unsigned int even_val(const unsigned int &_x,
                                                     const EvenTree &t);
  __attribute__((pure)) static unsigned int odd_val(const unsigned int &_x,
                                                    const OddTree &t);
  static inline const EvenTree leaf = EvenTree::eleaf();
  static inline const OddTree tree1 =
      OddTree::onode(0u, 10u, EvenTree::eleaf());
  static inline const EvenTree tree2 =
      EvenTree::enode(1u, 20u, OddTree::onode(0u, 10u, EvenTree::eleaf()));
  static inline const unsigned int test_leaf_val = even_val(0u, leaf);
  static inline const unsigned int test_tree1_val = odd_val(1u, tree1);
  static inline const unsigned int test_tree2_val = even_val(2u, tree2);
};

#endif // INCLUDED_MUTUAL_INDEXED
