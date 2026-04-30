#ifndef INCLUDED_THIS_CAPTURE_RECORD
#define INCLUDED_THIS_CAPTURE_RECORD

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct ThisCaptureRecord {
  /// A methodified function stores this-capturing closures in a
  /// Rocq record (not option/pair/fn_list). The record fields hold
  /// closures that reference tree_sum, which becomes this->tree_sum()
  /// in C++. After the temporary tree is destroyed, the closures'
  /// raw this pointer dangles.
  ///
  /// Different escape mechanism: record fields.
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::unique_ptr<tree> d_a0;
      unsigned int d_a1;
      std::unique_ptr<tree> d_a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : d_v_(_v) {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

    tree(const tree &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    tree(tree &&_other) : d_v_(std::move(_other.d_v_)) {}

    tree &operator=(const tree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    tree &operator=(tree &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    tree clone() const {
      tree _out{};

      struct _CloneFrame {
        const tree *_src;
        tree *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const tree *_src = _frame._src;
        tree *_dst = _frame._dst;
        if (std::holds_alternative<Leaf>(_src->v())) {
          _dst->d_v_ = Leaf{};
        } else {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->d_v_ =
              Node{_alt.d_a0 ? std::make_unique<tree>() : nullptr, _alt.d_a1,
                   _alt.d_a2 ? std::make_unique<tree>() : nullptr};
          auto &_dst_alt = std::get<Node>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
          if (_alt.d_a2) {
            _stack.push_back({_alt.d_a2.get(), _dst_alt.d_a2.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static tree leaf() { return tree(Leaf{}); }

    static tree node(tree a0, unsigned int a1, tree a2) {
      return tree(Node{std::make_unique<tree>(std::move(a0)), std::move(a1),
                       std::make_unique<tree>(std::move(a2))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::unique_ptr<tree>> _stack{};
      auto _drain = [&](tree &_node) {
        if (std::holds_alternative<Node>(_node.d_v_)) {
          auto &_alt = std::get<Node>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
          if (_alt.d_a2) {
            _stack.push_back(std::move(_alt.d_a2));
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

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

    unsigned int tree_sum() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        return 0u;
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(_sv.v());
        return (((*(d_a0)).tree_sum() + d_a1) + (*(d_a2)).tree_sum());
      }
    }

    template <typename T1, MapsTo<T1, tree, T1, unsigned int, tree, T1> F1>
    T1 tree_rec(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(_sv.v());
        return f0(*(d_a0), (*(d_a0)).template tree_rec<T1>(f, f0), d_a1,
                  *(d_a2), (*(d_a2)).template tree_rec<T1>(f, f0));
      }
    }

    template <typename T1, MapsTo<T1, tree, T1, unsigned int, tree, T1> F1>
    T1 tree_rect(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(_sv.v());
        return f0(*(d_a0), (*(d_a0)).template tree_rect<T1>(f, f0), d_a1,
                  *(d_a2), (*(d_a2)).template tree_rect<T1>(f, f0));
      }
    }
  };

  /// A second inductive to prevent tree_callbacks from being
  /// methodified on callback_rec instead of tree.
  struct tag {
    // TYPES
    struct MkTag {
      unsigned int d_a0;
    };

    using variant_t = std::variant<MkTag>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    tag() {}

    explicit tag(MkTag _v) : d_v_(std::move(_v)) {}

    tag(const tag &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    tag(tag &&_other) : d_v_(std::move(_other.d_v_)) {}

    tag &operator=(const tag &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    tag &operator=(tag &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    tag clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0] = std::get<MkTag>(_sv.v());
      return tag(MkTag{d_a0});
    }

    // CREATORS
    static tag mktag(unsigned int a0) { return tag(MkTag{std::move(a0)}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, unsigned int> F0>
    T1 tag_rec(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0] = std::get<typename tag::MkTag>(_sv.v());
      return f(d_a0);
    }

    template <typename T1, MapsTo<T1, unsigned int> F0>
    T1 tag_rect(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0] = std::get<typename tag::MkTag>(_sv.v());
      return f(d_a0);
    }
  };

  struct callback_rec {
    std::function<unsigned int(unsigned int)> cr_add;
    std::function<unsigned int(unsigned int)> cr_mul;

    // ACCESSORS
    callback_rec clone() const {
      return callback_rec{(*(this)).cr_add, (*(this)).cr_mul};
    }
  };

  /// Methodified on tree. The extra flag argument forces Crane to
  /// treat this as a multi-argument function (preventing eta-collapse).
  /// Returns a record whose fields are closures that capture this
  /// via =, this.
  static callback_rec tree_callbacks(tree t, const unsigned int &flag);
  /// test1: flag=0, tree_sum=5.
  /// cr_add(10) = 10 + 5 = 15, cr_mul(3) = 3 * 5 = 15.
  /// Total = 30.
  static inline const unsigned int test1 = []() {
    callback_rec cb =
        tree_callbacks(tree::node(tree::leaf(), 5u, tree::leaf()), 0u);
    return (cb.cr_add(10u) + cb.cr_mul(3u));
  }();
  /// test2: With noise to clobber memory.
  /// flag=0, tree_sum = 60. cr_add(0) = 60, cr_mul(1) = 60.
  /// Total = 120.
  static inline const unsigned int test2 = []() {
    callback_rec cb = tree_callbacks(
        tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                   tree::node(tree::leaf(), 30u, tree::leaf())),
        0u);
    return (cb.cr_add(0u) + cb.cr_mul(1u));
  }();
  /// test3: flag=1, tree_sum=100. cr_mul(7) = tree_sum = 100.
  static inline const unsigned int test3 =
      tree_callbacks(tree::node(tree::leaf(), 100u, tree::leaf()), 1u)
          .cr_mul(7u);
  /// Dummy use of tag to keep it around for extraction.
  static tag mk_tag(unsigned int n);
};

#endif // INCLUDED_THIS_CAPTURE_RECORD
