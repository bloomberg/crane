#ifndef INCLUDED_MUTUAL_INDEXED
#define INCLUDED_MUTUAL_INDEXED

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MutualIndexed {
  struct EvenTree;
  struct OddTree;

  struct EvenTree {
    // TYPES
    struct ELeaf {};

    struct ENode {
      uint64_t n;
      uint64_t a1;
      std::unique_ptr<OddTree> a2;
    };

    using variant_t = std::variant<ELeaf, ENode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    EvenTree() {}

    explicit EvenTree(ELeaf _v) : v_(_v) {}

    explicit EvenTree(ENode _v) : v_(std::move(_v)) {}

    EvenTree(const EvenTree &_other) : v_(std::move(_other.clone().v_)) {}

    EvenTree(EvenTree &&_other) noexcept : v_(std::move(_other.v_)) {}

    EvenTree &operator=(const EvenTree &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    EvenTree &operator=(EvenTree &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    EvenTree clone() const {
      EvenTree _out{};

      struct _CloneFrame {
        const EvenTree *_src;
        EvenTree *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const EvenTree *_src = _frame._src;
        EvenTree *_dst = _frame._dst;
        if (std::holds_alternative<ELeaf>(_src->v())) {
          _dst->v_ = ELeaf{};
        } else {
          const auto &_alt = std::get<ENode>(_src->v());
          _dst->v_ = ENode{_alt.n, _alt.a1,
                           _alt.a2 ? std::make_unique<OddTree>() : nullptr};
          auto &_dst_alt = std::get<ENode>(_dst->v_);
          if (_alt.a2) {
            if (std::holds_alternative<typename MutualIndexed::OddTree::ONode>(
                    _alt.a2->v())) {
              const auto &_psrc =
                  std::get<typename MutualIndexed::OddTree::ONode>(
                      _alt.a2->v());
              auto &_pdst = std::get<typename MutualIndexed::OddTree::ONode>(
                  _dst_alt.a2->v_mut());
              if (_psrc.a2) {
                _pdst.a2 = std::make_unique<EvenTree>();
                _stack.push_back({_psrc.a2.get(), _pdst.a2.get()});
              }
            }
          }
        }
      }
      return _out;
    }

    // CREATORS
    static EvenTree eleaf() { return EvenTree(ELeaf{}); }

    static EvenTree enode(uint64_t n, uint64_t a1, OddTree a2) {
      return EvenTree(ENode{n, a1, std::make_unique<OddTree>(std::move(a2))});
    }

    // MANIPULATORS
    ~EvenTree() {
      std::vector<std::unique_ptr<EvenTree>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](EvenTree &_node) {
        if (std::holds_alternative<ENode>(_node.v_)) {
          auto &_alt = std::get<ENode>(_node.v_);
          if (_alt.a2) {
            if (std::holds_alternative<typename MutualIndexed::OddTree::ONode>(
                    _alt.a2->v())) {
              auto &_palt = std::get<typename MutualIndexed::OddTree::ONode>(
                  _alt.a2->v_mut());
              if (_palt.a2) {
                _stack.push_back(std::move(_palt.a2));
              }
            }
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

  struct OddTree {
    // TYPES
    struct ONode {
      uint64_t n;
      uint64_t a1;
      std::unique_ptr<EvenTree> a2;
    };

    using variant_t = std::variant<ONode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    OddTree() {}

    explicit OddTree(ONode _v) : v_(std::move(_v)) {}

    OddTree(const OddTree &_other) : v_(std::move(_other.clone().v_)) {}

    OddTree(OddTree &&_other) noexcept : v_(std::move(_other.v_)) {}

    OddTree &operator=(const OddTree &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    OddTree &operator=(OddTree &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    OddTree clone() const {
      const auto &[n, a1, a2] = std::get<ONode>(this->v());
      return OddTree(
          ONode{n, a1,
                a2 ? std::make_unique<MutualIndexed::EvenTree>(a2->clone())
                   : nullptr});
    }

    // CREATORS
    static OddTree onode(uint64_t n, uint64_t a1, EvenTree a2) {
      return OddTree(ONode{n, a1, std::make_unique<EvenTree>(std::move(a2))});
    }

    // MANIPULATORS
    ~OddTree() {
      std::vector<std::unique_ptr<OddTree>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](OddTree &_node) {
        if (std::holds_alternative<ONode>(_node.v_)) {
          auto &_alt = std::get<ONode>(_node.v_);
          if (_alt.a2) {
            if (std::holds_alternative<typename MutualIndexed::EvenTree::ENode>(
                    _alt.a2->v())) {
              auto &_palt = std::get<typename MutualIndexed::EvenTree::ENode>(
                  _alt.a2->v_mut());
              if (_palt.a2) {
                _stack.push_back(std::move(_palt.a2));
              }
            }
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
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &, uint64_t &, OddTree &>
  static T1 EvenTree_rect(T1 f, F1 &&f0, uint64_t, const EvenTree &e) {
    if (std::holds_alternative<typename EvenTree::ELeaf>(e.v())) {
      return f;
    } else {
      const auto &[n1, a1, a2] = std::get<typename EvenTree::ENode>(e.v());
      return f0(n1, a1, *a2);
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &, uint64_t &, OddTree &>
  static T1 EvenTree_rec(T1 f, F1 &&f0, uint64_t, const EvenTree &e) {
    if (std::holds_alternative<typename EvenTree::ELeaf>(e.v())) {
      return f;
    } else {
      const auto &[n1, a1, a2] = std::get<typename EvenTree::ENode>(e.v());
      return f0(n1, a1, *a2);
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, uint64_t &, EvenTree &>
  static T1 OddTree_rect(F0 &&f, uint64_t, const OddTree &o) {
    const auto &[n1, a1, a2] = std::get<typename OddTree::ONode>(o.v());
    return f(n1, a1, *a2);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, uint64_t &, EvenTree &>
  static T1 OddTree_rec(F0 &&f, uint64_t, const OddTree &o) {
    const auto &[n1, a1, a2] = std::get<typename OddTree::ONode>(o.v());
    return f(n1, a1, *a2);
  }

  static uint64_t even_val(uint64_t _x, const EvenTree &t);
  static uint64_t odd_val(uint64_t _x, const OddTree &t);
  static inline const EvenTree leaf = EvenTree::eleaf();
  static inline const OddTree tree1 =
      OddTree::onode(UINT64_C(0), UINT64_C(10), EvenTree::eleaf());
  static inline const EvenTree tree2 = EvenTree::enode(
      UINT64_C(1), UINT64_C(20),
      OddTree::onode(UINT64_C(0), UINT64_C(10), EvenTree::eleaf()));
  static inline const uint64_t test_leaf_val = even_val(UINT64_C(0), leaf);
  static inline const uint64_t test_tree1_val = odd_val(UINT64_C(1), tree1);
  static inline const uint64_t test_tree2_val = even_val(UINT64_C(2), tree2);
};

#endif // INCLUDED_MUTUAL_INDEXED
