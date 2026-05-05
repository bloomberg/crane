#ifndef INCLUDED_MUTUAL_INDEXED
#define INCLUDED_MUTUAL_INDEXED

#include <memory>
#include <optional>
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

    EvenTree &operator=(const EvenTree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    EvenTree &operator=(EvenTree &&_other) {
      d_v_ = std::move(_other.d_v_);
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
          _dst->d_v_ = ELeaf{};
        } else {
          const auto &_alt = std::get<ENode>(_src->v());
          _dst->d_v_ = ENode{_alt.d_n, _alt.d_a1,
                             _alt.d_a2 ? std::make_unique<OddTree>() : nullptr};
          auto &_dst_alt = std::get<ENode>(_dst->d_v_);
          if (_alt.d_a2) {
            if (std::holds_alternative<typename MutualIndexed::OddTree::ONode>(
                    _alt.d_a2->v())) {
              const auto &_psrc =
                  std::get<typename MutualIndexed::OddTree::ONode>(
                      _alt.d_a2->v());
              auto &_pdst = std::get<typename MutualIndexed::OddTree::ONode>(
                  _dst_alt.d_a2->v_mut());
              if (_psrc.d_a2) {
                _pdst.d_a2 = std::make_unique<EvenTree>();
                _stack.push_back({_psrc.d_a2.get(), _pdst.d_a2.get()});
              }
            }
          }
        }
      }
      return _out;
    }

    // CREATORS
    static EvenTree eleaf() { return EvenTree(ELeaf{}); }

    static EvenTree enode(unsigned int n, unsigned int a1, OddTree a2) {
      return EvenTree(ENode{std::move(n), std::move(a1),
                            std::make_unique<OddTree>(std::move(a2))});
    }

    // MANIPULATORS
    ~EvenTree() {
      std::vector<std::unique_ptr<EvenTree>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](EvenTree &_node) {
        if (std::holds_alternative<ENode>(_node.d_v_)) {
          auto &_alt = std::get<ENode>(_node.d_v_);
          if (_alt.d_a2) {
            if (std::holds_alternative<typename MutualIndexed::OddTree::ONode>(
                    _alt.d_a2->v())) {
              auto &_palt = std::get<typename MutualIndexed::OddTree::ONode>(
                  _alt.d_a2->v_mut());
              if (_palt.d_a2) {
                _stack.push_back(std::move(_palt.d_a2));
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

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
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

    OddTree &operator=(const OddTree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    OddTree &operator=(OddTree &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    OddTree clone() const {
      auto &&_sv = *(this);
      const auto &[d_n, d_a1, d_a2] = std::get<ONode>(_sv.v());
      return OddTree(
          ONode{d_n, d_a1,
                d_a2 ? std::make_unique<MutualIndexed::EvenTree>(d_a2->clone())
                     : nullptr});
    }

    // CREATORS
    static OddTree onode(unsigned int n, unsigned int a1, EvenTree a2) {
      return OddTree(ONode{std::move(n), std::move(a1),
                           std::make_unique<EvenTree>(std::move(a2))});
    }

    // MANIPULATORS
    ~OddTree() {
      std::vector<std::unique_ptr<OddTree>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](OddTree &_node) {
        if (std::holds_alternative<ONode>(_node.d_v_)) {
          auto &_alt = std::get<ONode>(_node.d_v_);
          if (_alt.d_a2) {
            if (std::holds_alternative<typename MutualIndexed::EvenTree::ENode>(
                    _alt.d_a2->v())) {
              auto &_palt = std::get<typename MutualIndexed::EvenTree::ENode>(
                  _alt.d_a2->v_mut());
              if (_palt.d_a2) {
                _stack.push_back(std::move(_palt.d_a2));
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

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, unsigned int &, unsigned int &,
                                   OddTree &>
  static T1 EvenTree_rect(const T1 f, F1 &&f0, const unsigned int,
                          const EvenTree &e) {
    if (std::holds_alternative<typename EvenTree::ELeaf>(e.v())) {
      return f;
    } else {
      const auto &[d_n, d_a1, d_a2] = std::get<typename EvenTree::ENode>(e.v());
      return f0(d_n, d_a1, *(d_a2));
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, unsigned int &, unsigned int &,
                                   OddTree &>
  static T1 EvenTree_rec(const T1 f, F1 &&f0, const unsigned int,
                         const EvenTree &e) {
    if (std::holds_alternative<typename EvenTree::ELeaf>(e.v())) {
      return f;
    } else {
      const auto &[d_n, d_a1, d_a2] = std::get<typename EvenTree::ENode>(e.v());
      return f0(d_n, d_a1, *(d_a2));
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &, unsigned int &,
                                   EvenTree &>
  static T1 OddTree_rect(F0 &&f, const unsigned int, const OddTree &o) {
    const auto &[d_n, d_a1, d_a2] = std::get<typename OddTree::ONode>(o.v());
    return f(d_n, d_a1, *(d_a2));
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &, unsigned int &,
                                   EvenTree &>
  static T1 OddTree_rec(F0 &&f, const unsigned int, const OddTree &o) {
    const auto &[d_n, d_a1, d_a2] = std::get<typename OddTree::ONode>(o.v());
    return f(d_n, d_a1, *(d_a2));
  }

  static unsigned int even_val(const unsigned int _x, const EvenTree &t);
  static unsigned int odd_val(const unsigned int _x, const OddTree &t);
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
