#ifndef INCLUDED_THIS_CAPTURE_RECORD
#define INCLUDED_THIS_CAPTURE_RECORD

#include "crane_fn.h"
#include "fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

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
      std::shared_ptr<tree> a0;
      uint64_t a1;
      std::shared_ptr<tree> a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : v_(_v) {}

    explicit tree(Node _v) : v_(std::move(_v)) {}

    static tree leaf() { return tree(Leaf{}); }

    static tree node(tree a0, uint64_t a1, tree a2) {
      return tree(Node{std::make_shared<tree>(std::move(a0)), a1,
                       std::make_shared<tree>(std::move(a2))});
    }

    // MANIPULATORS
    ~tree() {
      crane::small_vector<std::shared_ptr<tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a2 && _alt->a2.use_count() == 1) {
            _stack.push_back(std::move(_alt->a2));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          _drain(_cur->v_mut());
        }
      }
    }

    tree(const tree &) = default;
    tree &operator=(const tree &) = default;
    tree(tree &&) = default;
    tree &operator=(tree &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t tree_sum() const {
      const tree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const tree *_self;
      };

      /// CraneCont_Node: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Node {
        uint64_t a1;
        std::shared_ptr<tree> a2;
      };

      /// CraneCont_Node_1: saves [_tmp2, a1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Node_1 {
        uint64_t _tmp2;
        uint64_t a1;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified tree_sum: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(CraneCont_Node{a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Node>(_frame));
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          _stack.emplace_back(CraneCont_Node_1{std::move(_result), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
          uint64_t a1 = _f.a1;
          _result = ((_f._tmp2 + a1) + std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
    T1 tree_rec(const T1 &f, F1 &&f0) const {
      return this->template tree_rect<T1>(f, f0);
    }

    template <typename T1, typename F1> T1 tree_rect(T1 f, F1 &&f0) const {
      const tree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const tree *_self;
      };

      /// CraneCont_Node: saves [a0, a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Node {
        std::shared_ptr<tree> a0;
        uint64_t a1;
        std::shared_ptr<tree> a2;
      };

      /// CraneCont_Node_1: saves [_tmp2, a0, a1, a2], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_Node_1 {
        T1 _tmp2;
        std::shared_ptr<tree> a0;
        uint64_t a1;
        std::shared_ptr<tree> a2;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified tree_rect: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(CraneCont_Node{a0, a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Node>(_frame));
          std::shared_ptr<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          _stack.emplace_back(
              CraneCont_Node_1{std::move(_result), std::move(a0), a1, a2});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
          std::shared_ptr<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          _result = f0(*a0, std::move(_f._tmp2), a1, *a2, std::move(_result));
        }
      }
      return _result;
    }
  };

  /// A second inductive to prevent tree_callbacks from being
  /// methodified on callback_rec instead of tree.
  struct tag {
    // DATA
    uint64_t a0;

    // ACCESSORS
    tag clone() const { return {a0}; }

    // CREATORS
    static tag mktag(uint64_t a0) { return {a0}; }

    template <typename T1, typename F0> T1 tag_rec(F0 &&f) const {
      return this->template tag_rect<T1>(f);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    T1 tag_rect(F0 &&f) const {
      const auto &[a0] = *this;
      return f(a0);
    }
  };

  struct callback_rec {
    crane::fn<uint64_t(uint64_t)> cr_add;
    crane::fn<uint64_t(uint64_t)> cr_mul;
  };

  /// Methodified on tree. The extra flag argument forces Crane to
  /// treat this as a multi-argument function (preventing eta-collapse).
  /// Returns a record whose fields are closures that capture this
  /// via =, this.
  static callback_rec tree_callbacks(tree t, uint64_t flag);
  /// test1: flag=0, tree_sum=5.
  /// cr_add(10) = 10 + 5 = 15, cr_mul(3) = 3 * 5 = 15.
  /// Total = 30.
  static inline const uint64_t test1 = []() {
    callback_rec cb = tree_callbacks(
        tree::node(tree::leaf(), UINT64_C(5), tree::leaf()), UINT64_C(0));
    return (cb.cr_add(UINT64_C(10)) + cb.cr_mul(UINT64_C(3)));
  }();
  /// test2: With noise to clobber memory.
  /// flag=0, tree_sum = 60. cr_add(0) = 60, cr_mul(1) = 60.
  /// Total = 120.
  static inline const uint64_t test2 = []() {
    callback_rec cb = tree_callbacks(
        tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                   UINT64_C(20),
                   tree::node(tree::leaf(), UINT64_C(30), tree::leaf())),
        UINT64_C(0));
    return (cb.cr_add(UINT64_C(0)) + cb.cr_mul(UINT64_C(1)));
  }();
  /// test3: flag=1, tree_sum=100. cr_mul(7) = tree_sum = 100.
  static inline const uint64_t test3 =
      tree_callbacks(tree::node(tree::leaf(), UINT64_C(100), tree::leaf()),
                     UINT64_C(1))
          .cr_mul(UINT64_C(7));
  /// Dummy use of tag to keep it around for extraction.
  static tag mk_tag(uint64_t n);
};

#endif // INCLUDED_THIS_CAPTURE_RECORD
