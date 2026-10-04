#ifndef INCLUDED_MEM_SAFETY_PROBE17
#define INCLUDED_MEM_SAFETY_PROBE17

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

struct MemSafetyProbe17 {
  /// Probe 17: Wide tree (4-ary) and complex ownership patterns.
  ///
  /// Attack vectors:
  /// 1. 4-ary tree with 4 unique_ptr children -- more complex frame structs
  /// 2. Functions that use ALL children in computations AND recursive calls
  /// 3. Owned match where one child is used in a closure AND others
  /// in recursive calls (testing pre-extraction with many children)
  /// 4. Mutual-like patterns where different functions process the
  /// same tree differently
  struct qtree {
    // TYPES
    struct QLeaf {};

    struct QNode {
      std::shared_ptr<qtree> a0;
      std::shared_ptr<qtree> a1;
      uint64_t a2;
      std::shared_ptr<qtree> a3;
      std::shared_ptr<qtree> a4;
    };

    using variant_t = std::variant<QLeaf, QNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    qtree() {}

    explicit qtree(QLeaf _v) : v_(_v) {}

    explicit qtree(QNode _v) : v_(std::move(_v)) {}

    static qtree qleaf() { return qtree(QLeaf{}); }

    static qtree qnode(qtree a0, qtree a1, uint64_t a2, qtree a3, qtree a4) {
      return qtree(QNode{std::make_shared<qtree>(std::move(a0)),
                         std::make_shared<qtree>(std::move(a1)), a2,
                         std::make_shared<qtree>(std::move(a3)),
                         std::make_shared<qtree>(std::move(a4))});
    }

    // MANIPULATORS
    ~qtree() {
      crane::small_vector<std::shared_ptr<qtree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<QNode>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
          }
          if (_alt->a3 && _alt->a3.use_count() == 1) {
            _stack.push_back(std::move(_alt->a3));
          }
          if (_alt->a4 && _alt->a4.use_count() == 1) {
            _stack.push_back(std::move(_alt->a4));
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

    qtree(const qtree &) = default;
    qtree &operator=(const qtree &) = default;
    qtree(qtree &&) = default;
    qtree &operator=(qtree &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// TEST 6: Compute a value using ALL children non-recursively,
    /// THEN use all children recursively. Tests frame saving with
    /// many unique_ptr fields.
    uint64_t weighted_sum() const {
      const qtree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const qtree *_self;
      };

      /// CraneCont_QNode: saves [a1, a3, a4, local_weight], resumes after
      /// recursive call, then processes rest.
      struct CraneCont_QNode {
        std::shared_ptr<qtree> a1;
        std::shared_ptr<qtree> a3;
        std::shared_ptr<qtree> a4;
        uint64_t local_weight;
      };

      /// CraneCont_QNode_1: saves [_tmp4, a3, a4, local_weight], resumes after
      /// recursive call, then processes rest.
      struct CraneCont_QNode_1 {
        uint64_t _tmp4;
        std::shared_ptr<qtree> a3;
        std::shared_ptr<qtree> a4;
        uint64_t local_weight;
      };

      /// CraneCont_QNode_2: saves [_tmp3, _tmp4, a4, local_weight], resumes
      /// after recursive call, then processes rest.
      struct CraneCont_QNode_2 {
        uint64_t _tmp3;
        uint64_t _tmp4;
        std::shared_ptr<qtree> a4;
        uint64_t local_weight;
      };

      /// CraneCont_QNode_3: saves [_tmp2, _tmp3, _tmp4, local_weight], resumes
      /// after recursive call, then processes rest.
      struct CraneCont_QNode_3 {
        uint64_t _tmp2;
        uint64_t _tmp3;
        uint64_t _tmp4;
        uint64_t local_weight;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_QNode, CraneCont_QNode_1,
                       CraneCont_QNode_2, CraneCont_QNode_3>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified weighted_sum: CraneEnter -> CraneCont_QNode ->
      /// CraneCont_QNode_1 -> CraneCont_QNode_2 -> CraneCont_QNode_3.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const qtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename qtree::QLeaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2, a3, a4] =
                std::get<typename qtree::QNode>(_sv.v());
            uint64_t local_weight =
                ((((a0->qtree_sum() + (UINT64_C(2) * a1->qtree_sum())) +
                   (UINT64_C(3) * a2)) +
                  (UINT64_C(4) * a3->qtree_sum())) +
                 (UINT64_C(5) * a4->qtree_sum()));
            _stack.emplace_back(CraneCont_QNode{a1, a3, a4, local_weight});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_QNode>(_frame)) {
          auto _f = std::move(std::get<CraneCont_QNode>(_frame));
          std::shared_ptr<qtree> a1 = std::move(_f.a1);
          std::shared_ptr<qtree> a3 = std::move(_f.a3);
          std::shared_ptr<qtree> a4 = std::move(_f.a4);
          uint64_t local_weight = _f.local_weight;
          _stack.emplace_back(CraneCont_QNode_1{
              std::move(_result), std::move(a3), std::move(a4), local_weight});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_QNode_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_QNode_1>(_frame));
          std::shared_ptr<qtree> a3 = std::move(_f.a3);
          std::shared_ptr<qtree> a4 = std::move(_f.a4);
          uint64_t local_weight = _f.local_weight;
          _stack.emplace_back(CraneCont_QNode_2{std::move(_result), _f._tmp4,
                                                std::move(a4), local_weight});
          _stack.emplace_back(CraneEnter{crane_raw(a3)});
        } else if (std::holds_alternative<CraneCont_QNode_2>(_frame)) {
          auto _f = std::move(std::get<CraneCont_QNode_2>(_frame));
          std::shared_ptr<qtree> a4 = std::move(_f.a4);
          uint64_t local_weight = _f.local_weight;
          _stack.emplace_back(CraneCont_QNode_3{std::move(_result), _f._tmp3,
                                                _f._tmp4, local_weight});
          _stack.emplace_back(CraneEnter{crane_raw(a4)});
        } else {
          auto _f = std::move(std::get<CraneCont_QNode_3>(_frame));
          uint64_t local_weight = _f.local_weight;
          _result = ((((local_weight + _f._tmp4) + _f._tmp3) + _f._tmp2) +
                     std::move(_result));
        }
      }
      return _result;
    }

    /// TEST 5: Zip two 4-ary trees.
    qtree qtree_zip(qtree t2) const {
      const qtree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const qtree *_self;
        qtree t2;
      };

      /// CraneCont_QNode: saves [a10, a2, a20, a3, a30, a4, a40, a5], resumes
      /// after recursive call, then processes rest.
      struct CraneCont_QNode {
        std::shared_ptr<qtree> a10;
        std::shared_ptr<qtree> a2;
        uint64_t a20;
        uint64_t a3;
        std::shared_ptr<qtree> a30;
        std::shared_ptr<qtree> a4;
        std::shared_ptr<qtree> a40;
        std::shared_ptr<qtree> a5;
      };

      /// CraneCont_QNode_1: saves [_tmp4, a20, a3, a30, a4, a40, a5], resumes
      /// after recursive call, then processes rest.
      struct CraneCont_QNode_1 {
        qtree _tmp4;
        uint64_t a20;
        uint64_t a3;
        std::shared_ptr<qtree> a30;
        std::shared_ptr<qtree> a4;
        std::shared_ptr<qtree> a40;
        std::shared_ptr<qtree> a5;
      };

      /// CraneCont_QNode_2: saves [_tmp3, _tmp4, a20, a3, a40, a5], resumes
      /// after recursive call, then processes rest.
      struct CraneCont_QNode_2 {
        qtree _tmp3;
        qtree _tmp4;
        uint64_t a20;
        uint64_t a3;
        std::shared_ptr<qtree> a40;
        std::shared_ptr<qtree> a5;
      };

      /// CraneCont_QNode_3: saves [_tmp2, _tmp3, _tmp4, a20, a3], resumes after
      /// recursive call, then processes rest.
      struct CraneCont_QNode_3 {
        qtree _tmp2;
        qtree _tmp3;
        qtree _tmp4;
        uint64_t a20;
        uint64_t a3;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_QNode, CraneCont_QNode_1,
                       CraneCont_QNode_2, CraneCont_QNode_3>;
      qtree _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self, std::move(t2)});
      /// Loopified qtree_zip: CraneEnter -> CraneCont_QNode ->
      /// CraneCont_QNode_1 -> CraneCont_QNode_2 -> CraneCont_QNode_3.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const qtree *_self = _f._self;
          qtree t2 = std::move(_f.t2);
          auto &&_sv = *_self;
          if (std::holds_alternative<typename qtree::QLeaf>(_sv.v())) {
            _result = std::move(t2);
          } else {
            const auto &[a0, a2, a3, a4, a5] =
                std::get<typename qtree::QNode>(_sv.v());
            if (std::holds_alternative<typename qtree::QLeaf>(t2.v_mut())) {
              _result = *_self;
            } else {
              auto &[a00, a10, a20, a30, a40] =
                  std::get<typename qtree::QNode>(t2.v_mut());
              _stack.emplace_back(
                  CraneCont_QNode{a10, a2, a20, a3, a30, a4, a40, a5});
              _stack.emplace_back(CraneEnter{crane_raw(a0), *a00});
            }
          }
        } else if (std::holds_alternative<CraneCont_QNode>(_frame)) {
          auto _f = std::move(std::get<CraneCont_QNode>(_frame));
          std::shared_ptr<qtree> a10 = std::move(_f.a10);
          std::shared_ptr<qtree> a2 = std::move(_f.a2);
          uint64_t a20 = _f.a20;
          uint64_t a3 = _f.a3;
          std::shared_ptr<qtree> a30 = std::move(_f.a30);
          std::shared_ptr<qtree> a4 = std::move(_f.a4);
          std::shared_ptr<qtree> a40 = std::move(_f.a40);
          std::shared_ptr<qtree> a5 = std::move(_f.a5);
          _stack.emplace_back(CraneCont_QNode_1{std::move(_result), a20, a3,
                                                std::move(a30), std::move(a4),
                                                std::move(a40), std::move(a5)});
          _stack.emplace_back(CraneEnter{crane_raw(a2), *a10});
        } else if (std::holds_alternative<CraneCont_QNode_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_QNode_1>(_frame));
          uint64_t a20 = _f.a20;
          uint64_t a3 = _f.a3;
          std::shared_ptr<qtree> a30 = std::move(_f.a30);
          std::shared_ptr<qtree> a4 = std::move(_f.a4);
          std::shared_ptr<qtree> a40 = std::move(_f.a40);
          std::shared_ptr<qtree> a5 = std::move(_f.a5);
          _stack.emplace_back(CraneCont_QNode_2{std::move(_result),
                                                std::move(_f._tmp4), a20, a3,
                                                std::move(a40), std::move(a5)});
          _stack.emplace_back(CraneEnter{crane_raw(a4), *a30});
        } else if (std::holds_alternative<CraneCont_QNode_2>(_frame)) {
          auto _f = std::move(std::get<CraneCont_QNode_2>(_frame));
          uint64_t a20 = _f.a20;
          uint64_t a3 = _f.a3;
          std::shared_ptr<qtree> a40 = std::move(_f.a40);
          std::shared_ptr<qtree> a5 = std::move(_f.a5);
          _stack.emplace_back(CraneCont_QNode_3{std::move(_result),
                                                std::move(_f._tmp3),
                                                std::move(_f._tmp4), a20, a3});
          _stack.emplace_back(CraneEnter{crane_raw(a5), *a40});
        } else {
          auto _f = std::move(std::get<CraneCont_QNode_3>(_frame));
          uint64_t a20 = _f.a20;
          uint64_t a3 = _f.a3;
          _result = qtree::qnode(std::move(_f._tmp4), std::move(_f._tmp3),
                                 (a3 + std::move(a20)), std::move(_f._tmp2),
                                 std::move(_result));
        }
      }
      return _result;
    }

    /// TEST 3: Mirror a 4-ary tree (reverse children order).
    qtree qtree_mirror() const {
      const qtree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const qtree *_self;
      };

      /// CraneCont_QNode: saves [a0, a1, a2, a3], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_QNode {
        std::shared_ptr<qtree> a0;
        std::shared_ptr<qtree> a1;
        uint64_t a2;
        std::shared_ptr<qtree> a3;
      };

      /// CraneCont_QNode_1: saves [_tmp4, a0, a1, a2], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_QNode_1 {
        qtree _tmp4;
        std::shared_ptr<qtree> a0;
        std::shared_ptr<qtree> a1;
        uint64_t a2;
      };

      /// CraneCont_QNode_2: saves [_tmp3, _tmp4, a0, a2], resumes after
      /// recursive call, then processes rest.
      struct CraneCont_QNode_2 {
        qtree _tmp3;
        qtree _tmp4;
        std::shared_ptr<qtree> a0;
        uint64_t a2;
      };

      /// CraneCont_QNode_3: saves [_tmp2, _tmp3, _tmp4, a2], resumes after
      /// recursive call, then processes rest.
      struct CraneCont_QNode_3 {
        qtree _tmp2;
        qtree _tmp3;
        qtree _tmp4;
        uint64_t a2;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_QNode, CraneCont_QNode_1,
                       CraneCont_QNode_2, CraneCont_QNode_3>;
      qtree _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified qtree_mirror: CraneEnter -> CraneCont_QNode ->
      /// CraneCont_QNode_1 -> CraneCont_QNode_2 -> CraneCont_QNode_3.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const qtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename qtree::QLeaf>(_sv.v())) {
            _result = qtree::qleaf();
          } else {
            const auto &[a0, a1, a2, a3, a4] =
                std::get<typename qtree::QNode>(_sv.v());
            _stack.emplace_back(CraneCont_QNode{a0, a1, a2, a3});
            _stack.emplace_back(CraneEnter{crane_raw(a4)});
          }
        } else if (std::holds_alternative<CraneCont_QNode>(_frame)) {
          auto _f = std::move(std::get<CraneCont_QNode>(_frame));
          std::shared_ptr<qtree> a0 = std::move(_f.a0);
          std::shared_ptr<qtree> a1 = std::move(_f.a1);
          uint64_t a2 = _f.a2;
          std::shared_ptr<qtree> a3 = std::move(_f.a3);
          _stack.emplace_back(CraneCont_QNode_1{
              std::move(_result), std::move(a0), std::move(a1), a2});
          _stack.emplace_back(CraneEnter{crane_raw(a3)});
        } else if (std::holds_alternative<CraneCont_QNode_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_QNode_1>(_frame));
          std::shared_ptr<qtree> a0 = std::move(_f.a0);
          std::shared_ptr<qtree> a1 = std::move(_f.a1);
          uint64_t a2 = _f.a2;
          _stack.emplace_back(CraneCont_QNode_2{
              std::move(_result), std::move(_f._tmp4), std::move(a0), a2});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_QNode_2>(_frame)) {
          auto _f = std::move(std::get<CraneCont_QNode_2>(_frame));
          std::shared_ptr<qtree> a0 = std::move(_f.a0);
          uint64_t a2 = _f.a2;
          _stack.emplace_back(CraneCont_QNode_3{std::move(_result),
                                                std::move(_f._tmp3),
                                                std::move(_f._tmp4), a2});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else {
          auto _f = std::move(std::get<CraneCont_QNode_3>(_frame));
          uint64_t a2 = _f.a2;
          _result = qtree::qnode(std::move(_f._tmp4), std::move(_f._tmp3), a2,
                                 std::move(_f._tmp2), std::move(_result));
        }
      }
      return _result;
    }

    uint64_t qtree_size() const {
      const qtree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const qtree *_self;
      };

      /// CraneCont_QNode: saves [a1, a3, a4], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_QNode {
        std::shared_ptr<qtree> a1;
        std::shared_ptr<qtree> a3;
        std::shared_ptr<qtree> a4;
      };

      /// CraneCont_QNode_1: saves [_tmp4, a3, a4], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_QNode_1 {
        uint64_t _tmp4;
        std::shared_ptr<qtree> a3;
        std::shared_ptr<qtree> a4;
      };

      /// CraneCont_QNode_2: saves [_tmp3, _tmp4, a4], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_QNode_2 {
        uint64_t _tmp3;
        uint64_t _tmp4;
        std::shared_ptr<qtree> a4;
      };

      /// CraneCont_QNode_3: saves [_tmp2, _tmp3, _tmp4], resumes after
      /// recursive call, then processes rest.
      struct CraneCont_QNode_3 {
        uint64_t _tmp2;
        uint64_t _tmp3;
        uint64_t _tmp4;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_QNode, CraneCont_QNode_1,
                       CraneCont_QNode_2, CraneCont_QNode_3>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified qtree_size: CraneEnter -> CraneCont_QNode ->
      /// CraneCont_QNode_1 -> CraneCont_QNode_2 -> CraneCont_QNode_3.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const qtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename qtree::QLeaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2, a3, a4] =
                std::get<typename qtree::QNode>(_sv.v());
            _stack.emplace_back(CraneCont_QNode{a1, a3, a4});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_QNode>(_frame)) {
          auto _f = std::move(std::get<CraneCont_QNode>(_frame));
          std::shared_ptr<qtree> a1 = std::move(_f.a1);
          std::shared_ptr<qtree> a3 = std::move(_f.a3);
          std::shared_ptr<qtree> a4 = std::move(_f.a4);
          _stack.emplace_back(CraneCont_QNode_1{std::move(_result),
                                                std::move(a3), std::move(a4)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_QNode_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_QNode_1>(_frame));
          std::shared_ptr<qtree> a3 = std::move(_f.a3);
          std::shared_ptr<qtree> a4 = std::move(_f.a4);
          _stack.emplace_back(
              CraneCont_QNode_2{std::move(_result), _f._tmp4, std::move(a4)});
          _stack.emplace_back(CraneEnter{crane_raw(a3)});
        } else if (std::holds_alternative<CraneCont_QNode_2>(_frame)) {
          auto _f = std::move(std::get<CraneCont_QNode_2>(_frame));
          std::shared_ptr<qtree> a4 = std::move(_f.a4);
          _stack.emplace_back(
              CraneCont_QNode_3{std::move(_result), _f._tmp3, _f._tmp4});
          _stack.emplace_back(CraneEnter{crane_raw(a4)});
        } else {
          auto _f = std::move(std::get<CraneCont_QNode_3>(_frame));
          _result = ((((UINT64_C(1) + _f._tmp4) + _f._tmp3) + _f._tmp2) +
                     std::move(_result));
        }
      }
      return _result;
    }

    uint64_t qtree_depth() const {
      const qtree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const qtree *_self;
      };

      /// CraneCont_QNode: saves [a1, a3, a4], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_QNode {
        std::shared_ptr<qtree> a1;
        std::shared_ptr<qtree> a3;
        std::shared_ptr<qtree> a4;
      };

      /// CraneCont_QNode_1: saves [a3, a4, da], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_QNode_1 {
        std::shared_ptr<qtree> a3;
        std::shared_ptr<qtree> a4;
        uint64_t da;
      };

      /// CraneCont_QNode_2: saves [a4, da, db], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_QNode_2 {
        std::shared_ptr<qtree> a4;
        uint64_t da;
        uint64_t db;
      };

      /// CraneCont_QNode_3: saves [da, db, dc], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_QNode_3 {
        uint64_t da;
        uint64_t db;
        uint64_t dc;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_QNode, CraneCont_QNode_1,
                       CraneCont_QNode_2, CraneCont_QNode_3>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified qtree_depth: CraneEnter -> CraneCont_QNode ->
      /// CraneCont_QNode_1 -> CraneCont_QNode_2 -> CraneCont_QNode_3.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const qtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename qtree::QLeaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2, a3, a4] =
                std::get<typename qtree::QNode>(_sv.v());
            _stack.emplace_back(CraneCont_QNode{a1, a3, a4});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_QNode>(_frame)) {
          auto _f = std::move(std::get<CraneCont_QNode>(_frame));
          std::shared_ptr<qtree> a1 = std::move(_f.a1);
          std::shared_ptr<qtree> a3 = std::move(_f.a3);
          std::shared_ptr<qtree> a4 = std::move(_f.a4);
          uint64_t da = std::move(_result);
          _stack.emplace_back(
              CraneCont_QNode_1{std::move(a3), std::move(a4), da});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_QNode_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_QNode_1>(_frame));
          std::shared_ptr<qtree> a3 = std::move(_f.a3);
          std::shared_ptr<qtree> a4 = std::move(_f.a4);
          uint64_t da = _f.da;
          uint64_t db = std::move(_result);
          _stack.emplace_back(CraneCont_QNode_2{std::move(a4), da, db});
          _stack.emplace_back(CraneEnter{crane_raw(a3)});
        } else if (std::holds_alternative<CraneCont_QNode_2>(_frame)) {
          auto _f = std::move(std::get<CraneCont_QNode_2>(_frame));
          std::shared_ptr<qtree> a4 = std::move(_f.a4);
          uint64_t da = _f.da;
          uint64_t db = _f.db;
          uint64_t dc = std::move(_result);
          _stack.emplace_back(CraneCont_QNode_3{da, db, dc});
          _stack.emplace_back(CraneEnter{crane_raw(a4)});
        } else {
          auto _f = std::move(std::get<CraneCont_QNode_3>(_frame));
          uint64_t da = _f.da;
          uint64_t db = _f.db;
          uint64_t dc = _f.dc;
          uint64_t dd = std::move(_result);
          uint64_t m1;
          if (da <= db) {
            m1 = db;
          } else {
            m1 = da;
          }
          uint64_t m2;
          if (dc <= dd) {
            m2 = dd;
          } else {
            m2 = dc;
          }
          _result = (UINT64_C(1) + (m1 <= m2 ? m2 : m1));
        }
      }
      return _result;
    }

    uint64_t qtree_sum() const {
      const qtree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const qtree *_self;
      };

      /// CraneCont_QNode: saves [a1, a2, a3, a4], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_QNode {
        std::shared_ptr<qtree> a1;
        uint64_t a2;
        std::shared_ptr<qtree> a3;
        std::shared_ptr<qtree> a4;
      };

      /// CraneCont_QNode_1: saves [_tmp4, a2, a3, a4], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_QNode_1 {
        uint64_t _tmp4;
        uint64_t a2;
        std::shared_ptr<qtree> a3;
        std::shared_ptr<qtree> a4;
      };

      /// CraneCont_QNode_2: saves [_tmp3, _tmp4, a2, a4], resumes after
      /// recursive call, then processes rest.
      struct CraneCont_QNode_2 {
        uint64_t _tmp3;
        uint64_t _tmp4;
        uint64_t a2;
        std::shared_ptr<qtree> a4;
      };

      /// CraneCont_QNode_3: saves [_tmp2, _tmp3, _tmp4, a2], resumes after
      /// recursive call, then processes rest.
      struct CraneCont_QNode_3 {
        uint64_t _tmp2;
        uint64_t _tmp3;
        uint64_t _tmp4;
        uint64_t a2;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_QNode, CraneCont_QNode_1,
                       CraneCont_QNode_2, CraneCont_QNode_3>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified qtree_sum: CraneEnter -> CraneCont_QNode ->
      /// CraneCont_QNode_1 -> CraneCont_QNode_2 -> CraneCont_QNode_3.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const qtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename qtree::QLeaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2, a3, a4] =
                std::get<typename qtree::QNode>(_sv.v());
            _stack.emplace_back(CraneCont_QNode{a1, a2, a3, a4});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_QNode>(_frame)) {
          auto _f = std::move(std::get<CraneCont_QNode>(_frame));
          std::shared_ptr<qtree> a1 = std::move(_f.a1);
          uint64_t a2 = _f.a2;
          std::shared_ptr<qtree> a3 = std::move(_f.a3);
          std::shared_ptr<qtree> a4 = std::move(_f.a4);
          _stack.emplace_back(CraneCont_QNode_1{std::move(_result), a2,
                                                std::move(a3), std::move(a4)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_QNode_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_QNode_1>(_frame));
          uint64_t a2 = _f.a2;
          std::shared_ptr<qtree> a3 = std::move(_f.a3);
          std::shared_ptr<qtree> a4 = std::move(_f.a4);
          _stack.emplace_back(CraneCont_QNode_2{std::move(_result), _f._tmp4,
                                                a2, std::move(a4)});
          _stack.emplace_back(CraneEnter{crane_raw(a3)});
        } else if (std::holds_alternative<CraneCont_QNode_2>(_frame)) {
          auto _f = std::move(std::get<CraneCont_QNode_2>(_frame));
          uint64_t a2 = _f.a2;
          std::shared_ptr<qtree> a4 = std::move(_f.a4);
          _stack.emplace_back(
              CraneCont_QNode_3{std::move(_result), _f._tmp3, _f._tmp4, a2});
          _stack.emplace_back(CraneEnter{crane_raw(a4)});
        } else {
          auto _f = std::move(std::get<CraneCont_QNode_3>(_frame));
          uint64_t a2 = _f.a2;
          _result =
              ((((_f._tmp4 + _f._tmp3) + a2) + _f._tmp2) + std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1> T1 qtree_rec(T1 f, F1 &&f0) const {
      const qtree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const qtree *_self;
      };

      /// CraneCont_QNode: saves [a0, a1, a2, a3, a4], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_QNode {
        std::shared_ptr<qtree> a0;
        std::shared_ptr<qtree> a1;
        uint64_t a2;
        std::shared_ptr<qtree> a3;
        std::shared_ptr<qtree> a4;
      };

      /// CraneCont_QNode_1: saves [_tmp4, a0, a1, a2, a3, a4], resumes after
      /// recursive call, then processes rest.
      struct CraneCont_QNode_1 {
        T1 _tmp4;
        std::shared_ptr<qtree> a0;
        std::shared_ptr<qtree> a1;
        uint64_t a2;
        std::shared_ptr<qtree> a3;
        std::shared_ptr<qtree> a4;
      };

      /// CraneCont_QNode_2: saves [_tmp3, _tmp4, a0, a1, a2, a3, a4], resumes
      /// after recursive call, then processes rest.
      struct CraneCont_QNode_2 {
        T1 _tmp3;
        T1 _tmp4;
        std::shared_ptr<qtree> a0;
        std::shared_ptr<qtree> a1;
        uint64_t a2;
        std::shared_ptr<qtree> a3;
        std::shared_ptr<qtree> a4;
      };

      /// CraneCont_QNode_3: saves [_tmp2, _tmp3, _tmp4, a0, a1, a2, a3, a4],
      /// resumes after recursive call, then processes rest.
      struct CraneCont_QNode_3 {
        T1 _tmp2;
        T1 _tmp3;
        T1 _tmp4;
        std::shared_ptr<qtree> a0;
        std::shared_ptr<qtree> a1;
        uint64_t a2;
        std::shared_ptr<qtree> a3;
        std::shared_ptr<qtree> a4;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_QNode, CraneCont_QNode_1,
                       CraneCont_QNode_2, CraneCont_QNode_3>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified qtree_rec: CraneEnter -> CraneCont_QNode ->
      /// CraneCont_QNode_1 -> CraneCont_QNode_2 -> CraneCont_QNode_3.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const qtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename qtree::QLeaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2, a3, a4] =
                std::get<typename qtree::QNode>(_sv.v());
            _stack.emplace_back(CraneCont_QNode{a0, a1, a2, a3, a4});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_QNode>(_frame)) {
          auto _f = std::move(std::get<CraneCont_QNode>(_frame));
          std::shared_ptr<qtree> a0 = std::move(_f.a0);
          std::shared_ptr<qtree> a1 = std::move(_f.a1);
          uint64_t a2 = _f.a2;
          std::shared_ptr<qtree> a3 = std::move(_f.a3);
          std::shared_ptr<qtree> a4 = std::move(_f.a4);
          _stack.emplace_back(CraneCont_QNode_1{std::move(_result),
                                                std::move(a0), a1, a2,
                                                std::move(a3), std::move(a4)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_QNode_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_QNode_1>(_frame));
          std::shared_ptr<qtree> a0 = std::move(_f.a0);
          std::shared_ptr<qtree> a1 = std::move(_f.a1);
          uint64_t a2 = _f.a2;
          std::shared_ptr<qtree> a3 = std::move(_f.a3);
          std::shared_ptr<qtree> a4 = std::move(_f.a4);
          _stack.emplace_back(CraneCont_QNode_2{
              std::move(_result), std::move(_f._tmp4), std::move(a0),
              std::move(a1), a2, a3, std::move(a4)});
          _stack.emplace_back(CraneEnter{crane_raw(a3)});
        } else if (std::holds_alternative<CraneCont_QNode_2>(_frame)) {
          auto _f = std::move(std::get<CraneCont_QNode_2>(_frame));
          std::shared_ptr<qtree> a0 = std::move(_f.a0);
          std::shared_ptr<qtree> a1 = std::move(_f.a1);
          uint64_t a2 = _f.a2;
          std::shared_ptr<qtree> a3 = std::move(_f.a3);
          std::shared_ptr<qtree> a4 = std::move(_f.a4);
          _stack.emplace_back(CraneCont_QNode_3{
              std::move(_result), std::move(_f._tmp3), std::move(_f._tmp4),
              std::move(a0), std::move(a1), a2, std::move(a3), a4});
          _stack.emplace_back(CraneEnter{crane_raw(a4)});
        } else {
          auto _f = std::move(std::get<CraneCont_QNode_3>(_frame));
          std::shared_ptr<qtree> a0 = std::move(_f.a0);
          std::shared_ptr<qtree> a1 = std::move(_f.a1);
          uint64_t a2 = _f.a2;
          std::shared_ptr<qtree> a3 = std::move(_f.a3);
          std::shared_ptr<qtree> a4 = std::move(_f.a4);
          _result = f0(*a0, std::move(_f._tmp4), *a1, std::move(_f._tmp3), a2,
                       *a3, std::move(_f._tmp2), *a4, std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1> T1 qtree_rect(T1 f, F1 &&f0) const {
      const qtree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const qtree *_self;
      };

      /// CraneCont_QNode: saves [a0, a1, a2, a3, a4], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_QNode {
        std::shared_ptr<qtree> a0;
        std::shared_ptr<qtree> a1;
        uint64_t a2;
        std::shared_ptr<qtree> a3;
        std::shared_ptr<qtree> a4;
      };

      /// CraneCont_QNode_1: saves [_tmp4, a0, a1, a2, a3, a4], resumes after
      /// recursive call, then processes rest.
      struct CraneCont_QNode_1 {
        T1 _tmp4;
        std::shared_ptr<qtree> a0;
        std::shared_ptr<qtree> a1;
        uint64_t a2;
        std::shared_ptr<qtree> a3;
        std::shared_ptr<qtree> a4;
      };

      /// CraneCont_QNode_2: saves [_tmp3, _tmp4, a0, a1, a2, a3, a4], resumes
      /// after recursive call, then processes rest.
      struct CraneCont_QNode_2 {
        T1 _tmp3;
        T1 _tmp4;
        std::shared_ptr<qtree> a0;
        std::shared_ptr<qtree> a1;
        uint64_t a2;
        std::shared_ptr<qtree> a3;
        std::shared_ptr<qtree> a4;
      };

      /// CraneCont_QNode_3: saves [_tmp2, _tmp3, _tmp4, a0, a1, a2, a3, a4],
      /// resumes after recursive call, then processes rest.
      struct CraneCont_QNode_3 {
        T1 _tmp2;
        T1 _tmp3;
        T1 _tmp4;
        std::shared_ptr<qtree> a0;
        std::shared_ptr<qtree> a1;
        uint64_t a2;
        std::shared_ptr<qtree> a3;
        std::shared_ptr<qtree> a4;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_QNode, CraneCont_QNode_1,
                       CraneCont_QNode_2, CraneCont_QNode_3>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified qtree_rect: CraneEnter -> CraneCont_QNode ->
      /// CraneCont_QNode_1 -> CraneCont_QNode_2 -> CraneCont_QNode_3.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const qtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename qtree::QLeaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2, a3, a4] =
                std::get<typename qtree::QNode>(_sv.v());
            _stack.emplace_back(CraneCont_QNode{a0, a1, a2, a3, a4});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_QNode>(_frame)) {
          auto _f = std::move(std::get<CraneCont_QNode>(_frame));
          std::shared_ptr<qtree> a0 = std::move(_f.a0);
          std::shared_ptr<qtree> a1 = std::move(_f.a1);
          uint64_t a2 = _f.a2;
          std::shared_ptr<qtree> a3 = std::move(_f.a3);
          std::shared_ptr<qtree> a4 = std::move(_f.a4);
          _stack.emplace_back(CraneCont_QNode_1{std::move(_result),
                                                std::move(a0), a1, a2,
                                                std::move(a3), std::move(a4)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_QNode_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_QNode_1>(_frame));
          std::shared_ptr<qtree> a0 = std::move(_f.a0);
          std::shared_ptr<qtree> a1 = std::move(_f.a1);
          uint64_t a2 = _f.a2;
          std::shared_ptr<qtree> a3 = std::move(_f.a3);
          std::shared_ptr<qtree> a4 = std::move(_f.a4);
          _stack.emplace_back(CraneCont_QNode_2{
              std::move(_result), std::move(_f._tmp4), std::move(a0),
              std::move(a1), a2, a3, std::move(a4)});
          _stack.emplace_back(CraneEnter{crane_raw(a3)});
        } else if (std::holds_alternative<CraneCont_QNode_2>(_frame)) {
          auto _f = std::move(std::get<CraneCont_QNode_2>(_frame));
          std::shared_ptr<qtree> a0 = std::move(_f.a0);
          std::shared_ptr<qtree> a1 = std::move(_f.a1);
          uint64_t a2 = _f.a2;
          std::shared_ptr<qtree> a3 = std::move(_f.a3);
          std::shared_ptr<qtree> a4 = std::move(_f.a4);
          _stack.emplace_back(CraneCont_QNode_3{
              std::move(_result), std::move(_f._tmp3), std::move(_f._tmp4),
              std::move(a0), std::move(a1), a2, std::move(a3), a4});
          _stack.emplace_back(CraneEnter{crane_raw(a4)});
        } else {
          auto _f = std::move(std::get<CraneCont_QNode_3>(_frame));
          std::shared_ptr<qtree> a0 = std::move(_f.a0);
          std::shared_ptr<qtree> a1 = std::move(_f.a1);
          uint64_t a2 = _f.a2;
          std::shared_ptr<qtree> a3 = std::move(_f.a3);
          std::shared_ptr<qtree> a4 = std::move(_f.a4);
          _result = f0(*a0, std::move(_f._tmp4), *a1, std::move(_f._tmp3), a2,
                       *a3, std::move(_f._tmp2), *a4, std::move(_result));
        }
      }
      return _result;
    }
  };

  /// TEST 1: Sum of a 4-ary tree. Basic correctness.
  static inline const uint64_t test_qtree_sum = []() {
    qtree t =
        qtree::qnode(qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(1),
                                  qtree::qleaf(), qtree::qleaf()),
                     qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(2),
                                  qtree::qleaf(), qtree::qleaf()),
                     UINT64_C(10),
                     qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(3),
                                  qtree::qleaf(), qtree::qleaf()),
                     qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(4),
                                  qtree::qleaf(), qtree::qleaf()));
    return std::move(t).qtree_sum();
  }();
  /// TEST 2: Depth of a deep 4-ary tree.
  static inline const uint64_t test_qtree_depth = []() {
    qtree inner = qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(1),
                               qtree::qleaf(), qtree::qleaf());
    qtree t = qtree::qnode(inner,
                           qtree::qnode(inner, qtree::qleaf(), UINT64_C(2),
                                        qtree::qleaf(), qtree::qleaf()),
                           UINT64_C(3), qtree::qleaf(), qtree::qleaf());
    return std::move(t).qtree_depth();
  }();
  static inline const uint64_t test_qtree_mirror = []() {
    qtree t =
        qtree::qnode(qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(1),
                                  qtree::qleaf(), qtree::qleaf()),
                     qtree::qleaf(), UINT64_C(10),
                     qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(3),
                                  qtree::qleaf(), qtree::qleaf()),
                     qtree::qleaf());
    return std::move(t).qtree_mirror().qtree_sum();
  }();

  /// TEST 4: Flatten a 4-ary tree to a list (inorder traversal).
  /// Uses all 4 children in recursive calls + value in list construction.
  template <typename A> struct mylist {
    // TYPES
    struct Mynil {};

    struct Mycons {
      A a0;
      std::shared_ptr<mylist<A>> a1;
    };

    using variant_t = std::variant<Mynil, Mycons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Mynil _v) : v_(_v) {}

    explicit mylist(Mycons _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    mylist(const mylist<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename mylist<CraneU>::Mynil>(
                    _other.v())) {
              return Mynil{};
            } else {
              const auto &[a0, a1] =
                  std::get<typename mylist<CraneU>::Mycons>(_other.v());
              return Mycons{
                  [&]() -> A {
                    if constexpr (crane_convertible<A, const CraneU &>) {
                      return crane_convert<A>(a0);
                    } else {
                      throw std::logic_error(
                          "unreachable: inactive constructor field at this "
                          "instantiation");
                    }
                  }(),
                  (a1 ? std::make_shared<mylist<A>>(
                            crane_convert<mylist<A>>(*a1))
                      : nullptr)};
            }
          }()) {}

    static mylist<A> mynil() { return mylist<A>(Mynil{}); }

    static mylist<A> mycons(A a0, mylist<A> a1) {
      return mylist<A>(
          Mycons{std::move(a0), std::make_shared<mylist<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<mylist<A>> {
        if (auto *_alt = std::get_if<Mycons>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      std::shared_ptr<mylist<A>> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    mylist(const mylist &) = default;
    mylist &operator=(const mylist &) = default;
    mylist(mylist &&) = default;
    mylist &operator=(mylist &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    mylist<A> myapp(mylist<A> l2) const {
      std::shared_ptr<mylist<A>> _head{};
      std::shared_ptr<mylist<A>> *_write = &_head;
      const mylist<A> *_loop_self = this;
      mylist<A> _loop_l2 = std::move(l2);
      while (true) {
        auto &&_sv = *_loop_self;
        if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
          *_write = std::make_shared<mylist<A>>(std::move(_loop_l2));
          break;
        } else {
          const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(_sv.v());
          auto _cell = std::make_shared<mylist<A>>(
              typename mylist<A>::Mycons(a0, nullptr));
          *_write = std::move(_cell);
          _write = &std::get<typename mylist<A>::Mycons>((*_write)->v_mut()).a1;
          _loop_self = crane_raw(a1);
          continue;
        }
      }
      return std::move(*_head);
    }

    template <typename T1, typename F1> T1 mylist_rec(T1 f, F1 &&f0) const {
      const mylist<A> *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const mylist<A> *_self;
      };

      /// CraneCont_Mycons: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Mycons {
        A a0;
        std::shared_ptr<mylist<A>> a1;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_Mycons>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified mylist_rec: CraneEnter -> CraneCont_Mycons.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const mylist<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] =
                std::get<typename mylist<A>::Mycons>(_sv.v());
            _stack.emplace_back(CraneCont_Mycons{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<CraneCont_Mycons>(_frame));
          auto a0 = std::move(_f.a0);
          std::shared_ptr<mylist<A>> a1 = std::move(_f.a1);
          _result = f0(a0, *a1, std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1> T1 mylist_rect(T1 f, F1 &&f0) const {
      const mylist<A> *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const mylist<A> *_self;
      };

      /// CraneCont_Mycons: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Mycons {
        A a0;
        std::shared_ptr<mylist<A>> a1;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_Mycons>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified mylist_rect: CraneEnter -> CraneCont_Mycons.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const mylist<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] =
                std::get<typename mylist<A>::Mycons>(_sv.v());
            _stack.emplace_back(CraneCont_Mycons{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<CraneCont_Mycons>(_frame));
          auto a0 = std::move(_f.a0);
          std::shared_ptr<mylist<A>> a1 = std::move(_f.a1);
          _result = f0(a0, *a1, std::move(_result));
        }
      }
      return _result;
    }
  };

  static uint64_t sum_list(const mylist<uint64_t> &l);
  static mylist<uint64_t> qtree_flatten(const qtree &t);
  static inline const uint64_t test_qtree_flatten = []() {
    qtree t =
        qtree::qnode(qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(1),
                                  qtree::qleaf(), qtree::qleaf()),
                     qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(2),
                                  qtree::qleaf(), qtree::qleaf()),
                     UINT64_C(5),
                     qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(3),
                                  qtree::qleaf(), qtree::qleaf()),
                     qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(4),
                                  qtree::qleaf(), qtree::qleaf()));
    return sum_list(qtree_flatten(std::move(t)));
  }();
  static inline const uint64_t test_qtree_zip = []() {
    qtree t1 = qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(10),
                            qtree::qleaf(), qtree::qleaf());
    qtree t2 = qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(20),
                            qtree::qleaf(), qtree::qleaf());
    return std::move(t1).qtree_zip(std::move(t2)).qtree_sum();
  }();
  static inline const uint64_t test_weighted = []() {
    qtree t =
        qtree::qnode(qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(1),
                                  qtree::qleaf(), qtree::qleaf()),
                     qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(2),
                                  qtree::qleaf(), qtree::qleaf()),
                     UINT64_C(3),
                     qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(4),
                                  qtree::qleaf(), qtree::qleaf()),
                     qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(5),
                                  qtree::qleaf(), qtree::qleaf()));
    return std::move(t).weighted_sum();
  }();
  /// TEST 7: Build a 4-ary tree programmatically and check.
  static qtree make_qtree(uint64_t n);
  static inline const uint64_t test_make_qtree =
      make_qtree(UINT64_C(4)).qtree_sum();
  /// TEST 8: Two-pass on a 4-ary tree: flatten then sum vs direct sum.
  static inline const uint64_t test_two_pass_qtree = []() {
    qtree t =
        qtree::qnode(qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(1),
                                  qtree::qleaf(), qtree::qleaf()),
                     qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(2),
                                  qtree::qleaf(), qtree::qleaf()),
                     UINT64_C(5),
                     qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(3),
                                  qtree::qleaf(), qtree::qleaf()),
                     qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(4),
                                  qtree::qleaf(), qtree::qleaf()));
    return (sum_list(qtree_flatten(t)) + t.qtree_sum());
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE17
