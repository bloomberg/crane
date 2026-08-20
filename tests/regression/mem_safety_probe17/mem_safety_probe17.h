#ifndef INCLUDED_MEM_SAFETY_PROBE17
#define INCLUDED_MEM_SAFETY_PROBE17

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <memory>
#include <type_traits>
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
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
          if (_alt->a3) {
            _stack.push_back(std::move(_alt->a3));
          }
          if (_alt->a4) {
            _stack.push_back(std::move(_alt->a4));
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

    qtree(const qtree &) = default;
    qtree &operator=(const qtree &) = default;
    qtree(qtree &&) noexcept = default;
    qtree &operator=(qtree &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// TEST 6: Compute a value using ALL children non-recursively,
    /// THEN use all children recursively. Tests frame saving with
    /// many unique_ptr fields.
    uint64_t weighted_sum() const {
      const qtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const qtree *_self;
      };

      /// _After_QNode: saves [a3, a1, a0, local_weight], dispatches next
      /// recursive call.
      struct _After_QNode {
        const qtree *a3;
        const qtree *a1;
        const qtree *a0;
        uint64_t local_weight;
      };

      /// _After_QNode_1: saves [_result, a1, a0, local_weight], dispatches next
      /// recursive call.
      struct _After_QNode_1 {
        uint64_t _result;
        const qtree *a1;
        const qtree *a0;
        uint64_t local_weight;
      };

      /// _After_QNode_2: saves [_result_0, _result_1, a0, local_weight],
      /// dispatches next recursive call.
      struct _After_QNode_2 {
        uint64_t _result_0;
        uint64_t _result_1;
        const qtree *a0;
        uint64_t local_weight;
      };

      /// _Combine_QNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_QNode {
        uint64_t _result_0;
        uint64_t _result_1;
        uint64_t _result_2;
        uint64_t local_weight;
      };

      using _Frame = std::variant<_Enter, _After_QNode, _After_QNode_1,
                                  _After_QNode_2, _Combine_QNode>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified weighted_sum: _Enter -> _After_QNode -> _After_QNode_1 ->
      /// _After_QNode_2 -> _Combine_QNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
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
            _stack.emplace_back(_After_QNode{crane_raw(a3), crane_raw(a1),
                                             crane_raw(a0), local_weight});
            _stack.emplace_back(_Enter{crane_raw(a4)});
          }
        } else if (std::holds_alternative<_After_QNode>(_frame)) {
          auto _f = std::move(std::get<_After_QNode>(_frame));
          _stack.emplace_back(_After_QNode_1{std::move(_result), _f.a1, _f.a0,
                                             _f.local_weight});
          _stack.emplace_back(_Enter{_f.a3});
        } else if (std::holds_alternative<_After_QNode_1>(_frame)) {
          auto _f = std::move(std::get<_After_QNode_1>(_frame));
          _stack.emplace_back(_After_QNode_2{_f._result, std::move(_result),
                                             _f.a0, _f.local_weight});
          _stack.emplace_back(_Enter{_f.a1});
        } else if (std::holds_alternative<_After_QNode_2>(_frame)) {
          auto _f = std::move(std::get<_After_QNode_2>(_frame));
          _stack.emplace_back(_Combine_QNode{
              _f._result_0, _f._result_1, std::move(_result), _f.local_weight});
          _stack.emplace_back(_Enter{_f.a0});
        } else {
          auto _f = std::move(std::get<_Combine_QNode>(_frame));
          _result = ((((_f.local_weight + std::move(_result)) + _f._result_2) +
                      _f._result_1) +
                     _f._result_0);
        }
      }
      return _result;
    }

    /// TEST 5: Zip two 4-ary trees.
    qtree qtree_zip(qtree t2) const {
      const qtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const qtree *_self;
        qtree t2;
      };

      /// _After_QNode: saves [a4, a30, a2, a10, a0, a00, _s6], dispatches next
      /// recursive call.
      struct _After_QNode {
        const qtree *a4;
        qtree a30;
        const qtree *a2;
        qtree a10;
        const qtree *a0;
        qtree a00;
        uint64_t _s6;
      };

      /// _After_QNode_1: saves [_result, a2, a10, a0, a00, _s5], dispatches
      /// next recursive call.
      struct _After_QNode_1 {
        qtree _result;
        const qtree *a2;
        qtree a10;
        const qtree *a0;
        qtree a00;
        uint64_t _s5;
      };

      /// _After_QNode_2: saves [_result_0, _result_1, a0, a00, _s4], dispatches
      /// next recursive call.
      struct _After_QNode_2 {
        qtree _result_0;
        qtree _result_1;
        const qtree *a0;
        qtree a00;
        uint64_t _s4;
      };

      /// _Combine_QNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_QNode {
        qtree _result_0;
        qtree _result_1;
        qtree _result_2;
        uint64_t _s3;
      };

      using _Frame = std::variant<_Enter, _After_QNode, _After_QNode_1,
                                  _After_QNode_2, _Combine_QNode>;
      qtree _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self, std::move(t2)});
      /// Loopified qtree_zip: _Enter -> _After_QNode -> _After_QNode_1 ->
      /// _After_QNode_2 -> _Combine_QNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
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
                  _After_QNode{crane_raw(a4), *a30, crane_raw(a2), *a10,
                               crane_raw(a0), *a00, (a3 + std::move(a20))});
              _stack.emplace_back(_Enter{crane_raw(a5), *a40});
            }
          }
        } else if (std::holds_alternative<_After_QNode>(_frame)) {
          auto _f = std::move(std::get<_After_QNode>(_frame));
          _stack.emplace_back(_After_QNode_1{std::move(_result), _f.a2,
                                             std::move(_f.a10), _f.a0,
                                             std::move(_f.a00), _f._s6});
          _stack.emplace_back(_Enter{_f.a4, std::move(_f.a30)});
        } else if (std::holds_alternative<_After_QNode_1>(_frame)) {
          auto _f = std::move(std::get<_After_QNode_1>(_frame));
          _stack.emplace_back(_After_QNode_2{std::move(_f._result),
                                             std::move(_result), _f.a0,
                                             std::move(_f.a00), _f._s5});
          _stack.emplace_back(_Enter{_f.a2, std::move(_f.a10)});
        } else if (std::holds_alternative<_After_QNode_2>(_frame)) {
          auto _f = std::move(std::get<_After_QNode_2>(_frame));
          _stack.emplace_back(_Combine_QNode{std::move(_f._result_0),
                                             std::move(_f._result_1),
                                             std::move(_result), _f._s4});
          _stack.emplace_back(_Enter{_f.a0, std::move(_f.a00)});
        } else {
          auto _f = std::move(std::get<_Combine_QNode>(_frame));
          _result =
              qtree::qnode(std::move(_result), std::move(_f._result_2), _f._s3,
                           std::move(_f._result_1), std::move(_f._result_0));
        }
      }
      return _result;
    }

    /// TEST 3: Mirror a 4-ary tree (reverse children order).
    qtree qtree_mirror() const {
      const qtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const qtree *_self;
      };

      /// _After_QNode: saves [a1, a3, a4, a2], dispatches next recursive call.
      struct _After_QNode {
        const qtree *a1;
        const qtree *a3;
        const qtree *a4;
        uint64_t a2;
      };

      /// _After_QNode_1: saves [_result, a3, a4, a2], dispatches next recursive
      /// call.
      struct _After_QNode_1 {
        qtree _result;
        const qtree *a3;
        const qtree *a4;
        uint64_t a2;
      };

      /// _After_QNode_2: saves [_result_0, _result_1, a4, a2], dispatches next
      /// recursive call.
      struct _After_QNode_2 {
        qtree _result_0;
        qtree _result_1;
        const qtree *a4;
        uint64_t a2;
      };

      /// _Combine_QNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_QNode {
        qtree _result_0;
        qtree _result_1;
        qtree _result_2;
        uint64_t a2;
      };

      using _Frame = std::variant<_Enter, _After_QNode, _After_QNode_1,
                                  _After_QNode_2, _Combine_QNode>;
      qtree _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified qtree_mirror: _Enter -> _After_QNode -> _After_QNode_1 ->
      /// _After_QNode_2 -> _Combine_QNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const qtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename qtree::QLeaf>(_sv.v())) {
            _result = qtree::qleaf();
          } else {
            const auto &[a0, a1, a2, a3, a4] =
                std::get<typename qtree::QNode>(_sv.v());
            _stack.emplace_back(
                _After_QNode{crane_raw(a1), crane_raw(a3), crane_raw(a4), a2});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_After_QNode>(_frame)) {
          auto _f = std::move(std::get<_After_QNode>(_frame));
          _stack.emplace_back(
              _After_QNode_1{std::move(_result), _f.a3, _f.a4, _f.a2});
          _stack.emplace_back(_Enter{_f.a1});
        } else if (std::holds_alternative<_After_QNode_1>(_frame)) {
          auto _f = std::move(std::get<_After_QNode_1>(_frame));
          _stack.emplace_back(_After_QNode_2{std::move(_f._result),
                                             std::move(_result), _f.a4, _f.a2});
          _stack.emplace_back(_Enter{_f.a3});
        } else if (std::holds_alternative<_After_QNode_2>(_frame)) {
          auto _f = std::move(std::get<_After_QNode_2>(_frame));
          _stack.emplace_back(_Combine_QNode{std::move(_f._result_0),
                                             std::move(_f._result_1),
                                             std::move(_result), _f.a2});
          _stack.emplace_back(_Enter{_f.a4});
        } else {
          auto _f = std::move(std::get<_Combine_QNode>(_frame));
          _result =
              qtree::qnode(std::move(_result), std::move(_f._result_2), _f.a2,
                           std::move(_f._result_1), std::move(_f._result_0));
        }
      }
      return _result;
    }

    uint64_t qtree_size() const {
      const qtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const qtree *_self;
      };

      /// _After_QNode: saves [a3, a1, a0, _s3], dispatches next recursive call.
      struct _After_QNode {
        const qtree *a3;
        const qtree *a1;
        const qtree *a0;
        std::decay_t<decltype(UINT64_C(1))> _s3;
      };

      /// _After_QNode_1: saves [_result, a1, a0, _s3], dispatches next
      /// recursive call.
      struct _After_QNode_1 {
        uint64_t _result;
        const qtree *a1;
        const qtree *a0;
        std::decay_t<decltype(UINT64_C(1))> _s3;
      };

      /// _After_QNode_2: saves [_result_0, _result_1, a0, _s3], dispatches next
      /// recursive call.
      struct _After_QNode_2 {
        uint64_t _result_0;
        uint64_t _result_1;
        const qtree *a0;
        std::decay_t<decltype(UINT64_C(1))> _s3;
      };

      /// _Combine_QNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_QNode {
        uint64_t _result_0;
        uint64_t _result_1;
        uint64_t _result_2;
        std::decay_t<decltype(UINT64_C(1))> _s3;
      };

      using _Frame = std::variant<_Enter, _After_QNode, _After_QNode_1,
                                  _After_QNode_2, _Combine_QNode>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified qtree_size: _Enter -> _After_QNode -> _After_QNode_1 ->
      /// _After_QNode_2 -> _Combine_QNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const qtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename qtree::QLeaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2, a3, a4] =
                std::get<typename qtree::QNode>(_sv.v());
            _stack.emplace_back(_After_QNode{crane_raw(a3), crane_raw(a1),
                                             crane_raw(a0), UINT64_C(1)});
            _stack.emplace_back(_Enter{crane_raw(a4)});
          }
        } else if (std::holds_alternative<_After_QNode>(_frame)) {
          auto _f = std::move(std::get<_After_QNode>(_frame));
          _stack.emplace_back(
              _After_QNode_1{std::move(_result), _f.a1, _f.a0, _f._s3});
          _stack.emplace_back(_Enter{_f.a3});
        } else if (std::holds_alternative<_After_QNode_1>(_frame)) {
          auto _f = std::move(std::get<_After_QNode_1>(_frame));
          _stack.emplace_back(
              _After_QNode_2{_f._result, std::move(_result), _f.a0, _f._s3});
          _stack.emplace_back(_Enter{_f.a1});
        } else if (std::holds_alternative<_After_QNode_2>(_frame)) {
          auto _f = std::move(std::get<_After_QNode_2>(_frame));
          _stack.emplace_back(_Combine_QNode{_f._result_0, _f._result_1,
                                             std::move(_result), _f._s3});
          _stack.emplace_back(_Enter{_f.a0});
        } else {
          auto _f = std::move(std::get<_Combine_QNode>(_frame));
          _result =
              ((((_f._s3 + std::move(_result)) + _f._result_2) + _f._result_1) +
               _f._result_0);
        }
      }
      return _result;
    }

    uint64_t qtree_depth() const {
      const qtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const qtree *_self;
      };

      /// _Cont_QNode: saves [a1, a3, a4], resumes after recursive call, then
      /// processes rest.
      struct _Cont_QNode {
        std::shared_ptr<qtree> a1;
        std::shared_ptr<qtree> a3;
        std::shared_ptr<qtree> a4;
      };

      /// _Cont_QNode_1: saves [a3, a4, da], resumes after recursive call, then
      /// processes rest.
      struct _Cont_QNode_1 {
        std::shared_ptr<qtree> a3;
        std::shared_ptr<qtree> a4;
        uint64_t da;
      };

      /// _Cont_QNode_2: saves [a4, da, db], resumes after recursive call, then
      /// processes rest.
      struct _Cont_QNode_2 {
        std::shared_ptr<qtree> a4;
        uint64_t da;
        uint64_t db;
      };

      /// _Cont_QNode_3: saves [da, db, dc], resumes after recursive call, then
      /// processes rest.
      struct _Cont_QNode_3 {
        uint64_t da;
        uint64_t db;
        uint64_t dc;
      };

      using _Frame = std::variant<_Enter, _Cont_QNode, _Cont_QNode_1,
                                  _Cont_QNode_2, _Cont_QNode_3>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified qtree_depth: _Enter -> _Cont_QNode -> _Cont_QNode_1 ->
      /// _Cont_QNode_2 -> _Cont_QNode_3.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const qtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename qtree::QLeaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2, a3, a4] =
                std::get<typename qtree::QNode>(_sv.v());
            _stack.emplace_back(_Cont_QNode{a1, a3, a4});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_Cont_QNode>(_frame)) {
          auto _f = std::move(std::get<_Cont_QNode>(_frame));
          std::shared_ptr<qtree> a1 = std::move(_f.a1);
          std::shared_ptr<qtree> a3 = std::move(_f.a3);
          std::shared_ptr<qtree> a4 = std::move(_f.a4);
          uint64_t da = std::move(_result);
          _stack.emplace_back(_Cont_QNode_1{std::move(a3), std::move(a4), da});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else if (std::holds_alternative<_Cont_QNode_1>(_frame)) {
          auto _f = std::move(std::get<_Cont_QNode_1>(_frame));
          std::shared_ptr<qtree> a3 = std::move(_f.a3);
          std::shared_ptr<qtree> a4 = std::move(_f.a4);
          uint64_t da = _f.da;
          uint64_t db = std::move(_result);
          _stack.emplace_back(_Cont_QNode_2{std::move(a4), da, db});
          _stack.emplace_back(_Enter{crane_raw(a3)});
        } else if (std::holds_alternative<_Cont_QNode_2>(_frame)) {
          auto _f = std::move(std::get<_Cont_QNode_2>(_frame));
          std::shared_ptr<qtree> a4 = std::move(_f.a4);
          uint64_t da = _f.da;
          uint64_t db = _f.db;
          uint64_t dc = std::move(_result);
          _stack.emplace_back(_Cont_QNode_3{da, db, dc});
          _stack.emplace_back(_Enter{crane_raw(a4)});
        } else {
          auto _f = std::move(std::get<_Cont_QNode_3>(_frame));
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

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const qtree *_self;
      };

      /// _After_QNode: saves [a3, a1, a0, a2], dispatches next recursive call.
      struct _After_QNode {
        const qtree *a3;
        const qtree *a1;
        const qtree *a0;
        uint64_t a2;
      };

      /// _After_QNode_1: saves [_result, a1, a0, a2], dispatches next recursive
      /// call.
      struct _After_QNode_1 {
        uint64_t _result;
        const qtree *a1;
        const qtree *a0;
        uint64_t a2;
      };

      /// _After_QNode_2: saves [_result_0, _result_1, a0, a2], dispatches next
      /// recursive call.
      struct _After_QNode_2 {
        uint64_t _result_0;
        uint64_t _result_1;
        const qtree *a0;
        uint64_t a2;
      };

      /// _Combine_QNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_QNode {
        uint64_t _result_0;
        uint64_t _result_1;
        uint64_t _result_2;
        uint64_t a2;
      };

      using _Frame = std::variant<_Enter, _After_QNode, _After_QNode_1,
                                  _After_QNode_2, _Combine_QNode>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified qtree_sum: _Enter -> _After_QNode -> _After_QNode_1 ->
      /// _After_QNode_2 -> _Combine_QNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const qtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename qtree::QLeaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2, a3, a4] =
                std::get<typename qtree::QNode>(_sv.v());
            _stack.emplace_back(
                _After_QNode{crane_raw(a3), crane_raw(a1), crane_raw(a0), a2});
            _stack.emplace_back(_Enter{crane_raw(a4)});
          }
        } else if (std::holds_alternative<_After_QNode>(_frame)) {
          auto _f = std::move(std::get<_After_QNode>(_frame));
          _stack.emplace_back(
              _After_QNode_1{std::move(_result), _f.a1, _f.a0, _f.a2});
          _stack.emplace_back(_Enter{_f.a3});
        } else if (std::holds_alternative<_After_QNode_1>(_frame)) {
          auto _f = std::move(std::get<_After_QNode_1>(_frame));
          _stack.emplace_back(
              _After_QNode_2{_f._result, std::move(_result), _f.a0, _f.a2});
          _stack.emplace_back(_Enter{_f.a1});
        } else if (std::holds_alternative<_After_QNode_2>(_frame)) {
          auto _f = std::move(std::get<_After_QNode_2>(_frame));
          _stack.emplace_back(_Combine_QNode{_f._result_0, _f._result_1,
                                             std::move(_result), _f.a2});
          _stack.emplace_back(_Enter{_f.a0});
        } else {
          auto _f = std::move(std::get<_Combine_QNode>(_frame));
          _result =
              ((((std::move(_result) + _f._result_2) + _f.a2) + _f._result_1) +
               _f._result_0);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, qtree &, T1 &, qtree &, T1 &,
                                     uint64_t &, qtree &, T1 &, qtree &, T1 &>
    T1 qtree_rec(T1 f, F1 &&f0) const {
      const qtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const qtree *_self;
      };

      /// _After_QNode: saves [a3_0, a1_0, a0_0, a4, a3_1, a2, a1_1, a0_1],
      /// dispatches next recursive call.
      struct _After_QNode {
        const qtree *a3_0;
        const qtree *a1_0;
        const qtree *a0_0;
        qtree a4;
        qtree a3_1;
        uint64_t a2;
        qtree a1_1;
        qtree a0_1;
      };

      /// _After_QNode_1: saves [_result, a1_0, a0_0, a4, a3, a2, a1_1, a0_1],
      /// dispatches next recursive call.
      struct _After_QNode_1 {
        std::decay_t<T1> _result;
        const qtree *a1_0;
        const qtree *a0_0;
        qtree a4;
        qtree a3;
        uint64_t a2;
        qtree a1_1;
        qtree a0_1;
      };

      /// _After_QNode_2: saves [_result_0, _result_1, a0_0, a4, a3, a2, a1,
      /// a0_1], dispatches next recursive call.
      struct _After_QNode_2 {
        std::decay_t<T1> _result_0;
        std::decay_t<T1> _result_1;
        const qtree *a0_0;
        qtree a4;
        qtree a3;
        uint64_t a2;
        qtree a1;
        qtree a0_1;
      };

      /// _Combine_QNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_QNode {
        std::decay_t<T1> _result_0;
        std::decay_t<T1> _result_1;
        std::decay_t<T1> _result_2;
        qtree a4;
        qtree a3;
        uint64_t a2;
        qtree a1;
        qtree a0;
      };

      using _Frame = std::variant<_Enter, _After_QNode, _After_QNode_1,
                                  _After_QNode_2, _Combine_QNode>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified qtree_rec: _Enter -> _After_QNode -> _After_QNode_1 ->
      /// _After_QNode_2 -> _Combine_QNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const qtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename qtree::QLeaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2, a3, a4] =
                std::get<typename qtree::QNode>(_sv.v());
            _stack.emplace_back(_After_QNode{crane_raw(a3), crane_raw(a1),
                                             crane_raw(a0), *a4, *a3, a2, *a1,
                                             *a0});
            _stack.emplace_back(_Enter{crane_raw(a4)});
          }
        } else if (std::holds_alternative<_After_QNode>(_frame)) {
          auto _f = std::move(std::get<_After_QNode>(_frame));
          _stack.emplace_back(
              _After_QNode_1{std::move(_result), _f.a1_0, _f.a0_0,
                             std::move(_f.a4), std::move(_f.a3_1), _f.a2,
                             std::move(_f.a1_1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a3_0});
        } else if (std::holds_alternative<_After_QNode_1>(_frame)) {
          auto _f = std::move(std::get<_After_QNode_1>(_frame));
          _stack.emplace_back(
              _After_QNode_2{std::move(_f._result), std::move(_result), _f.a0_0,
                             std::move(_f.a4), std::move(_f.a3), _f.a2,
                             std::move(_f.a1_1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a1_0});
        } else if (std::holds_alternative<_After_QNode_2>(_frame)) {
          auto _f = std::move(std::get<_After_QNode_2>(_frame));
          _stack.emplace_back(_Combine_QNode{
              std::move(_f._result_0), std::move(_f._result_1),
              std::move(_result), std::move(_f.a4), std::move(_f.a3), _f.a2,
              std::move(_f.a1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else {
          auto _f = std::move(std::get<_Combine_QNode>(_frame));
          _result = f0(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result_2), _f.a2, std::move(_f.a3),
                       std::move(_f._result_1), std::move(_f.a4),
                       std::move(_f._result_0));
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, qtree &, T1 &, qtree &, T1 &,
                                     uint64_t &, qtree &, T1 &, qtree &, T1 &>
    T1 qtree_rect(T1 f, F1 &&f0) const {
      const qtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const qtree *_self;
      };

      /// _After_QNode: saves [a3_0, a1_0, a0_0, a4, a3_1, a2, a1_1, a0_1],
      /// dispatches next recursive call.
      struct _After_QNode {
        const qtree *a3_0;
        const qtree *a1_0;
        const qtree *a0_0;
        qtree a4;
        qtree a3_1;
        uint64_t a2;
        qtree a1_1;
        qtree a0_1;
      };

      /// _After_QNode_1: saves [_result, a1_0, a0_0, a4, a3, a2, a1_1, a0_1],
      /// dispatches next recursive call.
      struct _After_QNode_1 {
        std::decay_t<T1> _result;
        const qtree *a1_0;
        const qtree *a0_0;
        qtree a4;
        qtree a3;
        uint64_t a2;
        qtree a1_1;
        qtree a0_1;
      };

      /// _After_QNode_2: saves [_result_0, _result_1, a0_0, a4, a3, a2, a1,
      /// a0_1], dispatches next recursive call.
      struct _After_QNode_2 {
        std::decay_t<T1> _result_0;
        std::decay_t<T1> _result_1;
        const qtree *a0_0;
        qtree a4;
        qtree a3;
        uint64_t a2;
        qtree a1;
        qtree a0_1;
      };

      /// _Combine_QNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_QNode {
        std::decay_t<T1> _result_0;
        std::decay_t<T1> _result_1;
        std::decay_t<T1> _result_2;
        qtree a4;
        qtree a3;
        uint64_t a2;
        qtree a1;
        qtree a0;
      };

      using _Frame = std::variant<_Enter, _After_QNode, _After_QNode_1,
                                  _After_QNode_2, _Combine_QNode>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified qtree_rect: _Enter -> _After_QNode -> _After_QNode_1 ->
      /// _After_QNode_2 -> _Combine_QNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const qtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename qtree::QLeaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2, a3, a4] =
                std::get<typename qtree::QNode>(_sv.v());
            _stack.emplace_back(_After_QNode{crane_raw(a3), crane_raw(a1),
                                             crane_raw(a0), *a4, *a3, a2, *a1,
                                             *a0});
            _stack.emplace_back(_Enter{crane_raw(a4)});
          }
        } else if (std::holds_alternative<_After_QNode>(_frame)) {
          auto _f = std::move(std::get<_After_QNode>(_frame));
          _stack.emplace_back(
              _After_QNode_1{std::move(_result), _f.a1_0, _f.a0_0,
                             std::move(_f.a4), std::move(_f.a3_1), _f.a2,
                             std::move(_f.a1_1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a3_0});
        } else if (std::holds_alternative<_After_QNode_1>(_frame)) {
          auto _f = std::move(std::get<_After_QNode_1>(_frame));
          _stack.emplace_back(
              _After_QNode_2{std::move(_f._result), std::move(_result), _f.a0_0,
                             std::move(_f.a4), std::move(_f.a3), _f.a2,
                             std::move(_f.a1_1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a1_0});
        } else if (std::holds_alternative<_After_QNode_2>(_frame)) {
          auto _f = std::move(std::get<_After_QNode_2>(_frame));
          _stack.emplace_back(_Combine_QNode{
              std::move(_f._result_0), std::move(_f._result_1),
              std::move(_result), std::move(_f.a4), std::move(_f.a3), _f.a2,
              std::move(_f.a1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else {
          auto _f = std::move(std::get<_Combine_QNode>(_frame));
          _result = f0(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result_2), _f.a2, std::move(_f.a3),
                       std::move(_f._result_1), std::move(_f.a4),
                       std::move(_f._result_0));
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

    template <typename _U> mylist(const mylist<_U> &_other) {
      if (std::holds_alternative<typename mylist<_U>::Mynil>(_other.v())) {
        this->v_ = Mynil{};
      } else {
        const auto &[a0, a1] =
            std::get<typename mylist<_U>::Mycons>(_other.v());
        this->v_ = Mycons{
            [&]() -> A {
              if constexpr (std::is_same_v<_U, std::any>) {
                if (a0.type() == typeid(A))
                  return std::any_cast<A>(a0);
                if constexpr (requires {
                                typename A::first_type;
                                typename A::second_type;
                              }) {
                  const auto &[_k, _v] =
                      std::any_cast<std::pair<std::any, std::any>>(a0);
                  return A{
                      [&]() -> typename A::first_type {
                        if constexpr (std::is_same_v<typename A::first_type,
                                                     std::any>)
                          return _k;
                        else
                          return std::any_cast<typename A::first_type>(_k);
                      }(),
                      [&]() -> typename A::second_type {
                        if constexpr (std::is_same_v<typename A::second_type,
                                                     std::any>)
                          return _v;
                        else
                          return std::any_cast<typename A::second_type>(_v);
                      }()};
                }
                return std::any_cast<A>(a0);
              } else
                return A(a0);
            }(),
            a1 ? std::make_shared<mylist<A>>(*a1) : nullptr};
      }
    }

    static mylist<A> mynil() { return mylist(Mynil{}); }

    static mylist<A> mycons(A a0, mylist<A> a1) {
      return mylist(
          Mycons{std::move(a0), std::make_shared<mylist<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      crane::small_vector<std::shared_ptr<mylist<A>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Mycons>(&_v)) {
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

    mylist(const mylist &) = default;
    mylist &operator=(const mylist &) = default;
    mylist(mylist &&) noexcept = default;
    mylist &operator=(mylist &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    mylist<A> myapp(mylist<A> l2) const {
      std::shared_ptr<mylist<A>> _head{};
      std::shared_ptr<mylist<A>> *_write = &_head;
      const mylist *_loop_self = this;
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

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, mylist<A> &, T1 &>
    T1 mylist_rec(T1 f, F1 &&f0) const {
      const mylist *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const mylist *_self;
      };

      /// _Resume_Mycons: saves [a1, a0], resumes after recursive call with
      /// _result.
      struct _Resume_Mycons {
        mylist<A> a1;
        std::decay_t<A> a0;
      };

      using _Frame = std::variant<_Enter, _Resume_Mycons>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified mylist_rec: _Enter -> _Resume_Mycons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const mylist *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] =
                std::get<typename mylist<A>::Mycons>(_sv.v());
            _stack.emplace_back(_Resume_Mycons{*a1, a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Mycons>(_frame));
          _result = f0(std::move(_f.a0), std::move(_f.a1), std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, mylist<A> &, T1 &>
    T1 mylist_rect(T1 f, F1 &&f0) const {
      const mylist *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const mylist *_self;
      };

      /// _Resume_Mycons: saves [a1, a0], resumes after recursive call with
      /// _result.
      struct _Resume_Mycons {
        mylist<A> a1;
        std::decay_t<A> a0;
      };

      using _Frame = std::variant<_Enter, _Resume_Mycons>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified mylist_rect: _Enter -> _Resume_Mycons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const mylist *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] =
                std::get<typename mylist<A>::Mycons>(_sv.v());
            _stack.emplace_back(_Resume_Mycons{*a1, a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Mycons>(_frame));
          _result = f0(std::move(_f.a0), std::move(_f.a1), std::move(_result));
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
