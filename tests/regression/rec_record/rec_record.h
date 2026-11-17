#ifndef INCLUDED_REC_RECORD
#define INCLUDED_REC_RECORD

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

struct RecRecord {
  template <typename A> struct rlist {
    // TYPES
    struct Rnil {};

    struct Rcons {
      A a0;
      std::shared_ptr<rlist<A>> a1;
    };

    using variant_t = std::variant<Rnil, Rcons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    rlist() {}

    explicit rlist(Rnil _v) : v_(_v) {}

    explicit rlist(Rcons _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    rlist(const rlist<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename rlist<CraneU>::Rnil>(_other.v())) {
              return Rnil{};
            } else {
              const auto &[a0, a1] =
                  std::get<typename rlist<CraneU>::Rcons>(_other.v());
              return Rcons{
                  [&]() -> A {
                    if constexpr (crane_convertible<A, const CraneU &>) {
                      return crane_convert<A>(a0);
                    } else {
                      throw std::logic_error("unreachable: inactive "
                                             "constructor field at this "
                                             "instantiation");
                    }
                  }(),
                  (a1 ? std::make_shared<rlist<A>>(crane_convert<rlist<A>>(*a1))
                      : nullptr)};
            }
          }()) {}

    static rlist<A> rnil() { return rlist<A>(Rnil{}); }

    static rlist<A> rcons(A a0, rlist<A> a1) {
      return rlist<A>(
          Rcons{std::move(a0), std::make_shared<rlist<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~rlist() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      auto _next = [&](variant_t &_v) -> std::shared_ptr<rlist<A>> {
        if (auto *_alt = std::get_if<Rcons>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      std::shared_ptr<rlist<A>> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    rlist(const rlist &) = default;
    rlist &operator=(const rlist &) = default;
    rlist(rlist &&) = default;
    rlist &operator=(rlist &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t rlist_length() const {
      const rlist<A> *_self = this;

      // Explicit stack replaces the non-tail recursion of rlist_length: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const rlist<A> *_self;
      };

      struct _after_rlist_length_in_Rcons {};

      using _frame = std::variant<_call, _after_rlist_length_in_Rcons>;
      uint64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const rlist<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename rlist<A>::Rnil>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[_, a1] = std::get<typename rlist<A>::Rcons>(_sv.v());
            _stack.emplace_back(_after_rlist_length_in_Rcons{});
            _stack.emplace_back(_call{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_after_rlist_length_in_Rcons>(_popped));
          _stack.pop_back();
          _result = (std::move(_result) + 1);
        }
      }
      return _result;
    }

    template <typename T1, typename F1> T1 rlist_rec(T1 f, F1 &&f0) const {
      return this->template rlist_rect<T1>(std::move(f), f0);
    }

    template <typename T1, typename F1> T1 rlist_rect(T1 f, F1 &&f0) const {
      const rlist<A> *_self = this;

      // Explicit stack replaces the non-tail recursion of rlist_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const rlist<A> *_self;
      };

      struct _after_rlist_rect_in_Rcons {
        A a0;
        std::shared_ptr<rlist<A>> a1;
      };

      using _frame = std::variant<_call, _after_rlist_rect_in_Rcons>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const rlist<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename rlist<A>::Rnil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = std::get<typename rlist<A>::Rcons>(_sv.v());
            _stack.emplace_back(_after_rlist_rect_in_Rcons{a0, a1});
            _stack.emplace_back(_call{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_after_rlist_rect_in_Rcons>(_popped));
          _stack.pop_back();
          auto a0 = std::move(_f.a0);
          std::shared_ptr<rlist<A>> a1 = std::move(_f.a1);
          _result = f0(a0, *a1, std::move(_result));
        }
      }
      return _result;
    }
  };

  struct RNode {
    // TYPES
    struct MkRNode {
      uint64_t rn_value;
      std::shared_ptr<std::optional<RNode>> rn_next;
    };

    using variant_t = std::variant<MkRNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    RNode() {}

    explicit RNode(MkRNode _v) : v_(std::move(_v)) {}

    static RNode mkrnode(uint64_t rn_value, std::optional<RNode> rn_next) {
      return RNode(MkRNode{
          rn_value,
          std::make_shared<std::optional<RNode>>(std::move(rn_next))});
    }

    // MANIPULATORS
    ~RNode() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      crane::small_vector<std::shared_ptr<RNode>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<MkRNode>(&_v)) {
          if (_alt->rn_next && _alt->rn_next.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            if ((*_alt->rn_next).has_value()) {
              _stack.push_back(
                  std::make_shared<RNode>(std::move(*(*_alt->rn_next))));
            }
            _alt->rn_next.reset();
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

    RNode(const RNode &) = default;
    RNode &operator=(const RNode &) = default;
    RNode(RNode &&) = default;
    RNode &operator=(RNode &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t rnode_depth() const {
      auto _cs = this->rn_next();
      if (_cs.has_value()) {
        const RNode &next = *_cs;
        return (next.rnode_depth() + 1);
      } else {
        return UINT64_C(1);
      }
    }

    std::optional<RNode> rn_next() const {
      const auto &[_, rn_next1] = std::get<typename RNode::MkRNode>(this->v());
      return *rn_next1;
    }

    uint64_t rn_value() const {
      const auto &[rn_value1, _] = std::get<typename RNode::MkRNode>(this->v());
      return rn_value1;
    }

    template <typename T1, typename F0> T1 RNode_rec(F0 &&f) const {
      return this->template RNode_rect<T1>(f);
    }

    template <typename T1, typename F0> T1 RNode_rect(F0 &&f) const {
      const auto &[rn_value1, rn_next1] =
          std::get<typename RNode::MkRNode>(this->v());
      return f(rn_value1, *rn_next1);
    }
  };

  struct Employee {
    uint64_t emp_name;
    uint64_t emp_dept;
  };

  struct Department {
    uint64_t dept_id;
    Employee dept_head;
    uint64_t dept_size;
  };

  static uint64_t rlist_sum(const rlist<uint64_t> &l);
  static inline const rlist<uint64_t> test_rlist = rlist<uint64_t>::rcons(
      UINT64_C(1), rlist<uint64_t>::rcons(
                       UINT64_C(2), rlist<uint64_t>::rcons(
                                        UINT64_C(3), rlist<uint64_t>::rnil())));
  static inline const uint64_t test_rlist_len = test_rlist.rlist_length();
  static inline const uint64_t test_rlist_sum = rlist_sum(test_rlist);
  static inline const RNode test_rnode = RNode::mkrnode(
      UINT64_C(1), std::make_optional<RNode>(RNode::mkrnode(
                       UINT64_C(2), std::make_optional<RNode>(RNode::mkrnode(
                                        UINT64_C(3),
                                        std::optional<RNode>())))));
  static inline const uint64_t test_rnode_depth = test_rnode.rnode_depth();
  static inline const Employee test_emp = Employee{UINT64_C(42), UINT64_C(7)};
  static inline const Department test_dept =
      Department{UINT64_C(7), test_emp, UINT64_C(50)};
  static inline const uint64_t test_dept_head_name =
      test_dept.dept_head.emp_name;
};

#endif // INCLUDED_REC_RECORD
