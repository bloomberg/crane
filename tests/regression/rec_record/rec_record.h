#ifndef INCLUDED_REC_RECORD
#define INCLUDED_REC_RECORD

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <optional>
#include <type_traits>
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

    template <typename _U> rlist(const rlist<_U> &_other) {
      if (std::holds_alternative<typename rlist<_U>::Rnil>(_other.v())) {
        this->v_ = Rnil{};
      } else {
        const auto &[a0, a1] = std::get<typename rlist<_U>::Rcons>(_other.v());
        this->v_ = Rcons{
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
            a1 ? std::make_shared<rlist<A>>(*a1) : nullptr};
      }
    }

    static rlist<A> rnil() { return rlist<A>(Rnil{}); }

    static rlist<A> rcons(A a0, rlist<A> a1) {
      return rlist<A>(
          Rcons{std::move(a0), std::make_shared<rlist<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~rlist() {
      crane::small_vector<std::shared_ptr<rlist<A>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Rcons>(&_v)) {
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
          std::atomic_thread_fence(std::memory_order_acquire);
          _drain(_cur->v_mut());
        }
      }
    }

    rlist(const rlist &) = default;
    rlist &operator=(const rlist &) = default;
    rlist(rlist &&) noexcept = default;
    rlist &operator=(rlist &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t rlist_length() const {
      const rlist *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const rlist *_self;
      };

      /// _Resume_Rcons: resumes after recursive call with _result.
      struct _Resume_Rcons {};

      using _Frame = std::variant<_Enter, _Resume_Rcons>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified rlist_length: _Enter -> _Resume_Rcons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const rlist *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename rlist<A>::Rnil>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1] = std::get<typename rlist<A>::Rcons>(_sv.v());
            _stack.emplace_back(_Resume_Rcons{});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Rcons>(_frame));
          _result = (std::move(_result) + 1);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, rlist<A> &, T1 &>
    T1 rlist_rec(T1 f, F1 &&f0) const {
      const rlist *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const rlist *_self;
      };

      /// _Resume_Rcons: saves [a1, a0], resumes after recursive call with
      /// _result.
      struct _Resume_Rcons {
        rlist<A> a1;
        std::decay_t<A> a0;
      };

      using _Frame = std::variant<_Enter, _Resume_Rcons>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified rlist_rec: _Enter -> _Resume_Rcons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const rlist *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename rlist<A>::Rnil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = std::get<typename rlist<A>::Rcons>(_sv.v());
            _stack.emplace_back(_Resume_Rcons{*a1, a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Rcons>(_frame));
          _result = f0(std::move(_f.a0), std::move(_f.a1), std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, rlist<A> &, T1 &>
    T1 rlist_rect(T1 f, F1 &&f0) const {
      const rlist *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const rlist *_self;
      };

      /// _Resume_Rcons: saves [a1, a0], resumes after recursive call with
      /// _result.
      struct _Resume_Rcons {
        rlist<A> a1;
        std::decay_t<A> a0;
      };

      using _Frame = std::variant<_Enter, _Resume_Rcons>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified rlist_rect: _Enter -> _Resume_Rcons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const rlist *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename rlist<A>::Rnil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = std::get<typename rlist<A>::Rcons>(_sv.v());
            _stack.emplace_back(_Resume_Rcons{*a1, a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Rcons>(_frame));
          _result = f0(std::move(_f.a0), std::move(_f.a1), std::move(_result));
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
      return RNode(MkRNode{rn_value, std::make_shared<std::optional<RNode>>(
                                         std::move(rn_next))});
    }

    // MANIPULATORS
    ~RNode() {
      crane::small_vector<std::shared_ptr<RNode>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<MkRNode>(&_v)) {
          if (_alt->rn_next && _alt->rn_next.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            if (((*(_alt->rn_next))).has_value()) {
              _stack.push_back(
                  std::make_shared<RNode>(std::move((*((*(_alt->rn_next)))))));
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
    RNode(RNode &&) noexcept = default;
    RNode &operator=(RNode &&) noexcept = default;

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
      const auto &[rn_value0, rn_next1] =
          std::get<typename RNode::MkRNode>(this->v());
      return *rn_next1;
    }

    uint64_t rn_value() const {
      const auto &[rn_value1, rn_next0] =
          std::get<typename RNode::MkRNode>(this->v());
      return rn_value1;
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &,
                                     std::optional<RNode> &>
    T1 RNode_rec(F0 &&f) const {
      const auto &[rn_value1, rn_next1] =
          std::get<typename RNode::MkRNode>(this->v());
      return f(rn_value1, *rn_next1);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &,
                                     std::optional<RNode> &>
    T1 RNode_rect(F0 &&f) const {
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
      UINT64_C(1),
      std::make_optional<RNode>(RNode::mkrnode(
          UINT64_C(2), std::make_optional<RNode>(RNode::mkrnode(
                           UINT64_C(3), std::optional<RNode>())))));
  static inline const uint64_t test_rnode_depth = test_rnode.rnode_depth();
  static inline const Employee test_emp = Employee{UINT64_C(42), UINT64_C(7)};
  static inline const Department test_dept =
      Department{UINT64_C(7), test_emp, UINT64_C(50)};
  static inline const uint64_t test_dept_head_name =
      test_dept.dept_head.emp_name;
};

#endif // INCLUDED_REC_RECORD
