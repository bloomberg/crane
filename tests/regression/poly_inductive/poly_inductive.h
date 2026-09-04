#ifndef INCLUDED_POLY_INDUCTIVE
#define INCLUDED_POLY_INDUCTIVE

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct PolyInductive {
  template <typename A> struct pbox {
    // DATA
    A a0;

    // ACCESSORS
    pbox<A> clone() const { return {a0}; }

    // CREATORS
    static pbox<A> PBox_(A a0) { return {std::move(a0)}; }

    A punbox() const {
      const auto &[a0] = *this;
      return a0;
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &>
    T1 pbox_rec(F0 &&f) const {
      const auto &[a0] = *this;
      return f(a0);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &>
    T1 pbox_rect(F0 &&f) const {
      const auto &[a0] = *this;
      return f(a0);
    }
  };

  template <typename A, typename B> struct ppair {
    // DATA
    A a0;
    B a1;

    // ACCESSORS
    ppair<A, B> clone() const { return {a0, a1}; }

    // CREATORS
    static ppair<A, B> PPair_(A a0, B a1) {
      return {std::move(a0), std::move(a1)};
    }

    B psnd() const {
      const auto &[a0, a1] = *this;
      return a1;
    }

    A pfst() const {
      const auto &[a0, a1] = *this;
      return a0;
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &, B &>
    T1 ppair_rec(F0 &&f) const {
      const auto &[a0, a1] = *this;
      return f(a0, a1);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &, B &>
    T1 ppair_rect(F0 &&f) const {
      const auto &[a0, a1] = *this;
      return f(a0, a1);
    }
  };

  template <typename A> struct pmaybe {
    // TYPES
    struct PNothing {};

    struct PJust {
      A a0;
    };

    using variant_t = std::variant<PNothing, PJust>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    pmaybe() {}

    explicit pmaybe(PNothing _v) : v_(_v) {}

    explicit pmaybe(PJust _v) : v_(std::move(_v)) {}

    template <typename _U> pmaybe(const pmaybe<_U> &_other) {
      if (std::holds_alternative<typename pmaybe<_U>::PNothing>(_other.v())) {
        this->v_ = PNothing{};
      } else {
        const auto &[a0] = std::get<typename pmaybe<_U>::PJust>(_other.v());
        this->v_ = PJust{[&]() -> A {
          if constexpr (std::is_same_v<_U, std::any>)
            return crane_any_cast<A>(a0);
          else
            return A(a0);
        }()};
      }
    }

    static pmaybe<A> pnothing() { return pmaybe<A>(PNothing{}); }

    static pmaybe<A> pjust(A a0) { return pmaybe<A>(PJust{std::move(a0)}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    A pmaybe_default(A d) const {
      if (std::holds_alternative<typename pmaybe<A>::PNothing>(this->v())) {
        return d;
      } else {
        const auto &[a0] = std::get<typename pmaybe<A>::PJust>(this->v());
        return a0;
      }
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &>
    pmaybe<T1> pmaybe_map(F0 &&f) const {
      if (std::holds_alternative<typename pmaybe<A>::PNothing>(this->v())) {
        return pmaybe<T1>::pnothing();
      } else {
        const auto &[a0] = std::get<typename pmaybe<A>::PJust>(this->v());
        return pmaybe<T1>::pjust(f(a0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &>
    T1 pmaybe_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename pmaybe<A>::PNothing>(this->v())) {
        return f;
      } else {
        const auto &[a0] = std::get<typename pmaybe<A>::PJust>(this->v());
        return f0(a0);
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &>
    T1 pmaybe_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename pmaybe<A>::PNothing>(this->v())) {
        return f;
      } else {
        const auto &[a0] = std::get<typename pmaybe<A>::PJust>(this->v());
        return f0(a0);
      }
    }
  };

  template <typename A> struct ptree {
    // TYPES
    struct PLeaf {
      A a0;
    };

    struct PNode {
      std::shared_ptr<ptree<A>> a0;
      std::shared_ptr<ptree<A>> a1;
    };

    using variant_t = std::variant<PLeaf, PNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    ptree() {}

    explicit ptree(PLeaf _v) : v_(std::move(_v)) {}

    explicit ptree(PNode _v) : v_(std::move(_v)) {}

    template <typename _U> ptree(const ptree<_U> &_other) {
      if (std::holds_alternative<typename ptree<_U>::PLeaf>(_other.v())) {
        const auto &[a0] = std::get<typename ptree<_U>::PLeaf>(_other.v());
        this->v_ = PLeaf{[&]() -> A {
          if constexpr (std::is_same_v<_U, std::any>)
            return crane_any_cast<A>(a0);
          else
            return A(a0);
        }()};
      } else {
        const auto &[a0, a1] = std::get<typename ptree<_U>::PNode>(_other.v());
        this->v_ = PNode{(a0 ? std::make_shared<ptree<A>>(*a0) : nullptr),
                         (a1 ? std::make_shared<ptree<A>>(*a1) : nullptr)};
      }
    }

    static ptree<A> pleaf(A a0) { return ptree<A>(PLeaf{std::move(a0)}); }

    static ptree<A> pnode(ptree<A> a0, ptree<A> a1) {
      return ptree<A>(PNode{std::make_shared<ptree<A>>(std::move(a0)),
                            std::make_shared<ptree<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~ptree() {
      crane::small_vector<std::shared_ptr<ptree<A>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<PNode>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
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

    ptree(const ptree &) = default;
    ptree &operator=(const ptree &) = default;
    ptree(ptree &&) noexcept = default;
    ptree &operator=(ptree &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t ptree_size() const {
      const ptree<A> *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const ptree<A> *_self;
      };

      /// _After_PNode: saves [a0], dispatches next recursive call.
      struct _After_PNode {
        ptree<A> *a0;
      };

      /// _Combine_PNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_PNode {
        uint64_t _result;
      };

      using _Frame = std::variant<_Enter, _After_PNode, _Combine_PNode>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified ptree_size: _Enter -> _After_PNode -> _Combine_PNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ptree<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ptree<A>::PLeaf>(_sv.v())) {
            _result = UINT64_C(1);
          } else {
            const auto &[a0, a1] = std::get<typename ptree<A>::PNode>(_sv.v());
            _stack.emplace_back(_After_PNode{crane_raw(a0)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else if (std::holds_alternative<_After_PNode>(_frame)) {
          auto _f = std::move(std::get<_After_PNode>(_frame));
          _stack.emplace_back(_Combine_PNode{std::move(_result)});
          _stack.emplace_back(_Enter{_f.a0});
        } else {
          auto _f = std::move(std::get<_Combine_PNode>(_frame));
          _result = ((std::move(_result) + std::move(_f._result)) + 1);
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, A &> &&
               std::is_invocable_r_v<T1, F1 &, ptree<A> &, T1 &, ptree<A> &,
                                     T1 &>
    T1 ptree_rec(F0 &&f, F1 &&f0) const {
      const ptree<A> *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const ptree<A> *_self;
      };

      /// _After_PNode: saves [a0_0, a1, a0_1], dispatches next recursive call.
      struct _After_PNode {
        ptree<A> *a0_0;
        ptree<A> a1;
        ptree<A> a0_1;
      };

      /// _Combine_PNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_PNode {
        std::decay_t<T1> _result;
        ptree<A> a1;
        ptree<A> a0;
      };

      using _Frame = std::variant<_Enter, _After_PNode, _Combine_PNode>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified ptree_rec: _Enter -> _After_PNode -> _Combine_PNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ptree<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ptree<A>::PLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename ptree<A>::PLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1] = std::get<typename ptree<A>::PNode>(_sv.v());
            _stack.emplace_back(_After_PNode{crane_raw(a0), *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else if (std::holds_alternative<_After_PNode>(_frame)) {
          auto _f = std::move(std::get<_After_PNode>(_frame));
          _stack.emplace_back(_Combine_PNode{
              std::move(_result), std::move(_f.a1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else {
          auto _f = std::move(std::get<_Combine_PNode>(_frame));
          _result = f0(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, A &> &&
               std::is_invocable_r_v<T1, F1 &, ptree<A> &, T1 &, ptree<A> &,
                                     T1 &>
    T1 ptree_rect(F0 &&f, F1 &&f0) const {
      const ptree<A> *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const ptree<A> *_self;
      };

      /// _After_PNode: saves [a0_0, a1, a0_1], dispatches next recursive call.
      struct _After_PNode {
        ptree<A> *a0_0;
        ptree<A> a1;
        ptree<A> a0_1;
      };

      /// _Combine_PNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_PNode {
        std::decay_t<T1> _result;
        ptree<A> a1;
        ptree<A> a0;
      };

      using _Frame = std::variant<_Enter, _After_PNode, _Combine_PNode>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified ptree_rect: _Enter -> _After_PNode -> _Combine_PNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ptree<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ptree<A>::PLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename ptree<A>::PLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1] = std::get<typename ptree<A>::PNode>(_sv.v());
            _stack.emplace_back(_After_PNode{crane_raw(a0), *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else if (std::holds_alternative<_After_PNode>(_frame)) {
          auto _f = std::move(std::get<_After_PNode>(_frame));
          _stack.emplace_back(_Combine_PNode{
              std::move(_result), std::move(_f.a1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else {
          auto _f = std::move(std::get<_Combine_PNode>(_frame));
          _result = f0(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result));
        }
      }
      return _result;
    }
  };

  static inline const uint64_t test_pbox =
      pbox<uint64_t>::PBox_(UINT64_C(42)).punbox();
  static inline const uint64_t test_ppair_fst =
      ppair<uint64_t, bool>::PPair_(UINT64_C(7), true).pfst();
  static inline const bool test_ppair_snd =
      ppair<uint64_t, bool>::PPair_(UINT64_C(7), true).psnd();
  static inline const uint64_t test_pjust =
      pmaybe<uint64_t>::pjust(UINT64_C(99)).pmaybe_default(UINT64_C(0));
  static inline const uint64_t test_pnothing =
      pmaybe<uint64_t>::pnothing().pmaybe_default(UINT64_C(0));
  static inline const uint64_t test_pmap =
      pmaybe<uint64_t>::pjust(UINT64_C(5))
          .template pmaybe_map<uint64_t>([](uint64_t x) { return (x + 1); })
          .pmaybe_default(UINT64_C(0));
  static inline const uint64_t test_ptree =
      ptree<uint64_t>::pnode(
          ptree<uint64_t>::pleaf(UINT64_C(1)),
          ptree<uint64_t>::pnode(ptree<uint64_t>::pleaf(UINT64_C(2)),
                                 ptree<uint64_t>::pleaf(UINT64_C(3))))
          .ptree_size();
};

#endif // INCLUDED_POLY_INDUCTIVE
