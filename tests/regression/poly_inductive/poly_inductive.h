#ifndef INCLUDED_POLY_INDUCTIVE
#define INCLUDED_POLY_INDUCTIVE

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct PolyInductive {
  template <typename A> struct pbox {
    // DATA
    A a0;

    // ACCESSORS
    pbox<A> clone() const { return {a0}; }

    template <typename CraneU> operator pbox<CraneU>() const {
      return {[&]() -> CraneU {
        if constexpr (crane_convertible<CraneU, const A &>) {
          return crane_convert<CraneU>(a0);
        } else {
          throw std::logic_error(
              "unreachable: inactive constructor field at this instantiation");
        }
      }()};
    }

    // CREATORS
    static pbox<A> pbox0(A a0) { return {std::move(a0)}; }

    A punbox() const {
      const auto &[a0] = *this;
      return a0;
    }

    template <typename T1, typename F0> T1 pbox_rec(F0 &&f) const {
      return this->template pbox_rect<T1>(f);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, const A &>
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

    template <typename CraneU0, typename CraneU1>
    operator ppair<CraneU0, CraneU1>() const {
      return {[&]() -> CraneU0 {
                if constexpr (crane_convertible<CraneU0, const A &>) {
                  return crane_convert<CraneU0>(a0);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }(),
              [&]() -> CraneU1 {
                if constexpr (crane_convertible<CraneU1, const B &>) {
                  return crane_convert<CraneU1>(a1);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }()};
    }

    // CREATORS
    static ppair<A, B> ppair0(A a0, B a1) {
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

    template <typename T1, typename F0> T1 ppair_rec(F0 &&f) const {
      return this->template ppair_rect<T1>(f);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, const A &, const B &>
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

    template <typename CraneU>
    pmaybe(const pmaybe<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename pmaybe<CraneU>::PNothing>(
                    _other.v())) {
              return PNothing{};
            } else {
              const auto &[a0] =
                  std::get<typename pmaybe<CraneU>::PJust>(_other.v());
              return PJust{[&]() -> A {
                if constexpr (crane_convertible<A, const CraneU &>) {
                  return crane_convert<A>(a0);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }()};
            }
          }()) {}

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
      requires std::is_invocable_r_v<T1, F0 &, const A &>
    pmaybe<T1> pmaybe_map(F0 &&f) const {
      if (std::holds_alternative<typename pmaybe<A>::PNothing>(this->v())) {
        return pmaybe<T1>::pnothing();
      } else {
        const auto &[a0] = std::get<typename pmaybe<A>::PJust>(this->v());
        return pmaybe<T1>::pjust(f(a0));
      }
    }

    template <typename T1, typename F1>
    T1 pmaybe_rec(const T1 &f, F1 &&f0) const {
      return this->template pmaybe_rect<T1>(f, f0);
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, const A &>
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

    template <typename CraneU>
    ptree(const ptree<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename ptree<CraneU>::PLeaf>(
                    _other.v())) {
              const auto &[a0] =
                  std::get<typename ptree<CraneU>::PLeaf>(_other.v());
              return PLeaf{[&]() -> A {
                if constexpr (crane_convertible<A, const CraneU &>) {
                  return crane_convert<A>(a0);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }()};
            } else {
              const auto &[a0, a1] =
                  std::get<typename ptree<CraneU>::PNode>(_other.v());
              return PNode{
                  (a0 ? std::make_shared<ptree<A>>(crane_convert<ptree<A>>(*a0))
                      : nullptr),
                  (a1 ? std::make_shared<ptree<A>>(crane_convert<ptree<A>>(*a1))
                      : nullptr)};
            }
          }()) {}

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
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
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
    ptree(ptree &&) = default;
    ptree &operator=(ptree &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t ptree_size() const {
      const ptree<A> *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const ptree<A> *_self;
      };

      /// CraneCont_PNode: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_PNode {
        std::shared_ptr<ptree<A>> a1;
      };

      /// CraneCont_PNode_1: saves [_tmp2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_PNode_1 {
        uint64_t _tmp2;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_PNode, CraneCont_PNode_1>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified ptree_size: CraneEnter -> CraneCont_PNode ->
      /// CraneCont_PNode_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const ptree<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ptree<A>::PLeaf>(_sv.v())) {
            _result = UINT64_C(1);
          } else {
            const auto &[a0, a1] = std::get<typename ptree<A>::PNode>(_sv.v());
            _stack.emplace_back(CraneCont_PNode{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_PNode>(_frame)) {
          auto _f = std::move(std::get<CraneCont_PNode>(_frame));
          std::shared_ptr<ptree<A>> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_PNode_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<CraneCont_PNode_1>(_frame));
          _result = ((_f._tmp2 + std::move(_result)) + 1);
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
    T1 ptree_rec(F0 &&f, F1 &&f0) const {
      return this->template ptree_rect<T1>(f, f0);
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, const A &>
    T1 ptree_rect(F0 &&f, F1 &&f0) const {
      const ptree<A> *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const ptree<A> *_self;
      };

      /// CraneCont_PNode: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_PNode {
        std::shared_ptr<ptree<A>> a0;
        std::shared_ptr<ptree<A>> a1;
      };

      /// CraneCont_PNode_1: saves [_tmp2, a0, a1], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_PNode_1 {
        T1 _tmp2;
        std::shared_ptr<ptree<A>> a0;
        std::shared_ptr<ptree<A>> a1;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_PNode, CraneCont_PNode_1>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified ptree_rect: CraneEnter -> CraneCont_PNode ->
      /// CraneCont_PNode_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const ptree<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ptree<A>::PLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename ptree<A>::PLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1] = std::get<typename ptree<A>::PNode>(_sv.v());
            _stack.emplace_back(CraneCont_PNode{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_PNode>(_frame)) {
          auto _f = std::move(std::get<CraneCont_PNode>(_frame));
          std::shared_ptr<ptree<A>> a0 = std::move(_f.a0);
          std::shared_ptr<ptree<A>> a1 = std::move(_f.a1);
          _stack.emplace_back(
              CraneCont_PNode_1{std::move(_result), std::move(a0), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<CraneCont_PNode_1>(_frame));
          std::shared_ptr<ptree<A>> a0 = std::move(_f.a0);
          std::shared_ptr<ptree<A>> a1 = std::move(_f.a1);
          _result = f0(*a0, std::move(_f._tmp2), *a1, std::move(_result));
        }
      }
      return _result;
    }
  };

  static inline const uint64_t test_pbox =
      pbox<uint64_t>::pbox0(UINT64_C(42)).punbox();
  static inline const uint64_t test_ppair_fst =
      ppair<uint64_t, bool>::ppair0(UINT64_C(7), true).pfst();
  static inline const bool test_ppair_snd =
      ppair<uint64_t, bool>::ppair0(UINT64_C(7), true).psnd();
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
