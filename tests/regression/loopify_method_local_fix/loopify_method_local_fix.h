#ifndef INCLUDED_LOOPIFY_METHOD_LOCAL_FIX
#define INCLUDED_LOOPIFY_METHOD_LOCAL_FIX

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <utility>
#include <variant>

struct LoopifyMethodLocalFix {
  struct Tree {
    struct tree {
      // TYPES
      struct Leaf {};

      struct Node {
        std::shared_ptr<tree> a0;
        uint64_t a1;
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

      static tree node(tree a0, uint64_t a1) {
        return tree(Node{std::make_shared<tree>(std::move(a0)), a1});
      }

      // MANIPULATORS
      ~tree() {
        auto _next = [&](variant_t &_v) -> std::shared_ptr<tree> {
          if (auto *_alt = std::get_if<Node>(&_v)) {
            if (_alt->a0 && _alt->a0.use_count() == 1) {
              std::atomic_thread_fence(std::memory_order_acquire);
              return std::move(_alt->a0);
            }
          }
          return nullptr;
        };
        std::shared_ptr<tree> _cur = _next(v_mut());
        while (_cur) {
          _cur = _next(_cur->v_mut());
        }
      }

      tree(const tree &) = default;
      tree &operator=(const tree &) = default;
      tree(tree &&) = default;
      tree &operator=(tree &&) = default;

      inline variant_t &v_mut() { return v_; }

      // ACCESSORS
      const variant_t &v() const { return v_; }

      template <typename T1, typename F1> T1 tree_rect(T1 f, F1 &&f0) const {
        const tree *_self = this;

        /// CraneEnter: captures varying parameters for each recursive call.
        struct CraneEnter {
          const tree *_self;
        };

        /// CraneCont_Node: saves [a0, a1], resumes after recursive call, then
        /// processes rest.
        struct CraneCont_Node {
          std::shared_ptr<tree> a0;
          uint64_t a1;
        };

        using CraneFrame = std::variant<CraneEnter, CraneCont_Node>;
        T1 _result{};
        crane::small_vector<CraneFrame> _stack;
        _stack.emplace_back(CraneEnter{_self});
        /// Loopified tree_rect: CraneEnter -> CraneCont_Node.
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
              const auto &[a0, a1] = std::get<typename tree::Node>(_sv.v());
              _stack.emplace_back(CraneCont_Node{a0, a1});
              _stack.emplace_back(CraneEnter{crane_raw(a0)});
            }
          } else {
            auto _f = std::move(std::get<CraneCont_Node>(_frame));
            std::shared_ptr<tree> a0 = std::move(_f.a0);
            uint64_t a1 = _f.a1;
            _result = f0(*a0, std::move(_result), a1);
          }
        }
        return _result;
      }

      template <typename T1, typename F1> T1 tree_rec(T1 f, F1 &&f0) const {
        return this->template tree_rect<T1>(std::move(f), f0);
      }

      uint64_t drain(uint64_t n) const {
        const tree *_loop_self = this;
        uint64_t _loop_n = n;
        while (true) {
          auto &&_sv = *_loop_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            auto go = [](uint64_t k, uint64_t acc) -> uint64_t {
              uint64_t _loop_acc = acc;
              uint64_t _loop_k = k;
              while (true) {
                if (_loop_k <= 0) {
                  return _loop_acc;
                } else {
                  uint64_t k_ = _loop_k - 1;
                  _loop_acc = (_loop_acc + 1);
                  _loop_k = k_;
                }
              }
            };
            return go(_loop_n, UINT64_C(0));
          } else {
            const auto &[a0, a1] = std::get<typename tree::Node>(_sv.v());
            _loop_self = crane_raw(a0);
            _loop_n = (_loop_n + a1);
          }
        }
      }
    };
  };
};

#endif // INCLUDED_LOOPIFY_METHOD_LOCAL_FIX
