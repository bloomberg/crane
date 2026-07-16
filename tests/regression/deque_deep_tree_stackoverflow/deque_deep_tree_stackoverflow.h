#ifndef INCLUDED_DEQUE_DEEP_TREE_STACKOVERFLOW
#define INCLUDED_DEQUE_DEEP_TREE_STACKOVERFLOW

#include <deque>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct DequeDeepTreeStackoverflow {
  struct rose {
    // TYPES
    struct RLeaf {
      uint64_t a0;
    };

    struct RNode {
      std::shared_ptr<std::deque<rose>> a0;
    };

    using variant_t = std::variant<RLeaf, RNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    rose() {}

    explicit rose(RLeaf _v) : v_(std::move(_v)) {}

    explicit rose(RNode _v) : v_(std::move(_v)) {}

    static rose rleaf(uint64_t a0) { return rose(RLeaf{a0}); }

    static rose rnode(std::deque<rose> a0) {
      return rose(RNode{std::make_shared<std::deque<rose>>(std::move(a0))});
    }

    // MANIPULATORS
    ~rose() {
      std::vector<std::shared_ptr<rose>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<RNode>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            for (auto &_elem : *_alt->a0) {
              _stack.push_back(std::make_shared<rose>(std::move(_elem)));
            }
            _alt->a0.reset();
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

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, std::deque<rose> &>
  static T1 rose_rect(F0 &&f, F1 &&f0, const rose &r) {
    if (std::holds_alternative<typename rose::RLeaf>(r.v())) {
      const auto &[a0] = std::get<typename rose::RLeaf>(r.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename rose::RNode>(r.v());
      return f0(*a0);
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, std::deque<rose> &>
  static T1 rose_rec(F0 &&f, F1 &&f0, const rose &r) {
    if (std::holds_alternative<typename rose::RLeaf>(r.v())) {
      const auto &[a0] = std::get<typename rose::RLeaf>(r.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename rose::RNode>(r.v());
      return f0(*a0);
    }
  }

  static rose deep_tree(uint64_t depth);
  static uint64_t test_deep(uint64_t n);
};

#endif // INCLUDED_DEQUE_DEEP_TREE_STACKOVERFLOW
