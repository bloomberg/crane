#ifndef INCLUDED_HIGHER_KINDED
#define INCLUDED_HIGHER_KINDED

#include <any>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct HigherKinded {
  template <typename T1, typename T2 = void, typename T3 = void, typename F0,
            typename F1>
  static T1 hk_map(F0 &&map_f, F1 &&f, const T1 &x) {
    return std::any_cast<T1>(map_f(f, x));
  }

  template <typename A> struct Tree {
    // TYPES
    struct Leaf {
      A a0;
    };

    struct Branch {
      std::shared_ptr<Tree<A>> a0;
      std::shared_ptr<Tree<A>> a1;
    };

    using variant_t = std::variant<Leaf, Branch>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    Tree() {}

    explicit Tree(Leaf _v) : v_(std::move(_v)) {}

    explicit Tree(Branch _v) : v_(std::move(_v)) {}

    Tree(const Tree<A> &_other) : v_(std::move(_other.clone().v_)) {}

    Tree(Tree<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

    Tree<A> &operator=(const Tree<A> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    Tree<A> &operator=(Tree<A> &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    Tree<A> clone() const {
      Tree<A> _out{};

      struct _CloneFrame {
        const Tree<A> *_src;
        Tree<A> *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const Tree<A> *_src = _frame._src;
        Tree<A> *_dst = _frame._dst;
        if (std::holds_alternative<Leaf>(_src->v())) {
          const auto &_alt = std::get<Leaf>(_src->v());
          _dst->v_ = Leaf{_alt.a0};
        } else {
          const auto &_alt = std::get<Branch>(_src->v());
          _dst->v_ = Branch{_alt.a0 ? std::make_shared<Tree<A>>() : nullptr,
                            _alt.a1 ? std::make_shared<Tree<A>>() : nullptr};
          auto &_dst_alt = std::get<Branch>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    template <typename _U> explicit Tree(const Tree<_U> &_other) {
      if (std::holds_alternative<typename Tree<_U>::Leaf>(_other.v())) {
        const auto &[a0] = std::get<typename Tree<_U>::Leaf>(_other.v());
        this->v_ = Leaf{A(a0)};
      } else {
        const auto &[a0, a1] = std::get<typename Tree<_U>::Branch>(_other.v());
        this->v_ = Branch{a0 ? std::make_shared<Tree<A>>(*a0) : nullptr,
                          a1 ? std::make_shared<Tree<A>>(*a1) : nullptr};
      }
    }

    static Tree<A> leaf(A a0) { return Tree(Leaf{std::move(a0)}); }

    static Tree<A> branch(Tree<A> a0, Tree<A> a1) {
      return Tree(Branch{std::make_shared<Tree<A>>(std::move(a0)),
                         std::make_shared<Tree<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~Tree() {
      std::vector<std::shared_ptr<Tree<A>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](Tree<A> &_node) {
        if (std::holds_alternative<Branch>(_node.v_)) {
          auto &_alt = std::get<Branch>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
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

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F0, typename F1>
    requires std::is_invocable_r_v<T2, F0 &, T1 &> &&
             std::is_invocable_r_v<T2, F1 &, Tree<T1> &, T2 &, Tree<T1> &, T2 &>
  static T2 Tree_rect(F0 &&f, F1 &&f0, const Tree<T1> &t) {
    if (std::holds_alternative<typename Tree<T1>::Leaf>(t.v())) {
      const auto &[a0] = std::get<typename Tree<T1>::Leaf>(t.v());
      return f(a0);
    } else {
      const auto &[a0, a1] = std::get<typename Tree<T1>::Branch>(t.v());
      return f0(*a0, Tree_rect<T1, T2>(f, f0, *a0), *a1,
                Tree_rect<T1, T2>(f, f0, *a1));
    }
  }

  template <typename T1, typename T2, typename F0, typename F1>
    requires std::is_invocable_r_v<T2, F0 &, T1 &> &&
             std::is_invocable_r_v<T2, F1 &, Tree<T1> &, T2 &, Tree<T1> &, T2 &>
  static T2 Tree_rec(F0 &&f, F1 &&f0, const Tree<T1> &t) {
    if (std::holds_alternative<typename Tree<T1>::Leaf>(t.v())) {
      const auto &[a0] = std::get<typename Tree<T1>::Leaf>(t.v());
      return f(a0);
    } else {
      const auto &[a0, a1] = std::get<typename Tree<T1>::Branch>(t.v());
      return f0(*a0, Tree_rec<T1, T2>(f, f0, *a0), *a1,
                Tree_rec<T1, T2>(f, f0, *a1));
    }
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static Tree<T2> tree_map(F0 &&f, const Tree<T1> &t) {
    if (std::holds_alternative<typename Tree<T1>::Leaf>(t.v())) {
      const auto &[a0] = std::get<typename Tree<T1>::Leaf>(t.v());
      return Tree<T2>::leaf(f(a0));
    } else {
      const auto &[a0, a1] = std::get<typename Tree<T1>::Branch>(t.v());
      return Tree<T2>::branch(tree_map<T1, T2>(f, *a0),
                              tree_map<T1, T2>(f, *a1));
    }
  }

  template <typename T1, typename T2, typename F0, typename F1>
    requires std::is_invocable_r_v<T2, F0 &, T1 &> &&
             std::is_invocable_r_v<T2, F1 &, T2 &, T2 &>
  static T2 tree_fold(F0 &&leaf_f, F1 &&branch_f, const Tree<T1> &t) {
    if (std::holds_alternative<typename Tree<T1>::Leaf>(t.v())) {
      const auto &[a0] = std::get<typename Tree<T1>::Leaf>(t.v());
      return leaf_f(a0);
    } else {
      const auto &[a0, a1] = std::get<typename Tree<T1>::Branch>(t.v());
      return branch_f(tree_fold<T1, T2>(leaf_f, branch_f, *a0),
                      tree_fold<T1, T2>(leaf_f, branch_f, *a1));
    }
  }

  static uint64_t tree_sum(const Tree<uint64_t> &t);

  template <typename T1> static uint64_t tree_size(const Tree<T1> &t) {
    return tree_fold<T1, uint64_t>(
        [](const T1 &) { return UINT64_C(1); },
        [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); }, t);
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static std::optional<T2> map_option(F0 &&f, const std::optional<T1> &o) {
    if (o.has_value()) {
      const T1 &x = *o;
      return std::make_optional<T2>(f(x));
    } else {
      return std::optional<T2>();
    }
  }

  static inline const Tree<uint64_t> test_tree = Tree<uint64_t>::branch(
      Tree<uint64_t>::leaf(UINT64_C(1)),
      Tree<uint64_t>::branch(Tree<uint64_t>::leaf(UINT64_C(2)),
                             Tree<uint64_t>::leaf(UINT64_C(3))));
  static inline const uint64_t test_tree_sum = tree_sum(test_tree);
  static inline const uint64_t test_tree_size = tree_size<uint64_t>(test_tree);
  static inline const Tree<uint64_t> test_tree_map =
      tree_map<uint64_t, uint64_t>([](uint64_t n) { return (n * UINT64_C(2)); },
                                   test_tree);
  static inline const std::optional<uint64_t> test_hk_option = hk_map(
      []<typename _T1>(auto &&a0,
                       const std::optional<_T1> &a1) -> decltype(auto) {
        return map_option<_T1, std::invoke_result_t<decltype(a0) &, _T1 &>>(
            std::forward<decltype(a0)>(a0), a1);
      },
      [](uint64_t n) { return (n + UINT64_C(1)); },
      std::make_optional<uint64_t>(UINT64_C(5)));
  static inline const Tree<uint64_t> test_hk_tree = hk_map(
      []<typename _T1>(auto &&a0, const Tree<_T1> &a1) -> decltype(auto) {
        return tree_map<_T1, std::invoke_result_t<decltype(a0) &, _T1 &>>(
            std::forward<decltype(a0)>(a0), a1);
      },
      [](uint64_t n) { return (n + UINT64_C(10)); }, test_tree);
};

#endif // INCLUDED_HIGHER_KINDED
