#ifndef INCLUDED_POLY_INDUCTIVE
#define INCLUDED_POLY_INDUCTIVE

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct PolyInductive {
  template <typename A> struct pbox {
    // DATA
    A a0;

    // ACCESSORS
    pbox<A> clone() const { return {a0}; }

    // CREATORS
    static pbox<A> PBox_(A a0) { return {std::move(a0)}; }

    A punbox() const {
      const auto &_sv = *this;
      const auto &[a0] = _sv;
      return a0;
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &>
    T1 pbox_rec(F0 &&f) const {
      const auto &_sv = *this;
      const auto &[a0] = _sv;
      return f(a0);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &>
    T1 pbox_rect(F0 &&f) const {
      const auto &_sv = *this;
      const auto &[a0] = _sv;
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
      const auto &_sv = *this;
      const auto &[a0, a1] = _sv;
      return a1;
    }

    A pfst() const {
      const auto &_sv = *this;
      const auto &[a0, a1] = _sv;
      return a0;
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &, B &>
    T1 ppair_rec(F0 &&f) const {
      const auto &_sv = *this;
      const auto &[a0, a1] = _sv;
      return f(a0, a1);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &, B &>
    T1 ppair_rect(F0 &&f) const {
      const auto &_sv = *this;
      const auto &[a0, a1] = _sv;
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

    pmaybe(const pmaybe<A> &_other) : v_(_other.v_) {}

    pmaybe(pmaybe<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

    pmaybe<A> &operator=(const pmaybe<A> &_other) {
      v_ = _other.v_;
      return *this;
    }

    pmaybe<A> &operator=(pmaybe<A> &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    pmaybe<A> clone() const {
      if (std::holds_alternative<PNothing>(this->v())) {
        return pmaybe<A>(PNothing{});
      } else {
        const auto &[a0] = std::get<PJust>(this->v());
        return pmaybe<A>(PJust{a0});
      }
    }

    // CREATORS
    template <typename _U> explicit pmaybe(const pmaybe<_U> &_other) {
      if (std::holds_alternative<typename pmaybe<_U>::PNothing>(_other.v())) {
        this->v_ = PNothing{};
      } else {
        const auto &[a0] = std::get<typename pmaybe<_U>::PJust>(_other.v());
        this->v_ = PJust{A(a0)};
      }
    }

    static pmaybe<A> pnothing() { return pmaybe(PNothing{}); }

    static pmaybe<A> pjust(A a0) { return pmaybe(PJust{std::move(a0)}); }

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
      std::unique_ptr<ptree<A>> a0;
      std::unique_ptr<ptree<A>> a1;
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

    ptree(const ptree<A> &_other) : v_(std::move(_other.clone().v_)) {}

    ptree(ptree<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

    ptree<A> &operator=(const ptree<A> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    ptree<A> &operator=(ptree<A> &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    ptree<A> clone() const {
      ptree<A> _out{};

      struct _CloneFrame {
        const ptree<A> *_src;
        ptree<A> *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const ptree<A> *_src = _frame._src;
        ptree<A> *_dst = _frame._dst;
        if (std::holds_alternative<PLeaf>(_src->v())) {
          const auto &_alt = std::get<PLeaf>(_src->v());
          _dst->v_ = PLeaf{_alt.a0};
        } else {
          const auto &_alt = std::get<PNode>(_src->v());
          _dst->v_ = PNode{_alt.a0 ? std::make_unique<ptree<A>>() : nullptr,
                           _alt.a1 ? std::make_unique<ptree<A>>() : nullptr};
          auto &_dst_alt = std::get<PNode>(_dst->v_);
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
    template <typename _U> explicit ptree(const ptree<_U> &_other) {
      if (std::holds_alternative<typename ptree<_U>::PLeaf>(_other.v())) {
        const auto &[a0] = std::get<typename ptree<_U>::PLeaf>(_other.v());
        this->v_ = PLeaf{A(a0)};
      } else {
        const auto &[a0, a1] = std::get<typename ptree<_U>::PNode>(_other.v());
        this->v_ = PNode{a0 ? std::make_unique<ptree<A>>(*a0) : nullptr,
                         a1 ? std::make_unique<ptree<A>>(*a1) : nullptr};
      }
    }

    static ptree<A> pleaf(A a0) { return ptree(PLeaf{std::move(a0)}); }

    static ptree<A> pnode(ptree<A> a0, ptree<A> a1) {
      return ptree(PNode{std::make_unique<ptree<A>>(std::move(a0)),
                         std::make_unique<ptree<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~ptree() {
      std::vector<std::unique_ptr<ptree<A>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](ptree<A> &_node) {
        if (std::holds_alternative<PNode>(_node.v_)) {
          auto &_alt = std::get<PNode>(_node.v_);
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

    unsigned int ptree_size() const {
      if (std::holds_alternative<typename ptree<A>::PLeaf>(this->v())) {
        return 1u;
      } else {
        const auto &[a0, a1] = std::get<typename ptree<A>::PNode>(this->v());
        return (((*a0).ptree_size() + (*a1).ptree_size()) + 1);
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, A &> &&
               std::is_invocable_r_v<T1, F1 &, ptree<A> &, T1 &, ptree<A> &,
                                     T1 &>
    T1 ptree_rec(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename ptree<A>::PLeaf>(this->v())) {
        const auto &[a0] = std::get<typename ptree<A>::PLeaf>(this->v());
        return f(a0);
      } else {
        const auto &[a0, a1] = std::get<typename ptree<A>::PNode>(this->v());
        return f0(*a0, (*a0).template ptree_rec<T1>(f, f0), *a1,
                  (*a1).template ptree_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, A &> &&
               std::is_invocable_r_v<T1, F1 &, ptree<A> &, T1 &, ptree<A> &,
                                     T1 &>
    T1 ptree_rect(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename ptree<A>::PLeaf>(this->v())) {
        const auto &[a0] = std::get<typename ptree<A>::PLeaf>(this->v());
        return f(a0);
      } else {
        const auto &[a0, a1] = std::get<typename ptree<A>::PNode>(this->v());
        return f0(*a0, (*a0).template ptree_rect<T1>(f, f0), *a1,
                  (*a1).template ptree_rect<T1>(f, f0));
      }
    }
  };

  static inline const unsigned int test_pbox =
      pbox<unsigned int>::PBox_(42u).punbox();
  static inline const unsigned int test_ppair_fst =
      ppair<unsigned int, bool>::PPair_(7u, true).pfst();
  static inline const bool test_ppair_snd =
      ppair<unsigned int, bool>::PPair_(7u, true).psnd();
  static inline const unsigned int test_pjust =
      pmaybe<unsigned int>::pjust(99u).pmaybe_default(0u);
  static inline const unsigned int test_pnothing =
      pmaybe<unsigned int>::pnothing().pmaybe_default(0u);
  static inline const unsigned int test_pmap =
      pmaybe<unsigned int>::pjust(5u)
          .template pmaybe_map<unsigned int>(
              [](unsigned int x) { return (x + 1); })
          .pmaybe_default(0u);
  static inline const unsigned int test_ptree =
      ptree<unsigned int>::pnode(
          ptree<unsigned int>::pleaf(1u),
          ptree<unsigned int>::pnode(ptree<unsigned int>::pleaf(2u),
                                     ptree<unsigned int>::pleaf(3u)))
          .ptree_size();
};

#endif // INCLUDED_POLY_INDUCTIVE
