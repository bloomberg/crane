#ifndef INCLUDED_SEPEXTEPONYMOUSMODULEIND
#define INCLUDED_SEPEXTEPONYMOUSMODULEIND

#include <memory>
#include <optional>
#include <utility>
#include <variant>
#include <vector>

#include "Datatypes.h"

namespace SepExtEponymousModuleInd {

template <typename A> struct Trie {
  // TYPES
  struct Leaf {};

  struct Branch {
    std::optional<A> t;
    std::unique_ptr<Trie<A>> t0;
    std::unique_ptr<Trie<A>> t1;
  };

  using variant_t = std::variant<Leaf, Branch>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Trie() {}

  explicit Trie(Leaf _v) : v_(_v) {}

  explicit Trie(Branch _v) : v_(std::move(_v)) {}

  Trie(const Trie<A> &_other) : v_(std::move(_other.clone().v_)) {}

  Trie(Trie<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  Trie<A> &operator=(const Trie<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  Trie<A> &operator=(Trie<A> &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  Trie<A> clone() const {
    Trie<A> _out{};

    struct _CloneFrame {
      const Trie<A> *_src;
      Trie<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const Trie<A> *_src = _frame._src;
      Trie<A> *_dst = _frame._dst;
      if (std::holds_alternative<Leaf>(_src->v())) {
        _dst->v_ = Leaf{};
      } else {
        const auto &_alt = std::get<Branch>(_src->v());
        _dst->v_ =
            Branch{_alt.t, _alt.t0 ? std::make_unique<Trie<A>>() : nullptr,
                   _alt.t1 ? std::make_unique<Trie<A>>() : nullptr};
        auto &_dst_alt = std::get<Branch>(_dst->v_);
        if (_alt.t0) {
          _stack.push_back({_alt.t0.get(), _dst_alt.t0.get()});
        }
        if (_alt.t1) {
          _stack.push_back({_alt.t1.get(), _dst_alt.t1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit Trie(const Trie<_U> &_other) {
    if (std::holds_alternative<typename Trie<_U>::Leaf>(_other.v())) {
      this->v_ = Leaf{};
    } else {
      const auto &[t, t0, t1] = std::get<typename Trie<_U>::Branch>(_other.v());
      this->v_ = Branch{std::optional<A>(t),
                        t0 ? std::make_unique<Trie<A>>(*t0) : nullptr,
                        t1 ? std::make_unique<Trie<A>>(*t1) : nullptr};
    }
  }

  static Trie<A> leaf() { return Trie(Leaf{}); }

  static Trie<A> branch(std::optional<A> t, Trie<A> t0, Trie<A> t1) {
    return Trie(Branch{std::move(t), std::make_unique<Trie<A>>(std::move(t0)),
                       std::make_unique<Trie<A>>(std::move(t1))});
  }

  // MANIPULATORS
  ~Trie() {
    std::vector<std::unique_ptr<Trie<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](Trie<A> &_node) {
      if (std::holds_alternative<Branch>(_node.v_)) {
        auto &_alt = std::get<Branch>(_node.v_);
        if (_alt.t0) {
          _stack.push_back(std::move(_alt.t0));
        }
        if (_alt.t1) {
          _stack.push_back(std::move(_alt.t1));
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

struct UseTrie {
  using memo = Trie::Trie<std::optional<Datatypes::Nat>>;
};

} // namespace SepExtEponymousModuleInd

#endif // INCLUDED_SEPEXTEPONYMOUSMODULEIND
