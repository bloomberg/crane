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
    std::shared_ptr<Trie<A>> t0;
    std::shared_ptr<Trie<A>> t1;
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

  template <typename _U> explicit Trie(const Trie<_U> &_other) {
    if (std::holds_alternative<typename Trie<_U>::Leaf>(_other.v())) {
      this->v_ = Leaf{};
    } else {
      const auto &[t, t0, t1] = std::get<typename Trie<_U>::Branch>(_other.v());
      this->v_ = Branch{std::optional<A>(t),
                        t0 ? std::make_shared<Trie<A>>(*t0) : nullptr,
                        t1 ? std::make_shared<Trie<A>>(*t1) : nullptr};
    }
  }

  static Trie<A> leaf() { return Trie(Leaf{}); }

  static Trie<A> branch(std::optional<A> t, Trie<A> t0, Trie<A> t1) {
    return Trie(Branch{std::move(t), std::make_shared<Trie<A>>(std::move(t0)),
                       std::make_shared<Trie<A>>(std::move(t1))});
  }

  // MANIPULATORS
  ~Trie() {
    std::vector<std::shared_ptr<Trie<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Branch>(&_v)) {
        if (_alt->t0) {
          _stack.push_back(std::move(_alt->t0));
        }
        if (_alt->t1) {
          _stack.push_back(std::move(_alt->t1));
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

struct UseTrie {
  using memo = Trie::Trie<std::optional<Datatypes::Nat>>;
};

} // namespace SepExtEponymousModuleInd

#endif // INCLUDED_SEPEXTEPONYMOUSMODULEIND
