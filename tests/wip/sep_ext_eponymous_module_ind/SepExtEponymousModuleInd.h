#ifndef INCLUDED_SEPEXTEPONYMOUSMODULEIND
#define INCLUDED_SEPEXTEPONYMOUSMODULEIND

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

#include "Datatypes.h"

namespace SepExtEponymousModuleInd {

template <typename t_A> struct Trie {
  // TYPES
  struct Leaf {};

  struct Branch {
    std::optional<t_A> d_t;
    std::unique_ptr<Trie<t_A>> d_t0;
    std::unique_ptr<Trie<t_A>> d_t1;
  };

  using variant_t = std::variant<Leaf, Branch>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Trie() {}

  explicit Trie(Leaf _v) : d_v_(_v) {}

  explicit Trie(Branch _v) : d_v_(std::move(_v)) {}

  Trie(const Trie<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Trie(Trie<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  Trie<t_A> &operator=(const Trie<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Trie<t_A> &operator=(Trie<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  Trie<t_A> clone() const {
    Trie<t_A> _out{};

    struct _CloneFrame {
      const Trie<t_A> *_src;
      Trie<t_A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const Trie<t_A> *_src = _frame._src;
      Trie<t_A> *_dst = _frame._dst;
      if (std::holds_alternative<Leaf>(_src->v())) {
        _dst->d_v_ = Leaf{};
      } else {
        const auto &_alt = std::get<Branch>(_src->v());
        _dst->d_v_ = Branch{
            _alt.d_t, _alt.d_t0 ? std::make_unique<Trie<t_A>>() : nullptr,
            _alt.d_t1 ? std::make_unique<Trie<t_A>>() : nullptr};
        auto &_dst_alt = std::get<Branch>(_dst->d_v_);
        if (_alt.d_t0) {
          _stack.push_back({_alt.d_t0.get(), _dst_alt.d_t0.get()});
        }
        if (_alt.d_t1) {
          _stack.push_back({_alt.d_t1.get(), _dst_alt.d_t1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit Trie(const Trie<_U> &_other) {
    if (std::holds_alternative<typename Trie<_U>::Leaf>(_other.v())) {
      this->d_v_ = Leaf{};
    } else {
      const auto &[d_t, d_t0, d_t1] =
          std::get<typename Trie<_U>::Branch>(_other.v());
      this->d_v_ = Branch{std::optional<t_A>(d_t),
                          d_t0 ? std::make_unique<Trie<t_A>>(*d_t0) : nullptr,
                          d_t1 ? std::make_unique<Trie<t_A>>(*d_t1) : nullptr};
    }
  }

  static Trie<t_A> leaf() { return Trie(Leaf{}); }

  static Trie<t_A> branch(std::optional<t_A> t, Trie<t_A> t0, Trie<t_A> t1) {
    return Trie(Branch{std::move(t), std::make_unique<Trie<t_A>>(std::move(t0)),
                       std::make_unique<Trie<t_A>>(std::move(t1))});
  }

  // MANIPULATORS
  ~Trie() {
    std::vector<std::unique_ptr<Trie<t_A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](Trie<t_A> &_node) {
      if (std::holds_alternative<Branch>(_node.d_v_)) {
        auto &_alt = std::get<Branch>(_node.d_v_);
        if (_alt.d_t0) {
          _stack.push_back(std::move(_alt.d_t0));
        }
        if (_alt.d_t1) {
          _stack.push_back(std::move(_alt.d_t1));
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

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
};

struct UseTrie {
  using memo = Trie<std::optional<Datatypes::Nat>>;
};

} // namespace SepExtEponymousModuleInd

#endif // INCLUDED_SEPEXTEPONYMOUSMODULEIND
