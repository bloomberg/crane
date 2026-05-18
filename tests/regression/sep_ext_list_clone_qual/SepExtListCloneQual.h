#ifndef INCLUDED_SEPEXTLISTCLONEQUAL
#define INCLUDED_SEPEXTLISTCLONEQUAL

#include <memory>
#include <utility>
#include <variant>
#include <vector>

#include "Datatypes.h"

namespace SepExtListCloneQual {

template <typename A> struct Forest {
  // TYPES
  struct Leaf {};

  struct Node {
    A a0;
    std::unique_ptr<typename Datatypes::template List<Forest<A>>> a1;
  };

  using variant_t = std::variant<Leaf, Node>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Forest() {}

  explicit Forest(Leaf _v) : v_(_v) {}

  explicit Forest(Node _v) : v_(std::move(_v)) {}

  Forest(const Forest<A> &_other) : v_(std::move(_other.clone().v_)) {}

  Forest(Forest<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  Forest<A> &operator=(const Forest<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  Forest<A> &operator=(Forest<A> &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  Forest<A> clone() const {
    Forest<A> _out{};

    struct _CloneFrame {
      const Forest<A> *_src;
      Forest<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const Forest<A> *_src = _frame._src;
      Forest<A> *_dst = _frame._dst;
      if (std::holds_alternative<Leaf>(_src->v())) {
        _dst->v_ = Leaf{};
      } else {
        const auto &_alt = std::get<Node>(_src->v());
        _dst->v_ =
            Node{_alt.a0,
                 _alt.a1 ? std::make_unique<
                               typename Datatypes::template List<Forest<A>>>()
                         : nullptr};
        auto &_dst_alt = std::get<Node>(_dst->v_);
        [&] {
          if (_alt.a1) {
            const Datatypes::List<Forest<A>> *_lsrc = _alt.a1.get();
            Datatypes::List<Forest<A>> *_ldst = _dst_alt.a1.get();
            while (std::holds_alternative<
                   typename Datatypes::List<Forest<A>>::Cons>(_lsrc->v())) {
              const auto &_lsrc_c =
                  std::get<typename Datatypes::List<Forest<A>>::Cons>(
                      _lsrc->v());
              _ldst->v_mut() = typename Datatypes::List<Forest<A>>::Cons{
                  Forest<A>{},
                  _lsrc_c.l ? std::make_unique<Datatypes::List<Forest<A>>>()
                            : nullptr};
              auto &_ldst_c =
                  std::get<typename Datatypes::List<Forest<A>>::Cons>(
                      _ldst->v_mut());
              _stack.push_back({&_lsrc_c.a, &_ldst_c.a});
              if (_lsrc_c.l) {
                _lsrc = _lsrc_c.l.get();
                _ldst = _ldst_c.l.get();
              } else {
                break;
              }
            }
            if (std::holds_alternative<
                    typename Datatypes::List<Forest<A>>::Nil>(_lsrc->v())) {
              _ldst->v_mut() = typename Datatypes::List<Forest<A>>::Nil{};
            }
          }
        }();
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit Forest(const Forest<_U> &_other) {
    if (std::holds_alternative<typename Forest<_U>::Leaf>(_other.v())) {
      this->v_ = Leaf{};
    } else {
      const auto &[a0, a1] = std::get<typename Forest<_U>::Node>(_other.v());
      this->v_ = Node{
          A(a0), a1 ? std::make_unique<
                          Datatypes::List<SepExtListCloneQual::Forest<A>>>(*a1)
                    : nullptr};
    }
  }

  static Forest<A> leaf() { return Forest(Leaf{}); }

  static Forest<A> node(A a0, typename Datatypes::template List<Forest<A>> a1) {
    return Forest(
        Node{std::move(a0),
             std::make_unique<typename Datatypes::template List<Forest<A>>>(
                 std::move(a1))});
  }

  // MANIPULATORS
  ~Forest() {
    std::vector<std::unique_ptr<Forest<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](Forest<A> &_node) {
      if (std::holds_alternative<Node>(_node.v_)) {
        auto &_alt = std::get<Node>(_node.v_);
        if (_alt.a1) {
          auto *_lp = _alt.a1.get();
          while (
              std::holds_alternative<typename Datatypes::List<Forest<A>>::Cons>(
                  _lp->v())) {
            auto &_lc = std::get<typename Datatypes::List<Forest<A>>::Cons>(
                _lp->v_mut());
            _stack.push_back(std::make_unique<Forest<A>>(std::move(_lc.a)));
            if (_lc.l) {
              _lp = _lc.l.get();
            } else {
              break;
            }
          }
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

} // namespace SepExtListCloneQual

#endif // INCLUDED_SEPEXTLISTCLONEQUAL
