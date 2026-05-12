#ifndef INCLUDED_SEPEXTLISTCLONEQUAL
#define INCLUDED_SEPEXTLISTCLONEQUAL

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

#include "Datatypes.h"

namespace SepExtListCloneQual {

template <typename t_A> struct Forest {
  // TYPES
  struct Leaf {};

  struct Node {
    t_A d_a0;
    std::unique_ptr<typename Datatypes::template List<Forest<t_A>>> d_a1;
  };

  using variant_t = std::variant<Leaf, Node>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Forest() {}

  explicit Forest(Leaf _v) : d_v_(_v) {}

  explicit Forest(Node _v) : d_v_(std::move(_v)) {}

  Forest(const Forest<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Forest(Forest<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  Forest<t_A> &operator=(const Forest<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Forest<t_A> &operator=(Forest<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  Forest<t_A> clone() const {
    Forest<t_A> _out{};

    struct _CloneFrame {
      const Forest<t_A> *_src;
      Forest<t_A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const Forest<t_A> *_src = _frame._src;
      Forest<t_A> *_dst = _frame._dst;
      if (std::holds_alternative<Leaf>(_src->v())) {
        _dst->d_v_ = Leaf();
      } else {
        const auto &_alt = std::get<Node>(_src->v());
        _dst->d_v_ = Node(
            _alt.d_a0,
            _alt.d_a1 ? std::make_unique<
                            typename Datatypes::template List<Forest<t_A>>>()
                      : nullptr);
        auto &_dst_alt = std::get<Node>(_dst->d_v_);
        [&] {
          if (_alt.d_a1) {
            const Datatypes::List<Forest<t_A>> *_lsrc = _alt.d_a1.get();
            Datatypes::List<Forest<t_A>> *_ldst = _dst_alt.d_a1.get();
            while (std::holds_alternative<
                   typename Datatypes::List<Forest<t_A>>::Cons>(_lsrc->v())) {
              const auto &_lsrc_c =
                  std::get<typename Datatypes::List<Forest<t_A>>::Cons>(
                      _lsrc->v());
              _ldst->v_mut() = typename Datatypes::List<Forest<t_A>>::Cons{
                  Forest<t_A>{},
                  _lsrc_c.d_a1
                      ? std::make_unique<Datatypes::List<Forest<t_A>>>()
                      : nullptr};
              auto &_ldst_c =
                  std::get<typename Datatypes::List<Forest<t_A>>::Cons>(
                      _ldst->v_mut());
              _stack.push_back({&_lsrc_c.d_a0, &_ldst_c.d_a0});
              if (_lsrc_c.d_a1) {
                _lsrc = _lsrc_c.d_a1.get();
                _ldst = _ldst_c.d_a1.get();
              } else {
                break;
              }
            }
            if (std::holds_alternative<
                    typename Datatypes::List<Forest<t_A>>::Nil>(_lsrc->v())) {
              _ldst->v_mut() = typename Datatypes::List<Forest<t_A>>::Nil{};
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
      this->d_v_ = Leaf();
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename Forest<_U>::Node>(_other.v());
      this->d_v_ = Node(
          t_A(d_a0),
          d_a1 ? std::make_unique<
                     Datatypes::List<SepExtListCloneQual::Forest<t_A>>>(*d_a1)
               : nullptr);
    }
  }

  static Forest<t_A> leaf() { return Forest(Leaf()); }

  static Forest<t_A> node(t_A a0,
                          typename Datatypes::template List<Forest<t_A>> a1) {
    return Forest(
        Node(std::move(a0),
             std::make_unique<typename Datatypes::template List<Forest<t_A>>>(
                 std::move(a1))));
  }

  // MANIPULATORS
  ~Forest() {
    std::vector<std::unique_ptr<Forest<t_A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](Forest<t_A> &_node) {
      if (std::holds_alternative<Node>(_node.d_v_)) {
        auto &_alt = std::get<Node>(_node.d_v_);
        if (_alt.d_a1) {
          auto *_lp = _alt.d_a1.get();
          while (std::holds_alternative<
                 typename Datatypes::List<Forest<t_A>>::Cons>(_lp->v())) {
            auto &_lc = std::get<typename Datatypes::List<Forest<t_A>>::Cons>(
                _lp->v_mut());
            _stack.push_back(
                std::make_unique<Forest<t_A>>(std::move(_lc.d_a0)));
            if (_lc.d_a1) {
              _lp = _lc.d_a1.get();
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

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
};

} // namespace SepExtListCloneQual

#endif // INCLUDED_SEPEXTLISTCLONEQUAL
