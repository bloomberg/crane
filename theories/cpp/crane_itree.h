// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Reified interaction tree: a deferred computation that can be run or
// inspected.  R is the result type (use void for effectful computations
// that produce no value).  Tau is intentionally omitted -- it is a
// coinductive guardedness marker with no runtime meaning.
//
// Invariants (enforced here so host/generated code cannot forge invalid
// nodes):
//   * Nodes are only constructible through the ret/tau/vis factories, which
//     return a std::shared_ptr.  The constructor takes a private passkey, so
//     external code cannot build a node from a hand-crafted variant or stack
//     allocate one (a stack ITree would make shared_from_this throw)
//     (CWE-665 / CWE-476, finding 132).
//   * A Tau's next pointer and a Vis continuation's result are never null:
//     the factories reject a null argument up front and run() rechecks the
//     continuation result before dereferencing it (finding 132).
//   * run() keeps the current node alive for the whole loop via
//     shared_from_this -- including the void specialization, which must not
//     fabricate a non-owning alias of [this] that an effect could outlive
//     (CWE-416, finding 86).
//
// run() intentionally has no step budget: an itree is coinductive and may be
// legitimately infinite, so bounding it here would be wrong.  A caller that
// needs to stop a divergent computation controls that at its own effect
// boundary.

#ifndef INCLUDED_CRANE_ITREE
#define INCLUDED_CRANE_ITREE

#include <any>
#include <functional>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <variant>

#include "crane_fn.h"  // crane_any_cast

template <typename R>
struct ITree : public std::enable_shared_from_this<ITree<R>> {
    // The tree's own result type, for helpers that have only the pointer.
    using result_type = R;

    struct Ret { R value; };
    struct Tau { std::shared_ptr<ITree<R>> next; };
    struct Vis {
        std::function<std::any()> effect;
        std::function<std::shared_ptr<ITree<R>>(std::any)> cont;
    };
    using variant_t = std::variant<Ret, Tau, Vis>;
    variant_t node;

  private:
    // Passkey: only ITree's own factories can name it, so the public
    // constructor cannot be called from outside despite make_shared needing it.
    struct Private { explicit Private() = default; };

  public:
    ITree(Private, variant_t n) : node(std::move(n)) {}

    static std::shared_ptr<ITree<R>> ret(R value) {
        return std::make_shared<ITree<R>>(Private{}, Ret{std::move(value)});
    }
    static std::shared_ptr<ITree<R>> tau(std::shared_ptr<ITree<R>> next) {
        if (!next)
            throw std::invalid_argument("crane: ITree::tau given a null next");
        return std::make_shared<ITree<R>>(Private{}, Tau{std::move(next)});
    }
    static std::shared_ptr<ITree<R>> vis(
        std::function<std::any()> effect,
        std::function<std::shared_ptr<ITree<R>>(std::any)> cont) {
        if (!effect || !cont)
            throw std::invalid_argument("crane: ITree::vis given a null effect or continuation");
        return std::make_shared<ITree<R>>(Private{}, Vis{std::move(effect), std::move(cont)});
    }

    R run() {
        // Hold an owning reference to the current node for the whole loop:
        // effects and continuations may drop every other owner, so a
        // non-owning alias would dangle (finding 86).
        auto cur = this->shared_from_this();
        while (true) {
            // Copy (not move) the payload: cur is reached via shared_ptr and
            // observe() lets callers hold onto and re-run the same tree, so
            // moving out of a shared node would corrupt it for later runs
            // (finding 37, CWE-664).
            if (auto *r = std::get_if<Ret>(&cur->node))
                return r->value;
            if (auto *t = std::get_if<Tau>(&cur->node)) {
                if (!t->next)
                    throw std::runtime_error("crane: ITree Tau has a null next");
                cur = t->next;
                continue;
            }
            auto &v = std::get<Vis>(cur->node);
            std::any response = v.effect();
            auto next = v.cont(std::move(response));
            if (!next)
                throw std::runtime_error("crane: ITree Vis continuation returned null");
            cur = std::move(next);
        }
    }
    const variant_t &observe() const { return node; }
};

// Void specialization (Ret holds nothing).
template <>
struct ITree<void> : public std::enable_shared_from_this<ITree<void>> {
    using result_type = void;

    struct Ret { std::monostate value = {}; };
    struct Tau { std::shared_ptr<ITree<void>> next; };
    struct Vis {
        std::function<std::any()> effect;
        std::function<std::shared_ptr<ITree<void>>(std::any)> cont;
    };
    using variant_t = std::variant<Ret, Tau, Vis>;
    variant_t node;

  private:
    struct Private { explicit Private() = default; };

  public:
    ITree(Private, variant_t n) : node(std::move(n)) {}

    static std::shared_ptr<ITree<void>> ret() {
        return std::make_shared<ITree<void>>(Private{}, Ret{});
    }
    static std::shared_ptr<ITree<void>> ret(std::monostate) {
        return std::make_shared<ITree<void>>(Private{}, Ret{});
    }
    static std::shared_ptr<ITree<void>> tau(std::shared_ptr<ITree<void>> next) {
        if (!next)
            throw std::invalid_argument("crane: ITree::tau given a null next");
        return std::make_shared<ITree<void>>(Private{}, Tau{std::move(next)});
    }
    static std::shared_ptr<ITree<void>> vis(
        std::function<std::any()> effect,
        std::function<std::shared_ptr<ITree<void>>(std::any)> cont) {
        if (!effect || !cont)
            throw std::invalid_argument("crane: ITree::vis given a null effect or continuation");
        return std::make_shared<ITree<void>>(Private{}, Vis{std::move(effect), std::move(cont)});
    }

    void run() {
        // Owning reference (not a non-owning alias of [this]): an effect or
        // continuation may release the last other owner mid-run (finding 86).
        auto cur = this->shared_from_this();
        while (true) {
            if (std::holds_alternative<Ret>(cur->node))
                return;
            if (auto *t = std::get_if<Tau>(&cur->node)) {
                if (!t->next)
                    throw std::runtime_error("crane: ITree Tau has a null next");
                cur = t->next;
                continue;
            }
            auto &v = std::get<Vis>(cur->node);
            std::any response = v.effect();
            auto next = v.cont(std::move(response));
            if (!next)
                throw std::runtime_error("crane: ITree Vis continuation returned null");
            cur = std::move(next);
        }
    }
    const variant_t &observe() const { return node; }
};

// Type alias for itreeF — makes template argument deduction work
// (typename ITree<R>::variant_t is a non-deduced context).
template<typename R>
using itreeF_t = typename ITree<R>::variant_t;

// Bind: graft the continuation onto every leaf of the first tree.
//
// A tree is data, so binding it performs no effect: a Ret hands its value to
// the continuation, a Vis keeps its event and binds whatever its own
// continuation yields, and a Tau keeps the step.  Only run() performs
// anything, which is what lets a tree be built over an event nothing here
// knows how to interpret.
//
// The continuation is taken by value, not by forwarding reference: a Vis
// stores it in the node it returns, which outlives this call.  K stays a
// generic callable (not a std::function) so lambdas deduce against it.
template<typename A, typename K>
auto itree_bind(std::shared_ptr<ITree<A>> m, K k)
    -> decltype(k(std::declval<A>())) {
    using tree_b = decltype(k(std::declval<A>()));
    using node_b = typename tree_b::element_type;
    if (!m)
        throw std::invalid_argument("crane: itree_bind given a null tree");
    if (auto *r = std::get_if<typename ITree<A>::Ret>(&m->node))
        return k(r->value);
    if (auto *t = std::get_if<typename ITree<A>::Tau>(&m->node))
        return node_b::tau(itree_bind(t->next, k));
    auto &v = std::get<typename ITree<A>::Vis>(m->node);
    auto cont = v.cont;
    return node_b::vis(
        v.effect,
        std::function<tree_b(std::any)>(
            [cont, k](std::any x) { return itree_bind(cont(std::move(x)), k); }));
}

// Bind specialization for void first argument.
template<typename K>
auto itree_bind(std::shared_ptr<ITree<void>> m, K k)
    -> decltype(k()) {
    using tree_b = decltype(k());
    using node_b = typename tree_b::element_type;
    if (!m)
        throw std::invalid_argument("crane: itree_bind given a null tree");
    if (std::get_if<typename ITree<void>::Ret>(&m->node))
        return k();
    if (auto *t = std::get_if<typename ITree<void>::Tau>(&m->node))
        return node_b::tau(itree_bind(t->next, k));
    auto &v = std::get<typename ITree<void>::Vis>(m->node);
    auto cont = v.cont;
    return node_b::vis(
        v.effect,
        std::function<tree_b(std::any)>(
            [cont, k](std::any x) { return itree_bind(cont(std::move(x)), k); }));
}

// Ret constructor with template argument deduction.  The result type is
// decayed: the argument commonly arrives as an xvalue (`std::move(n)`), and
// naming its `decltype` directly would ask for an `ITree<R&&>`.
template<typename A>
auto itree_ret(A &&value) {
    return ITree<std::decay_t<A>>::ret(std::forward<A>(value));
}

// The dictionary the reified mode's monad presents when a generic definition
// asks for one.  A tree's `bind` and `ret` are named by their own mappings
// wherever they are written directly, so nothing here is reachable from
// ordinary generated code; what needs it is a *constrained* template --
// `Monad_stateT<Monad_itree, S>` -- whose parameter is spelled by the
// generated `Monad` concept and so has to be satisfied by a real type.
//
// Parameterised by the event family, as the Rocq instance is; reified trees
// carry their events at the node rather than in the tree's type, so the
// parameter is unused here and defaulted for the erased spellings.
template<typename E = void>
struct Monad_itree {
    template<typename A> using m = std::shared_ptr<ITree<A>>;

    template<typename A>
    static m<A> ret(A x) { return itree_ret(std::move(x)); }

    template<typename A, typename B>
    static m<B> bind(m<A> t, std::function<m<B>(A)> k) {
        return itree_bind(std::move(t), std::move(k));
    }
};

// The `Functor` half of the same story.  `interp` is constrained by all three
// of `Functor`, `Monad` and `MonadIter`, and a constraint is discharged by
// naming a type that satisfies the concept: skipped, the instance left the
// template parameter with nothing to be, and it is not deducible from the
// arguments either.
template<typename E = void>
struct Functor_itree {
    template<typename A> using F = std::shared_ptr<ITree<A>>;

    template<typename A, typename B>
    static F<B> fmap(std::function<B(A)> f, F<A> t) {
        return itree_bind(std::move(t),
                          std::function<F<B>(A)>([f](A a) { return itree_ret(f(a)); }));
    }
};

// Tau constructor with template argument deduction.
template<typename R>
auto itree_tau(std::shared_ptr<ITree<R>> next) {
    return ITree<R>::tau(std::move(next));
}

// `ITree.iter step i` calls `step` until it answers with the sum's right
// injection.  The loop is written as a `Tau`-guarded self-call rather than a
// C++ loop: the tree it builds is the tree Rocq's definition denotes, and an
// iteration that never answers is then a divergent tree rather than a hang.
//
// The sum is whatever Crane generated for `I + R` in the caller's file, so it
// is read through the shape every Crane variant has -- `v()`, a nested `Inl`
// and `Inr` -- and its payloads through structured bindings, which do not
// depend on the field's name.
template<typename Sum>
auto itree_iter_rhs(const Sum &s) {
    const auto &[r] = *std::get_if<typename Sum::Inr>(&s.v());
    return r;
}

template<typename Step, typename I>
auto itree_iter(Step step, I i)
    -> std::shared_ptr<ITree<decltype(itree_iter_rhs(
        std::declval<typename decltype(step(i))::element_type::result_type>()))>> {
    using Sum = typename decltype(step(i))::element_type::result_type;
    using R = decltype(itree_iter_rhs(std::declval<Sum>()));
    return itree_bind(
        step(i),
        std::function<std::shared_ptr<ITree<R>>(Sum)>(
            [step](const Sum &s) -> std::shared_ptr<ITree<R>> {
                if (std::holds_alternative<typename Sum::Inl>(s.v())) {
                    const auto &[next] = *std::get_if<typename Sum::Inl>(&s.v());
                    return itree_tau(itree_iter(step, next));
                }
                return itree_ret(itree_iter_rhs(s));
            }));
}

// The dictionary a generic definition is given when it iterates in the tree
// monad, the counterpart of `Monad_itree` for `MonadIter`.  Skipped, it left
// an argument with no value at all -- `<void>()` -- because `ITree.iter`'s own
// mapping only covers the places the constant is written directly, not the
// places the dictionary is passed on to something else's `iter`.
//
// Parameterised by the event family, as the Rocq instance is, and unused here
// for the same reason `Monad_itree`'s parameter is.
template<typename E = void>
inline constexpr auto MonadIter_itree = [](auto step, std::any i) {
    return itree_iter(step, i);
};

// The result of a trigger: one Vis node whose continuation returns the
// event's own response.
//
// The response type is an index of the event type, so it has no C++ spelling
// of its own and the tree cannot be named where the trigger is written.  The
// conversion operator lets the use site name it instead, which the enclosing
// signature always does.
struct itree_trigger_t {
    std::function<std::any()> effect;

    template <typename R>
    operator std::shared_ptr<ITree<R>>() const {
        return ITree<R>::vis(effect,
            std::function<std::shared_ptr<ITree<R>>(std::any)>(
                [](std::any x) {
                    return ITree<R>::ret(std::any_cast<R>(std::move(x)));
                }));
    }
};

// A tree read at another result type.
//
// Only a [Ret] leaf knows the result type, so the conversion is one
// [crane_any_cast] per leaf and nothing else: [Tau] and [Vis] are rebuilt
// around a converted child, and a [Vis] continuation is converted where it is
// resumed, which keeps an unexplored branch unexplored.
//
// This is the [crane_container_cast] hook: a tree has an element type but
// nothing to walk, so the carrier supplies the conversion itself.
template <typename B, typename A>
std::shared_ptr<ITree<B>> crane_cast_to(crane_tag<std::shared_ptr<ITree<B>>>,
                                        const std::shared_ptr<ITree<A>> &t) {
    if constexpr (std::is_same_v<A, B>) {
        return t;
    } else {
        if (!t)
            return nullptr;
        const auto &n = t->observe();
        if (const auto *r = std::get_if<typename ITree<A>::Ret>(&n))
            return ITree<B>::ret(crane_convert<B>(r->value));
        if (const auto *u = std::get_if<typename ITree<A>::Tau>(&n))
            return ITree<B>::tau(
                crane_cast_to(crane_tag<std::shared_ptr<ITree<B>>>{}, u->next));
        const auto &v = *std::get_if<typename ITree<A>::Vis>(&n);
        auto cont = v.cont;
        return ITree<B>::vis(
            v.effect,
            std::function<std::shared_ptr<ITree<B>>(std::any)>(
                [cont](std::any x) {
                    return crane_cast_to(
                        crane_tag<std::shared_ptr<ITree<B>>>{},
                        cont(std::move(x)));
                }));
    }
}

// The event of a [Vis] node, as a pattern match over the node sees it.
//
// A tree stores its event as the thunk that yields it -- see [itree_trigger]
// -- because a tree that only carries an event has no name for its type.  A
// handler is the first thing that does name it, in its own parameter, so the
// recovery belongs at the conversion rather than at the projection: the thunk
// is run and its box opened at whatever type the use site asks for.  Asking
// for the thunk itself gets it back unchanged, which is what a match that
// only passes the event along to another [Vis] wants.
struct crane_event {
    std::function<std::any()> effect;

    operator std::function<std::any()>() const { return effect; }

    template <typename E>
    operator E() const { return crane_any_cast<E>(effect()); }
};

// Trigger with template argument deduction.  An event given an effect
// spelling is already the thunk [ITree::vis] wants; one that is plain data is
// reified as the thunk that yields it, for a handler to interpret later.
template<typename E>
itree_trigger_t itree_trigger(E e) {
    if constexpr (std::is_invocable_r_v<std::any, E &>)
        return {std::function<std::any()>(std::move(e))};
    else
        return {[e = std::move(e)]() -> std::any { return std::any(e); }};
}

// A sum of event families: [E +' F].
//
// An event is erased wherever it is only carried -- the tree boxes it -- but a
// handler takes one apart, and telling the two sides apart is a runtime
// question.  The shape is the one Crane gives any variant, so the dispatch it
// generates for a match over a sum needs nothing written for it here.
//
// The index the family is applied at is erased, so [E] and [F] are the event
// structs themselves rather than the families.
template<typename E, typename F, typename X = void>
struct Sum1 {
    struct Inl1 { E a0; };
    struct Inr1 { F a0; };
    using variant_t = std::variant<Inl1, Inr1>;

    variant_t v_;

    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }

    static Sum1 inl1(E a0) { return {variant_t{Inl1{std::move(a0)}}}; }
    static Sum1 inr1(F a0) { return {variant_t{Inr1{std::move(a0)}}}; }
};

// [case_ f g] -- the handler that reads which side of a [Sum1] an event came
// from and passes it to the matching handler.
//
// The result is a callable rather than a rendered dispatch, because [case_] is
// written both bare (as the handler an [interp] is given) and applied to an
// event, and only a value can be both.  The sum is taken generically: what
// arrives is whatever Crane generated for [E +' F] at the use site, read
// through the shape every variant has.
template<typename F, typename G>
auto itree_case(F f, G g) {
    return [f, g](const auto &ab) {
        using Sum = std::decay_t<decltype(ab)>;
        if (auto *l = std::get_if<typename Sum::Inl1>(&ab.v()))
            return f(l->a0);
        return g(std::get<typename Sum::Inr1>(ab.v()).a0);
    };
}

// Injections into a sum whose other side the injection does not name.  The
// proxy defers that to the use site, as [itree_trigger_t] defers the response
// type of a trigger.
template<typename E>
struct sum1_inl_t {
    E a0;
    template<typename F, typename X>
    operator Sum1<E, F, X>() const { return Sum1<E, F, X>::inl1(a0); }
};

template<typename F>
struct sum1_inr_t {
    F a0;
    template<typename E, typename X>
    operator Sum1<E, F, X>() const { return Sum1<E, F, X>::inr1(a0); }
};

template<typename E> sum1_inl_t<E> sum1_inl(E a0) { return {std::move(a0)}; }
template<typename F> sum1_inr_t<F> sum1_inr(F a0) { return {std::move(a0)}; }

// The single argument a non-generic callable takes.
template<typename T> struct crane_fn_arg;
template<typename C, typename R, typename A>
struct crane_fn_arg<R (C::*)(A) const> { using type = std::decay_t<A>; };
template<typename C, typename R, typename A>
struct crane_fn_arg<R (C::*)(A)> { using type = std::decay_t<A>; };

// Binding a trigger directly.
//
// [itree_trigger] defers naming the response type to the use site, and a bind
// is a use site that cannot name it either: the continuation is where the
// response goes, so the two have to agree, and here it is the continuation
// that decides.  A continuation taking the response as a value of its own
// names it, and the tree is converted at that type; one written generically
// -- which is what an absurd response leaves -- is handed the boxed response
// as it stands, with no type to recover it at.
template<typename K>
auto itree_bind(itree_trigger_t m, K k) {
    if constexpr (std::is_invocable_v<K &>)
        return itree_bind(
            static_cast<std::shared_ptr<ITree<void>>>(m), std::move(k));
    else if constexpr (requires { k(std::declval<std::any>()); }) {
        using tree_b = decltype(k(std::declval<std::any>()));
        using node_b = typename tree_b::element_type;
        return node_b::vis(
            m.effect,
            std::function<tree_b(std::any)>(
                [k](std::any x) { return k(std::move(x)); }));
    } else {
        using A = typename crane_fn_arg<decltype(&K::operator())>::type;
        return itree_bind(
            static_cast<std::shared_ptr<ITree<A>>>(m), std::move(k));
    }
}

// Vis constructor with template argument deduction.  Deduces R from the
// continuation's return type (shared_ptr<ITree<R>>).
template<typename Effect, typename Cont>
auto itree_vis(Effect effect, Cont cont) {
    using TreePtr = std::invoke_result_t<Cont, std::any>;
    using TreeT = typename TreePtr::element_type;
    std::function<std::any()> eff;
    if constexpr (std::is_same_v<std::decay_t<Effect>, std::any>) {
        eff = std::any_cast<std::function<std::any()>>(effect);
    } else {
        eff = std::function<std::any()>(std::move(effect));
    }
    return TreeT::vis(std::move(eff),
        std::function<TreePtr(std::any)>(std::move(cont)));
}

#endif // INCLUDED_CRANE_ITREE
