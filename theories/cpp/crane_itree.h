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
#include "obj.h"
#include <functional>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <variant>

#include "crane_fn.h"  // crane_any_cast

// A response, with the side an injected effect was stored under taken off;
// see [sum1_erased].
crane::obj crane_injected_response(crane::obj response);

// What a [Ret] leaf holds: the result, or [std::monostate] for a tree whose
// result is [unit] and spelled [void].
template <typename R> struct itree_value { using type = R; };
template <> struct itree_value<void> { using type = std::monostate; };

template <typename R>
struct ITree : public std::enable_shared_from_this<ITree<R>> {
    // The tree's own result type, for helpers that have only the pointer.
    using result_type = R;
    using value_type = typename itree_value<R>::type;

    struct Ret { value_type value{}; };
    struct Tau { std::shared_ptr<ITree<R>> next; };
    struct Vis {
        crane::fn<crane::obj()> effect;
        crane::fn<std::shared_ptr<ITree<R>>(crane::obj)> cont;
    };
    using variant_t = std::variant<Ret, Tau, Vis>;

  private:
    // A [Tau] whose child is not built yet: see [delay].  [observe] builds it
    // and stores it as an ordinary [Tau], so nothing outside sees the state.
    mutable variant_t node;
    mutable crane::fn<std::shared_ptr<ITree<R>>()> pending;

    // Passkey: only ITree's own factories can name it, so the public
    // constructor cannot be called from outside despite make_shared needing it.
    struct Private { explicit Private() = default; };

  public:
    ITree(Private, variant_t n) : node(std::move(n)) {}
    ITree(Private, crane::fn<std::shared_ptr<ITree<R>>()> p)
        : node(Tau{}), pending(std::move(p)) {}

    // A [Tau] chain is as long as the loop that built it, so it is torn down
    // a link at a time rather than by each node's destructor calling the
    // next one's.
    ~ITree() {
        auto *t = std::get_if<Tau>(&node);
        if (!t)
            return;
        std::shared_ptr<ITree<R>> next = std::move(t->next);
        while (next && next.use_count() == 1) {
            auto *nt = std::get_if<Tau>(&next->node);
            if (!nt)
                break;
            next = std::shared_ptr<ITree<R>>(std::move(nt->next));
        }
    }

    // A [Tau] whose child is computed when the node is first observed.
    // [bind] and [iter] produce one where an eager child would recurse: down
    // a [Tau] chain, or into the next step of an iteration that answered at
    // once -- one C++ frame per step, so a long pure loop overflowed.
    static std::shared_ptr<ITree<R>> delay(
        crane::fn<std::shared_ptr<ITree<R>>()> next) {
        return std::make_shared<ITree<R>>(Private{}, std::move(next));
    }

    static std::shared_ptr<ITree<R>> ret(value_type value) {
        return std::make_shared<ITree<R>>(Private{}, Ret{std::move(value)});
    }
    static std::shared_ptr<ITree<R>> ret()
        requires std::is_void_v<R>
    {
        return ret(std::monostate{});
    }
    static std::shared_ptr<ITree<R>> tau(std::shared_ptr<ITree<R>> next) {
        if (!next)
            throw std::invalid_argument("crane: ITree::tau given a null next");
        return std::make_shared<ITree<R>>(Private{}, Tau{std::move(next)});
    }
    static std::shared_ptr<ITree<R>> vis(
        crane::fn<crane::obj()> effect,
        crane::fn<std::shared_ptr<ITree<R>>(crane::obj)> cont) {
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
            const auto &n = cur->observe();
            if (auto *r = std::get_if<Ret>(&n)) {
                if constexpr (std::is_void_v<R>)
                    return;
                else
                    return r->value;
            }
            if (auto *t = std::get_if<Tau>(&n)) {
                if (!t->next)
                    throw std::runtime_error("crane: ITree Tau has a null next");
                cur = t->next;
                continue;
            }
            auto &v = std::get<Vis>(n);
            crane::obj response = crane_injected_response(v.effect());
            auto next = v.cont(std::move(response));
            if (!next)
                throw std::runtime_error("crane: ITree Vis continuation returned null");
            cur = std::move(next);
        }
    }
    const variant_t &observe() const {
        if (pending) {
            auto next = std::exchange(pending, nullptr)();
            if (!next)
                throw std::runtime_error("crane: a delayed ITree Tau has a null next");
            node = Tau{std::move(next)};
        }
        return node;
    }
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
//
// A continuation that ignores the bound value is written with no parameter at
// all -- `t ;; k` in Rocq discards it, and the generated lambda says so.  That
// is a fact about the continuation, not about the element type, so it is
// handled here rather than by a separate overload per element type.
template<typename K, typename A>
decltype(auto) crane_itree_apply(K &k, const A &value) {
    if constexpr (std::is_invocable_v<K &>)
        return k();
    else
        return k(value);
}

template<typename A, typename K>
auto itree_bind(std::shared_ptr<ITree<A>> m, K k)
    -> decltype(crane_itree_apply(
        k, std::declval<const typename ITree<A>::value_type &>())) {
    using tree_b = decltype(crane_itree_apply(
        k, std::declval<const typename ITree<A>::value_type &>()));
    using node_b = typename tree_b::element_type;
    if (!m)
        throw std::invalid_argument("crane: itree_bind given a null tree");
    const auto &n = m->observe();
    if (auto *r = std::get_if<typename ITree<A>::Ret>(&n))
        return crane_itree_apply(k, r->value);
    if (auto *t = std::get_if<typename ITree<A>::Tau>(&n))
        return node_b::delay(
            [next = t->next, k]() -> tree_b { return itree_bind(next, k); });
    auto &v = std::get<typename ITree<A>::Vis>(n);
    auto cont = v.cont;
    return node_b::vis(
        v.effect,
        crane::fn<tree_b(crane::obj)>(
            [cont, k](crane::obj x) { return itree_bind(cont(std::move(x)), k); }));
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

    // The continuation is a `crane::fn`, the type the generated `Monad`
    // concept hands it: `A` and `B` are deduced from it there.
    template<typename A, typename B>
    static m<B> bind(m<A> t, crane::fn<m<B>(A)> k) {
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
// The `Tau`'s child is delayed, so building the tree runs one step, not all
// of them.
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
        crane::fn<std::shared_ptr<ITree<R>>(Sum)>(
            [step](const Sum &s) -> std::shared_ptr<ITree<R>> {
                if (std::holds_alternative<typename Sum::Inl>(s.v())) {
                    const auto &[next] = *std::get_if<typename Sum::Inl>(&s.v());
                    return ITree<R>::delay(
                        [step, next]() { return itree_iter(step, next); });
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
inline constexpr auto MonadIter_itree = [](auto step, crane::obj i) {
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
    crane::fn<crane::obj()> effect;

    template <typename R>
    operator std::shared_ptr<ITree<R>>() const {
        return ITree<R>::vis(effect,
            crane::fn<std::shared_ptr<ITree<R>>(crane::obj)>(
                [](crane::obj x) {
                    return ITree<R>::ret(crane::any_cast<R>(std::move(x)));
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
            crane::fn<std::shared_ptr<ITree<B>>(crane::obj)>(
                [cont](crane::obj x) {
                    return crane_cast_to(
                        crane_tag<std::shared_ptr<ITree<B>>>{},
                        cont(std::move(x)));
                }));
    }
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
//
// The side the injection *does* name is deferred too, because a signature may
// have erased it: a handler whose event family was a variable takes
// [Sum1<crane::obj, ...>], and the event being injected still has to reach it.
// Any target the event can be spelled at is accepted; the exact one is the
// case where that spelling is the identity.
template<typename E>
struct sum1_inl_t {
    E a0;
    template<typename E2, typename F, typename X>
        requires std::is_constructible_v<E2, const E &>
    operator Sum1<E2, F, X>() const { return Sum1<E2, F, X>::inl1(E2(a0)); }
};

template<typename F>
struct sum1_inr_t {
    F a0;
    template<typename E, typename F2, typename X>
        requires std::is_constructible_v<F2, const F &>
    operator Sum1<E, F2, X>() const { return Sum1<E, F2, X>::inr1(F2(a0)); }
};

template<typename E> sum1_inl_t<E> sum1_inl(E a0) { return {std::move(a0)}; }
template<typename F> sum1_inr_t<F> sum1_inr(F a0) { return {std::move(a0)}; }

template<typename T> struct is_sum1_injection : std::false_type {};
template<typename E> struct is_sum1_injection<sum1_inl_t<E>> : std::true_type {};
template<typename F> struct is_sum1_injection<sum1_inr_t<F>> : std::true_type {};

template<typename E> E crane_event_read(crane::obj o);

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
    crane::fn<crane::obj()> effect;

    operator crane::fn<crane::obj()>() const { return effect; }

    template <typename E>
    operator E() const { return crane_event_read<E>(effect()); }
};

// An injection as a tree stores it.
//
// A [Vis] keeps its event as a thunk, and a sum names no type at the trigger,
// so the side an injection names is stored next to the event it carries:
// [inl1 e] and [inr1 e] are different events even where [E] and [F] are the
// same type, and a handler over [E +' F] dispatches on which one it got.
//
// An injection of an effect -- a thunk that performs I/O when run, as an IO
// event is -- is still unwrapped: [run] performs whatever a [Vis] holds, and
// no handler will ever take that event apart.
struct sum1_erased {
    bool right;
    crane::obj a0;
};

template<typename T> struct injected_leaf { using type = T; };
template<typename E> struct injected_leaf<sum1_inl_t<E>> : injected_leaf<E> {};
template<typename F> struct injected_leaf<sum1_inr_t<F>> : injected_leaf<F> {};

template<typename T>
inline constexpr bool injects_effect =
    std::is_invocable_r_v<crane::obj, typename injected_leaf<T>::type &>;

template<typename T>
crane::obj erase_injected(T e) {
    // A handler written generically ([translate]'s) is handed the event as
    // the deferral a match binds; what it stands for is what its thunk
    // yields.
    if constexpr (std::is_same_v<T, crane_event>)
        return e.effect();
    else if constexpr (is_sum1_injection<T>::value)
        return crane::obj(sum1_erased{
            !std::is_same_v<T, sum1_inl_t<decltype(e.a0)>>,
            erase_injected(std::move(e.a0))});
    else
        return crane::obj(std::move(e));
}

template<typename T> struct is_sum1 : std::false_type {};
template<typename E, typename F, typename X>
struct is_sum1<Sum1<E, F, X>> : std::true_type {};

// An event read back at the type a use site names.  A sum is rebuilt from
// the side stored with it; anything else is opened at that type.
template<typename E>
E crane_event_read(crane::obj o) {
    if constexpr (std::is_same_v<E, crane::obj>)
        return o;
    else if constexpr (is_sum1<E>::value) {
        if (const auto *s = crane::any_cast<sum1_erased>(&o)) {
            using L = std::remove_cvref_t<decltype(std::declval<typename E::Inl1>().a0)>;
            using R = std::remove_cvref_t<decltype(std::declval<typename E::Inr1>().a0)>;
            if (s->right)
                return E::inr1(crane_event_read<R>(s->a0));
            return E::inl1(crane_event_read<L>(s->a0));
        }
        return crane_any_cast<E>(std::move(o));
    } else
        return crane_any_cast<E>(std::move(o));
}

// What [run] gives a continuation: an effect injected into a sum was
// performed, and its response is the effect's own, whatever side it was
// injected at.
inline crane::obj crane_injected_response(crane::obj response) {
    while (const auto *s = crane::any_cast<sum1_erased>(&response)) {
        crane::obj inner = s->a0;
        response = std::move(inner);
    }
    return response;
}

// The event of a [Vis] node, bound at whatever the generator knows about it.
//
// Deferring the recovery to the use site is right when the binding site has
// nothing to say, and wrong when it does: a match on the event in the branch
// that binds it never reaches a use that names a type, so it asks a
// [crane_event] for the variant accessor an event inductive has and a thunk
// does not.  Where the generator does know the type, binding at it is what
// makes that match compile.
//
// [crane::obj] is the generator saying it does not know -- either the type was
// erased or it names something this file cannot spell -- and there the old
// deferral is exactly what is wanted, so it is what comes back.
template <typename E>
auto crane_event_as(crane::fn<crane::obj()> effect) {
    if constexpr (std::is_same_v<E, crane::obj>)
        return crane_event{std::move(effect)};
    else
        return crane_event_read<E>(effect());
}

// An event as a tree stores it.  One given an effect spelling is already the
// thunk [ITree::vis] wants; one that is plain data is reified as the thunk
// that yields it, for a handler to interpret later.
template<typename E>
crane::fn<crane::obj()> itree_reify_event(E e) {
    if constexpr (is_sum1_injection<E>::value && injects_effect<E>)
        return itree_reify_event(std::move(e.a0));
    else if constexpr (is_sum1_injection<E>::value)
        return [o = erase_injected(std::move(e))]() -> crane::obj { return o; };
    else if constexpr (std::is_invocable_r_v<crane::obj, E &>)
        return crane::fn<crane::obj()>(std::move(e));
    else
        return [e = std::move(e)]() -> crane::obj { return crane::obj(e); };
}

// Trigger with template argument deduction.
template<typename E>
itree_trigger_t itree_trigger(E e) {
    return {itree_reify_event(std::move(e))};
}

// The single argument a non-generic callable takes.
template<typename T> struct crane_fn_arg;
template<typename C, typename R, typename A>
struct crane_fn_arg<R (C::*)(A) const> { using type = std::decay_t<A>; };
template<typename C, typename R, typename A>
struct crane_fn_arg<R (C::*)(A)> { using type = std::decay_t<A>; };
template<typename R, typename A>
struct crane_fn_arg<R (*)(A)> { using type = std::decay_t<A>; };
template<typename R, typename A>
struct crane_fn_arg<R(A)> { using type = std::decay_t<A>; };

// The same question asked of the callable itself.
//
// A continuation need not be a closure: a named function template left to
// decay -- [void_elim<std::shared_ptr<ITree<R>>>], eliminating an absurd
// response -- arrives as a function pointer, which has no [operator()] to
// take the address of.  Spelling [&K::operator()] at the use site is a hard
// error there rather than a substitution failure, so the choice is made here.
template<typename K, typename = void>
struct crane_callable_arg : crane_fn_arg<std::decay_t<K>> {};
template<typename K>
struct crane_callable_arg<K,
    std::void_t<decltype(&std::decay_t<K>::operator())>>
    : crane_fn_arg<decltype(&std::decay_t<K>::operator())> {};

// Binding a trigger directly.
//
// [itree_trigger] defers naming the response type to the use site, and a bind
// is a use site that cannot name it either: the continuation is where the
// response goes, so the two have to agree, and here it is the continuation
// that decides.  A continuation taking the response as a value of its own
// names it, and the tree is converted at that type; one written generically
// -- which is what an absurd response leaves -- is handed the boxed response
// as it stands, with no type to recover it at.
// The result of a bind whose continuation's own result type erased.
//
// A continuation returning a type variable -- [void_elim : void -> A],
// eliminating an absurd response -- comes out returning [crane::obj], so the
// bind has no tree type to be.  The use site always names one, as it does for
// [itree_trigger_t], and the deferral is the same.
struct itree_erased_bind_t {
    crane::fn<crane::obj()> effect;
    crane::fn<crane::obj(crane::obj)> cont;

    template <typename R>
    operator std::shared_ptr<ITree<R>>() const {
        auto k = cont;
        return ITree<R>::vis(effect,
            crane::fn<std::shared_ptr<ITree<R>>(crane::obj)>(
                [k](crane::obj x) {
                    return crane_any_cast<std::shared_ptr<ITree<R>>>(
                        k(std::move(x)));
                }));
    }
};

template<typename K>
auto itree_bind(itree_trigger_t m, K k) {
    if constexpr (std::is_invocable_v<K &>)
        return itree_bind(
            static_cast<std::shared_ptr<ITree<void>>>(m), std::move(k));
    else if constexpr (requires { k(std::declval<crane::obj>()); }) {
        using tree_b = decltype(k(std::declval<crane::obj>()));
        using node_b = typename tree_b::element_type;
        return node_b::vis(
            m.effect,
            crane::fn<tree_b(crane::obj)>(
                [k](crane::obj x) { return k(std::move(x)); }));
    } else {
        using A = typename crane_callable_arg<K>::type;
        using tree_b = decltype(k(std::declval<const A &>()));
        if constexpr (std::is_same_v<tree_b, crane::obj>)
            return itree_erased_bind_t{
                m.effect,
                crane::fn<crane::obj(crane::obj)>([k](crane::obj x) {
                    return k(crane_any_cast<A>(std::move(x)));
                })};
        else
            return itree_bind(
                static_cast<std::shared_ptr<ITree<A>>>(m), std::move(k));
    }
}

// Vis constructor with template argument deduction.  Deduces R from the
// continuation's return type (shared_ptr<ITree<R>>).
template<typename Effect, typename Cont>
auto itree_vis(Effect effect, Cont cont) {
    using TreePtr = std::invoke_result_t<Cont, crane::obj>;
    using TreeT = typename TreePtr::element_type;
    // An injection is stored with its side; see [itree_reify_event].
    if constexpr (is_sum1_injection<std::decay_t<Effect>>::value)
        return TreeT::vis(itree_reify_event(std::move(effect)),
            crane::fn<TreePtr(crane::obj)>(std::move(cont)));
    else {
        crane::fn<crane::obj()> eff;
        if constexpr (std::is_same_v<std::decay_t<Effect>, crane::obj>)
            eff = crane::any_cast<crane::fn<crane::obj()>>(effect);
        else
            eff = itree_reify_event(std::move(effect));
        return TreeT::vis(std::move(eff),
            crane::fn<TreePtr(crane::obj)>(std::move(cont)));
    }
}

// [translate h t]: [t] with [h] applied to every event.
//
// A [Vis] keeps its event as a thunk, so the translated event is a thunk too,
// applying [h] to what the original yields when it is asked for -- by a
// handler, which reads the event, or by [run], which performs it.  [h] is
// handed the deferral a match binds, so a handler declared at its event
// struct reads it there and a generic one passes it on.  The [Tau] child is
// delayed, as [bind]'s is, so a long tree is translated a step at a time.
template<typename H, typename R>
std::shared_ptr<ITree<R>> itree_translate(H h, std::shared_ptr<ITree<R>> t) {
    if (!t)
        throw std::invalid_argument("crane: itree_translate given a null tree");
    const auto &n = t->observe();
    if (std::holds_alternative<typename ITree<R>::Ret>(n))
        return t;
    if (auto *u = std::get_if<typename ITree<R>::Tau>(&n))
        return ITree<R>::delay(
            [h, next = u->next]() { return itree_translate(h, next); });
    const auto &v = std::get<typename ITree<R>::Vis>(n);
    auto effect = v.effect;
    auto cont = v.cont;
    return ITree<R>::vis(
        [h, effect]() -> crane::obj {
            return itree_reify_event(h(crane_event{effect}))();
        },
        crane::fn<std::shared_ptr<ITree<R>>(crane::obj)>(
            [h, cont](crane::obj x) {
                return itree_translate(h, cont(std::move(x)));
            }));
}

#endif // INCLUDED_CRANE_ITREE
