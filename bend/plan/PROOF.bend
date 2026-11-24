import Base
import ./LAWS.bend as Laws
import ./core.bend as C
import ../keys/core.bend as K
import ../comp/core.bend as M
import ../keys/FACTS.bend as F
import ../comp/FACTS.bend as MF

# The proofs of the laws in LAWS.bend. Each law's proof sits under its own
# "# ---- name ----" header, which mutants.ts relies on.

# ---- tools: what pick answers ----
def PickSpec(r: C.Pick, +cs: List<&2, M.Comp>, +avail: List<&2, Nat>) -> Type:
  match r:
    case C.Got{+c, +rest}:
      {M.ready(c, avail) == True{}: Bool} & {List.length(&2, M.Comp, cs) == 1n+List.length(&2, M.Comp, rest): Nat} & (@n: Nat -> {F.count(n, M.ids(cs)) == F.count(n, M.ids(c <> rest)): Nat})
    case C.Stuck{+all}:
      {Laws.none_ready(all, avail) == True{}: Bool} & {all == cs: List<&2, M.Comp>}

def stuck_none(+avail: List<&2, Nat>, +h: M.Comp, +all: List<&2, M.Comp>, eb: {False{} == M.ready(h, avail): Bool}, hn: {Laws.none_ready(all, avail) == True{}: Bool}) -> {Laws.none_ready(h <> all, avail) == True{}: Bool}:
  %eb: {Bool.and(Bool.not(_), Laws.none_ready(all, avail)) == True{}: Bool}
  %Equal.sym(Bool, Laws.none_ready(all, avail), True{}, hn): {Bool.and(True{}, _) == True{}: Bool}
  {==}

def got_count(+h: M.Comp, +c: M.Comp, +t: List<&2, M.Comp>, +rest: List<&2, M.Comp>, hc: @n: Nat -> {F.count(n, M.ids(t)) == F.count(n, M.ids(c <> rest)): Nat}, +n: Nat) -> {F.count(n, M.ids(h <> t)) == F.count(n, M.ids(c <> (h <> rest))): Nat}:
  %Equal.sym(Nat, F.count(n, M.ids(t)), F.count(n, M.ids(c <> rest)), hc(n)): {F.count.put(Nat.is_eq(n, M.id_of(h)), _) == F.count(n, M.ids(c <> (h <> rest))): Nat}
  F.put_comm(Nat.is_eq(n, M.id_of(h)), Nat.is_eq(n, M.id_of(c)), F.count(n, M.ids(rest)))

def cons_spec(+avail: List<&2, Nat>, +h: M.Comp, +t: List<&2, M.Comp>, r: C.Pick, eb: {False{} == M.ready(h, avail): Bool}, ih: PickSpec(r, t, avail)) -> PickSpec(C.pick.cons(h, r), h <> t, avail):
  match r:
    case C.Got{+c, +rest}:
      (hr, hl, hc) = ih
      (hr, Equal.cong(Nat, Nat, x => 1n+x, List.length(&2, M.Comp, t), 1n+List.length(&2, M.Comp, rest), hl), n => got_count(h, c, t, rest, hc, n))
    case C.Stuck{+all}:
      (hn, he) = ih
      (stuck_none(avail, h, all, eb, hn), Equal.cong(List<&2, M.Comp>, List<&2, M.Comp>, x => h <> x, all, t, he))

def put_spec(+avail: List<&2, Nat>, +h: M.Comp, +t: List<&2, M.Comp>, b: Bool, eb: {b == M.ready(h, avail): Bool}, r: C.Pick, ih: PickSpec(r, t, avail)) -> PickSpec(C.pick.put(b, h, t, r), h <> t, avail):
  match b:
    case True{}:
      (Equal.sym(Bool, True{}, M.ready(h, avail), eb), {==}, n => {==})
    case False{}:
      cons_spec(avail, h, t, r, eb, ih)

def pick_spec(cs: List<&2, M.Comp>, +avail: List<&2, Nat>) -> PickSpec(C.pick(cs, avail), cs, avail):
  match cs:
    case Nil{}:
      ({==}, {==})
    case Con{+h, +t}:
      put_spec(avail, h, t, M.ready(h, avail), {==}, C.pick(t, avail), pick_spec(t, avail))

# ---- tools: a plan, one component longer ----
def order_cons(+c: M.Comp, p: C.Plan) -> {c <> C.order_of(p) == C.order_of(C.plan.cons(c, p)): List<&2, M.Comp>}:
  match p:
    case C.Plan{o, b}:
      {==}

def blocked_cons(+c: M.Comp, p: C.Plan) -> {C.blocked_of(p) == C.blocked_of(C.plan.cons(c, p)): List<&2, M.Comp>}:
  match p:
    case C.Plan{o, b}:
      {==}

# ---- plan_sound ----
def sound_next(+avail: List<&2, Nat>, r: C.Pick, +cs: List<&2, M.Comp>, spec: PickSpec(r, cs, avail), +g: Nat, ih: @a: List<&2, Nat> -> @p: List<&2, M.Comp> -> {MF.valid_order(C.order_of(C.schedule(g, a, p)), a) == True{}: Bool}) -> {MF.valid_order(C.order_of(C.schedule.next(r, avail, a => p => C.schedule(g, a, p))), avail) == True{}: Bool}:
  match r:
    case C.Stuck{all}:
      {==}
    case C.Got{+c, +rest}:
      (hr, hl, hc) = spec
      %order_cons(c, C.schedule(g, List.append(&2, Nat, avail, M.provides(c)), rest)): {MF.valid_order(_, avail) == True{}: Bool}
      %Equal.sym(Bool, M.ready(c, avail), True{}, hr): {Bool.and(_, MF.valid_order(C.order_of(C.schedule(g, List.append(&2, Nat, avail, M.provides(c)), rest)), List.append(&2, Nat, avail, M.provides(c)))) == True{}: Bool}
      %Equal.sym(Bool, MF.valid_order(C.order_of(C.schedule(g, List.append(&2, Nat, avail, M.provides(c)), rest)), List.append(&2, Nat, avail, M.provides(c))), True{}, ih(List.append(&2, Nat, avail, M.provides(c)), rest)): {Bool.and(True{}, _) == True{}: Bool}
      {==}

def sched_sound(f: Nat, +avail: List<&2, Nat>, +cs: List<&2, M.Comp>) -> {MF.valid_order(C.order_of(C.schedule(f, avail, cs)), avail) == True{}: Bool}:
  match f:
    case 0n:
      {==}
    case 1n++g:
      sound_next(avail, C.pick(cs, avail), cs, pick_spec(cs, avail), g, a => p => sched_sound(g, a, p))

def Laws.plan_sound(root, cs):
  sched_sound(List.length(&2, M.Comp, cs), root, cs)

# ---- plan_maximal ----

#
# The fuel is the number of components still pending: each Got takes one.
# So fuel runs out only on an empty list, and every stop is a Stuck, where
# nothing pending is ready on what the order provides.
def max_zero(cs: List<&2, M.Comp>, +avail: List<&2, Nat>, hl: {List.length(&2, M.Comp, cs) == 0n: Nat}) -> {Laws.none_ready(cs, avail) == True{}: Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Empty.absurd({Laws.none_ready(h <> t, avail) == True{}: Bool}, F.succ_ne_zero(List.length(&2, M.Comp, t), hl))

def max_next(+avail: List<&2, Nat>, r: C.Pick, +cs: List<&2, M.Comp>, spec: PickSpec(r, cs, avail), +g: Nat, hl: {List.length(&2, M.Comp, cs) == 1n+g: Nat}, ih: @a: List<&2, Nat> -> @p: List<&2, M.Comp> -> @h: {List.length(&2, M.Comp, p) == g: Nat} -> {Laws.none_ready(C.blocked_of(C.schedule(g, a, p)), MF.after(C.order_of(C.schedule(g, a, p)), a)) == True{}: Bool}) -> {Laws.none_ready(C.blocked_of(C.schedule.next(r, avail, a => p => C.schedule(g, a, p))), MF.after(C.order_of(C.schedule.next(r, avail, a => p => C.schedule(g, a, p))), avail)) == True{}: Bool}:
  match r:
    case C.Stuck{+all}:
      (hn, he) = spec
      hn
    case C.Got{+c, +rest}:
      (hr, hlen, hc) = spec
      +a2 = List.append(&2, Nat, avail, M.provides(c))
      %order_cons(c, C.schedule(g, a2, rest)): {Laws.none_ready(C.blocked_of(C.plan.cons(c, C.schedule(g, a2, rest))), MF.after(_, avail)) == True{}: Bool}
      %blocked_cons(c, C.schedule(g, a2, rest)): {Laws.none_ready(_, MF.after(c <> C.order_of(C.schedule(g, a2, rest)), avail)) == True{}: Bool}
      ih(a2, rest, Equal.cong(Nat, Nat, x => F.pred(x), 1n+List.length(&2, M.Comp, rest), 1n+g, Equal.trans(Nat, 1n+List.length(&2, M.Comp, rest), List.length(&2, M.Comp, cs), 1n+g, Equal.sym(Nat, List.length(&2, M.Comp, cs), 1n+List.length(&2, M.Comp, rest), hlen), hl)))

def sched_max(f: Nat, +avail: List<&2, Nat>, +cs: List<&2, M.Comp>, hl: {List.length(&2, M.Comp, cs) == f: Nat}) -> {Laws.none_ready(C.blocked_of(C.schedule(f, avail, cs)), MF.after(C.order_of(C.schedule(f, avail, cs)), avail)) == True{}: Bool}:
  match f:
    case 0n:
      max_zero(cs, avail, hl)
    case 1n++g:
      max_next(avail, C.pick(cs, avail), cs, pick_spec(cs, avail), g, hl, a => p => h => sched_max(g, a, p, h))

def Laws.plan_maximal(root, cs):
  sched_max(List.length(&2, M.Comp, cs), root, cs, {==})

# ---- plan_conserves ----
def cons_next(+avail: List<&2, Nat>, r: C.Pick, +cs: List<&2, M.Comp>, spec: PickSpec(r, cs, avail), +g: Nat, +n: Nat, ih: @a: List<&2, Nat> -> @p: List<&2, M.Comp> -> {F.count(n, M.ids(p)) == Nat.add(F.count(n, M.ids(C.order_of(C.schedule(g, a, p)))), F.count(n, M.ids(C.blocked_of(C.schedule(g, a, p))))): Nat}) -> {F.count(n, M.ids(cs)) == Nat.add(F.count(n, M.ids(C.order_of(C.schedule.next(r, avail, a => p => C.schedule(g, a, p))))), F.count(n, M.ids(C.blocked_of(C.schedule.next(r, avail, a => p => C.schedule(g, a, p)))))): Nat}:
  match r:
    case C.Stuck{+all}:
      (hn, he) = spec
      %he: {F.count(n, M.ids(_)) == F.count(n, M.ids(all)): Nat}
      {==}
    case C.Got{+c, +rest}:
      (hr, hlen, hc) = spec
      +a2 = List.append(&2, Nat, avail, M.provides(c))
      +o = C.order_of(C.schedule(g, a2, rest))
      +b = C.blocked_of(C.schedule(g, a2, rest))
      %order_cons(c, C.schedule(g, a2, rest)): {F.count(n, M.ids(cs)) == Nat.add(F.count(n, M.ids(_)), F.count(n, M.ids(C.blocked_of(C.plan.cons(c, C.schedule(g, a2, rest)))))): Nat}
      %blocked_cons(c, C.schedule(g, a2, rest)): {F.count(n, M.ids(cs)) == Nat.add(F.count(n, M.ids(c <> o)), F.count(n, M.ids(_))): Nat}
      %Equal.sym(Nat, F.count(n, M.ids(cs)), F.count(n, M.ids(c <> rest)), hc(n)): {_ == Nat.add(F.count(n, M.ids(c <> o)), F.count(n, M.ids(b))): Nat}
      %Equal.sym(Nat, F.count(n, M.ids(rest)), Nat.add(F.count(n, M.ids(o)), F.count(n, M.ids(b))), ih(a2, rest)): {F.count.put(Nat.is_eq(n, M.id_of(c)), _) == Nat.add(F.count(n, M.ids(c <> o)), F.count(n, M.ids(b))): Nat}
      F.put_add_l(Nat.is_eq(n, M.id_of(c)), F.count(n, M.ids(o)), F.count(n, M.ids(b)))

def sched_cons(f: Nat, +avail: List<&2, Nat>, +cs: List<&2, M.Comp>, +n: Nat) -> {F.count(n, M.ids(cs)) == Nat.add(F.count(n, M.ids(C.order_of(C.schedule(f, avail, cs)))), F.count(n, M.ids(C.blocked_of(C.schedule(f, avail, cs))))): Nat}:
  match f:
    case 0n:
      {==}
    case 1n++g:
      cons_next(avail, C.pick(cs, avail), cs, pick_spec(cs, avail), g, n, a => p => sched_cons(g, a, p, n))

def Laws.plan_conserves(root, cs, n):
  sched_cons(List.length(&2, M.Comp, cs), root, cs, n)
