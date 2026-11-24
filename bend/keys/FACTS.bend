import Base
import ./core.bend as C
import bend-mathlib@0.7.4.0/nat.bend as MN
import bend-mathlib@0.7.4.0/list.bend as ML
import bend-mathlib@0.7.4.0/bool.bend as MB

# Facts about the key-list helpers in core.bend, proved once and imported by
# every unit's PROOF.bend. A fact here is a lemma, not a law: no law
# states it, and the gate checks this file on its own.

# ---- reference definitions: shared with other units' laws and proofs ----
def count.put(hit: Bool, r: Nat) -> Nat:
  match hit:
    case True{}:
      1n+r
    case False{}:
      r

def count(+n: Nat, xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      count.put(Nat.is_eq(n, h), count(n, t))

# No element twice.
def distinct(ks: List<&2, Nat>) -> Bool:
  match ks:
    case Nil{}:
      True{}
    case Con{+h, +t}:
      Bool.and(Bool.not(C.mem(h, t)), distinct(t))

def put_add_l(e: Bool, a: Nat, b: Nat) -> {count.put(e, Nat.add(a, b)) == Nat.add(count.put(e, a), b): Nat}:
  match e:
    case True{}:
      {==}
    case False{}:
      {==}

def put_add_r(e: Bool, a: Nat, b: Nat) -> {count.put(e, Nat.add(a, b)) == Nat.add(a, count.put(e, b)): Nat}:
  match e:
    case True{}:
      %MN.add_succ(a, b): {_ == Nat.add(a, 1n+b): Nat}
      {==}
    case False{}:
      {==}

def count_append(+n: Nat, a: List<&2, Nat>, +b: List<&2, Nat>) -> {count(n, List.append(&2, Nat, a, b)) == Nat.add(count(n, a), count(n, b)): Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Nat, count(n, List.append(&2, Nat, t, b)), Nat.add(count(n, t), count(n, b)), count_append(n, t, b)): {count.put(Nat.is_eq(n, h), _) == Nat.add(count.put(Nat.is_eq(n, h), count(n, t)), count(n, b)): Nat}
      %put_add_l(Nat.is_eq(n, h), count(n, t), count(n, b)): {count.put(Nat.is_eq(n, h), Nat.add(count(n, t), count(n, b))) == _: Nat}
      {==}

def count_split(+n: Nat, a: List<&2, Nat>, +b: List<&2, Nat>) -> {Nat.add(count(n, a), count(n, b)) == count(n, List.append(&2, Nat, a, b)): Nat}:
  Equal.sym(Nat, count(n, List.append(&2, Nat, a, b)), Nat.add(count(n, a), count(n, b)), count_append(n, a, b))

#
# Got{c, rest}: c is ready, and rest is cs less one, with the same ids.
# Stuck{all}: nothing in cs is ready, and all is cs.
def put_comm(a: Bool, b: Bool, x: Nat) -> {count.put(a, count.put(b, x)) == count.put(b, count.put(a, x)): Nat}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def Pos(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

def succ_ne_zero(-x: Nat, e: {1n+x == 0n: Nat}) -> Empty:
  %e: Pos(_)
  Unit{}

def TagF(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def true_ne_false(e: {True{} == False{}: Bool}) -> Empty:
  %e: TagF(_)
  Unit{}

def not_true(x: Bool, h: {Bool.not(x) == True{}: Bool}) -> {x == False{}: Bool}:
  match x:
    case True{}:
      Empty.absurd({True{} == False{}: Bool}, true_ne_false(Equal.sym(Bool, False{}, True{}, h)))
    case False{}:
      {==}

def or_false_l(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{}: Bool}) -> {a == False{}: Bool}:
  match a:
    case True{}:
      Empty.absurd({True{} == False{}: Bool}, true_ne_false(h))
    case False{}:
      {==}

def or_false_r(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{}: Bool}) -> {b == False{}: Bool}:
  match a:
    case True{}:
      Empty.absurd({b == False{}: Bool}, true_ne_false(h))
    case False{}:
      h

#
# Induct on the order, carrying three facts: it is a valid order on avail,
# its ids are distinct, and avail ++ its keys are distinct. A component that
# does not restart injects only keys in avail, and no restart provides one of
# those, because every key has one source.
def mem_append(+k: Nat, a: List<&2, Nat>, +b: List<&2, Nat>) -> {C.mem(k, List.append(&2, Nat, a, b)) == Bool.or(C.mem(k, a), C.mem(k, b)): Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, C.mem(k, List.append(&2, Nat, t, b)), Bool.or(C.mem(k, t), C.mem(k, b)), mem_append(k, t, b)): {Bool.or(Nat.is_eq(k, h), _) == Bool.or(Bool.or(Nat.is_eq(k, h), C.mem(k, t)), C.mem(k, b)): Bool}
      Equal.sym(Bool, Bool.or(Bool.or(Nat.is_eq(k, h), C.mem(k, t)), C.mem(k, b)), Bool.or(Nat.is_eq(k, h), Bool.or(C.mem(k, t), C.mem(k, b))), MB.or_assoc(Nat.is_eq(k, h), C.mem(k, t), C.mem(k, b)))

def or_ff(a: Bool, b: Bool, ha: {a == False{}: Bool}, hb: {b == False{}: Bool}) -> {Bool.or(a, b) == False{}: Bool}:
  %Equal.sym(Bool, a, False{}, ha): {Bool.or(_, b) == False{}: Bool}
  %Equal.sym(Bool, b, False{}, hb): {Bool.or(False{}, _) == False{}: Bool}
  {==}

def mem_app_ff(+k: Nat, +x: List<&2, Nat>, +y: List<&2, Nat>, hx: {C.mem(k, x) == False{}: Bool}, hy: {C.mem(k, y) == False{}: Bool}) -> {C.mem(k, List.append(&2, Nat, x, y)) == False{}: Bool}:
  Equal.trans(Bool, C.mem(k, List.append(&2, Nat, x, y)), Bool.or(C.mem(k, x), C.mem(k, y)), False{}, mem_append(k, x, y), or_ff(C.mem(k, x), C.mem(k, y), hx, hy))

def mem_app_or(+k: Nat, +x: List<&2, Nat>, +y: List<&2, Nat>, h: {C.mem(k, List.append(&2, Nat, x, y)) == False{}: Bool}) -> {Bool.or(C.mem(k, x), C.mem(k, y)) == False{}: Bool}:
  Equal.trans(Bool, Bool.or(C.mem(k, x), C.mem(k, y)), C.mem(k, List.append(&2, Nat, x, y)), False{}, Equal.sym(Bool, C.mem(k, List.append(&2, Nat, x, y)), Bool.or(C.mem(k, x), C.mem(k, y)), mem_append(k, x, y)), h)

def mem_app_l(+k: Nat, +x: List<&2, Nat>, +y: List<&2, Nat>, h: {C.mem(k, List.append(&2, Nat, x, y)) == False{}: Bool}) -> {C.mem(k, x) == False{}: Bool}:
  or_false_l(C.mem(k, x), C.mem(k, y), mem_app_or(k, x, y, h))

def mem_app_r(+k: Nat, +x: List<&2, Nat>, +y: List<&2, Nat>, h: {C.mem(k, List.append(&2, Nat, x, y)) == False{}: Bool}) -> {C.mem(k, y) == False{}: Bool}:
  or_false_r(C.mem(k, x), C.mem(k, y), mem_app_or(k, x, y, h))

def any_app_ff(a: List<&2, Nat>, +x: List<&2, Nat>, +y: List<&2, Nat>, +hx: {C.any_in(a, x) == False{}: Bool}, +hy: {C.any_in(a, y) == False{}: Bool}) -> {C.any_in(a, List.append(&2, Nat, x, y)) == False{}: Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      or_ff(C.mem(h, List.append(&2, Nat, x, y)), C.any_in(t, List.append(&2, Nat, x, y)), mem_app_ff(h, x, y, or_false_l(C.mem(h, x), C.any_in(t, x), hx), or_false_l(C.mem(h, y), C.any_in(t, y), hy)), any_app_ff(t, x, y, or_false_r(C.mem(h, x), C.any_in(t, x), hx), or_false_r(C.mem(h, y), C.any_in(t, y), hy)))

def any_app_l(a: List<&2, Nat>, +x: List<&2, Nat>, +y: List<&2, Nat>, +h: {C.any_in(a, List.append(&2, Nat, x, y)) == False{}: Bool}) -> {C.any_in(a, x) == False{}: Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+k, +t}:
      or_ff(C.mem(k, x), C.any_in(t, x), mem_app_l(k, x, y, or_false_l(C.mem(k, List.append(&2, Nat, x, y)), C.any_in(t, List.append(&2, Nat, x, y)), h)), any_app_l(t, x, y, or_false_r(C.mem(k, List.append(&2, Nat, x, y)), C.any_in(t, List.append(&2, Nat, x, y)), h)))

def any_app_r(a: List<&2, Nat>, +x: List<&2, Nat>, +y: List<&2, Nat>, +h: {C.any_in(a, List.append(&2, Nat, x, y)) == False{}: Bool}) -> {C.any_in(a, y) == False{}: Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+k, +t}:
      or_ff(C.mem(k, y), C.any_in(t, y), mem_app_r(k, x, y, or_false_l(C.mem(k, List.append(&2, Nat, x, y)), C.any_in(t, List.append(&2, Nat, x, y)), h)), any_app_r(t, x, y, or_false_r(C.mem(k, List.append(&2, Nat, x, y)), C.any_in(t, List.append(&2, Nat, x, y)), h)))

# distinct(a ++ b): nothing in a is in b.
def disjoint(a: List<&2, Nat>, +b: List<&2, Nat>, +h: {distinct(List.append(&2, Nat, a, b)) == True{}: Bool}) -> {C.any_in(a, b) == False{}: Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+k, +t}:
      +ht = MB.eq_true_of_and_left(Bool.not(C.mem(k, List.append(&2, Nat, t, b))), distinct(List.append(&2, Nat, t, b)), h)
      or_ff(C.mem(k, b), C.any_in(t, b), mem_app_r(k, t, b, not_true(C.mem(k, List.append(&2, Nat, t, b)), ht)), disjoint(t, b, MB.eq_true_of_and_right(Bool.not(C.mem(k, List.append(&2, Nat, t, b))), distinct(List.append(&2, Nat, t, b)), h)))

def mem_not_put(e: Bool, +k: Nat, +a: Nat, +t: List<&2, Nat>, +b: List<&2, Nat>, ee: {e == Nat.is_eq(k, a): Bool}, hm: {Bool.or(e, C.mem(k, t)) == True{}: Bool}, ha: {C.mem(a, b) == False{}: Bool}, ih: @_: {C.mem(k, t) == True{}: Bool} -> {C.mem(k, b) == False{}: Bool}) -> {C.mem(k, b) == False{}: Bool}:
  match e:
    case True{}:
      %Equal.sym(Nat, k, a, MN.eq_of_is_eq(k, a, Equal.sym(Bool, True{}, Nat.is_eq(k, a), ee))): {C.mem(_, b) == False{}: Bool}
      ha
    case False{}:
      ih(hm)

# k is in a, and nothing in a is in b: k is not in b.
def mem_not(a: List<&2, Nat>, +b: List<&2, Nat>, +k: Nat, hm: {C.mem(k, a) == True{}: Bool}, +hany: {C.any_in(a, b) == False{}: Bool}) -> {C.mem(k, b) == False{}: Bool}:
  match a:
    case Nil{}:
      Empty.absurd({C.mem(k, b) == False{}: Bool}, true_ne_false(Equal.sym(Bool, False{}, True{}, hm)))
    case Con{+h, +t}:
      mem_not_put(Nat.is_eq(k, h), k, h, t, b, {==}, hm, or_false_l(C.mem(h, b), C.any_in(t, b), hany), x => mem_not(t, b, k, x, or_false_r(C.mem(h, b), C.any_in(t, b), hany)))

# every k of ks is in a, and nothing in a is in b: nothing of ks is in b.
def all_any(ks: List<&2, Nat>, +a: List<&2, Nat>, +b: List<&2, Nat>, +hall: {C.all_in(ks, a) == True{}: Bool}, +hany: {C.any_in(a, b) == False{}: Bool}) -> {C.any_in(ks, b) == False{}: Bool}:
  match ks:
    case Nil{}:
      {==}
    case Con{+k, +t}:
      or_ff(C.mem(k, b), C.any_in(t, b), mem_not(a, b, k, MB.eq_true_of_and_left(C.mem(k, a), C.all_in(t, a), hall), hany), all_any(t, a, b, MB.eq_true_of_and_right(C.mem(k, a), C.all_in(t, a), hall), hany))

def miss(ks: List<&2, Nat>, +d: List<&2, Nat>, +k2: List<&2, Nat>, +hd: {C.any_in(ks, d) == False{}: Bool}, +hk: {C.any_in(ks, k2) == False{}: Bool}) -> {C.any_in(ks, List.append(&2, Nat, d, k2)) == False{}: Bool}:
  match ks:
    case Nil{}:
      {==}
    case Con{+k, +t}:
      or_ff(C.mem(k, List.append(&2, Nat, d, k2)), C.any_in(t, List.append(&2, Nat, d, k2)), mem_app_ff(k, d, k2, or_false_l(C.mem(k, d), C.any_in(t, d), hd), or_false_l(C.mem(k, k2), C.any_in(t, k2), hk)), miss(t, d, k2, or_false_r(C.mem(k, d), C.any_in(t, d), hd), or_false_r(C.mem(k, k2), C.any_in(t, k2), hk)))

def assoc_distinct(+a: List<&2, Nat>, +b: List<&2, Nat>, +c: List<&2, Nat>, h: {distinct(List.append(&2, Nat, a, List.append(&2, Nat, b, c))) == True{}: Bool}) -> {distinct(List.append(&2, Nat, List.append(&2, Nat, a, b), c)) == True{}: Bool}:
  %ML.append_assoc_sym(&2, Nat, a, b, c): {distinct(_) == True{}: Bool}
  h

def fd_put(b: Bool, +h: Nat, +t: List<&2, Nat>, eb: {b == C.mem(h, t): Bool}, ih: {Maybe.is_none(&2, Nat, C.first_dup(t)) == distinct(t): Bool}) -> {Maybe.is_none(&2, Nat, C.first_dup.put(b, h, C.first_dup(t))) == Bool.and(Bool.not(b), distinct(t)): Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# first_dup finds nothing exactly when the list is distinct.
def fd_none(ks: List<&2, Nat>) -> {Maybe.is_none(&2, Nat, C.first_dup(ks)) == distinct(ks): Bool}:
  match ks:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      fd_put(C.mem(h, t), h, t, {==}, fd_none(t))

def get_or(m: Maybe<&2, Nat>, d: Nat) -> Nat:
  match m:
    case Some{v}:
      v
    case None{}:
      d

# x is in t: it occurs there at least once.
def mem_count_put(e: Bool, +x: Nat, +y: Nat, +r: List<&2, Nat>, h: {Bool.or(e, C.mem(x, r)) == True{}: Bool}, ih: @_: {C.mem(x, r) == True{}: Bool} -> {Nat.is_lt(0n, count(x, r)) == True{}: Bool}) -> {Nat.is_lt(0n, count.put(e, count(x, r))) == True{}: Bool}:
  match e:
    case True{}:
      {==}
    case False{}:
      ih(h)

def mem_count(+x: Nat, t: List<&2, Nat>, h: {C.mem(x, t) == True{}: Bool}) -> {Nat.is_lt(0n, count(x, t)) == True{}: Bool}:
  match t:
    case Nil{}:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{}: Bool}, true_ne_false(Equal.sym(Bool, False{}, True{}, h)))
    case Con{+y, +r}:
      mem_count_put(Nat.is_eq(x, y), x, y, r, h, hh => mem_count(x, r, hh))

def lt1_succ(c: Nat, h: {Nat.is_lt(1n, c) == True{}: Bool}) -> {Nat.is_lt(1n, 1n+c) == True{}: Bool}:
  match c:
    case 0n:
      Empty.absurd({Nat.is_lt(1n, 1n) == True{}: Bool}, true_ne_false(Equal.sym(Bool, False{}, True{}, h)))
    case 1n+p:
      {==}

def lt1_put(b: Bool, c: Nat, h: {Nat.is_lt(1n, c) == True{}: Bool}) -> {Nat.is_lt(1n, count.put(b, c)) == True{}: Bool}:
  match b:
    case True{}:
      lt1_succ(c, h)
    case False{}:
      h

def SomeEmpty(-A: Data, m: Maybe<&2, A>) -> Type:
  match m:
    case Some{v}:
      Empty
    case None{}:
      Unit

def none_ne_some(-A: Data, -v: A, e: {None{} == Some{v}: Maybe<&2, A>}) -> Empty:
  %e: SomeEmpty(A, _)
  Unit{}

def fd_count_put(b: Bool, +h: Nat, +t: List<&2, Nat>, +x: Nat, eb: {b == C.mem(h, t): Bool}, hs: {C.first_dup.put(b, h, C.first_dup(t)) == Some{x}: Maybe<&2, Nat>}, ih: @_: {C.first_dup(t) == Some{x}: Maybe<&2, Nat>} -> {Nat.is_lt(1n, count(x, t)) == True{}: Bool}) -> {Nat.is_lt(1n, count(x, h <> t)) == True{}: Bool}:
  match b:
    case True{}:
      %Equal.cong(Maybe<&2, Nat>, Nat, m => get_or(m, x), Some{h}, Some{x}, hs): {Nat.is_lt(1n, count(_, h <> t)) == True{}: Bool}
      %MN.is_eq_refl_sym(h): {Nat.is_lt(1n, count.put(_, count(h, t))) == True{}: Bool}
      mem_count(h, t, Equal.sym(Bool, True{}, C.mem(h, t), eb))
    case False{}:
      lt1_put(Nat.is_eq(x, h), count(x, t), ih(hs))

# first_dup names x: x occurs at least twice.
def fd_count(ks: List<&2, Nat>, +x: Nat, h: {C.first_dup(ks) == Some{x}: Maybe<&2, Nat>}) -> {Nat.is_lt(1n, count(x, ks)) == True{}: Bool}:
  match ks:
    case Nil{}:
      Empty.absurd({Nat.is_lt(1n, 0n) == True{}: Bool}, none_ne_some(Nat, x, h))
    case Con{+y, +t}:
      fd_count_put(C.mem(y, t), y, t, x, {==}, h, hh => fd_count(t, x, hh))

# ---- tools: Bool.and ----
def and_r(x: Bool, -y: Bool, h: {Bool.and(x, y) == True{}: Bool}) -> {y == True{}: Bool}:
  match x:
    case True{}:
      h
    case False{}:
      Empty.absurd({y == True{}: Bool}, true_ne_false(Equal.sym(Bool, False{}, True{}, h)))

def and_or(e: Bool, x: Bool, +y: Bool, h: {Bool.and(x, y) == True{}: Bool}) -> {Bool.and(Bool.or(e, x), y) == True{}: Bool}:
  match e:
    case True{}:
      and_r(x, y, h)
    case False{}:
      h

# ---- tools: missing ----

# missing finds nothing exactly when every name is in the set.
def me_put(b: Bool, +h: Nat, +t: List<&2, Nat>, +have: List<&2, Nat>, ih: {Maybe.is_none(&2, Nat, C.missing(t, have)) == C.all_in(t, have): Bool}) -> {Maybe.is_none(&2, Nat, C.missing.put(b, h, C.missing(t, have))) == Bool.and(b, C.all_in(t, have)): Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      {==}

def me_go(ks: List<&2, Nat>, +have: List<&2, Nat>) -> {Maybe.is_none(&2, Nat, C.missing(ks, have)) == C.all_in(ks, have): Bool}:
  match ks:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      me_put(C.mem(h, have), h, t, have, me_go(t, have))

# ---- add and remove: membership ----

# An id that is in the set already, and equals x, puts x in the set.
def mem_contra(+x: Nat, +c: Nat, +cs: List<&2, Nat>, xc: {x == c: Nat}, em: {False{} == C.mem(x, cs): Bool}, hc: {True{} == C.mem(c, cs): Bool}) -> {True{} == False{}: Bool}:
  %Equal.sym(Bool, False{}, C.mem(x, cs), em): {True{} == _: Bool}
  %Equal.sym(Nat, x, c, xc): {True{} == C.mem(_, cs): Bool}
  hc

def mem_or_eq(m: Bool, b: Bool, +x: Nat, +c: Nat, +cs: List<&2, Nat>, em: {m == C.mem(x, cs): Bool}, eb: {b == Nat.is_eq(x, c): Bool}, hc: {True{} == C.mem(c, cs): Bool}) -> {m == Bool.or(m, b): Bool}:
  match m b:
    case True{} _:
      {==}
    case False{} False{}:
      {==}
    case False{} True{}:
      Equal.sym(Bool, True{}, False{}, mem_contra(x, c, cs, MN.eq_of_is_eq(x, c, Equal.sym(Bool, True{}, Nat.is_eq(x, c), eb)), em, hc))

def mem_add_put(have: Bool, +x: Nat, +c: Nat, +cs: List<&2, Nat>, eh: {have == C.mem(c, cs): Bool}) -> {C.mem(x, C.add.put(have, c, cs)) == Bool.or(C.mem(x, cs), Nat.is_eq(x, c)): Bool}:
  match have:
    case True{}:
      mem_or_eq(C.mem(x, cs), Nat.is_eq(x, c), x, c, cs, {==}, {==}, eh)
    case False{}:
      MB.or_comm(Nat.is_eq(x, c), C.mem(x, cs))

def mem_add(+x: Nat, +c: Nat, +cs: List<&2, Nat>) -> {C.mem(x, C.add(c, cs)) == Bool.or(C.mem(x, cs), Nat.is_eq(x, c)): Bool}:
  mem_add_put(C.mem(c, cs), x, c, cs, {==})

# Equal ids cannot be told apart: these three are the impossible rows.
def contra_keep(+x: Nat, +c: Nat, +h: Nat, es: {False{} == Nat.is_eq(c, h): Bool}, e1: {True{} == Nat.is_eq(x, h): Bool}, e2: {True{} == Nat.is_eq(x, c): Bool}) -> {True{} == False{}: Bool}:
  %Equal.sym(Bool, False{}, Nat.is_eq(c, h), es): {True{} == _: Bool}
  %MN.eq_of_is_eq(x, c, Equal.sym(Bool, True{}, Nat.is_eq(x, c), e2)): {True{} == Nat.is_eq(_, h): Bool}
  e1

def contra_drop(+x: Nat, +c: Nat, +h: Nat, es: {True{} == Nat.is_eq(c, h): Bool}, e1: {True{} == Nat.is_eq(x, h): Bool}, e2: {False{} == Nat.is_eq(x, c): Bool}) -> {True{} == False{}: Bool}:
  %Equal.sym(Bool, False{}, Nat.is_eq(x, c), e2): {True{} == _: Bool}
  %Equal.sym(Nat, x, h, MN.eq_of_is_eq(x, h, Equal.sym(Bool, True{}, Nat.is_eq(x, h), e1))): {True{} == Nat.is_eq(_, c): Bool}
  %Equal.sym(Nat, c, h, MN.eq_of_is_eq(c, h, Equal.sym(Bool, True{}, Nat.is_eq(c, h), es))): {True{} == Nat.is_eq(h, _): Bool}
  Equal.sym(Bool, Nat.is_eq(h, h), True{}, MN.is_eq_refl(h))

# The head is kept: x is in the head or in the rest, minus c.
def rm_keep_bool(b1: Bool, b2: Bool, m: Bool, +x: Nat, +c: Nat, +h: Nat, es: {False{} == Nat.is_eq(c, h): Bool}, e1: {b1 == Nat.is_eq(x, h): Bool}, e2: {b2 == Nat.is_eq(x, c): Bool}) -> {Bool.or(b1, Bool.and(m, Bool.not(b2))) == Bool.and(Bool.or(b1, m), Bool.not(b2)): Bool}:
  match b1 b2:
    case True{} True{}:
      contra_keep(x, c, h, es, e1, e2)
    case True{} False{}:
      {==}
    case False{} _:
      {==}

# The head is dropped (it equals c).
def rm_drop_bool(b1: Bool, b2: Bool, m: Bool, +x: Nat, +c: Nat, +h: Nat, es: {True{} == Nat.is_eq(c, h): Bool}, e1: {b1 == Nat.is_eq(x, h): Bool}, e2: {b2 == Nat.is_eq(x, c): Bool}) -> {Bool.and(m, Bool.not(b2)) == Bool.and(Bool.or(b1, m), Bool.not(b2)): Bool}:
  match b1 b2 m:
    case False{} _ _:
      {==}
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      Equal.sym(Bool, True{}, False{}, contra_drop(x, c, h, es, e1, e2))

def mem_remove_put(same: Bool, +b1: Bool, +b2: Bool, +m: Bool, +x: Nat, +c: Nat, +h: Nat, +t: List<&2, Nat>, es: {same == Nat.is_eq(c, h): Bool}, +e1: {b1 == Nat.is_eq(x, h): Bool}, e2: {b2 == Nat.is_eq(x, c): Bool}, ih: {C.mem(x, C.remove(c, t)) == Bool.and(m, Bool.not(b2)): Bool}) -> {C.mem(x, C.remove.put(same, h, C.remove(c, t))) == Bool.and(Bool.or(b1, m), Bool.not(b2)): Bool}:
  match same:
    case True{}:
      %Equal.sym(Bool, C.mem(x, C.remove(c, t)), Bool.and(m, Bool.not(b2)), ih): {_ == Bool.and(Bool.or(b1, m), Bool.not(b2)): Bool}
      rm_drop_bool(b1, b2, m, x, c, h, es, e1, e2)
    case False{}:
      %e1: {Bool.or(_, C.mem(x, C.remove(c, t))) == Bool.and(Bool.or(b1, m), Bool.not(b2)): Bool}
      %Equal.sym(Bool, C.mem(x, C.remove(c, t)), Bool.and(m, Bool.not(b2)), ih): {Bool.or(b1, _) == Bool.and(Bool.or(b1, m), Bool.not(b2)): Bool}
      rm_keep_bool(b1, b2, m, x, c, h, es, e1, e2)

def mem_remove(+x: Nat, +c: Nat, cs: List<&2, Nat>) -> {C.mem(x, C.remove(c, cs)) == Bool.and(C.mem(x, cs), Bool.not(Nat.is_eq(x, c))): Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      mem_remove_put(Nat.is_eq(c, h), Nat.is_eq(x, h), Nat.is_eq(x, c), C.mem(x, t), x, c, h, t, {==}, {==}, {==}, mem_remove(x, c, t))

def and_not_true(m: Bool) -> {Bool.and(m, Bool.not(True{})) == False{}: Bool}:
  match m:
    case True{}:
      {==}
    case False{}:
      {==}

def mem_remove_self(+q: Nat, +o: List<&2, Nat>) -> {C.mem(q, C.remove(q, o)) == False{}: Bool}:
  %Equal.sym(Bool, C.mem(q, C.remove(q, o)), Bool.and(C.mem(q, o), Bool.not(Nat.is_eq(q, q))), mem_remove(q, q, o)): {_ == False{}: Bool}
  %MN.is_eq_refl_sym(q): {Bool.and(C.mem(q, o), Bool.not(_)) == False{}: Bool}
  and_not_true(C.mem(q, o))

def mrf_put(e: Bool, +k: Nat, +h: Nat, +x: Nat, +t: List<&2, Nat>, +hx: {Nat.is_eq(h, x) == False{}: Bool}, ih: {C.mem(h, C.remove(k, t)) == False{}: Bool}) -> {C.mem(h, C.remove.put(e, x, C.remove(k, t))) == False{}: Bool}:
  match e:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(h, x), False{}, hx): {Bool.or(_, C.mem(h, C.remove(k, t))) == False{}: Bool}
      ih

def mem_remove_false(t: List<&2, Nat>, +k: Nat, +h: Nat, +hf: {C.mem(h, t) == False{}: Bool}) -> {C.mem(h, C.remove(k, t)) == False{}: Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      mrf_put(Nat.is_eq(k, x), k, h, x, r, or_false_l(Nat.is_eq(h, x), C.mem(h, r), hf), mem_remove_false(r, k, h, or_false_r(Nat.is_eq(h, x), C.mem(h, r), hf)))

def rs_go(b: Bool, +o: List<&2, Nat>, +k: Nat, +p: Nat, eb: {b == C.mem(p, o): Bool}, h: {C.mem(p, C.remove(k, o)) == True{}: Bool}) -> {b == True{}: Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{}: Bool}, true_ne_false(Equal.trans(Bool, True{}, C.mem(p, C.remove(k, o)), False{}, Equal.sym(Bool, C.mem(p, C.remove(k, o)), True{}, h), mem_remove_false(o, k, p, Equal.sym(Bool, False{}, C.mem(p, o), eb)))))

def mem_remove_sub(+o: List<&2, Nat>, +k: Nat, +p: Nat, h: {C.mem(p, C.remove(k, o)) == True{}: Bool}) -> {C.mem(p, o) == True{}: Bool}:
  rs_go(C.mem(p, o), o, k, p, {==}, h)
