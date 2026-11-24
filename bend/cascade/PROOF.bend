import Base
import ./LAWS.bend as Laws
import ./core.bend as C
import ../keys/core.bend as K
import ../comp/core.bend as M
import ../keys/FACTS.bend as F
import bend-mathlib@0.7.4.0/nat.bend as MN
import bend-mathlib@0.7.4.0/list.bend as ML
import bend-mathlib@0.7.4.0/bool.bend as MB
import ../comp/FACTS.bend as MF

# The proofs of the laws in LAWS.bend. Each law's proof sits under its own
# "# ---- name ----" header, which mutants.ts relies on.

# ---- cascade_sub ----
def sub_put(b: Bool, +c: M.Comp, +t: List<&2, M.Comp>, +dirty: List<&2, Nat>, ih: @d: List<&2, Nat> -> {Laws.is_sub(M.ids(C.cascade(t, d)), M.ids(t)) == True{}: Bool}) -> {Laws.is_sub(M.ids(C.cascade.put(b, c, dirty, d => C.cascade(t, d))), M.ids(c <> t)) == True{}: Bool}:
  match b:
    case True{}:
      +x = M.ids(C.cascade(t, List.append(&2, Nat, dirty, M.provides(c))))
      %MN.is_eq_refl_sym(M.id_of(c)): {Bool.or(Bool.and(_, Laws.is_sub.go(M.ids(t), x)), Laws.is_sub.go(M.ids(t), M.id_of(c) <> x)) == True{}: Bool}
      %Equal.sym(Bool, Laws.is_sub.go(M.ids(t), x), True{}, ih(List.append(&2, Nat, dirty, M.provides(c)))): {Bool.or(Bool.and(True{}, _), Laws.is_sub.go(M.ids(t), M.id_of(c) <> x)) == True{}: Bool}
      {==}
    case False{}:
      +x = M.ids(C.cascade(t, dirty))
      %Equal.sym(Bool, Laws.is_sub.go(M.ids(t), x), True{}, ih(dirty)): {Bool.or(Laws.is_sub.head(x, M.id_of(c), z => Laws.is_sub.go(M.ids(t), z)), _) == True{}: Bool}
      MB.or_true(Laws.is_sub.head(x, M.id_of(c), z => Laws.is_sub.go(M.ids(t), z)))

def Laws.cascade_sub(o, d):
  match o:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      sub_put(M.hit(c, d), c, t, d, dd => Laws.cascade_sub(t, dd))

# ---- cascade_chain ----
def chain_put(b: Bool, +c: M.Comp, +t: List<&2, M.Comp>, +dirty: List<&2, Nat>, eb: {b == M.hit(c, dirty): Bool}, ih: @d: List<&2, Nat> -> {Laws.chain(C.cascade(t, d), d) == True{}: Bool}) -> {Laws.chain(C.cascade.put(b, c, dirty, d => C.cascade(t, d)), dirty) == True{}: Bool}:
  match b:
    case True{}:
      +d2 = List.append(&2, Nat, dirty, M.provides(c))
      %eb: {Bool.and(_, Laws.chain(C.cascade(t, d2), d2)) == True{}: Bool}
      %Equal.sym(Bool, Laws.chain(C.cascade(t, d2), d2), True{}, ih(d2)): {Bool.and(True{}, _) == True{}: Bool}
      {==}
    case False{}:
      ih(dirty)

def Laws.cascade_chain(o, d):
  match o:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      chain_put(M.hit(c, d), c, t, d, {==}, dd => Laws.cascade_chain(t, dd))

# ---- cascade_complete ----
def after_eq(o: List<&2, M.Comp>, +a: List<&2, Nat>) -> {MF.after(o, a) == List.append(&2, Nat, a, M.keys_of(o)): List<&2, Nat>}:
  match o:
    case Nil{}:
      ML.append_nil_sym(&2, Nat, a)
    case Con{+c, +t}:
      %Equal.sym(List<&2, Nat>, MF.after(t, List.append(&2, Nat, a, M.provides(c))), List.append(&2, Nat, List.append(&2, Nat, a, M.provides(c)), M.keys_of(t)), after_eq(t, List.append(&2, Nat, a, M.provides(c)))): {_ == List.append(&2, Nat, a, List.append(&2, Nat, M.provides(c), M.keys_of(t))): List<&2, Nat>}
      ML.append_assoc(&2, Nat, a, M.provides(c), M.keys_of(t))

# A restart provides only keys some component of the order provides.
def keys_put(b: Bool, +a: List<&2, Nat>, +c: M.Comp, +t: List<&2, M.Comp>, +dirty: List<&2, Nat>, +hp: {K.any_in(a, M.provides(c)) == False{}: Bool}, ih: @d: List<&2, Nat> -> {K.any_in(a, M.keys_of(C.cascade(t, d))) == False{}: Bool}) -> {K.any_in(a, M.keys_of(C.cascade.put(b, c, dirty, d => C.cascade(t, d)))) == False{}: Bool}:
  match b:
    case True{}:
      F.any_app_ff(a, M.provides(c), M.keys_of(C.cascade(t, List.append(&2, Nat, dirty, M.provides(c)))), hp, ih(List.append(&2, Nat, dirty, M.provides(c))))
    case False{}:
      ih(dirty)

def keys_any(t: List<&2, M.Comp>, +d: List<&2, Nat>, +a: List<&2, Nat>, +h: {K.any_in(a, M.keys_of(t)) == False{}: Bool}) -> {K.any_in(a, M.keys_of(C.cascade(t, d))) == False{}: Bool}:
  match t:
    case Nil{}:
      h
    case Con{+c, +r}:
      keys_put(M.hit(c, d), a, c, r, d, F.any_app_l(a, M.provides(c), M.keys_of(r), h), dd => keys_any(r, dd, a, F.any_app_r(a, M.provides(c), M.keys_of(r), h)))

# A restart is a component of the order: an id not in the order is not in it.
def ids_put(b: Bool, +x: Nat, +c: M.Comp, +t: List<&2, M.Comp>, +dirty: List<&2, Nat>, +he: {Nat.is_eq(x, M.id_of(c)) == False{}: Bool}, ih: @d: List<&2, Nat> -> {K.mem(x, M.ids(C.cascade(t, d))) == False{}: Bool}) -> {K.mem(x, M.ids(C.cascade.put(b, c, dirty, d => C.cascade(t, d)))) == False{}: Bool}:
  match b:
    case True{}:
      F.or_ff(Nat.is_eq(x, M.id_of(c)), K.mem(x, M.ids(C.cascade(t, List.append(&2, Nat, dirty, M.provides(c))))), he, ih(List.append(&2, Nat, dirty, M.provides(c))))
    case False{}:
      ih(dirty)

def ids_absent(t: List<&2, M.Comp>, +d: List<&2, Nat>, +x: Nat, +h: {K.mem(x, M.ids(t)) == False{}: Bool}) -> {K.mem(x, M.ids(C.cascade(t, d))) == False{}: Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{+c, +r}:
      ids_put(M.hit(c, d), x, c, r, d, F.or_false_l(Nat.is_eq(x, M.id_of(c)), K.mem(x, M.ids(r)), h), dd => ids_absent(r, dd, x, F.or_false_r(Nat.is_eq(x, M.id_of(c)), K.mem(x, M.ids(r)), h)))

# Skipping an id that is not in the order changes nothing.
def skip_absent(t: List<&2, M.Comp>, +x: Nat, +k: List<&2, Nat>, +h: {K.mem(x, M.ids(t)) == False{}: Bool}) -> {Laws.skip(t, k) == Laws.skip(t, x <> k): List<&2, M.Comp>}:
  match t:
    case Nil{}:
      {==}
    case Con{+c, +r}:
      +he = Equal.trans(Bool, Nat.is_eq(M.id_of(c), x), Nat.is_eq(x, M.id_of(c)), False{}, MN.is_eq_comm(M.id_of(c), x), F.or_false_l(Nat.is_eq(x, M.id_of(c)), K.mem(x, M.ids(r)), h))
      %Equal.sym(Bool, Nat.is_eq(M.id_of(c), x), False{}, he): {Laws.skip.put(K.mem(M.id_of(c), k), c, Laws.skip(r, k)) == Laws.skip.put(Bool.or(_, K.mem(M.id_of(c), k)), c, Laws.skip(r, x <> k)): List<&2, M.Comp>}
      %skip_absent(r, x, k, F.or_false_r(Nat.is_eq(x, M.id_of(c)), K.mem(x, M.ids(r)), h)): {Laws.skip.put(K.mem(M.id_of(c), k), c, Laws.skip(r, k)) == Laws.skip.put(K.mem(M.id_of(c), k), c, _): List<&2, M.Comp>}
      {==}

def complete_put(b: Bool, +cid: Nat, +inj: List<&2, Nat>, +prov: List<&2, Nat>, +t: List<&2, M.Comp>, +avail: List<&2, Nat>, +d: List<&2, Nat>, +eb: {b == K.any_in(inj, d): Bool}, +hv: {MF.valid_order(M.Comp{cid, inj, prov} <> t, avail) == True{}: Bool}, +hi: {F.distinct(M.ids(M.Comp{cid, inj, prov} <> t)) == True{}: Bool}, +hk: {F.distinct(List.append(&2, Nat, avail, M.keys_of(M.Comp{cid, inj, prov} <> t))) == True{}: Bool}, ih: @a: List<&2, Nat> -> @dd: List<&2, Nat> -> @h1: {MF.valid_order(t, a) == True{}: Bool} -> @h2: {F.distinct(M.ids(t)) == True{}: Bool} -> @h3: {F.distinct(List.append(&2, Nat, a, M.keys_of(t))) == True{}: Bool} -> {Laws.none_hit(Laws.skip(t, M.ids(C.cascade(t, dd))), MF.after(C.cascade(t, dd), dd)) == True{}: Bool}) -> {Laws.none_hit(Laws.skip(M.Comp{cid, inj, prov} <> t, M.ids(C.cascade.put(b, M.Comp{cid, inj, prov}, d, x => C.cascade(t, x)))), MF.after(C.cascade.put(b, M.Comp{cid, inj, prov}, d, x => C.cascade(t, x)), d)) == True{}: Bool}:
  match b:
    case True{}:
      +a2 = List.append(&2, Nat, avail, prov)
      +hv1 = MB.eq_true_of_and_left(K.all_in(inj, avail), MF.valid_order(t, a2), hv)
      +hv2 = MB.eq_true_of_and_right(K.all_in(inj, avail), MF.valid_order(t, a2), hv)
      +hi1 = F.not_true(K.mem(cid, M.ids(t)), MB.eq_true_of_and_left(Bool.not(K.mem(cid, M.ids(t))), F.distinct(M.ids(t)), hi))
      +hi2 = MB.eq_true_of_and_right(Bool.not(K.mem(cid, M.ids(t))), F.distinct(M.ids(t)), hi)
      +hk2 = F.assoc_distinct(avail, prov, M.keys_of(t), hk)
      +d2 = List.append(&2, Nat, d, prov)
      +r = C.cascade(t, d2)
      %MN.is_eq_refl_sym(cid): {Laws.none_hit(Laws.skip.put(Bool.or(_, K.mem(cid, M.ids(r))), M.Comp{cid, inj, prov}, Laws.skip(t, cid <> M.ids(r))), MF.after(r, d2)) == True{}: Bool}
      %skip_absent(t, cid, M.ids(r), hi1): {Laws.none_hit(_, MF.after(r, d2)) == True{}: Bool}
      ih(a2, d2, hv2, hi2, hk2)
    case False{}:
      +a2 = List.append(&2, Nat, avail, prov)
      +hv1 = MB.eq_true_of_and_left(K.all_in(inj, avail), MF.valid_order(t, a2), hv)
      +hv2 = MB.eq_true_of_and_right(K.all_in(inj, avail), MF.valid_order(t, a2), hv)
      +hi1 = F.not_true(K.mem(cid, M.ids(t)), MB.eq_true_of_and_left(Bool.not(K.mem(cid, M.ids(t))), F.distinct(M.ids(t)), hi))
      +hi2 = MB.eq_true_of_and_right(Bool.not(K.mem(cid, M.ids(t))), F.distinct(M.ids(t)), hi)
      +hk2 = F.assoc_distinct(avail, prov, M.keys_of(t), hk)
      +r = C.cascade(t, d)
      %Equal.sym(Bool, K.mem(cid, M.ids(r)), False{}, ids_absent(t, d, cid, hi1)): {Laws.none_hit(Laws.skip.put(_, M.Comp{cid, inj, prov}, Laws.skip(t, M.ids(r))), MF.after(r, d)) == True{}: Bool}
      %Equal.sym(List<&2, Nat>, MF.after(r, d), List.append(&2, Nat, d, M.keys_of(r)), after_eq(r, d)): {Bool.and(Bool.not(K.any_in(inj, _)), Laws.none_hit(Laws.skip(t, M.ids(r)), MF.after(r, d))) == True{}: Bool}
      +hany = keys_any(t, d, avail, F.any_app_r(avail, prov, M.keys_of(t), F.disjoint(avail, List.append(&2, Nat, prov, M.keys_of(t)), hk)))
      +hm = F.miss(inj, d, M.keys_of(r), Equal.sym(Bool, False{}, K.any_in(inj, d), eb), F.all_any(inj, avail, M.keys_of(r), hv1, hany))
      %Equal.sym(Bool, K.any_in(inj, List.append(&2, Nat, d, M.keys_of(r))), False{}, hm): {Bool.and(Bool.not(_), Laws.none_hit(Laws.skip(t, M.ids(r)), MF.after(r, d))) == True{}: Bool}
      %Equal.sym(Bool, Laws.none_hit(Laws.skip(t, M.ids(r)), MF.after(r, d)), True{}, ih(a2, d, hv2, hi2, hk2)): {Bool.and(True{}, _) == True{}: Bool}
      {==}

def complete_go(o: List<&2, M.Comp>, +avail: List<&2, Nat>, +d: List<&2, Nat>, +hv: {MF.valid_order(o, avail) == True{}: Bool}, +hi: {F.distinct(M.ids(o)) == True{}: Bool}, +hk: {F.distinct(List.append(&2, Nat, avail, M.keys_of(o))) == True{}: Bool}) -> {Laws.none_hit(Laws.skip(o, M.ids(C.cascade(o, d))), MF.after(C.cascade(o, d), d)) == True{}: Bool}:
  match o:
    case Nil{}:
      {==}
    case Con{M.Comp{+cid, +inj, +prov}, +t}:
      complete_put(K.any_in(inj, d), cid, inj, prov, t, avail, d, {==}, hv, hi, hk, a => dd => h1 => h2 => h3 => complete_go(t, a, dd, h1, h2, h3))

def complete_wf(+root: List<&2, Nat>, +o: List<&2, M.Comp>, +d: List<&2, Nat>, hv: {MF.valid_order(o, root) == True{}: Bool}, +hw: {MF.wf(root, o) == True{}: Bool}) -> {Laws.none_hit(Laws.skip(o, M.ids(C.cascade(o, d))), MF.after(C.cascade(o, d), d)) == True{}: Bool}:
  complete_go(o, root, d, hv, MB.eq_true_of_and_left(F.distinct(M.ids(o)), F.distinct(List.append(&2, Nat, root, M.keys_of(o))), hw), MB.eq_true_of_and_right(F.distinct(M.ids(o)), F.distinct(List.append(&2, Nat, root, M.keys_of(o))), hw))

def Laws.cascade_complete(root, o, d, hv, hw):
  complete_wf(root, o, d, hv, hw)
