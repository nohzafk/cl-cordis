import Base
import ./LAWS.bend as Laws
import ./core.bend as C
import ./FACTS.bend as F
import bend-mathlib@0.7.4.0/nat.bend as MN

# The proofs of the laws in LAWS.bend. Each law's proof sits under its own
# "# ---- name ----" header, which mutants.ts relies on.

# ---- missing_exact ----
def Laws.missing_exact(ks, have):
  F.me_go(ks, have)

# ---- missing_accurate ----
def ma_put(b: Bool, +h: Nat, +t: List<&2, Nat>, +have: List<&2, Nat>, +k: Nat, eb: {b == C.mem(h, have): Bool}, hs: {C.missing.put(b, h, C.missing(t, have)) == Some{k}: Maybe<&2, Nat>}, ih: @_: {C.missing(t, have) == Some{k}: Maybe<&2, Nat>} -> {Bool.and(C.mem(k, t), Bool.not(C.mem(k, have))) == True{}: Bool}) -> {Bool.and(C.mem(k, h <> t), Bool.not(C.mem(k, have))) == True{}: Bool}:
  match b:
    case True{}:
      F.and_or(Nat.is_eq(k, h), C.mem(k, t), Bool.not(C.mem(k, have)), ih(hs))
    case False{}:
      %Equal.cong(Maybe<&2, Nat>, Nat, m => F.get_or(m, h), Some{h}, Some{k}, hs): {Bool.and(C.mem(_, h <> t), Bool.not(C.mem(_, have))) == True{}: Bool}
      %Equal.sym(Bool, Nat.is_eq(h, h), True{}, MN.is_eq_refl(h)): {Bool.and(Bool.or(_, C.mem(h, t)), Bool.not(C.mem(h, have))) == True{}: Bool}
      %eb: {Bool.not(_) == True{}: Bool}
      {==}

def ma_go(ks: List<&2, Nat>, +have: List<&2, Nat>, +k: Nat, h: {C.missing(ks, have) == Some{k}: Maybe<&2, Nat>}) -> {Bool.and(C.mem(k, ks), Bool.not(C.mem(k, have))) == True{}: Bool}:
  match ks:
    case Nil{}:
      Empty.absurd({Bool.and(C.mem(k, []), Bool.not(C.mem(k, have))) == True{}: Bool}, F.none_ne_some(Nat, k, h))
    case Con{+x, +t}:
      ma_put(C.mem(x, have), x, t, have, k, {==}, h, hh => ma_go(t, have, k, hh))

def Laws.missing_accurate(ks, have, k, h):
  ma_go(ks, have, k, h)
