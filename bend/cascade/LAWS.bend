import Base
import ./core.bend as C
import ../comp/core.bend as M
import ../comp/FACTS.bend as MF
import ../keys/core.bend as K

# Every law here is approved, and proved in PROOF.bend.
#
# cascade: a change restarts exactly the affected chains
#   cascade_sub, cascade_chain, cascade_complete

# ---- reference definitions: what the laws are stated with ----

# xs occurs in ys in order, possibly with gaps: either xs starts with y and
# the rest occurs in what follows y, or xs occurs in what follows y.
def is_sub.head(xs: List<&2, Nat>, +y: Nat, k: List<&2, Nat> -> Bool) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, r}:
      Bool.and(Nat.is_eq(x, y), k(r))

def is_sub.go(ys: List<&2, Nat>, +xs: List<&2, Nat>) -> Bool:
  match ys:
    case Nil{}:
      List.is_empty(&2, Nat, xs)
    case Con{+y, +t}:
      Bool.or(is_sub.head(xs, y, z => is_sub.go(t, z)), is_sub.go(t, xs))

def is_sub(+xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  is_sub.go(ys, xs)

# Each restart injects a key that was dirty, or provided by an earlier restart.
def chain(rs: List<&2, M.Comp>, +dirty: List<&2, Nat>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{+c, t}:
      Bool.and(M.hit(c, dirty), chain(t, List.append(&2, Nat, dirty, M.provides(c))))

def none_hit(cs: List<&2, M.Comp>, +dirty: List<&2, Nat>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{c, t}:
      Bool.and(Bool.not(M.hit(c, dirty)), none_hit(t, dirty))

# The components of o whose id is not in ks.
def skip.put(gone: Bool, c: M.Comp, r: List<&2, M.Comp>) -> List<&2, M.Comp>:
  match gone:
    case True{}:
      r
    case False{}:
      c <> r

def skip(o: List<&2, M.Comp>, +ks: List<&2, Nat>) -> List<&2, M.Comp>:
  match o:
    case Nil{}:
      Nil{}
    case Con{+c, t}:
      skip.put(K.mem(M.id_of(c), ks), c, skip(t, ks))

# Guarantees: Every component the cascade restarts is one of the active components, and they
#   come out in the active order (no premises).
# Why it matters: A change could restart a component that is not running, or restart
#   components out of dependency order.
law cascade_sub:
  for +o: List<&2, M.Comp>
  for +d: List<&2, Nat>
  {is_sub(M.ids(C.cascade(o, d)), M.ids(o)) == True{} : Bool}

# Guarantees: Each restarted component injects a key that changed, or a key that an earlier
#   restart provides (no premises).
# Why it matters: A running component that depends on nothing that changed would be
#   restarted for no reason, and lose its state.
law cascade_chain:
  for +o: List<&2, M.Comp>
  for +d: List<&2, Nat>
  {chain(C.cascade(o, d), d) == True{} : Bool}

# Guarantees: If the order is valid from root and the registry is well-formed (distinct ids,
#   one source per key), no component left running injects a changed key or a key a restart
#   provides.
# Why it matters: A component that should have restarted would keep running on a stale
#   value, and the plugin that depends on it would see old data.
law cascade_complete:
  for +root: List<&2, Nat>
  for +o: List<&2, M.Comp>
  for +d: List<&2, Nat>
  for hv: {MF.valid_order(o, root) == True{} : Bool}
  for hw: {MF.wf(root, o) == True{} : Bool}
  {none_hit(skip(o, M.ids(C.cascade(o, d))), MF.after(C.cascade(o, d), d)) == True{} : Bool}
