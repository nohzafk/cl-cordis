import Base
import ./core.bend as C
import ../keys/core.bend as K
import ../comp/core.bend as M
import ../comp/FACTS.bend as MF
import ../keys/FACTS.bend as KF

# Every law here is approved, and proved in PROOF.bend.
#
# plan: the activation order is the least fixpoint, found in one pass
#   plan_sound, plan_maximal, plan_conserves

# ---- reference definitions: what the laws are stated with ----

def none_ready(cs: List<&2, M.Comp>, +avail: List<&2, Nat>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{c, t}:
      Bool.and(Bool.not(M.ready(c, avail)), none_ready(t, avail))

# Guarantees: Each component in the planned order is ready on the root keys plus the keys
#   that the components before it provide (no premises).
# Why it matters: A component could activate before its dependencies, and start with an
#   injected key unset.
law plan_sound:
  for +root: List<&2, Nat>
  for +cs: List<&2, M.Comp>
  {MF.valid_order(C.order_of(C.plan(root, cs)), root) == True{} : Bool}

# Guarantees: No blocked component is ready on the root keys plus everything the planned
#   order provides (no premises).
# Why it matters: A component that could activate would be left waiting for no reason.
law plan_maximal:
  for +root: List<&2, Nat>
  for +cs: List<&2, M.Comp>
  {none_ready(C.blocked_of(C.plan(root, cs)), MF.after(C.order_of(C.plan(root, cs)), root)) == True{} : Bool}

# Guarantees: Every component id occurs in the input exactly as often as in the order and in
#   blocked together (no premises). With plan_sound and plan_maximal, exactly the least
#   fixpoint activates and a cycle never does.
# Why it matters: A component could be dropped without a trace, or come out twice.
law plan_conserves:
  for +root: List<&2, Nat>
  for +cs: List<&2, M.Comp>
  for +n: Nat
  {KF.count(n, M.ids(cs)) == Nat.add(KF.count(n, M.ids(C.order_of(C.plan(root, cs)))), KF.count(n, M.ids(C.blocked_of(C.plan(root, cs))))) : Nat}
