import Base
import ./core.bend as C
import ../keys/core.bend as K
import ../keys/FACTS.bend as KF

# Every law here is approved, and proved in PROOF.bend.
#
# undo: unloading reverts what loading installed
#   undo_exact, undo_newest, undo_append, undo_child

# ---- reference definitions: what the laws are stated with ----

# Every id the ledger installed, in no particular order: the specification of
# "every effect is reverted exactly once".
def installed(xs: List<&2, C.Entry>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{C.Eff{id}, t}:
      id <> installed(t)
    case Con{C.Sub{id, kids}, t}:
      id <> List.append(&2, Nat, installed(kids), installed(t))

# Guarantees: Each installed effect's inverse runs exactly as often as it was installed, for
#   every id (no premises). The count is kept even if ids repeat; it does not prove that a
#   release succeeds.
# Why it matters: An inverse could be skipped, so a resource leaks, or run twice.
law undo_exact:
  for +xs: List<&2, C.Entry>
  for +n: Nat
  {KF.count(n, C.undo(xs)) == KF.count(n, installed(xs)) : Nat}

# Guarantees: With the newest effect at the head of the ledger, its inverse is the first
#   release, followed by the release of the rest (no premises).
# Why it matters: A later effect could outlive the earlier one it was built on (a FIFO undo
#   passes undo_append but not this law).
law undo_newest:
  for +i: Nat
  for +t: List<&2, C.Entry>
  {C.undo(C.Eff{i} <> t) == i <> C.undo(t) : List<&2, Nat>}

# Guarantees: For any split of a ledger, the release of the newer part comes wholly before
#   the release of the older part (no premises). With undo_newest and undo_child, the three
#   laws determine undo completely.
# Why it matters: Releases of the two parts could interleave, so an older resource is
#   released while a newer one still uses it.
law undo_append:
  for +xs: List<&2, C.Entry>
  for +ys: List<&2, C.Entry>
  {C.undo(List.append(&2, C.Entry, xs, ys)) == List.append(&2, Nat, C.undo(xs), C.undo(ys)) : List<&2, Nat>}

# Guarantees: A child component's own ledger is released first, and its creation is reverted
#   immediately after that and before the older remainder (no premises).
# Why it matters: A child could be destroyed while its own resources were still held, or be
#   torn down at the wrong time among the parent's releases.
law undo_child:
  for +i: Nat
  for +ks: List<&2, C.Entry>
  for +t: List<&2, C.Entry>
  {C.undo(C.Sub{i, ks} <> t) == List.append(&2, Nat, C.undo(ks), i <> C.undo(t)) : List<&2, Nat>}
