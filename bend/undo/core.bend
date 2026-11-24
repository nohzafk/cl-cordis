import Base

# ---- undo: the ledger of revertible effects ----
#
# A component's ledger, newest entry first. An entry is an effect, or a child
# component, whose creation is itself an effect of its parent and which owns a
# ledger of its own. undo answers the ids whose inverses run, in the order they
# run: newest first, and a child's whole ledger before the child itself.
type Entry is Data:
  Eff{id: Nat}
  Sub{id: Nat, kids: List<&2, Entry>}

def undo(xs: List<&2, Entry>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{Eff{id}, t}:
      id <> undo(t)
    case Con{Sub{id, kids}, t}:
      List.append(&2, Nat, undo(kids), id <> undo(t))
