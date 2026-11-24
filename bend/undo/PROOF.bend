import Base
import ./LAWS.bend as Laws
import ./core.bend as C
import ../keys/core.bend as K
import ../keys/FACTS.bend as F
import bend-mathlib@0.7.4.0/list.bend as ML

# The proofs of the laws in LAWS.bend. Each law's proof sits under its own
# "# ---- name ----" header, which mutants.ts relies on.

# ---- undo_exact ----
def Laws.undo_exact(xs, n):
  match xs:
    case Nil{}:
      {==}
    case Con{C.Eff{+id}, +t}:
      %Laws.undo_exact(t, n): {F.count.put(Nat.is_eq(n, id), F.count(n, C.undo(t))) == F.count.put(Nat.is_eq(n, id), _): Nat}
      {==}
    case Con{C.Sub{+id, +kids}, +t}:
      %F.count_split(n, C.undo(kids), id <> C.undo(t)): {_ == F.count.put(Nat.is_eq(n, id), F.count(n, List.append(&2, Nat, Laws.installed(kids), Laws.installed(t)))): Nat}
      %F.count_split(n, Laws.installed(kids), Laws.installed(t)): {Nat.add(F.count(n, C.undo(kids)), F.count(n, id <> C.undo(t))) == F.count.put(Nat.is_eq(n, id), _): Nat}
      %Laws.undo_exact(kids, n): {Nat.add(F.count(n, C.undo(kids)), F.count(n, id <> C.undo(t))) == F.count.put(Nat.is_eq(n, id), Nat.add(_, F.count(n, Laws.installed(t)))): Nat}
      %Laws.undo_exact(t, n): {Nat.add(F.count(n, C.undo(kids)), F.count(n, id <> C.undo(t))) == F.count.put(Nat.is_eq(n, id), Nat.add(F.count(n, C.undo(kids)), _)): Nat}
      %F.put_add_r(Nat.is_eq(n, id), F.count(n, C.undo(kids)), F.count(n, C.undo(t))): {_ == F.count.put(Nat.is_eq(n, id), Nat.add(F.count(n, C.undo(kids)), F.count(n, C.undo(t)))): Nat}
      {==}

# ---- undo_newest ----
def Laws.undo_newest(i, t):
  {==}

# ---- undo_append ----
def Laws.undo_append(xs, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{C.Eff{+id}, +t}:
      %Laws.undo_append(t, ys): {id <> C.undo(List.append(&2, C.Entry, t, ys)) == id <> _: List<&2, Nat>}
      {==}
    case Con{C.Sub{+id, +kids}, +t}:
      %ML.append_assoc_sym(&2, Nat, C.undo(kids), id <> C.undo(t), C.undo(ys)): {List.append(&2, Nat, C.undo(kids), id <> C.undo(List.append(&2, C.Entry, t, ys))) == _: List<&2, Nat>}
      %Laws.undo_append(t, ys): {List.append(&2, Nat, C.undo(kids), id <> C.undo(List.append(&2, C.Entry, t, ys))) == List.append(&2, Nat, C.undo(kids), id <> _): List<&2, Nat>}
      {==}

# ---- undo_child ----
def Laws.undo_child(i, ks, t):
  {==}
