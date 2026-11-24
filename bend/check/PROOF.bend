import Base
import ./LAWS.bend as Laws
import ./core.bend as C
import ../keys/core.bend as K
import ../comp/core.bend as M
import ../keys/FACTS.bend as F
import ../comp/FACTS.bend as MF

# The proofs of the laws in LAWS.bend. Each law's proof sits under its own
# "# ---- name ----" header, which mutants.ts relies on.

# ---- check_exact ----
def cp_none(m: Maybe<&2, Nat>, k: Maybe<&2, C.Err>) -> {Maybe.is_none(&2, C.Err, C.check.put(m, k)) == Bool.and(Maybe.is_none(&2, Nat, m), Maybe.is_none(&2, C.Err, k)): Bool}:
  match m:
    case None{}:
      {==}
    case Some{i}:
      {==}

def ck_none(m: Maybe<&2, Nat>) -> {Maybe.is_none(&2, C.Err, C.check.keys(m)) == Maybe.is_none(&2, Nat, m): Bool}:
  match m:
    case None{}:
      {==}
    case Some{k}:
      {==}

def ce_and(+ids: List<&2, Nat>, +ks: List<&2, Nat>) -> {Bool.and(Maybe.is_none(&2, Nat, K.first_dup(ids)), Maybe.is_none(&2, C.Err, C.check.keys(K.first_dup(ks)))) == Bool.and(F.distinct(ids), F.distinct(ks)): Bool}:
  %F.fd_none(ids): {Bool.and(Maybe.is_none(&2, Nat, K.first_dup(ids)), Maybe.is_none(&2, C.Err, C.check.keys(K.first_dup(ks)))) == Bool.and(_, F.distinct(ks)): Bool}
  %F.fd_none(ks): {Bool.and(Maybe.is_none(&2, Nat, K.first_dup(ids)), Maybe.is_none(&2, C.Err, C.check.keys(K.first_dup(ks)))) == Bool.and(Maybe.is_none(&2, Nat, K.first_dup(ids)), _): Bool}
  %ck_none(K.first_dup(ks)): {Bool.and(Maybe.is_none(&2, Nat, K.first_dup(ids)), Maybe.is_none(&2, C.Err, C.check.keys(K.first_dup(ks)))) == Bool.and(Maybe.is_none(&2, Nat, K.first_dup(ids)), _): Bool}
  {==}

def Laws.check_exact(root, cs):
  Equal.trans(Bool, Maybe.is_none(&2, C.Err, C.check(root, cs)), Bool.and(Maybe.is_none(&2, Nat, K.first_dup(M.ids(cs))), Maybe.is_none(&2, C.Err, C.check.keys(K.first_dup(List.append(&2, Nat, root, M.keys_of(cs)))))), MF.wf(root, cs), cp_none(K.first_dup(M.ids(cs)), C.check.keys(K.first_dup(List.append(&2, Nat, root, M.keys_of(cs))))), ce_and(M.ids(cs), List.append(&2, Nat, root, M.keys_of(cs))))

# ---- check_accurate ----
def err_or(m: Maybe<&2, C.Err>, d: C.Err) -> C.Err:
  match m:
    case Some{v}:
      v
    case None{}:
      d

def acc_keys(ks: Maybe<&2, Nat>, +root: List<&2, Nat>, +cs: List<&2, M.Comp>, ek: {K.first_dup(List.append(&2, Nat, root, M.keys_of(cs))) == ks: Maybe<&2, Nat>}, +e: C.Err, h: {C.check.keys(ks) == Some{e}: Maybe<&2, C.Err>}) -> {Laws.real(e, root, cs) == True{}: Bool}:
  match ks:
    case None{}:
      Empty.absurd({Laws.real(e, root, cs) == True{}: Bool}, F.none_ne_some(C.Err, e, h))
    case Some{+k}:
      %Equal.cong(Maybe<&2, C.Err>, C.Err, m => err_or(m, e), Some{C.DupKey{k}}, Some{e}, h): {Laws.real(_, root, cs) == True{}: Bool}
      F.fd_count(List.append(&2, Nat, root, M.keys_of(cs)), k, ek)

def acc_put(m: Maybe<&2, Nat>, +root: List<&2, Nat>, +cs: List<&2, M.Comp>, em: {K.first_dup(M.ids(cs)) == m: Maybe<&2, Nat>}, +e: C.Err, h: {C.check.put(m, C.check.keys(K.first_dup(List.append(&2, Nat, root, M.keys_of(cs))))) == Some{e}: Maybe<&2, C.Err>}) -> {Laws.real(e, root, cs) == True{}: Bool}:
  match m:
    case Some{+i}:
      %Equal.cong(Maybe<&2, C.Err>, C.Err, mm => err_or(mm, e), Some{C.DupId{i}}, Some{e}, h): {Laws.real(_, root, cs) == True{}: Bool}
      F.fd_count(M.ids(cs), i, em)
    case None{}:
      acc_keys(K.first_dup(List.append(&2, Nat, root, M.keys_of(cs))), root, cs, {==}, e, h)

def Laws.check_accurate(root, cs, e, h):
  acc_put(K.first_dup(M.ids(cs)), root, cs, {==}, e, h)
