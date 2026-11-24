import Base
import ./LAWS.bend as Laws
import ./core.bend as C
import ../keys/core.bend as K
import ../keys/FACTS.bend as F
import bend-mathlib@0.7.4.0/nat.bend as MN
import bend-mathlib@0.7.4.0/bool.bend as MB

# ---- contains_spec ----
def Laws.contains_spec(p, es):
  match es:
    case Nil{}:
      {==}
    case Con{C.Entry{owner}, t}:
      %Laws.contains_spec(p, t): {Bool.or(Nat.is_eq(p, owner), C.contains(p, t)) == Bool.or(Nat.is_eq(p, owner), _): Bool}
      {==}

# ---- add_unique ----
def add_none_put(b: Bool, +p: Nat, +es: List<&2, C.Entry>) -> {Maybe.is_none(&2, List<&2, C.Entry>, C.add.put(b, p, es)) == b: Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.add_unique(p, es):
  add_none_put(C.contains(p, es), p, es)

# ---- add_fresh ----
def Laws.add_fresh(p, es, h):
  %Equal.sym(Bool, C.contains(p, es), False{}, h): {C.add.put(_, p, es) == Some{List.append(&2, C.Entry, es, [C.Entry{p}])}: Maybe<&2, List<&2, C.Entry>>}
  {==}

# ---- remove_absent ----
def remove_absent_put(b: Bool, +p: Nat, +owner: Nat, +t: List<&2, C.Entry>, h: {Bool.or(b, C.contains(p, t)) == False{}: Bool}, ih: @_: {C.contains(p, t) == False{}: Bool} -> {C.remove(p, t) == t: List<&2, C.Entry>}) -> {C.remove.put(b, owner, C.remove(p, t)) == C.Entry{owner} <> t: List<&2, C.Entry>}:
  match b:
    case True{}:
      Empty.absurd({C.remove.put(True{}, owner, C.remove(p, t)) == C.Entry{owner} <> t: List<&2, C.Entry>}, F.true_ne_false(h))
    case False{}:
      %ih(h): {C.Entry{owner} <> C.remove(p, t) == C.Entry{owner} <> _: List<&2, C.Entry>}
      {==}

def Laws.remove_absent(p, es, h):
  match es:
    case Nil{}:
      {==}
    case Con{C.Entry{owner}, t}:
      remove_absent_put(Nat.is_eq(p, owner), p, owner, t, h, hh => Laws.remove_absent(p, t, hh))

# ---- remove_owner_absent ----
def remove_owner_put(b: Bool, +p: Nat, +owner: Nat, +rest: List<&2, C.Entry>, eb: {b == Nat.is_eq(p, owner): Bool}, hr: {C.contains(p, rest) == False{}: Bool}) -> {C.contains(p, C.remove.put(b, owner, rest)) == False{}: Bool}:
  match b:
    case True{}:
      hr
    case False{}:
      %eb: {Bool.or(_, C.contains(p, rest)) == False{}: Bool}
      hr

def Laws.remove_owner_absent(p, es):
  match es:
    case Nil{}:
      {==}
    case Con{C.Entry{+owner}, +t}:
      remove_owner_put(Nat.is_eq(p, owner), p, owner, C.remove(p, t), {==}, Laws.remove_owner_absent(p, t))

# ---- remove_spec ----
def remove_spec_put(b: Bool, +owner: Nat, +rest: List<&2, C.Entry>) -> {C.remove.put(b, owner, rest) == List.append(&2, C.Entry, Laws.survivor_chunk(b, owner), rest): List<&2, C.Entry>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.remove_spec(p, es):
  match es:
    case Nil{}:
      {==}
    case Con{C.Entry{owner}, t}:
      %Laws.remove_spec(p, t): {C.remove.put(Nat.is_eq(p, owner), owner, C.remove(p, t)) == List.append(&2, C.Entry, Laws.survivor_chunk(Nat.is_eq(p, owner), owner), _): List<&2, C.Entry>}
      remove_spec_put(Nat.is_eq(p, owner), owner, C.remove(p, t))

# ---- rejoin_kept ----
def Laws.rejoin_kept(p, es, h):
  %Equal.sym(Bool, C.contains(p, es), True{}, h): {C.rejoin.keep(C.add.put(_, p, es), es) == es: List<&2, C.Entry>}
  {==}

# ---- rejoin_new ----
def Laws.rejoin_new(p, es, h):
  %Equal.sym(Maybe<&2, List<&2, C.Entry>>, C.add(p, es), Some{List.append(&2, C.Entry, es, [C.Entry{p}])}, Laws.add_fresh(p, es, h)): {C.rejoin.keep(_, es) == List.append(&2, C.Entry, es, [C.Entry{p}]): List<&2, C.Entry>}
  {==}

# ---- rejoin_dropped ----
def Laws.rejoin_dropped(p, es):
  {==}

# ---- restore_absent ----

# Removing the plugin's own single entry leaves nothing.
def remove_self(+p: Nat) -> {C.remove(p, [C.Entry{p}]) == []: List<&2, C.Entry>}:
  %MN.is_eq_refl_sym(p): {C.remove.put(_, p, []) == []: List<&2, C.Entry>}
  {==}

# An entry appended for a plugin that owned none is the only one remove drops.
def remove_snoc(+p: Nat, es: List<&2, C.Entry>, +h: {C.contains(p, es) == False{}: Bool}) -> {C.remove(p, List.append(&2, C.Entry, es, [C.Entry{p}])) == es: List<&2, C.Entry>}:
  match es:
    case Nil{}:
      remove_self(p)
    case Con{C.Entry{+owner}, +t}:
      %Equal.sym(Bool, Nat.is_eq(p, owner), False{}, F.or_false_l(Nat.is_eq(p, owner), C.contains(p, t), h)): {C.remove.put(_, owner, C.remove(p, List.append(&2, C.Entry, t, [C.Entry{p}]))) == C.Entry{owner} <> t: List<&2, C.Entry>}
      %Equal.sym(List<&2, C.Entry>, C.remove(p, List.append(&2, C.Entry, t, [C.Entry{p}])), t, remove_snoc(p, t, F.or_false_r(Nat.is_eq(p, owner), C.contains(p, t), h))): {C.Entry{owner} <> _ == C.Entry{owner} <> t: List<&2, C.Entry>}
      {==}

# A plugin that owns no entry has no position.
def index_absent(+p: Nat, es: List<&2, C.Entry>, +h: {C.contains(p, es) == False{}: Bool}) -> {C.index(p, es) == None{}: Maybe<&2, Nat>}:
  match es:
    case Nil{}:
      {==}
    case Con{C.Entry{+owner}, +t}:
      %Equal.sym(Bool, Nat.is_eq(p, owner), False{}, F.or_false_l(Nat.is_eq(p, owner), C.contains(p, t), h)): {C.index.put(_, C.index(p, t)) == None{}: Maybe<&2, Nat>}
      %Equal.sym(Maybe<&2, Nat>, C.index(p, t), None{}, index_absent(p, t, F.or_false_r(Nat.is_eq(p, owner), C.contains(p, t), h))): {C.index.next(_) == None{}: Maybe<&2, Nat>}
      {==}

def restore_absent_w(w: Bool, +p: Nat, +es: List<&2, C.Entry>, +h: {C.contains(p, es) == False{}: Bool}) -> {C.remove(p, C.rejoin(w, p, es)) == es: List<&2, C.Entry>}:
  match w:
    case True{}:
      %Equal.sym(List<&2, C.Entry>, C.rejoin(True{}, p, es), List.append(&2, C.Entry, es, [C.Entry{p}]), Laws.rejoin_new(p, es, h)): {C.remove(p, _) == es: List<&2, C.Entry>}
      remove_snoc(p, es, h)
    case False{}:
      %Equal.sym(List<&2, C.Entry>, C.remove(p, es), es, Laws.remove_absent(p, es, h)): {C.remove(p, _) == es: List<&2, C.Entry>}
      Laws.remove_absent(p, es, h)

def Laws.restore_absent(w, p, es, h):
  %Equal.sym(Maybe<&2, Nat>, C.index(p, es), None{}, index_absent(p, es, h)): {C.restore(_, p, C.rejoin(w, p, es)) == es: List<&2, C.Entry>}
  restore_absent_w(w, p, es, h)

# ---- restore_held ----

# The plugin's entry after entries it does not own stands at their count.
def index_mid(+p: Nat, pre: List<&2, C.Entry>, +post: List<&2, C.Entry>, +h: {C.contains(p, pre) == False{}: Bool}) -> {C.index(p, List.append(&2, C.Entry, pre, C.Entry{p} <> post)) == Some{List.length(&2, C.Entry, pre)}: Maybe<&2, Nat>}:
  match pre:
    case Nil{}:
      %MN.is_eq_refl_sym(p): {C.index.put(_, C.index(p, post)) == Some{0n}: Maybe<&2, Nat>}
      {==}
    case Con{C.Entry{+owner}, +t}:
      %Equal.sym(Bool, Nat.is_eq(p, owner), False{}, F.or_false_l(Nat.is_eq(p, owner), C.contains(p, t), h)): {C.index.put(_, C.index(p, List.append(&2, C.Entry, t, C.Entry{p} <> post))) == Some{1n+List.length(&2, C.Entry, t)}: Maybe<&2, Nat>}
      %Equal.sym(Maybe<&2, Nat>, C.index(p, List.append(&2, C.Entry, t, C.Entry{p} <> post)), Some{List.length(&2, C.Entry, t)}, index_mid(p, t, post, F.or_false_r(Nat.is_eq(p, owner), C.contains(p, t), h))): {C.index.next(_) == Some{1n+List.length(&2, C.Entry, t)}: Maybe<&2, Nat>}
      {==}

# A chain that holds the plugin's entry contains it.
def contains_mid(+p: Nat, pre: List<&2, C.Entry>, +post: List<&2, C.Entry>) -> {C.contains(p, List.append(&2, C.Entry, pre, C.Entry{p} <> post)) == True{}: Bool}:
  match pre:
    case Nil{}:
      %MN.is_eq_refl_sym(p): {Bool.or(_, C.contains(p, post)) == True{}: Bool}
      {==}
    case Con{C.Entry{+owner}, +t}:
      %Equal.sym(Bool, C.contains(p, List.append(&2, C.Entry, t, C.Entry{p} <> post)), True{}, contains_mid(p, t, post)): {Bool.or(Nat.is_eq(p, owner), _) == True{}: Bool}
      MB.or_true(Nat.is_eq(p, owner))

# Removing the plugin's one entry joins what stood before and after it.
def remove_mid(+p: Nat, pre: List<&2, C.Entry>, +post: List<&2, C.Entry>, +h: {C.contains(p, pre) == False{}: Bool}, +hpost: {C.contains(p, post) == False{}: Bool}) -> {C.remove(p, List.append(&2, C.Entry, pre, C.Entry{p} <> post)) == List.append(&2, C.Entry, pre, post): List<&2, C.Entry>}:
  match pre:
    case Nil{}:
      %MN.is_eq_refl_sym(p): {C.remove.put(_, p, C.remove(p, post)) == post: List<&2, C.Entry>}
      Laws.remove_absent(p, post, hpost)
    case Con{C.Entry{+owner}, +t}:
      %Equal.sym(Bool, Nat.is_eq(p, owner), False{}, F.or_false_l(Nat.is_eq(p, owner), C.contains(p, t), h)): {C.remove.put(_, owner, C.remove(p, List.append(&2, C.Entry, t, C.Entry{p} <> post))) == C.Entry{owner} <> List.append(&2, C.Entry, t, post): List<&2, C.Entry>}
      %Equal.sym(List<&2, C.Entry>, C.remove(p, List.append(&2, C.Entry, t, C.Entry{p} <> post)), List.append(&2, C.Entry, t, post), remove_mid(p, t, post, F.or_false_r(Nat.is_eq(p, owner), C.contains(p, t), h), hpost)): {C.Entry{owner} <> _ == C.Entry{owner} <> List.append(&2, C.Entry, t, post): List<&2, C.Entry>}
      {==}

# Placing at position 0 conses the entry on.
def place_zero(+p: Nat, es: List<&2, C.Entry>) -> {C.place(p, 0n, es) == C.Entry{p} <> es: List<&2, C.Entry>}:
  match es:
    case Nil{}:
      {==}
    case Con{e, t}:
      {==}

# Placing at the count of the entries before the gap fills the gap.
def place_mid(+p: Nat, pre: List<&2, C.Entry>, +post: List<&2, C.Entry>) -> {C.place(p, List.length(&2, C.Entry, pre), List.append(&2, C.Entry, pre, post)) == List.append(&2, C.Entry, pre, C.Entry{p} <> post): List<&2, C.Entry>}:
  match pre:
    case Nil{}:
      place_zero(p, post)
    case Con{+e, +t}:
      %Equal.sym(List<&2, C.Entry>, C.place(p, List.length(&2, C.Entry, t), List.append(&2, C.Entry, t, post)), List.append(&2, C.Entry, t, C.Entry{p} <> post), place_mid(p, t, post)): {e <> _ == e <> List.append(&2, C.Entry, t, C.Entry{p} <> post): List<&2, C.Entry>}
      {==}

# Whatever the new version wraps, removing the plugin from the chain it left
# gives the chain without its entry.
def restore_held_w(w: Bool, +p: Nat, +pre: List<&2, C.Entry>, +post: List<&2, C.Entry>, +hpre: {C.contains(p, pre) == False{}: Bool}, +hpost: {C.contains(p, post) == False{}: Bool}) -> {C.remove(p, C.rejoin(w, p, List.append(&2, C.Entry, pre, C.Entry{p} <> post))) == List.append(&2, C.Entry, pre, post): List<&2, C.Entry>}:
  match w:
    case True{}:
      %Equal.sym(List<&2, C.Entry>, C.rejoin(True{}, p, List.append(&2, C.Entry, pre, C.Entry{p} <> post)), List.append(&2, C.Entry, pre, C.Entry{p} <> post), Laws.rejoin_kept(p, List.append(&2, C.Entry, pre, C.Entry{p} <> post), contains_mid(p, pre, post))): {C.remove(p, _) == List.append(&2, C.Entry, pre, post): List<&2, C.Entry>}
      remove_mid(p, pre, post, hpre, hpost)
    case False{}:
      %Equal.sym(List<&2, C.Entry>, C.remove(p, C.remove(p, List.append(&2, C.Entry, pre, C.Entry{p} <> post))), C.remove(p, List.append(&2, C.Entry, pre, C.Entry{p} <> post)), Laws.remove_absent(p, C.remove(p, List.append(&2, C.Entry, pre, C.Entry{p} <> post)), Laws.remove_owner_absent(p, List.append(&2, C.Entry, pre, C.Entry{p} <> post)))): {_ == List.append(&2, C.Entry, pre, post): List<&2, C.Entry>}
      remove_mid(p, pre, post, hpre, hpost)

def Laws.restore_held(w, p, pre, post, hpre, hpost):
  %Equal.sym(Maybe<&2, Nat>, C.index(p, List.append(&2, C.Entry, pre, C.Entry{p} <> post)), Some{List.length(&2, C.Entry, pre)}, index_mid(p, pre, post, hpre)): {C.restore(_, p, C.rejoin(w, p, List.append(&2, C.Entry, pre, C.Entry{p} <> post))) == List.append(&2, C.Entry, pre, C.Entry{p} <> post): List<&2, C.Entry>}
  %Equal.sym(List<&2, C.Entry>, C.remove(p, C.rejoin(w, p, List.append(&2, C.Entry, pre, C.Entry{p} <> post))), List.append(&2, C.Entry, pre, post), restore_held_w(w, p, pre, post, hpre, hpost)): {C.place(p, List.length(&2, C.Entry, pre), _) == List.append(&2, C.Entry, pre, C.Entry{p} <> post): List<&2, C.Entry>}
  place_mid(p, pre, post)

# ---- step_empty_default ----
def Laws.step_empty_default(n):
  {==}

# ---- chain_empty ----
def Laws.chain_empty():
  {==}

# ---- step_first ----
def Laws.step_first(p, t):
  {==}

# ---- step_agrees ----
def Laws.step_agrees(es, n):
  match es n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      {==}
    case Con{C.Entry{owner}, t} 0n:
      {==}
    case Con{C.Entry{owner}, t} 1n+p:
      Laws.step_agrees(t, p)

# ---- step_spec ----
def Laws.step_spec(es, n):
  match es n:
    case Nil{} _:
      {==}
    case Con{C.Entry{owner}, t} 0n:
      {==}
    case Con{C.Entry{owner}, t} 1n+p:
      Laws.step_spec(t, p)

# ---- chain_at_end ----
def Laws.chain_at_end(es):
  match es:
    case Nil{}:
      {==}
    case Con{C.Entry{owner}, t}:
      Laws.chain_at_end(t)

# ---- walk_spec ----

# Counting one extra position on a nonempty snapshot exposes its head and
# shifts every remaining position onto the tail snapshot.
def walk_cons(k: Nat, +owner: Nat, +t: List<&2, C.Entry>) -> {Laws.walk(1n+k, C.Entry{owner} <> t) == C.Owner{owner} <> Laws.walk(k, t): List<&2, C.Link>}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(List<&2, C.Link>, Laws.walk(1n+p, C.Entry{owner} <> t), C.Owner{owner} <> Laws.walk(p, t), walk_cons(p, owner, t)): {List.append(&2, C.Link, _, [C.step(t, p)]) == C.Owner{owner} <> Laws.walk(1n+p, t): List<&2, C.Link>}
      {==}

def Laws.walk_spec(es):
  match es:
    case Nil{}:
      {==}
    case Con{C.Entry{+owner}, +t}:
      %Laws.walk_spec(t): {Laws.walk(1n+Nat.add(List.length(&2, C.Entry, t), 1n), C.Entry{owner} <> t) == C.Owner{owner} <> _: List<&2, C.Link>}
      walk_cons(Nat.add(List.length(&2, C.Entry, t), 1n), owner, t)

# ---- walk_owners ----
def chain_owners(+es: List<&2, C.Entry>) -> {Laws.link_owners(Laws.chain(es)) == Laws.owners(es): List<&2, Nat>}:
  match es:
    case Nil{}:
      {==}
    case Con{C.Entry{owner}, t}:
      %chain_owners(t): {owner <> Laws.link_owners(Laws.chain(t)) == owner <> _: List<&2, Nat>}
      {==}

def Laws.walk_owners(es):
  %Equal.sym(List<&2, C.Link>, Laws.walk(Nat.add(List.length(&2, C.Entry, es), 1n), es), Laws.chain(es), Laws.walk_spec(es)): {Laws.link_owners(_) == Laws.owners(es): List<&2, Nat>}
  chain_owners(es)

# ---- step_in_snapshot ----

# A held link remains held when one entry is prepended to its snapshot.
def held_cons(l: C.Link, +owner: Nat, +t: List<&2, C.Entry>, h: {Laws.held(l, t) == True{}: Bool}) -> {Laws.held(l, C.Entry{owner} <> t) == True{}: Bool}:
  match l:
    case C.Default{}:
      {==}
    case C.Owner{+p}:
      %Equal.sym(Bool, K.mem(p, Laws.owners(t)), True{}, h): {Bool.or(Nat.is_eq(p, owner), _) == True{}: Bool}
      MB.or_true(Nat.is_eq(p, owner))

def Laws.step_in_snapshot(es, n):
  match es n:
    case Nil{} _:
      {==}
    case Con{C.Entry{+owner}, t} 0n:
      %MN.is_eq_refl_sym(owner): {Bool.or(_, K.mem(owner, Laws.owners(t))) == True{}: Bool}
      {==}
    case Con{C.Entry{+owner}, +t} 1n+p:
      held_cons(C.step(t, p), owner, t, Laws.step_in_snapshot(t, p))

# ---- held_default ----
def Laws.held_default(es):
  {==}

# ---- held_owner ----
def Laws.held_owner(p, es):
  {==}

# ---- resolve_open_snapshot ----
def Laws.resolve_open_snapshot(t, es, s, h):
  match t s:
    case C.Token{+a, _, +position} C.Calls{+activation, +next, +open}:
      %Equal.sym(Bool, Nat.is_eq(a, activation), True{}, h): {C.resolve.activation(_, C.Token{a, next, position}, C.Calls{activation, 1n+next, C.Open{next, es} <> open}) == C.Resolved{C.step(es, position)}: C.Outcome}
      %MN.is_eq_refl_sym(next): {C.resume.at(_, es, C.Token{a, next, position}, C.resume(next, C.Token{a, next, position}, open, C.gone(C.Token{a, next, position}, C.Calls{activation, 1n+next, C.Open{next, es} <> open}))) == C.Resolved{C.step(es, position)}: C.Outcome}
      {==}

# ---- resolve_live_owner ----
def Laws.resolve_live_owner(t, es, h):
  match t:
    case C.Token{+a, _, +position}:
      %MN.is_eq_refl_sym(a): {C.resolve.activation(_, C.Token{a, 0n, position}, C.Calls{a, 1n, [C.Open{0n, es}]}) == C.Resolved{Laws.link_spec(es, position)}: C.Outcome}
      %Laws.step_spec(es, position): {C.Resolved{C.step(es, position)} == C.Resolved{_}: C.Outcome}
      {==}

# ---- resolve_live_default ----

# A position at or beyond the snapshot length has no wrapper.
def step_after(es: List<&2, C.Entry>, +n: Nat, h: {Nat.is_ge(n, List.length(&2, C.Entry, es)) == True{}: Bool}) -> {C.step(es, n) == C.Default{}: C.Link}:
  match es n:
    case Nil{} _:
      {==}
    case Con{C.Entry{owner}, t} 0n:
      Empty.absurd({C.step(C.Entry{owner} <> t, 0n) == C.Default{}: C.Link}, F.true_ne_false(Equal.sym(Bool, False{}, True{}, h)))
    case Con{_, t} 1n+p:
      step_after(t, p, h)

def Laws.resolve_live_default(t, es, h):
  match t:
    case C.Token{+a, _, +position}:
      %MN.is_eq_refl_sym(a): {C.resolve.activation(_, C.Token{a, 0n, position}, C.Calls{a, 1n, [C.Open{0n, es}]}) == C.Resolved{C.Default{}}: C.Outcome}
      %Equal.sym(C.Link, C.step(es, position), C.Default{}, step_after(es, position, h)): {C.Resolved{_} == C.Resolved{C.Default{}}: C.Outcome}
      {==}

# ---- resolve_ended ----
def Laws.resolve_ended(t, es):
  match t:
    case C.Token{+a, _, position}:
      %MN.is_eq_refl_sym(a): {C.resolve.activation(_, C.Token{a, 0n, position}, C.Calls{a, 1n, []}) == C.Ended{}: C.Outcome}
      {==}

# ---- resolve_unissued ----

# Nothing is below zero.
def lt_zero(+c: Nat) -> {Nat.is_lt(c, 0n) == False{}: Bool}:
  match c:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Laws.resolve_unissued(t):
  match t:
    case C.Token{+a, call, position}:
      %MN.is_eq_refl_sym(a): {C.resolve.activation(_, C.Token{a, call, position}, C.Calls{a, 0n, []}) == C.Unissued{}: C.Outcome}
      %Equal.sym(Bool, Nat.is_lt(call, 0n), False{}, lt_zero(call)): {C.gone.put(_) == C.Unissued{}: C.Outcome}
      {==}

# ---- resolve_other_activation ----
def Laws.resolve_other_activation(t, s, h):
  match t s:
    case C.Token{+a, +call, +position} C.Calls{+activation, +next, +open}:
      %Equal.sym(Bool, Nat.is_eq(a, activation), False{}, F.not_true(Nat.is_eq(a, activation), h)): {C.resolve.activation(_, C.Token{a, call, position}, C.Calls{activation, next, open}) == C.Stale{}: C.Outcome}
      {==}

# ---- token_independent_end ----

# Removing another id does not change the first matching snapshot.
def resume_drop_put(b: Bool, +q: Nat, +call: Nat, +o: C.Open, +rest: List<&2, C.Open>, +t: C.Token, +r: C.Outcome, eb: {b == Nat.is_eq(call, C.call_at(o)): Bool}, +h: {Nat.is_eq(q, call) == False{}: Bool}, ih: {C.resume(q, t, C.drop_open(call, rest), r) == C.resume(q, t, rest, r): C.Outcome}) -> {C.resume(q, t, C.drop_open.put(b, o, C.drop_open(call, rest)), r) == C.resume(q, t, o <> rest, r): C.Outcome}:
  match b:
    case True{}:
      %MN.eq_of_is_eq(call, C.call_at(o), Equal.sym(Bool, True{}, Nat.is_eq(call, C.call_at(o)), eb)): {C.resume(q, t, C.drop_open(call, rest), r) == C.resume.at(Nat.is_eq(q, _), C.snapshot_of(o), t, C.resume(q, t, rest, r)): C.Outcome}
      %Equal.sym(Bool, Nat.is_eq(q, call), False{}, h): {C.resume(q, t, C.drop_open(call, rest), r) == C.resume.at(_, C.snapshot_of(o), t, C.resume(q, t, rest, r)): C.Outcome}
      ih
    case False{}:
      %ih: {C.resume.at(Nat.is_eq(q, C.call_at(o)), C.snapshot_of(o), t, C.resume(q, t, C.drop_open(call, rest), r)) == C.resume.at(Nat.is_eq(q, C.call_at(o)), C.snapshot_of(o), t, _): C.Outcome}
      {==}

def resume_drop(os: List<&2, C.Open>, +q: Nat, +call: Nat, +t: C.Token, +r: C.Outcome, +h: {Nat.is_eq(q, call) == False{}: Bool}) -> {C.resume(q, t, C.drop_open(call, os), r) == C.resume(q, t, os, r): C.Outcome}:
  match os:
    case Nil{}:
      {==}
    case Con{+o, +rest}:
      resume_drop_put(Nat.is_eq(call, C.call_at(o)), q, call, o, rest, t, r, {==}, h, resume_drop(rest, q, call, t, r, h))

def independent_end_live(b: Bool, +t: C.Token, +a: Nat, +next: Nat, +os: List<&2, C.Open>, +call: Nat, +h: {Nat.is_eq(C.call_of(t), call) == False{}: Bool}) -> {C.resolve.call(t, C.end_call.put(b, call, C.Calls{a, next, os})) == C.resolve.call(t, C.Calls{a, next, os}): C.Outcome}:
  match b:
    case True{}:
      resume_drop(os, C.call_of(t), call, t, C.gone.put(Nat.is_lt(C.call_of(t), next)), h)
    case False{}:
      {==}

def independent_end_same(b: Bool, +t: C.Token, +a: Nat, +next: Nat, +os: List<&2, C.Open>, +call: Nat, +h: {Nat.is_eq(C.call_of(t), call) == False{}: Bool}) -> {C.resolve.activation(b, t, C.Calls{a, next, C.drop_open(call, os)}) == C.resolve.activation(b, t, C.Calls{a, next, os}): C.Outcome}:
  match b:
    case True{}:
      independent_end_live(True{}, t, a, next, os, call, h)
    case False{}:
      {==}

def independent_end_activation(b: Bool, +t: C.Token, +a: Nat, +next: Nat, +os: List<&2, C.Open>, +call: Nat, +h: {Nat.is_eq(C.call_of(t), call) == False{}: Bool}) -> {C.resolve(t, C.end_call.put(b, call, C.Calls{a, next, os})) == C.resolve(t, C.Calls{a, next, os}): C.Outcome}:
  match b:
    case True{}:
      independent_end_same(Nat.is_eq(C.activation_of(t), a), t, a, next, os, call, h)
    case False{}:
      {==}

def Laws.token_independent_end(t, s, call, h):
  match s:
    case C.Calls{+a, +next, +os}:
      independent_end_activation(K.mem(call, C.open_ids(os)), t, a, next, os, call, F.not_true(Nat.is_eq(C.call_of(t), call), h))

# ---- token_independent_open ----

# Raising the bound by one changes the answer only for the id that was at the bound.
def lt_succ_ne(+c: Nat, +n: Nat, h: {Nat.is_eq(c, n) == False{}: Bool}) -> {Nat.is_lt(c, 1n+n) == Nat.is_lt(c, n): Bool}:
  match c n:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 1n) == Nat.is_lt(0n, 0n): Bool}, F.true_ne_false(h))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      lt_zero(p)
    case 1n+p 1n+q:
      lt_succ_ne(p, q, h)

def independent_open_same(b: Bool, +t: C.Token, +es: List<&2, C.Entry>, +a: Nat, +next: Nat, +os: List<&2, C.Open>, +h: {Nat.is_eq(C.call_of(t), next) == False{}: Bool}) -> {C.resolve.activation(b, t, C.Calls{a, 1n+next, C.Open{next, es} <> os}) == C.resolve.activation(b, t, C.Calls{a, next, os}): C.Outcome}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(C.call_of(t), next), False{}, h): {C.resume.at(_, es, t, C.resume(C.call_of(t), t, os, C.gone.put(Nat.is_lt(C.call_of(t), 1n+next)))) == C.resolve.call(t, C.Calls{a, next, os}): C.Outcome}
      %Equal.sym(Bool, Nat.is_lt(C.call_of(t), 1n+next), Nat.is_lt(C.call_of(t), next), lt_succ_ne(C.call_of(t), next, h)): {C.resume.at(False{}, es, t, C.resume(C.call_of(t), t, os, C.gone.put(_))) == C.resolve.call(t, C.Calls{a, next, os}): C.Outcome}
      {==}
    case False{}:
      {==}

def Laws.token_independent_open(t, es, s, h):
  match s:
    case C.Calls{+a, +next, +os}:
      independent_open_same(Nat.is_eq(C.activation_of(t), a), t, es, a, next, os, F.not_true(Nat.is_eq(C.call_of(t), next), h))

# ---- end_idempotent ----

# Every occurrence of an ended id is removed, including duplicate open ids.
def drop_absent_put(b: Bool, +call: Nat, +o: C.Open, +rest: List<&2, C.Open>, eb: {b == Nat.is_eq(call, C.call_at(o)): Bool}, ih: {K.mem(call, C.open_ids(rest)) == False{}: Bool}) -> {K.mem(call, C.open_ids(C.drop_open.put(b, o, rest))) == False{}: Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      %eb: {Bool.or(_, K.mem(call, C.open_ids(rest))) == False{}: Bool}
      ih

def drop_absent(os: List<&2, C.Open>, +call: Nat) -> {K.mem(call, C.open_ids(C.drop_open(call, os))) == False{}: Bool}:
  match os:
    case Nil{}:
      {==}
    case Con{+o, +rest}:
      drop_absent_put(Nat.is_eq(call, C.call_at(o)), call, o, C.drop_open(call, rest), {==}, drop_absent(rest, call))

def end_absent(b: Bool, +call: Nat, +a: Nat, +next: Nat, +os: List<&2, C.Open>, eb: {b == K.mem(call, C.open_ids(os)): Bool}) -> {K.mem(call, C.open_ids(C.open_of(C.end_call.put(b, call, C.Calls{a, next, os})))) == False{}: Bool}:
  match b:
    case True{}:
      drop_absent(os, call)
    case False{}:
      Equal.sym(Bool, False{}, K.mem(call, C.open_ids(os)), eb)

def Laws.end_idempotent(call, s):
  match s:
    case C.Calls{+a, +next, +os}:
      %Equal.sym(Bool, K.mem(call, C.open_ids(C.open_of(C.end_call(call, C.Calls{a, next, os})))), False{}, end_absent(K.mem(call, C.open_ids(os)), call, a, next, os, {==})): {C.end_call.put(_, call, C.end_call(call, C.Calls{a, next, os})) == C.end_call(call, C.Calls{a, next, os}): C.Calls}
      {==}

# ---- end_not_open_unchanged ----
def Laws.end_not_open_unchanged(call, s, h):
  %Equal.sym(Bool, K.mem(call, C.open_ids(C.open_of(s))), False{}, h): {C.end_call.put(_, call, s) == s: C.Calls}
  {==}

# ---- open_increments_next ----
def Laws.open_increments_next(es, s):
  match s:
    case C.Calls{a, next, os}:
      {==}

# ---- open_id_fresh ----

# The open ids are all below the next allocation counter.
def Below(xs: List<&2, Nat>, +n: Nat) -> Data:
  match xs:
    case Nil{}:
      Unit
    case Con{h, t}:
      Sigma<&2, &2, MN.lt(h, n), _ => Below(t, n)>

def Bounded(+s: C.Calls) -> Data:
  Below(C.open_ids(C.open_of(s)), C.next_of(s))

# Raising the counter preserves every existing strict bound.
def below_succ(xs: List<&2, Nat>, +n: Nat, h: Below(xs, n)) -> Below(xs, 1n+n):
  match xs h:
    case Nil{} _:
      Unit{}
    case Con{+x, +t} Tuple{hx, ht}: (MN.lt_of_lt_of_le(x, n, 1n+n, hx, MN.le_succ(n)), below_succ(t, n, ht))

# An id found in a bounded list inherits its strict bound.
def below_member_put(b: Bool, +q: Nat, +x: Nat, +n: Nat, +t: List<&2, Nat>, eb: {b == Nat.is_eq(q, x): Bool}, hm: {Bool.or(b, K.mem(q, t)) == True{}: Bool}, hx: MN.lt(x, n), ih: @_: {K.mem(q, t) == True{}: Bool} -> MN.lt(q, n)) -> MN.lt(q, n):
  match b:
    case True{}:
      %Equal.sym(Nat, q, x, MN.eq_of_is_eq(q, x, Equal.sym(Bool, True{}, Nat.is_eq(q, x), eb))): MN.lt(_, n)
      hx
    case False{}:
      ih(hm)

def below_member(xs: List<&2, Nat>, +q: Nat, +n: Nat, hm: {K.mem(q, xs) == True{}: Bool}, h: Below(xs, n)) -> MN.lt(q, n):
  match xs h:
    case Nil{} _:
      Empty.absurd(MN.lt(q, n), F.true_ne_false(Equal.sym(Bool, False{}, True{}, hm)))
    case Con{+x, +t} Tuple{hx, ht}: below_member_put(Nat.is_eq(q, x), q, x, n, t, {==}, hm, hx, hh => below_member(t, q, n, hh, ht))

# Removing open records cannot introduce an id outside the bound.
def below_drop_put(b: Bool, +o: C.Open, +rest: List<&2, C.Open>, +n: Nat, hx: MN.lt(C.call_at(o), n), ht: Below(C.open_ids(rest), n)) -> Below(C.open_ids(C.drop_open.put(b, o, rest)), n):
  match b:
    case True{}:
      ht
    case False{}:
      (hx, ht)

def below_drop(os: List<&2, C.Open>, +call: Nat, +n: Nat, h: Below(C.open_ids(os), n)) -> Below(C.open_ids(C.drop_open(call, os)), n):
  match os h:
    case Nil{} _:
      Unit{}
    case Con{+o, +rest} Tuple{hx, ht}: below_drop_put(Nat.is_eq(call, C.call_at(o)), o, C.drop_open(call, rest), n, hx, below_drop(rest, call, n, ht))

# Ending transfers an existing open id; ending any other id is a no-op.
def bounded_end_put(b: Bool, +call: Nat, +a: Nat, +next: Nat, +os: List<&2, C.Open>, ho: Below(C.open_ids(os), next)) -> Bounded(C.end_call.put(b, call, C.Calls{a, next, os})):
  match b:
    case True{}:
      below_drop(os, call, next, ho)
    case False{}:
      ho

def bounded_action(action: Laws.CallAction, s: C.Calls, h: Bounded(s)) -> Bounded(Laws.apply_action(action, s)):
  match action s h:
    case Laws.OpenSnapshot{snapshot} C.Calls{a, +next, +os} ho:
      (MN.lt_succ_self(next), below_succ(C.open_ids(os), next, ho))
    case Laws.EndId{+call} C.Calls{+a, +next, +os} ho:
      bounded_end_put(K.mem(call, C.open_ids(os)), call, a, next, os, ho)

# Induction follows replay's left-to-right finite history.
def bounded_replay(history: List<&2, Laws.CallAction>, +s: C.Calls, h: Bounded(s)) -> Bounded(Laws.replay(history, s)):
  match history:
    case Nil{}:
      h
    case Con{+action, rest}:
      bounded_replay(rest, Laws.apply_action(action, s), bounded_action(action, s, h))

# A strictly smaller id cannot equal the counter.
def below_neq(b: Bool, +n: Nat, +x: Nat, eb: {b == Nat.is_eq(n, x): Bool}, hx: MN.lt(x, n)) -> {b == False{}: Bool}:
  match b:
    case True{}:
      e = MN.eq_of_is_eq(n, x, Equal.sym(Bool, True{}, Nat.is_eq(n, x), eb))
      Empty.absurd({True{} == False{}: Bool}, MN.lt_irrefl(x, (%e: MN.lt(x, _); hx)))
    case False{}:
      {==}

def below_absent(xs: List<&2, Nat>, +n: Nat, h: Below(xs, n)) -> {K.mem(n, xs) == False{}: Bool}:
  match xs h:
    case Nil{} _:
      {==}
    case Con{+x, +t} Tuple{hx, ht}: F.or_ff(Nat.is_eq(n, x), K.mem(n, t), below_neq(Nat.is_eq(n, x), n, x, {==}, hx), below_absent(t, n, ht))

def bounded_fresh(s: C.Calls, h: Bounded(s)) -> {Bool.not(K.mem(C.next_of(s), C.open_ids(C.open_of(s)))) == True{}: Bool}:
  match s h:
    case C.Calls{a, +next, +os} ho:
      %Equal.sym(Bool, K.mem(next, C.open_ids(os)), False{}, below_absent(C.open_ids(os), next, ho)): {Bool.not(_) == True{}: Bool}
      {==}

# Expose state fields without inspecting the allocator's returned id.
def calls_fields(+s: C.Calls) -> {C.Calls{C.s_activation(s), C.next_of(s), C.open_of(s)} == s: C.Calls}:
  match s:
    case C.Calls{a, next, os}:
      {==}

# The allocator returns the reachable state's next counter, not an old id.
def Laws.open_id_fresh(a, history, es):
  %calls_fields(Laws.replay(history, C.begin(a))): {Bool.not(K.mem(Laws.opened_id(C.open_call(es, _)), C.open_ids(C.open_of(Laws.replay(history, C.begin(a)))))) == True{}: Bool}
  bounded_fresh(Laws.replay(history, C.begin(a)), bounded_replay(history, C.begin(a), Unit{}))

# ---- finish_same_activation ----
def Laws.finish_same_activation(t, s, h):
  %Equal.sym(Bool, Nat.is_eq(C.activation_of(t), C.s_activation(s)), True{}, h): {C.finish.put(_, t, s) == C.end_call(C.call_of(t), s): C.Calls}
  {==}

# ---- finish_other_activation ----
def Laws.finish_other_activation(t, s, h):
  %Equal.sym(Bool, Nat.is_eq(C.activation_of(t), C.s_activation(s)), False{}, F.not_true(Nat.is_eq(C.activation_of(t), C.s_activation(s)), h)): {C.finish.put(_, t, s) == s: C.Calls}
  {==}

# ---- issue_resolves_next ----
def Laws.issue_resolves_next(p, es, s):
  match s:
    case C.Calls{+a, +next, +os}:
      %MN.is_eq_refl_sym(a): {C.resolve.activation(_, C.Token{a, next, 1n+p}, C.Calls{a, 1n+next, C.Open{next, es} <> os}) == C.Resolved{C.step(es, 1n+p)}: C.Outcome}
      %MN.is_eq_refl_sym(next): {C.resume.at(_, es, C.Token{a, next, 1n+p}, C.resume(next, C.Token{a, next, 1n+p}, os, C.gone(C.Token{a, next, 1n+p}, C.Calls{a, 1n+next, C.Open{next, es} <> os}))) == C.Resolved{C.step(es, 1n+p)}: C.Outcome}
      {==}
