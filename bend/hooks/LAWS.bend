import Base
import ./core.bend as C
import ../keys/core.bend as K

# ---- reference definitions: what the laws are stated with ----

# Project entries to owner ids for the independent membership specification.
def owners(entries: List<&2, C.Entry>) -> List<&2, Nat>:
  match entries:
    case Nil{}:
      []
    case Con{C.Entry{owner}, t}:
      owner <> owners(t)

def chain.links(+es: List<&2, C.Entry>) -> List<&2, C.Link>:
  match es:
    case Nil{}:
      []
    case Con{e, t}:
      C.to_link(e) <> chain.links(t)

# The snapshot as a chain: its owners outermost first, then Default.
def chain(+es: List<&2, C.Entry>) -> List<&2, C.Link>:
  List.append(&2, C.Link, chain.links(es), [C.Default{}])

def link_owner(l: C.Link) -> List<&2, Nat>:
  match l:
    case C.Owner{plugin}:
      [plugin]
    case C.Default{}:
      []

def prepend(ps: List<&2, Nat>, +suffix: List<&2, Nat>) -> List<&2, Nat>:
  match ps:
    case Nil{}:
      suffix
    case Con{h, t}:
      h <> prepend(t, suffix)

# The owners a chain runs, in order, Default contributing none.
def link_owners(ls: List<&2, C.Link>) -> List<&2, Nat>:
  match ls:
    case Nil{}:
      []
    case Con{l, t}:
      prepend(link_owner(l), link_owners(t))

# Which link an enumerated chain names at a position, Default past its end.
def chain_at(ls: List<&2, C.Link>, n: Nat) -> C.Link:
  Maybe.default(&2, C.Link, List.get(&2, C.Link, ls, n), C.Default{})

# The links a call runs walking its snapshot from position 0, one per
# position, for k positions.
def walk(+k: Nat, +es: List<&2, C.Entry>) -> List<&2, C.Link>:
  match k:
    case 0n:
      []
    case 1n+p:
      List.append(&2, C.Link, walk(p, es), [C.step(es, p)])

# Whether a snapshot holds the wrapper a link names. The host default is not a
# wrapper, so every snapshot holds it.
def held(l: C.Link, +es: List<&2, C.Entry>) -> Bool:
  match l:
    case C.Owner{plugin}:
      K.mem(plugin, owners(es))
    case C.Default{}:
      True{}

def opened_id(r: C.Opened) -> Nat:
  match r:
    case C.Opened{call, _}:
      call

def opened_state(r: C.Opened) -> C.Calls:
  match r:
    case C.Opened{_, state}:
      state

# Guarantees: contains is true exactly when the plugin owns some entry, whichever position
#   it is in (no premises).
# Why it matters: Only the first entry would be checked, so a plugin registered later would
#   count as absent.
law contains_spec:
  for +p: Nat
  for +es: List<&2, C.Entry>
  {C.contains(p, es) == K.mem(p, owners(es)) : Bool}


# Guarantees: add returns nothing exactly when the plugin already owns an entry (no
#   premises).
# Why it matters: A plugin could register the same hook twice, or a first registration be
#   refused; a duplicate must be refused, not replaced, so lifecycle mistakes stay visible.
law add_unique:
  for +p: Nat
  for +es: List<&2, C.Entry>
  {Maybe.is_none(&2, List<&2, C.Entry>, C.add(p, es)) == C.contains(p, es) : Bool}


# Guarantees: If the plugin owns no entry, add succeeds and appends exactly one entry for it
#   at the end (premise: the plugin is absent).
# Why it matters: A new registration could be lost or placed first; wrappers apply in
#   registration order and there is no prepend.
law add_fresh:
  for +p: Nat
  for +es: List<&2, C.Entry>
  for h: {C.contains(p, es) == False{} : Bool}
  {C.add(p, es) == Some{List.append(&2, C.Entry, es, [C.Entry{p}])} : Maybe<&2, List<&2, C.Entry>>}

# Independent specification: each entry contributes zero or one entries;
# concatenating these chunks preserves survivor order and multiplicity.
def survivor_chunk(hit: Bool, owner: Nat) -> List<&2, C.Entry>:
  match hit:
    case True{}:
      []
    case False{}:
      [C.Entry{owner}]

def survivor_chunks(+p: Nat, es: List<&2, C.Entry>) -> List<&2, List<&2, C.Entry>>:
  match es:
    case Nil{}:
      []
    case Con{C.Entry{+owner}, t}:
      survivor_chunk(Nat.is_eq(p, owner), owner) <> survivor_chunks(p, t)

# Guarantees: If the plugin owns no entry, remove returns the list unchanged (premise: the
#   plugin is absent).
# Why it matters: Removing a plugin that registered nothing could disturb the order or the
#   entries of other plugins.
law remove_absent:
  for +p: Nat
  for +es: List<&2, C.Entry>
  for h: {C.contains(p, es) == False{} : Bool}
  {C.remove(p, es) == es : List<&2, C.Entry>}

# Guarantees: After remove, the plugin owns no entry, whatever the list was (no premises).
# Why it matters: An unloaded plugin's wrapper could stay in the chain, and a call would
#   be routed to a worker that is gone.
law remove_owner_absent:
  for +p: Nat
  for es: List<&2, C.Entry>
  {C.contains(p, C.remove(p, es)) == False{} : Bool}

# Guarantees: remove returns exactly the entries of other owners, in their original order
#   and multiplicity (no premises).
# Why it matters: Unloading one plugin could reorder or drop the wrappers of the others.
law remove_spec:
  for +p: Nat
  for +es: List<&2, C.Entry>
  {C.remove(p, es) == List.concat(&2, C.Entry, survivor_chunks(p, es)) : List<&2, C.Entry>}

# ---- reload ----

# Guarantees: When the plugin already has an entry on a hook its new version
#   wraps, rejoin leaves that hook's chain exactly as it was (premise: the
#   plugin owns an entry).
# Why it matters: A reloaded plugin would move to the end of every chain it
#   wraps, so reloading one plugin to fix a typo would change the order every
#   later call runs the wrappers in.
law rejoin_kept:
  for +p: Nat
  for +es: List<&2, C.Entry>
  for h: {C.contains(p, es) == True{} : Bool}
  {C.rejoin(True{}, p, es) == es : List<&2, C.Entry>}

# Guarantees: On a hook the new version wraps and the old one did not, rejoin
#   appends the plugin's entry at the end and leaves the others as they were
#   (premise: the plugin owns no entry).
# Why it matters: A wrapper the new version adds could be lost, or jump ahead
#   of plugins that were registered before it.
law rejoin_new:
  for +p: Nat
  for +es: List<&2, C.Entry>
  for h: {C.contains(p, es) == False{} : Bool}
  {C.rejoin(True{}, p, es) == List.append(&2, C.Entry, es, [C.Entry{p}]) : List<&2, C.Entry>}

# Guarantees: On a hook the new version does not wrap, rejoin is remove: the
#   plugin's entry leaves and the others keep their order (no premises).
# Why it matters: A new version that no longer wraps a hook would still be
#   called on it.
law rejoin_dropped:
  for +p: Nat
  for +es: List<&2, C.Entry>
  {C.rejoin(False{}, p, es) == C.remove(p, es) : List<&2, C.Entry>}

# Guarantees: On a hook where the plugin had no entry before the reload,
#   restoring with the position read before the reload gives back the chain as
#   it was, whatever the new version wraps (premise: the plugin owns no entry).
# Why it matters: A refused reload whose new version wrapped an extra hook would
#   leave the old version wrapping a hook it never declared.
law restore_absent:
  for +w: Bool
  for +p: Nat
  for +es: List<&2, C.Entry>
  for +h: {C.contains(p, es) == False{} : Bool}
  {C.restore(C.index(p, es), p, C.rejoin(w, p, es)) == es : List<&2, C.Entry>}

# Guarantees: On a hook where the plugin had one entry before the reload,
#   restoring with the position read before the reload puts it back at that
#   position, whatever the new version wraps, so the chain is as it was
#   (premise: the plugin owns no other entry).
# Why it matters: A refused reload would move the old version to the end of a
#   chain, or out of a chain its new version did not wrap, so a failed reload
#   would still change what every later call runs.
law restore_held:
  for +w: Bool
  for +p: Nat
  for +pre: List<&2, C.Entry>
  for +post: List<&2, C.Entry>
  for +hpre: {C.contains(p, pre) == False{} : Bool}
  for hpost: {C.contains(p, post) == False{} : Bool}
  {C.restore(C.index(p, List.append(&2, C.Entry, pre, C.Entry{p} <> post)), p, C.rejoin(w, p, List.append(&2, C.Entry, pre, C.Entry{p} <> post))) == List.append(&2, C.Entry, pre, C.Entry{p} <> post) : List<&2, C.Entry>}

# ---- independent specification of the position walk ----
#
# The link at a position stated again, on its own, and core's version held to
# it: a law written through core's own helper says nothing about a bug inside
# it.

def link_spec(es: List<&2, C.Entry>, n: Nat) -> C.Link:
  match es n:
    case Nil{} _:
      C.Default{}
    case Con{C.Entry{owner}, _} 0n:
      C.Owner{owner}
    case Con{_, t} 1n+p:
      link_spec(t, p)

# ---- chain ----

# Guarantees: With an empty snapshot, the step at any position is the host default (no
#   premises).
# Why it matters: A hook nobody wraps could fail instead of behaving as if it had no chain.
law step_empty_default:
  for +n: Nat
  {C.step([], n) == C.Default{} : C.Link}

# Guarantees: The chain of an empty snapshot is the default and nothing else (no premises).
# Why it matters: The enumerated chain of an unwrapped hook could contain a wrapper that
#   does not exist.
law chain_empty:
  {chain([]) == [C.Default{}] : List<&2, C.Link>}

# Guarantees: Position 0 of a snapshot is the owner of the first entry (no premises).
# Why it matters: The plugin that registered first could fail to be the outermost wrapper
#   and decide how the rest of the chain is called.
law step_first:
  for +p: Nat
  for +t: List<&2, C.Entry>
  {C.step(C.Entry{p} <> t, 0n) == C.Owner{p} : C.Link}

# Guarantees: The position-driven step equals the link at that position of the enumerated
#   chain, for any snapshot and position (no premises).
# Why it matters: There could be two orders for one chain, which drift apart.
law step_agrees:
  for +es: List<&2, C.Entry>
  for +n: Nat
  {C.step(es, n) == chain_at(chain(es), n) : C.Link}

# Guarantees: The step at a position is the owner of the entry the snapshot has there, and
#   the default past its end (no premises). It is held to an independent definition,
#   link_spec.
# Why it matters: The walk could invent a wrapper, or run off the end of the chain.
law step_spec:
  for +es: List<&2, C.Entry>
  for +n: Nat
  {C.step(es, n) == link_spec(es, n) : C.Link}

# Guarantees: The link at the position just past the last entry is the default (no
#   premises).
# Why it matters: A call's last step could miss the base handler and run off the end of the
#   chain.
law chain_at_end:
  for +es: List<&2, C.Entry>
  {chain_at(chain(es), List.length(&2, C.Entry, es)) == C.Default{} : C.Link}

# Guarantees: Walking a snapshot's first length+1 positions gives its chain exactly (no
#   premises).
# Why it matters: A call could run a different order from the registration order, or a link
#   the walk adds itself.
law walk_spec:
  for +es: List<&2, C.Entry>
  {walk(Nat.add(List.length(&2, C.Entry, es), 1n), es) == chain(es) : List<&2, C.Link>}

# Guarantees: That walk visits every registered owner once, in registration order, and no
#   other owner (no premises).
# Why it matters: A wrapper could be skipped, repeated or invented.
law walk_owners:
  for +es: List<&2, C.Entry>
  {link_owners(walk(Nat.add(List.length(&2, C.Entry, es), 1n), es)) == owners(es) : List<&2, Nat>}

# Guarantees: The step never answers a wrapper that the snapshot does not hold (no
#   premises).
# Why it matters: A call could run a plugin that it did not snapshot, so a later
#   registration or an unload would leak into a call already running.
law step_in_snapshot:
  for +es: List<&2, C.Entry>
  for +n: Nat
  {held(C.step(es, n), es) == True{} : Bool}

# Guarantees: Every snapshot holds the host default (no premises).
# Why it matters: Falling through to the base handler could be refused.
law held_default:
  for +es: List<&2, C.Entry>
  {held(C.Default{}, es) == True{} : Bool}

# Guarantees: A snapshot holds an owner's wrapper exactly when it lists that plugin (no
#   premises). It fixes the membership test that step_in_snapshot and held_default are read
#   through.
# Why it matters: Those two laws could be satisfied by a test that answers whatever it
#   likes.
law held_owner:
  for +p: Nat
  for +es: List<&2, C.Entry>
  {held(C.Owner{p}, es) == K.mem(p, owners(es)) : Bool}

# ---- tokens ----

# Give a continuation the returned id, retaining its activation and position.
def issued(+t: C.Token, r: C.Opened) -> C.Token:
  C.Token{C.activation_of(t), opened_id(r), C.position_of(t)}

# Guarantees: A token of an open call resolves to the link its own call's snapshot names at
#   the token's position, whatever the activation state was before (premise: the token is of
#   the current activation).
# Why it matters: A later registration or unload could change what an open call runs.
law resolve_open_snapshot:
  for +t: C.Token
  for +es: List<&2, C.Entry>
  for +s: C.Calls
  for h: {Nat.is_eq(C.activation_of(t), C.s_activation(s)) == True{} : Bool}
  {C.resolve(issued(t, C.open_call(es, s)), opened_state(C.open_call(es, s))) == C.Resolved{C.step(es, C.position_of(t))} : C.Outcome}

# Guarantees: A live token whose position is inside its call's snapshot resolves to the
#   owner the snapshot has there (premise: the position is less than the snapshot's length).
# Why it matters: The machine could refuse a continuation it should pass.
law resolve_live_owner:
  for +t: C.Token
  for +es: List<&2, C.Entry>
  for h: {Nat.is_lt(C.position_of(t), List.length(&2, C.Entry, es)) == True{} : Bool}
  {C.resolve(issued(t, C.open_call(es, C.begin(C.activation_of(t)))), opened_state(C.open_call(es, C.begin(C.activation_of(t))))) == C.Resolved{link_spec(es, C.position_of(t))} : C.Outcome}

# Guarantees: A live token at or past the end of its call's snapshot resolves to the default
#   (premise: the position is at least the snapshot's length).
# Why it matters: Reaching the host's base handler could be treated as a failure instead of
#   as a successful link.
law resolve_live_default:
  for +t: C.Token
  for +es: List<&2, C.Entry>
  for h: {Nat.is_ge(C.position_of(t), List.length(&2, C.Entry, es)) == True{} : Bool}
  {C.resolve(issued(t, C.open_call(es, C.begin(C.activation_of(t)))), opened_state(C.open_call(es, C.begin(C.activation_of(t))))) == C.Resolved{C.Default{}} : C.Outcome}

# Guarantees: A token whose call has ended resolves to Ended, for any snapshot (no
#   premises).
# Why it matters: A finished or cancelled call could resume, or "your call is over" could be
#   confused with "you never had one".
law resolve_ended:
  for +t: C.Token
  for +es: List<&2, C.Entry>
  {C.resolve(issued(t, C.open_call(es, C.begin(C.activation_of(t)))), C.end_call(opened_id(C.open_call(es, C.begin(C.activation_of(t)))), opened_state(C.open_call(es, C.begin(C.activation_of(t)))))) == C.Ended{} : C.Outcome}

# Guarantees: A token resolves to Unissued in an activation that never opened its call (no
#   premises).
# Why it matters: A continuation could be presented before its call was issued.
law resolve_unissued:
  for +t: C.Token
  {C.resolve(t, C.begin(C.activation_of(t))) == C.Unissued{} : C.Outcome}

# Guarantees: A token of another activation resolves to Stale, whatever its call number is
#   there (premise: the token's activation differs from the state's).
# Why it matters: A call begun in one activation could resume in a later one, so a reloaded
#   plugin's old continuation would reach the new code.
law resolve_other_activation:
  for +t: C.Token
  for +s: C.Calls
  for h: {Nat.is_ne(C.activation_of(t), C.s_activation(s)) == True{} : Bool}
  {C.resolve(t, s) == C.Stale{} : C.Outcome}

# Guarantees: Ending one call leaves the resolution of another call's token unchanged
#   (premise: the call numbers differ).
# Why it matters: One plugin stopping could decide the outcome of a call it is not part of.
law token_independent_end:
  for +t: C.Token
  for +s: C.Calls
  for +call: Nat
  for h: {Nat.is_ne(C.call_of(t), call) == True{} : Bool}
  {C.resolve(t, C.end_call(call, s)) == C.resolve(t, s) : C.Outcome}

# Guarantees: Opening a call leaves the resolution of another call's token unchanged,
#   whatever snapshot the new call took (premise: the new call's id differs from the token's
#   call).
# Why it matters: Issuing a continuation could revive or kill a different call's
#   continuation.
law token_independent_open:
  for +t: C.Token
  for +es: List<&2, C.Entry>
  for +s: C.Calls
  for h: {Nat.is_ne(C.call_of(t), opened_id(C.open_call(es, s))) == True{} : Bool}
  {C.resolve(t, opened_state(C.open_call(es, s))) == C.resolve(t, s) : C.Outcome}

# Guarantees: Ending a call twice gives the same state as ending it once (no premises).
# Why it matters: A stop that arrives twice (an unload and a cancel, say) could disturb the
#   calls left open.
law end_idempotent:
  for +call: Nat
  for +s: C.Calls
  {C.end_call(call, C.end_call(call, s)) == C.end_call(call, s) : C.Calls}

# Guarantees: Ending a call that is not open returns the state unchanged (premise: the call
#   is not among the open calls).
# Why it matters: Cancelling a call that never started could move the counter, so a token
#   yet to come would look like one whose call is over.
law end_not_open_unchanged:
  for +call: Nat
  for +s: C.Calls
  for h: {K.mem(call, C.open_ids(C.open_of(s))) == False{} : Bool}
  {C.end_call(call, s) == s : C.Calls}

# ---- reachable histories ----

# Reachable states are exactly finite histories of opening snapshots and ending ids.
# Arbitrary Calls can place next in open, so freshness needs this domain.
type CallAction is Data:
  OpenSnapshot{snapshot: List<&2, C.Entry>}
  EndId{call: Nat}

def apply_action(action: CallAction, s: C.Calls) -> C.Calls:
  match action:
    case OpenSnapshot{snapshot}:
      opened_state(C.open_call(snapshot, s))
    case EndId{call}:
      C.end_call(call, s)

def replay(history: List<&2, CallAction>, s: C.Calls) -> C.Calls:
  match history:
    case Nil{}:
      s
    case Con{action, rest}:
      replay(rest, apply_action(action, s))

# Guarantees: The id allocated by opening a call is absent from the open calls, on every
#   state reached by a finite history of opens and ends (premise: the state comes from a
#   history, not an arbitrary Calls value).
# Why it matters: A call id could be reused, and a token could resolve to another call.
law open_id_fresh:
  for +a: Nat
  for +history: List<&2, CallAction>
  for +es: List<&2, C.Entry>
  {Bool.not(K.mem(opened_id(C.open_call(es, replay(history, C.begin(a)))), C.open_ids(C.open_of(replay(history, C.begin(a)))))) == True{} : Bool}

# Guarantees: Opening a call raises the counter of the next id by exactly one (no premises).
# Why it matters: The next allocation might not advance while older calls are open or ended,
#   which would reuse an id.
law open_increments_next:
  for +es: List<&2, C.Entry>
  for +s: C.Calls
  {C.next_of(opened_state(C.open_call(es, s))) == 1n+C.next_of(s) : Nat}

# ---- finish and issue ----

# Guarantees: A token of the current activation ends its own call, exactly as ending by id
#   (premise: the token's activation equals the state's).
# Why it matters: A cancel could fail to end the call it belongs to.
law finish_same_activation:
  for +t: C.Token
  for +s: C.Calls
  for h: {Nat.is_eq(C.activation_of(t), C.s_activation(s)) == True{} : Bool}
  {C.finish(t, s) == C.end_call(C.call_of(t), s) : C.Calls}

# Guarantees: A token from another activation ends nothing and leaves the state unchanged
#   (premise: the activations differ).
# Why it matters: A cancel left over from before a reload could end the new activation's
#   call that has the same id.
law finish_other_activation:
  for +t: C.Token
  for +s: C.Calls
  for h: {Nat.is_ne(C.activation_of(t), C.s_activation(s)) == True{} : Bool}
  {C.finish(t, s) == s : C.Calls}

# Guarantees: The inner handed to the wrapper at position p resolves to exactly link p+1 of
#   its own snapshot (no premises).
# Why it matters: Inner could skip the next link, or return to itself.
law issue_resolves_next:
  for +p: Nat
  for +es: List<&2, C.Entry>
  for +s: C.Calls
  {C.resolve(C.token_of(C.issue(p, es, s)), C.state_of(C.issue(p, es, s))) == C.Resolved{C.step(es, 1n+p)} : C.Outcome}
