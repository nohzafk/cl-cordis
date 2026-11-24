# cl-cordis

A Common Lisp (SBCL) live-image implementation of [Cordis](https://github.com/cordiverse/cordis) — bringing **spatiotemporal composability** to a live Lisp image with **formally proved Bend 2 cores** and **reversible side-effect ledgers**.

[Cordis](https://github.com/cordiverse/cordis) is a TypeScript meta-framework for dynamic software composition that enables runtime mounting, unmounting, and rewiring of components without restarting a system. Formalized in [*A Programming Paradigm for Spatiotemporal Composability*](https://arxiv.org/abs/2608.25512) (Yifan Shi, Wei Zhang, and Tianyi Cui; Peking University & DeepSeek-AI, 2026) and used in Koishi and DeepSeek Harness, it models dynamic composition cleanly across dependency graphs and side-effect lifetimes. `cl-cordis` brings that model to SBCL, adding layered live-image definitions, `cl-scope`-backed failure parking, and kernel-checked Bend 2 decision cores.

- **Clean undo for a live Lisp image**: every mutation a component makes — functions, variables, macros, background threads, hook wrappers, custom resources — goes through `cordis:effect` and is undone in reverse order when the component stops.
- **Dependency-driven lifecycle**: components declare what they `:inject` and `:provide`; they activate automatically once every dependency is live and cascade-restart whenever a key they read changes.
- **Formally proved scheduling & undo**: load checking, activation planning, cascade restart selection, reverse ledger undo, missing-key checks, and hook wrapper chains are decided by 7 [Bend 2](https://github.com/HigherOrderCO/Bend) cores (Bend `2.0.40`, kernel-checked `PROOF.bend` included in `bend/`), pre-emitted to Common Lisp under `cores/` in private `cl-cordis.*` packages — **no Bend or Bun toolchain is required to load `cl-cordis`**.
- **Park & repair on failure**: built on [`cl-scope`](https://github.com/nohzafk/cl-scope), a failing component `:apply` parks on its real SBCL call stack with nothing undone until you inspect it and answer with a restart (`cordis:retry`, `cordis:abandon`, or a restart of its own code).
- **Interception & hooks**: Cordis-style contextual metadata merging (`merge-rule`, `with-intercept`, `metadata`) and snapshot-isolated hook wrapper chains (`define-hook`, `chain`) with stale-`inner` detection.

Package: `cl-cordis` (nickname: `cordis`). SBCL only. Depends only on [`cl-scope`](https://github.com/nohzafk/cl-scope) and SBCL's built-in `sb-md5`.

---

## Quick Start

```lisp
(cordis:start)

(defparameter *db*
  (cordis:make-component
   :name "db" :provide '(:db)
   :apply (lambda (config)
            (let ((pool (open-pool (getf config :url))))
              (cordis:revertible nil (close-pool pool))     ; undone when db stops
              (cordis:provide :db pool)))))                 ; must be set before apply returns

(defparameter *app*
  (cordis:make-component
   :name "app" :inject '(:db)
   :apply (lambda (config)
            (declare (ignore config))
            (let ((pool (cordis:inject :db)))
              ;; Layered live-image definition: removed automatically when app stops.
              (cordis:eval-form `(defun banner () (format nil "app on ~a" ',pool)))))))

(cordis:use *app*)                                ; loaded, blocked: nothing provides :db
(let ((db (cordis:use *db* :config '(:url "pg://1"))))   ; db activates, then app
  (print (banner))
  (cordis:retire db))                             ; app stops first (BANNER is gone), then pool closes
(cordis:stop)
```

---

## Proved Cores (`bend/` & `cores/`)

All discrete scheduling, dependency, hook-chain, and undo-order decisions are delegated to 7 self-contained Bend 2 cores (`bend/`, Bend `2.0.40`), compiled into zero-dependency Common Lisp under `cores/` via [`bend-emit-cl`](https://github.com/nohzafk/bend-emit-cl) into private `cl-cordis.*` packages (`cl-cordis.runtime`, `cl-cordis.base`, `cl-cordis.core.*`) so `cl-cordis` never collides with a host image's own `bend.*` packages:

| Core | Package | Laws (`LAWS.bend`) | What it decides |
|---|---|---:|---|
| `keys` | `cl-cordis.core.keys` | — | Key-set membership and `missing` (provided keys left unset, undeclared reads/hooks) |
| `comp` | `cl-cordis.core.comp` | *(imported by others)* | Component record representation shared across cores |
| `check` | `cl-cordis.core.check` | 1 | Whether a load is refused (duplicate fiber id or duplicate key provider) |
| `cascade` | `cl-cordis.core.cascade` | 7 | Which active fibers must stop when keys change |
| `plan` | `cl-cordis.core.plan` | 1 | Which loaded fiber activates next, one at a time, and which remain blocked |
| `undo` | `cl-cordis.core.undo` | 1 | Inverse execution order: newest first, a child's whole ledger before the child |
| `hooks` | `cl-cordis.core.hooks` | 17 | Hook wrapper order, in-place reload placement, snapshot stepping, and stale-`inner` tokens |

All 6 `PROOF.bend` files pass Bend `2.0.40`'s kernel (`ALL PROOFS CHECK`). Normal users load the pre-emitted `cores/*.lisp` directly; to re-verify all proofs and rebuild `cores/*.lisp` from `bend/`:

```sh
cores/build.sh            # check every PROOF.bend and re-emit cores/*.lisp
cores/build.sh --check    # verify committed cores/*.lisp match a fresh build byte-for-byte
```

---

## Core Concepts

### 1. Operations & Reconciliation
`use`, `retire`, `rebuild`, `revive`, `apply-config`, and the root's `provide` are serialized operations. Each runs alone and is followed by one reconcile pass:

1. **Stop**: `cascade` selects active fibers reachable from changed or removed keys (plus descendants). They stop newest first: each fiber's ledger runs in the order `undo` produces, then its provided keys are cleared.
2. **Start**: `plan` picks the next loaded fiber whose dependencies are satisfied, runs its `:apply`, verifies every `:provide` key was set (`keys:missing`), and repeats until no more fibers can activate.

- **Re-providing a key**: setting a provided key again while active restarts all readers before `provide` returns.
- **Parked failures**: if a component's `:apply` signals an error, the operation parks on its real call stack with nothing undone. `(cordis:parked-report)` reports the condition, restarts, and trimmed backtrace; `(cordis:respond id restart &rest args)` answers with `cordis:abandon` (rollback and mark failed), `cordis:retry` (rollback and re-run `:apply`, picking up hot-redefined functions), or any restart established by the component. While an operation is parked, all other operations are immediately refused with `component-parked` to prevent deadlocks.
- **Layered definitions & threads**: `eval-form` (`defun`/`defmacro`/`defvar`/`defparameter`) and `bind-function` push layers onto names so two components can override the same function and unload in either order; `thread` runs a background `cl-scope` scope cancelled and joined automatically when its fiber stops.

### 2. Interception Metadata
Following Section 3.2.3 of [*A Programming Paradigm for Spatiotemporal Composability*](https://arxiv.org/abs/2608.25512), any key may carry contextual **metadata** alongside its value:

- A component declares `:metadata (key value ...)`.
- Contexts layer metadata outermost first: every ancestor fiber's `:intercept`, followed by any dynamic `(cordis:with-intercept (key value ...) ...)` forms on the current thread.
- `(cordis:metadata key)` merges the layers using the rule registered via `(cordis:merge-rule key merge &optional empty)` (an effect owned by the registering fiber; without a rule, the innermost value wins). Changing metadata reloads nothing.

### 3. Hook Chains
The root declares hooks with `(cordis:define-hook name default)`. Components wrap hooks via `:wrap ((hook . wrapper) ...)`, where each wrapper takes `(inner input)`:

```lisp
(cordis:define-hook "dir.list" (lambda (input) (list :none input)))
(cordis:use (cordis:make-component
             :name "dirs"
             :wrap (list (cons "dir.list"
                               (lambda (inner input)
                                 (or (my-listing input) (funcall inner input)))))))
(cordis:chain "dir.list" "/tmp")
```

- Wrappers execute outermost first (load order) over the default; inactive fibers are skipped without losing their slot, and `apply-config` replacements keep their slot in the chain.
- A call runs against the chain snapshot taken when it started. Calling `inner` after its call ends signals `stale-inner` (`:ended`); calling an `inner` retained across fiber activations signals `stale-inner` (`:stale`).

---

## Installation & Loading

`cl-cordis` depends only on [`cl-scope`](https://github.com/nohzafk/cl-scope) and SBCL's built-in `sb-md5`.

With ASDF (once `cl-scope` is on `CL_SOURCE_REGISTRY` or loaded via `asdf:load-asd`):

```lisp
(asdf:load-asd "/path/to/cl-cordis/cl-cordis.asd")
(asdf:load-system "cl-cordis")
```

With [qlot](https://github.com/fukamachi/qlot):

```text
git cl-scope https://github.com/nohzafk/cl-scope.git
git cl-cordis https://github.com/nohzafk/cl-cordis.git
```

---

## API Summary

| Symbol | Description |
|---|---|
| `(cordis:start &key root)` / `(cordis:stop)` / `(cordis:running-p)` | Start the runtime (with root keys `((key value) ...)`); unwind all fibers newest first and stop; check status. |
| `(cordis:make-component :name :inject :provide :apply :wrap :metadata)` | Construct a component descriptor. |
| `(cordis:use comp &key config id intercept)` / `(cordis:retire fiber)` | Load a fiber under the current fiber (or root); remove it permanently, stopping readers first. |
| `(cordis:rebuild fiber)` / `(cordis:revive fiber)` | Stop and re-activate a fiber (with readers); allow a failed fiber to activate again. |
| `(cordis:effect callback)` / `(cordis:revertible action undo...)` | Register a reversible effect whose inverse runs when the owning fiber stops (or when the returned undo thunk is called). |
| `(cordis:provide key value)` / `(cordis:inject key)` / `(cordis:value key)` | Provide a declared key; read an injected key; peek at an active key's value `(values val present-p)`. |
| `(cordis:providing prefix)` / `(cordis:providers prefix)` | List keys matching `prefix` in provider activation order (root first). |
| `(cordis:merge-rule key merge &optional empty)` / `(cordis:metadata key)` / `(cordis:with-intercept ...)` | Register a metadata merge rule, read merged metadata, or derive a dynamic intercept context. |
| `(cordis:define-hook name default)` / `(cordis:chain hook input)` / `(cordis:chain-of hook)` | Declare a hook, invoke its wrapper chain, and inspect registered wrappers. |
| `(cordis:thread fn &key name)` | Run a component-owned background `cl-scope` thread, cancelled and joined on unload. |
| `(cordis:eval-form form)` / `(cordis:bind-function name fn)` / `(cordis:undo-definition name)` | Layered live-image definitions (`defun`/`defmacro`/`defvar`/`defparameter`) tracked as reversible effects. |
| `(cordis:file-component path)` / `(cordis:apply-config specs)` / `(cordis:amend-entry id config)` | Load file-based components and declaratively reconcile a configuration list, rebuilding only changed entries. |
| `(cordis:settle)` / `(cordis:await fiber)` / `(cordis:blocked)` / `(cordis:status id)` / `(cordis:active)` / `(cordis:faults)` | Synchronization and runtime inspection. |
| `(cordis:watch listener)` / `(cordis:changes key listener)` | Observe key writes and clears. |
| `(cordis:parked-report)` / `(cordis:respond fiber restart &rest args)` | Inspect and answer parked component operations or component threads (`cordis:retry`, `cordis:abandon`, or user restarts). |
| `(cordis:image :packages ...)` / `(cordis:image-diff a b)` / `(cordis:in-fiber (fiber) body...)` | Snapshot/diff live image definitions to detect out-of-effect mutations; act inside a fiber's context. |

---

## Testing

Run the full check suite (51 checks in one image + `K1` cross-image parity check = 52 checks) or the mutation suite (72 mutants, ~10 seconds in parallel):

```sh
./check.sh        # -v prints measured detail; set CL_SCOPE_DIR if cl-scope is not at ../cl-scope
./mutants.sh      # removes 72 behaviours one by one and verifies every mutant is caught
```

Or via ASDF:

```lisp
(asdf:test-system "cl-cordis")
```

The test suite (`test.lisp`) covers:
- **L1–L3, N1–N2 (Ledgers & Nesting)**: reverse undo order, refusal on uninstalled fibers, failing-inverse fault recording, nested child components as parent effects.
- **C1–C8 (Dependencies)**: arbitrary load order, reader-before-provider teardown, key re-binding, duplicate key/id refusal, undeclared access guards, live key updates, unset provided keys, cycle reporting.
- **O1–O4 (Operations & Observing)**: serialized operations, refusal while parked, `watch`, `changes`, `status`, `active`, `faults`.
- **F1–F5, R1, T1 (Parking, Rebuild, Threads)**: parking on `:apply` error, `abandon`/`revive`/`retry`/custom restarts, `rebuild`, and component-owned `cl-scope` threads.
- **D1–D3, E1–E8 (Live Definitions & Config Lists)**: layered `defun`/`defvar`/`defmacro`/`bind-function`, declarative `apply-config`, file-change detection, `amend-entry`, and `image-diff`.
- **I1–I4 (Interception)**: prefix ordering, contextual metadata merging, `with-intercept`, merge rule cleanup.
- **H1–H7 (Hooks)**: wrapper order, slot preservation on reload, snapshot isolation, `:ended` / `:stale` `inner` tokens, file headers.
- **Z1–Z2 (Core Conformance)**: 700 drawn cases for `check`/`plan`/`cascade`/`undo` (`test/cases/cordis.sexp`) and 250 hook-chain sequences / 6,214 operations (`test/cases/cordis-hooks.sexp`).
- **K1 & Thread Leak Check**: cross-image equivalence between a long history of edits and a fresh load of the final config, plus zero leaked SBCL threads.

---

## Known Limitations

- **SBCL only**: depends on `cl-scope` and `sb-md5`.
- **Effects are the boundary**: direct `setf` of globals, CLOS methods, classes, or packages created outside `cordis:effect` are not automatically undone (`image-diff` can report unexpected function/variable changes after the fact).
- **Parked operations serialize the runtime**: while an `:apply` is parked (or blocks indefinitely), other lifecycle operations are refused until it is answered.
- **Inlined callers**: functions compiled with an old definition inlined retain the inlined copy; active calls finish on the function they entered.
- **One variable layer per fiber**: setting the same variable twice inside one fiber replaces that fiber's layer rather than stacking two undo steps.

---

## License

MIT. See [LICENSE](LICENSE).
