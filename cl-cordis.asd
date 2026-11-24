;;; Cordis in Common Lisp: components whose effects are undone when they leave.

(defsystem "cl-cordis"
  :description "Live-image component meta-framework for SBCL: proved dependency scheduling, cascading reloads, hook chains, interception metadata, and reversible side-effect ledgers."
  :version "0.2.0"
  :author "nohzafk"
  :license "MIT"
  :homepage "https://github.com/nohzafk/cl-cordis"
  :bug-tracker "https://github.com/nohzafk/cl-cordis/issues"
  :source-control (:git "https://github.com/nohzafk/cl-cordis.git")
  :depends-on ("cl-scope" (:require "sb-md5"))
  :serial t
  ;; Pre-emitted from bend/ by cores/build.sh (Bend 2.0.40 + bend-emit-cl) into
  ;; private cl-cordis.* packages so cl-cordis never collides with a host's own
  ;; bend.* packages and requires no Bend or Bun toolchain to load.
  :components ((:module "cores" :serial t
                :components ((:file "runtime") (:file "base")
                             (:file "keys") (:file "comp") (:file "cascade")
                             (:file "check") (:file "hooks") (:file "plan")
                             (:file "undo")))
               (:file "cordis"))
  :in-order-to ((test-op (test-op "cl-cordis/test"))))

(defsystem "cl-cordis/test"
  :depends-on ("cl-cordis")
  :components ((:file "test"))
  :perform (test-op (o c)
             (unless (uiop:symbol-call :cl-cordis/test :run-all)
               (error "cl-cordis: a check failed"))))
