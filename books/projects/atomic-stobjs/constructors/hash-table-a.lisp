;;; Copyright 2025 J. David Taylor
;;;
;;; Redistribution and use in source and binary forms, with or without
;;; modification, are permitted provided that the following conditions are met:
;;;
;;; 1. Redistributions of source code must retain the above copyright notice,
;;;    this list of conditions and the following disclaimer.
;;;
;;; 2. Redistributions in binary form must reproduce the above copyright notice,
;;;    this list of conditions and the following disclaimer in the documentation
;;;    and/or other materials provided with the distribution.
;;;
;;; 3. Neither the name of the copyright holder nor the names of its
;;;    contributors may be used to endorse or promote products derived from this
;;;    software without specific prior written permission.
;;;
;;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
;;; AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
;;; IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
;;; ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
;;; LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
;;; CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
;;; SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
;;; INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
;;; CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
;;; ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
;;; POSSIBILITY OF SUCH DAMAGE.


(in-package "ATOMIC-STOBJS")
(set-verify-guards-eagerness 2)

#||
(include-book "../lemmas/hash-table-a")
||#

(include-book "std/osets/top" :dir :system)

(include-book "../utilities/top")


;;;; `SET::EQUIV'
(defun set::equiv (x y)
  (declare (xargs :guard (and (set::setp x)
                              (set::setp y))))
  (mbe :logic (equal (set::sfix x)
                     (set::sfix y))
       :exec (equal x y)))

(defequiv set::equiv)

(defcong set::equiv equal (set::sfix x) 1)

(defthm set::sfix-mode-set-equiv
  (set::equiv (set::sfix x) x))


;;;; `DEFINE-HASH-TABLE$A'
(defmacro define-hash-table$a
    (hash-table test
     &key
       (key-recognizer 'nil)
       (key-fixer 'nil)
       (key-equiv 'equal)
       (key 'nil)
       (%key 'nil)
       (default-key 'nil)
       (val-recognizer 'nil)
       (val-fixer 'nil)
       (val-equiv 'equal)
       (val 'nil)
       (%val 'nil)
       (default-val 'nil)
       (set 'nil)
       (%set 'nil)
       (copyable 't)

       (contents 'nil)
       (recognizer 'nil)
       (creator 'nil)
       (fixer 'nil)
       (equiv 'nil)
       (accessor 'nil)
       (updater 'nil)
       (boundp 'nil)
       (getp 'nil)
       (remover 'nil)
       (count 'nil)
       (clear 'nil)
       (init 'nil)
       (keysp 'nil)
       (keys-fix 'nil)
       (keys-equiv 'nil)
       (keys 'nil)
       (keys-set 'nil)

       (package-witness 'nil package-witness-supplied-p)
       (debug 'nil))

  (declare (xargs :guard (and (symbolp hash-table)
                              (symbolp test)
                              (member test '(eq eql hons-equal equal) :test 'eq)
                              (symbol-listp (list key-recognizer
                                                  key-fixer
                                                  key-equiv
                                                  key
                                                  val-recognizer
                                                  val-fixer
                                                  val-equiv
                                                  val))
                              (or (and (not key-recognizer)
                                       (not key-fixer)
                                       (not (or (eq test 'eq)
                                                (eq test 'eql))))
                                  (and key-recognizer
                                       key-fixer))
                              (or (and (not val-recognizer)
                                       (not val-fixer))
                                  (and val-recognizer
                                       val-fixer))
                              (booleanp copyable)
                              (symbol-listp (list recognizer
                                                  fixer
                                                  equiv
                                                  creator
                                                  accessor
                                                  updater
                                                  boundp
                                                  getp
                                                  remover
                                                  count
                                                  clear
                                                  init
                                                  keysp
                                                  keys-fix
                                                  keys-equiv
                                                  keys
                                                  keys-set))
                              (or copyable
                                  (and (not keys)
                                       (not keys-set)
                                       (not keysp)
                                       (not keys-fix)
                                       (not keys-equiv)))
                              (package-witness-p package-witness)
                              (booleanp debug))))

  `(with-output
     ,@(and (not debug)
            *constructor-output*)

     (make-event
       (let* ((hash-table ',hash-table)
              (package-witness (if ',package-witness-supplied-p
                                   ',package-witness
                                   (current-package state)))
              (test ',test)

              (key (or ',key
                       (symbolicate package-witness "K")))
              (%key (or ',%key
                        (symbolicate key "%" key)))
              (key-recognizer ',key-recognizer)
              (key-fixer ',key-fixer)
              (key-equiv ',key-equiv)
              (default-key-name (symbolicate package-witness "*" hash-table "-DEFAULT-KEY*"))
              (default-key default-key-name)

              (val (or ',val
                       (symbolicate package-witness "V")))
              (%val (or ',%val
                        (symbolicate val "%" val)))
              (world (w state))
              (stobj-property (getpropc val 'acl2::stobj))
              (absstobj-info (and stobj-property
                                  (getpropc val 'acl2::absstobj-info)))
              (stobj$a-property (cdr (assoc val (table-alist 'stobj$a-property world))))
              (val-recognizer (cond
                                (',val-recognizer)
                                (stobj$a-property
                                 (first (second stobj$a-property)))))
              (guard-val-recognizer (if stobj-property
                                        (caadr stobj-property)
                                        val-recognizer))
              (val-creator (cond
                             (stobj$a-property
                              (second (second stobj$a-property)))))
              (val-fixer (cond
                           (',val-fixer)
                           (stobj$a-property
                            (third (second stobj$a-property)))
                           (t
                            (cdr (assoc val (table-alist 'fixer world))))))
              (val-equiv (cond
                           (',val-equiv)
                           (stobj$a-property
                            (fourth (second stobj$a-property)))))
              (default-val-name (symbolicate package-witness "*" hash-table "-DEFAULT-VAL*"))
              (default-val (if val-creator
                               `(,val-creator)
                               default-val-name))
              (set (or ',set
                       (symbolicate package-witness "S")))
              (%set (or ',%set
                        (symbolicate set "%" set)))
              (copyable ',copyable)

              (contents ',contents)
              (recognizer ',recognizer)
              (creator ',creator)
              (fixer ',fixer)
              (equiv ',equiv)
              (accessor ',accessor)
              (updater ',updater)
              (boundp ',boundp)
              (getp ',getp)
              (remover ',remover)
              (count ',count)
              (clear ',clear)
              (init ',init)
              (keysp ',keysp)
              (keys-fix ',keys-fix)
              (keys-equiv ',keys-equiv)
              (keys ',keys)
              (keys-set ',keys-set)

              ;; Interface Symbols
              (recognizer (or recognizer
                              (symbolicate package-witness hash-table (make-predicate-suffix hash-table))))
              (creator (or creator
                           (symbolicate package-witness "CREATE-" hash-table)))
              (fixer (or fixer
                         (symbolicate package-witness hash-table "-FIX")))
              (equiv (or equiv
                         (symbolicate package-witness hash-table "-EQUIV")))
              (accessor (or accessor
                            (symbolicate package-witness hash-table "-GET")))
              (updater (or updater
                           (symbolicate package-witness hash-table "-PUT")))
              (boundp (or boundp
                          (symbolicate package-witness hash-table "-BOUNDP")))
              (getp (or getp
                        (symbolicate package-witness hash-table "-GETP")))
              (remover (or remover
                           (symbolicate package-witness hash-table "-REM")))
              (count (or count
                         (symbolicate package-witness hash-table "-COUNT")))
              (clear (or clear
                         (symbolicate package-witness hash-table "-CLEAR")))
              (init (or init
                        (symbolicate package-witness hash-table "-INIT")))
              (keysp (if (and copyable
                              key-recognizer)
                         (or keysp
                             (symbolicate package-witness hash-table "-KEYS-P"))
                         'set::setp))
              (keys-fix (if (and copyable
                                 key-recognizer)
                            (or keys-fix
                                (symbolicate package-witness hash-table "-KEYS-FIX"))
                            'set::sfix))
              (keys-equiv (if (and copyable
                                   key-recognizer)
                              (or keys-equiv
                                  (symbolicate package-witness hash-table "-KEYS-EQUIV"))
                              'set::equiv))
              (keys (or keys
                        (symbolicate package-witness hash-table "-KEYS")))
              (keys-set (or keys-set
                            (symbolicate package-witness hash-table "-KEYS-SET")))
              (contents (if copyable
                            (or contents
                                (symbolicate package-witness hash-table "-CONTENTS"))
                            hash-table))
              (contents-recognizer (if copyable
                                       (symbolicate package-witness contents "-P")
                                       recognizer))
              (contents-creator (if copyable
                                    (symbolicate package-witness "CREATE-" contents)
                                    creator))
              (contents-fixer (if copyable
                                  (symbolicate package-witness contents "-FIX")
                                  fixer))
              (contents-accessor (if copyable
                                     (symbolicate package-witness contents "-GET")
                                     accessor))
              (contents-updater (if copyable
                                    (symbolicate package-witness contents "-PUT")
                                    updater))
              (contents-boundp (if copyable
                                   (symbolicate package-witness contents "-BOUNDP")
                                   boundp))
              (contents-getp (if copyable
                                 (symbolicate package-witness contents "-GETP")
                                 getp))
              (contents-remover (if copyable
                                    (symbolicate package-witness contents "-REM")
                                    remover))
              (contents-count (if copyable
                                  (symbolicate package-witness contents "-COUNT")
                                  count))
              (contents-clear (if copyable
                                  (symbolicate package-witness contents "-CLEAR")
                                  clear))
              (contents-init (if copyable
                                 (symbolicate package-witness contents "-INIT")
                                 init))

              ;; Prologue
              (hash-table-begin (symbolicate package-witness hash-table "-BEGIN"))
              (hash-table-end (symbolicate package-witness hash-table "-END"))
              (prologue
               `((deflabel ,hash-table-begin)

                 (defconst ,default-key-name ',',default-key)

                 ,@(and (not stobj-property)
                        `((defconst ,default-val-name ',',default-val)))))

              ;; Theorem Names
              (key-recognizer-constraints (symbolicate "ATOMIC-STOBJS" key-recognizer "-CONSTRAINTS-1"))
              (key-fixer-constraints (symbolicate "ATOMIC-STOBJS" key-fixer "-CONSTRAINTS-1"))
              (key-equiv-constraints (symbolicate "ATOMIC-STOBJS" key-equiv "-CONSTRAINTS-1"))
              (val-recognizer-constraints (symbolicate "ATOMIC-STOBJS" val-recognizer "-CONSTRAINTS-2"))
              (val-fixer-constraints (symbolicate "ATOMIC-STOBJS" val-fixer "-CONSTRAINTS-2"))
              (val-equiv-constraints (symbolicate "ATOMIC-STOBJS" val-equiv "-CONSTRAINTS-2"))

              (hash-table-constraints (symbolicate package-witness hash-table "-CONSTRAINTS"))

              (keysp-tp (symbolicate package-witness keysp "-TP"))
              (keysp-cr (symbolicate package-witness keysp "-CR"))
              (keysp-def (symbolicate package-witness keysp "-DEF"))
              (setp-when-keysp (symbolicate package-witness "SETP-WHEN-" keysp))
              (keysp-when-emptyp (symbolicate package-witness keysp "-WHEN-EMPTYP"))
              (keysp-of-keys-fix (symbolicate package-witness keysp "-OF-" keys-fix))
              (keysp-of-keys (symbolicate package-witness (if key-recognizer keysp "SETP") "-OF-" keys))
              (keysp-of-sfix (symbolicate package-witness keysp "-OF-SFIX"))
              (key-recognizer-of-head-when-keysp (symbolicate package-witness key-recognizer "-OF-HEAD-WHEN-" keysp))
              (keysp-of-tail-when-keysp (symbolicate package-witness keysp "-OF-TAIL-WHEN-" keysp))
              (keysp-of-insert (symbolicate package-witness keysp "-OF-INSERT"))
              (in-when-keysp (symbolicate package-witness "IN-WHEN-" keysp))
              (in-when-keysp-split (symbolicate package-witness in-when-keysp "-SPLIT"))
              (subset-when-keysp (symbolicate package-witness keysp "-WHEN-SUBSET"))
              (keysp-of-delete (symbolicate package-witness keysp "-OF-DELETE"))
              (keysp-of-union (symbolicate package-witness keysp "-OF-UNION"))
              (keysp-of-intersect (symbolicate package-witness keysp "-OF-INTERSECT"))
              (keysp-of-difference (symbolicate package-witness keysp "-OF-DIFFERENCE"))

              (keys-fix-tp (symbolicate package-witness keys-fix "-TP"))
              (keys-fix-when-keysp (symbolicate package-witness keys-fix "-WHEN-" keysp))
              (keys-fix-when-not-keysp (symbolicate package-witness keys-fix "-WHEN-NOT-" keysp))

              (keys-equiv-tp (symbolicate package-witness keys-equiv "-TP"))
              (keys-fix-mod-keys-equiv (symbolicate package-witness keys-fix "-MOD-" keys-equiv))
              (keys-equiv-when-not-keysp (symbolicate package-witness keys-equiv "-WHEN-NOT-" keysp))

              (recognizer-tp (symbolicate package-witness recognizer "-TP"))
              (recognizer-cr (symbolicate package-witness recognizer "-CR"))
              (recognizer-of-creator (symbolicate package-witness recognizer "-OF-" creator))
              (recognizer-of-fixer (symbolicate package-witness recognizer "-OF-" fixer))
              (recognizer-of-updater (symbolicate package-witness recognizer "-OF-" updater))
              (recognizer-of-remover (symbolicate package-witness recognizer "-OF-" remover))
              (recognizer-of-keys-set (symbolicate package-witness recognizer "-OF-" keys-set))

              (fixer-tp (symbolicate package-witness fixer "-TP"))
              (fixer-when-recognizer (symbolicate package-witness fixer "-WHEN-" recognizer))
              (fixer-when-not-recognizer (symbolicate package-witness fixer "-WHEN-NOT-" recognizer))

              (equiv-tp (symbolicate package-witness equiv "-TP"))
              (fixer-mod-equiv (symbolicate package-witness fixer "-MOD-" equiv))
              (equiv-when-not-recognizer (symbolicate package-witness equiv "-WHEN-NOT-" recognizer))

              (val-recognizer-of-accessor (symbolicate package-witness val-recognizer "-OF-" accessor))
              (accessor-when-not-key-recognizer (symbolicate package-witness accessor "-WHEN-NOT-" key-recognizer))
              (accessor-when-not-recognizer (symbolicate package-witness accessor "-WHEN-NOT-" recognizer))
              (accessor-of-creator (symbolicate package-witness accessor "-OF-" creator))
              (accessor-of-updater (symbolicate package-witness accessor "-OF-" updater))
              (accessor-of-updater-same (symbolicate package-witness accessor-of-updater "-SAME"))
              (accessor-of-updater-diff (symbolicate package-witness accessor-of-updater "-DIFF"))
              (accessor-when-not-boundp (symbolicate package-witness accessor "-WHEN-NOT-" boundp))
              (accessor-of-remover (symbolicate package-witness accessor "-OF-" remover))
              (accessor-of-remover-same (symbolicate package-witness accessor-of-remover "-SAME"))
              (accessor-of-remover-diff (symbolicate package-witness accessor-of-remover "-DIFF"))
              (accessor-of-keys-set (symbolicate package-witness accessor "-OF-" keys-set))
              (accessor-when-count-is-zero (symbolicate package-witness accessor "-WHEN-" count "-IS-ZERO"))

              (updater-tp (symbolicate package-witness updater "-TP"))
              (updater-when-not-key-recognizer (symbolicate package-witness updater "-WHEN-NOT-" key-recognizer))
              (updater-when-not-val-recognizer (symbolicate package-witness updater "-WHEN-NOT-" val-recognizer))
              (updater-when-not-key-recognizer (if (eq updater-when-not-key-recognizer updater-when-not-val-recognizer)
                                                   (symbolicate package-witness updater-when-not-key-recognizer "-1")
                                                   updater-when-not-key-recognizer))
              (updater-when-not-val-recognizer (if (eq updater-when-not-key-recognizer updater-when-not-val-recognizer)
                                                   (symbolicate package-witness updater-when-not-val-recognizer "-2")
                                                   updater-when-not-val-recognizer))
              (updater-when-not-recognizer (symbolicate package-witness updater "-WHEN-NOT-" recognizer))
              (updater-of-accessor (symbolicate package-witness updater "-OF-" accessor))
              (updater-of-accessor-when-boundp (symbolicate package-witness updater-of-accessor "-WHEN-" boundp))
              (updater-of-accessor-when-boundp-free (symbolicate package-witness updater-of-accessor-when-boundp "-FREE"))
              (updater-of-accessor-when-not-boundp (symbolicate package-witness updater-of-accessor "-WHEN-NOT-" boundp))
              (updater-of-updater (symbolicate package-witness updater "-OF-" updater))
              (updater-of-updater-same (symbolicate package-witness updater-of-updater "-SAME"))
              (updater-of-updater-diff (symbolicate package-witness updater-of-updater "-DIFF"))
              (updater-of-remover-same (symbolicate package-witness updater "-OF-" remover "-SAME"))

              (boundp-tp (symbolicate package-witness boundp "-TP"))
              (boundp-when-not-key-recognizer (symbolicate package-witness boundp "-WHEN-NOT-" key-recognizer))
              (boundp-when-not-recognizer (symbolicate package-witness boundp "-WHEN-NOT-" recognizer))
              (boundp-of-creator (symbolicate package-witness boundp "-OF-" creator))
              (boundp-of-updater (symbolicate package-witness boundp "-OF-" updater))
              (boundp-of-updater-same (symbolicate package-witness boundp-of-updater "-SAME"))
              (boundp-of-updater-diff (symbolicate package-witness boundp-of-updater "-DIFF"))
              (boundp-of-remover (symbolicate package-witness boundp "-OF-" remover))
              (boundp-of-remover-same (symbolicate package-witness boundp-of-remover "-SAME"))
              (boundp-of-remover-diff (symbolicate package-witness boundp-of-remover "-DIFF"))
              (boundp-of-keys-set (symbolicate package-witness boundp "-OF-" keys-set))
              (boundp-when-count-is-zero (symbolicate package-witness boundp "-WHEN-" count "-IS-ZERO"))

              (getp-tp (symbolicate package-witness getp "-TP"))
              (getp-rw (symbolicate package-witness getp "-RW"))

              (remover-tp (symbolicate package-witness remover "-TP"))
              (remover-when-not-key-recognizer (symbolicate package-witness remover "-WHEN-NOT-" key-recognizer))
              (remover-when-not-recognizer (symbolicate package-witness remover "-WHEN-NOT-" recognizer))
              (remover-of-creator (symbolicate package-witness remover "-OF-" creator))
              (remover-of-updater (symbolicate package-witness remover "-OF-" updater))
              (remover-of-updater-same (symbolicate package-witness remover-of-updater "-SAME"))
              (remover-of-updater-diff (symbolicate package-witness remover-of-updater "-DIFF"))
              (remover-when-not-boundp (symbolicate package-witness remover "-WHEN-NOT-" boundp))
              (remover-of-remover (symbolicate package-witness remover "-OF-" remover))
              (remover-of-remover-same (symbolicate package-witness remover-of-remover "-SAME"))
              (remover-of-remover-diff (symbolicate package-witness remover-of-remover "-DIFF"))
              (remover-when-count-is-zero (symbolicate package-witness remover "-WHEN-" count "-IS-ZERO"))

              (count-tp (symbolicate package-witness count "-TP"))
              (count-when-not-recognizer (symbolicate package-witness count "-WHEN-NOT-" recognizer))
              (count-of-creator (symbolicate package-witness count "-OF-" creator))
              (count-of-updater (symbolicate package-witness count "-OF-" updater))
              (count-of-updater-when-boundp (symbolicate package-witness count-of-updater "-WHEN-" boundp))
              (count-of-updater-when-not-boundp (symbolicate package-witness count-of-updater "-WHEN-NOT-" boundp))
              (count-when-boundp (symbolicate package-witness count "-WHEN-" boundp))
              (count-of-remover (symbolicate package-witness count "-OF-" remover))
              (count-of-remover-when-boundp (symbolicate package-witness count-of-remover "-WHEN-" boundp))
              (count-of-remover-when-not-boundp (symbolicate package-witness count-of-remover "-WHEN-NOT-" boundp))
              (count-of-keys-set (symbolicate package-witness count "-OF-" keys-set))
              (creator-when-count-is-zero (symbolicate package-witness creator "-WHEN-" count "-IS-ZERO"))

              (clear-tp (symbolicate package-witness clear "-TP"))
              (clear-rw (symbolicate package-witness clear "-RW"))

              (init-tp (symbolicate package-witness init "-TP"))
              (init-rw (symbolicate package-witness init "-RW"))

              (keys-tp (symbolicate package-witness keys "-TP"))
              (keys-when-not-recognizer (symbolicate package-witness keys "-WHEN-NOT-" recognizer))
              (keys-of-creator (symbolicate package-witness keys "-OF-" creator))
              (keys-of-updater (symbolicate package-witness keys "-OF-" updater))
              (keys-of-remover (symbolicate package-witness keys "-OF-" remover))
              (keys-of-keys-set (symbolicate package-witness keys "-OF-" keys-set))

              (keys-set-tp (symbolicate package-witness keys-set "-TP"))
              (keys-set-when-not-keysp (symbolicate package-witness keys-set "-WHEN-NOT-" (if key-recognizer keysp "SETP")))
              (keys-set-when-not-recognizer (symbolicate package-witness keys-set "-WHEN-NOT-" recognizer))
              (keys-set-of-creator (symbolicate package-witness keys-set "-OF-" creator))
              (keys-set-of-updater (symbolicate package-witness keys-set "-OF-" updater))
              (keys-set-of-remover (symbolicate package-witness keys-set "-OF-" remover))
              (keys-set-of-keys (symbolicate package-witness keys-set "-OF-" keys))
              (keys-set-of-keys-free (symbolicate package-witness keys-set-of-keys "-FREE"))
              (keys-set-of-keys-set (symbolicate package-witness keys-set "-OF-" keys-set))

              (%hash-table (symbolicate package-witness "%" hash-table))
              (keys-equal (symbolicate package-witness hash-table "-KEYS-EQUAL"))
              (keys-equal-necc (symbolicate package-witness keys-equal "-NECC"))
              (keys-equal-witness (symbolicate package-witness keys-equal "-WITNESS"))
              (vals-equal (symbolicate package-witness hash-table "-VALS-EQUAL"))
              (vals-equal-necc (symbolicate package-witness vals-equal "-NECC"))
              (vals-equal-witness (symbolicate package-witness vals-equal "-WITNESS"))
              (hash-table-equal (symbolicate package-witness hash-table "-EQUAL"))
              (hash-table-equal-constraints (symbolicate package-witness hash-table-equal "-CONSTRAINTS"))
              (hash-table-equal-fc (symbolicate package-witness hash-table-equal "-FC"))

              ;; Epilogue
              (hash-table-theorems (symbolicate package-witness hash-table "-THEOREMS"))
              (hash-table-aggressive (symbolicate package-witness hash-table "-AGGRESSIVE"))
              (epilogue
               `((deflabel ,hash-table-end)

                 (deftheory-static ,hash-table-theorems
                   (set-difference-theories
                    (set-difference-theories
                     (current-theory ',hash-table-end)
                     (current-theory ',hash-table-begin))
                    (union-theories ',(append
                                       (list contents-recognizer
                                             contents-creator
                                             contents-fixer
                                             equiv
                                             contents-accessor
                                             contents-updater
                                             contents-boundp
                                             contents-getp
                                             contents-remover
                                             contents-count
                                             contents-clear
                                             contents-init
                                             hash-table-equal)
                                       (and copyable
                                            (list recognizer
                                                  creator
                                                  fixer
                                                  accessor
                                                  updater
                                                  boundp
                                                  getp
                                                  remover
                                                  count
                                                  clear
                                                  init
                                                  keys
                                                  keys-set))
                                       (and copyable
                                            key-recognizer
                                            (list keysp
                                                  keys-fix
                                                  keys-equiv)))
                                    '(,hash-table-constraints
                                      ,hash-table-equal-constraints))))

                 (deftheory-static ,hash-table-aggressive
                   ',(append
                      (list accessor-when-not-recognizer
                            accessor-of-updater
                            accessor-when-not-boundp
                            accessor-of-remover
                            accessor-when-count-is-zero
                            updater-when-not-recognizer
                            updater-of-accessor-when-boundp-free
                            updater-of-accessor
                            updater-of-updater
                            boundp-when-not-recognizer
                            boundp-of-updater
                            boundp-of-remover
                            boundp-when-count-is-zero
                            remover-when-not-recognizer
                            remover-of-updater
                            remover-when-not-boundp
                            remover-of-remover
                            remover-when-count-is-zero
                            count-when-not-recognizer
                            count-of-updater
                            count-when-boundp
                            count-of-remover)
                      (and key-recognizer
                           (list accessor-when-not-key-recognizer
                                 updater-when-not-key-recognizer
                                 boundp-when-not-key-recognizer
                                 remover-when-not-key-recognizer))
                      (and val-recognizer
                           (list updater-when-not-val-recognizer))
                      (and copyable
                           (list keys-when-not-recognizer
                                 keys-set-when-not-keysp
                                 keys-set-when-not-recognizer
                                 keys-set-of-keys-free))
                      (and copyable
                           key-recognizer
                           (list keysp-when-emptyp
                                 in-when-keysp-split
                                 subset-when-keysp))))

                 (in-theory
                   (union-theories (current-theory ',hash-table-begin)
                                   (theory ',hash-table-theorems)))

                 (in-theory
                   ;; Ensure `:USE' `HASH-TABLE-EQUAL' automagically works.
                   (enable ,keys-equal
                           ,vals-equal))))

              ;; Functional Instantiation
              (fi-bindings
               (append
                (list `(lem-hash-table$a::keysp ,keysp)
                      `(lem-hash-table$a::keys-fix ,keys-fix)
                      `(lem-hash-table$a::keys-equiv ,keys-equiv)

                      `(lem-hash-table$a::key-recognizer ,(or key-recognizer
                                                              '(lambda (key)
                                                                t)))
                      `(lem-hash-table$a::default-key (lambda ()
                                                        ,default-key-name))
                      `(lem-hash-table$a::key-fixer ,(or key-fixer
                                                         '(lambda (key)
                                                           key)))
                      `(lem-hash-table$a::key-equiv ,key-equiv)

                      `(lem-hash-table$a::val-recognizer ,(or val-recognizer
                                                              '(lambda (val)
                                                                t)))
                      `(lem-hash-table$a::default-val ,(or val-creator
                                                           `(lambda ()
                                                              ,default-val-name)))
                      `(lem-hash-table$a::val-fixer ,(or val-fixer
                                                         '(lambda (val)
                                                           val)))
                      `(lem-hash-table$a::val-equiv ,val-equiv)

                      `(lem-hash-table$a::recognizer/unique ,contents-recognizer)
                      `(lem-hash-table$a::creator/unique ,contents-creator)
                      `(lem-hash-table$a::fixer/unique ,contents-fixer)
                      (if copyable
                          `(lem-hash-table$a::equiv/copyable ,equiv)
                          `(lem-hash-table$a::equiv/unique ,equiv))
                      `(lem-hash-table$a::accessor/unique ,contents-accessor)
                      `(lem-hash-table$a::updater/unique ,contents-updater)
                      `(lem-hash-table$a::boundp/unique ,contents-boundp)
                      `(lem-hash-table$a::getp/unique ,contents-getp)
                      `(lem-hash-table$a::remover/unique ,contents-remover)
                      `(lem-hash-table$a::count/unique ,contents-count)
                      `(lem-hash-table$a::clear/unique ,contents-clear)
                      `(lem-hash-table$a::init/unique ,contents-init))

                (and copyable
                     (list `(lem-hash-table$a::recognizer/copyable ,recognizer)
                           `(lem-hash-table$a::creator/copyable ,creator)
                           `(lem-hash-table$a::fixer/copyable ,fixer)
                           `(lem-hash-table$a::accessor/copyable ,accessor)
                           `(lem-hash-table$a::updater/copyable ,updater)
                           `(lem-hash-table$a::boundp/copyable ,boundp)
                           `(lem-hash-table$a::getp/copyable ,getp)
                           `(lem-hash-table$a::remover/copyable ,remover)
                           `(lem-hash-table$a::count/copyable ,count)
                           `(lem-hash-table$a::clear/copyable ,clear)
                           `(lem-hash-table$a::init/copyable ,init)
                           `(lem-hash-table$a::keys ,keys)
                           `(lem-hash-table$a::keys-set ,keys-set)))))

              (fi-bindings-with-contents-skolem
               (list* `(lem-hash-table$a::keys-equal/unique ,keys-equal)
                      `(lem-hash-table$a::keys-equal/unique-witness ,keys-equal-witness)
                      `(lem-hash-table$a::vals-equal/unique ,vals-equal)
                      `(lem-hash-table$a::vals-equal/unique-witness ,vals-equal-witness)
                      `(lem-hash-table$a::equal/unique ,hash-table-equal)
                      fi-bindings))
              (fi-bindings-with-skolem
               (append
                (and copyable
                     (list `(lem-hash-table$a::keys-equal/copyable ,keys-equal)
                           `(lem-hash-table$a::keys-equal/copyable-witness ,keys-equal-witness)
                           `(lem-hash-table$a::vals-equal/copyable ,vals-equal)
                           `(lem-hash-table$a::vals-equal/copyable-witness ,vals-equal-witness)
                           `(lem-hash-table$a::equal/copyable ,hash-table-equal)))
                fi-bindings-with-contents-skolem))

              (body
               `(encapsulate ()

                  ,@(and key-fixer
                         key-recognizer
                         (not (eq key-equiv 'equal))
                         `((local
                             (defthm ,key-recognizer-constraints
                               (and (booleanp (,key-recognizer ,key))
                                    (,key-recognizer ,default-key))
                               :rule-classes
                               ((:rewrite :corollary
                                          (booleanp (,key-recognizer ,key))))))

                           (local
                             (defthm ,key-fixer-constraints
                               (equal (,key-fixer ,key)
                                      (if (,key-recognizer ,key)
                                          ,key
                                          ,default-key))))

                           (local
                             (defthm ,key-equiv-constraints
                               (equal (,key-equiv ,%key ,key)
                                      (equal (,key-fixer ,%key)
                                             (,key-fixer ,key)))))))

                  ,@(and val-fixer
                         val-recognizer
                         (not (eq val-equiv 'equal))
                         `((local
                             (defthm ,val-recognizer-constraints
                               (and (booleanp (,val-recognizer ,val))
                                    (,val-recognizer ,default-val))
                               :rule-classes
                               ((:rewrite :corollary
                                          (booleanp (,val-recognizer ,val))))))

                           (local
                             (defthm ,val-fixer-constraints
                               (equal (,val-fixer ,val)
                                      (if (,val-recognizer ,val)
                                          ,val
                                          ,default-val))))

                           (local
                             (defthm ,val-equiv-constraints
                               (equal (,val-equiv ,%val ,val)
                                      (equal (,val-fixer ,%val)
                                             (,val-fixer ,val)))))))

                  (local
                    (deflabel end-of-prologue))

                  (local
                    (include-book "projects/atomic-stobjs/lemmas/hash-table-a" :dir :system))

                  (local
                    (table acl2::theory-invariant-table nil nil :clear))

                  (local
                    (in-theory
                      (union-theories (current-theory 'acl2::ground-zero)
                                      (set-difference-theories
                                       (universal-theory 'end-of-prologue)
                                       (universal-theory ',hash-table-begin)))))

                  ,@(and absstobj-info
                         `((local
                             (in-theory
                               (enable ,@(strip-cars (cdr absstobj-info)))))))

                  ,@(and (eq keysp 'set::setp)
                         `((local
                             (in-theory
                               (enable acl2::fast-<<-is-<<)))))

                  ,@(and key-recognizer
                         `((local
                             (in-theory
                               (enable (:e ,key-recognizer))))))

                  ,@(and val-recognizer
                         `((local
                             (in-theory
                               (enable (:e ,val-recognizer))))))

                  ,@(and copyable
                         key-recognizer
                         `((defun ,keysp (,set)
                             (declare (xargs :guard t))
                             (if (consp ,set)
                                 (and (,key-recognizer (car ,set))
                                      (or (null (cdr ,set))
                                          (and (consp (cdr ,set))
                                               (<< (car ,set)
                                                   (cadr ,set))
                                               (,keysp (cdr ,set)))))
                                 (null ,set)))

                           (defun-inline ,keys-fix (,set)
                             (declare (xargs :guard (,keysp ,set)))
                             (mbe :logic (if (,keysp ,set)
                                             ,set
                                             ())
                                  :exec ,set))

                           (defun ,keys-equiv (,%set ,set)
                             (declare (xargs :guard (and (,keysp ,%set)
                                                         (,keysp ,set))))
                             (equal (,keys-fix ,%set)
                                    (,keys-fix ,set)))))

                  ;; If hash-table isn't copyable, then all "CONTENTS"-prefixed
                  ;; symbols refer to their non-prefixed base.
                  (defun ,contents-recognizer (,contents)
                    (declare (xargs :guard t))
                    (if (consp ,contents)
                        (and (consp (car ,contents))
                             ,@(and key-recognizer
                                    `((,key-recognizer (caar ,contents))))
                             ,@(and val-recognizer
                                    `((,val-recognizer (cdar ,contents))))
                             (or (null (cdr ,contents))
                                 (and (consp (cdr ,contents))
                                      (consp (cadr ,contents))
                                      (<< (caar ,contents) (caadr ,contents))
                                      (,contents-recognizer (cdr ,contents)))))
                        (null ,contents)))

                  ,@(and copyable
                         `((defun ,recognizer (,hash-table)
                             (declare (xargs :guard t))
                             (and (consp ,hash-table)
                                  (,keysp (car ,hash-table))
                                  (,contents-recognizer (cdr ,hash-table))))))

                  (defun-nx ,contents-creator ()
                    (declare (xargs :guard t))
                    '())

                  ,@(and copyable
                         `((defun-nx ,creator ()
                             (declare (xargs :guard t))
                             (cons '() (,contents-creator)))))

                  (defun ,contents-fixer (,contents)
                    (declare (xargs :guard (,contents-recognizer ,contents)))
                    (if (,contents-recognizer ,contents)
                        ,contents
                        (,contents-creator)))

                  ,@(and copyable
                         `((defun ,fixer (,hash-table)
                             (declare (xargs :guard (,recognizer ,hash-table)))
                             (if (,recognizer ,hash-table)
                                 ,hash-table
                                 (,creator)))))

                  (defun ,equiv (,%hash-table ,hash-table)
                    (declare (xargs :guard (and (,recognizer ,%hash-table)
                                                (,recognizer ,hash-table))))
                    (equal (,fixer ,%hash-table)
                           (,fixer ,hash-table)))

                  (defun ,contents-accessor (,key ,contents)
                    (declare (xargs :guard ,(if key-recognizer
                                                `(and (,key-recognizer ,key)
                                                      (,contents-recognizer ,contents))
                                                `(,contents-recognizer ,contents))
                                    :measure (len ,contents)))
                    (let (,@(and key-fixer
                                 `((,key (,key-fixer ,key))))
                          (,contents (,contents-fixer ,contents)))
                      (cond
                        ((or (endp ,contents)
                             (<< ,key (caar ,contents)))
                         ,default-val)
                        ((equal ,key (caar ,contents))
                         ,(if val-fixer
                              `(,val-fixer (cdar ,contents))
                              `(cdar ,contents)))
                        (t
                         (,contents-accessor ,key (cdr ,contents))))))

                  ,@(and copyable
                         `((defun ,accessor (,key ,hash-table)
                             (declare (xargs :guard ,(if key-recognizer
                                                         `(and (,key-recognizer ,key)
                                                               (,recognizer ,hash-table))
                                                         `(,recognizer ,hash-table))))
                             (let (,@(and key-fixer
                                          `((,key (,key-fixer ,key))))
                                   (,hash-table (,fixer ,hash-table)))
                               (,contents-accessor ,key (cdr ,hash-table))))))

                  (defun ,contents-updater (,key ,val ,contents)
                    (declare (xargs :guard ,(cond
                                              ((and key-recognizer
                                                    guard-val-recognizer)
                                               `(and (,key-recognizer ,key)
                                                     (,guard-val-recognizer ,val)
                                                     (,contents-recognizer ,contents)))
                                              (key-recognizer
                                               `(and (,key-recognizer ,key)
                                                     (,contents-recognizer ,contents)))
                                              (guard-val-recognizer
                                               `(and (,guard-val-recognizer ,val)
                                                     (,contents-recognizer ,contents)))
                                              (t
                                               `(,contents-recognizer ,contents)))
                                    :measure (len ,contents)))
                    (let (,@(and key-fixer
                                 `((,key (,key-fixer ,key))))
                          ,@(and val-fixer
                                 `((,val (,val-fixer ,val))))
                            (,contents (,contents-fixer ,contents)))
                      (cond
                        ((endp ,contents)
                         (list (cons ,key ,val)))
                        ((<< ,key (caar ,contents))
                         (cons (cons ,key ,val) ,contents))
                        ((equal ,key (caar ,contents))
                         (cons (cons ,key ,val) (cdr ,contents)))
                        (t
                         (cons (car ,contents)
                               (,contents-updater ,key ,val (cdr ,contents)))))))

                  ,@(and copyable
                         `((defun ,updater (,key ,val ,hash-table)
                             (declare (xargs :guard ,(cond
                                                       ((and key-recognizer
                                                             guard-val-recognizer)
                                                        `(and (,key-recognizer ,key)
                                                              (,guard-val-recognizer ,val)
                                                              (,recognizer ,hash-table)))
                                                       (key-recognizer
                                                        `(and (,key-recognizer ,key)
                                                              (,recognizer ,hash-table)))
                                                       (guard-val-recognizer
                                                        `(and (,guard-val-recognizer ,val)
                                                              (,recognizer ,hash-table)))
                                                       (t
                                                        `(,recognizer ,hash-table)))))
                             (let (,@(and key-fixer
                                          `((,key (,key-fixer ,key))))
                                   ,@(and val-fixer
                                          `((,val (,val-fixer ,val))))
                                     (,hash-table (,fixer ,hash-table)))
                               (cons (car ,hash-table)
                                     (,contents-updater ,key ,val (cdr ,hash-table)))))))

                  (defun ,contents-boundp (,key ,contents)
                    (declare (xargs :guard ,(if key-recognizer
                                                `(and (,key-recognizer ,key)
                                                      (,contents-recognizer ,contents))
                                                `(,contents-recognizer ,contents))
                                    :measure (len ,contents)))
                    (let (,@(and key-fixer
                                 `((,key (,key-fixer ,key))))
                          (,contents (,contents-fixer ,contents)))
                      (cond
                        ((or (endp ,contents)
                             (<< ,key (caar ,contents)))
                         'nil)
                        ((equal ,key (caar ,contents))
                         't)
                        (t
                         (,contents-boundp ,key (cdr ,contents))))))

                  ,@(and copyable
                         `((defun ,boundp (,key ,hash-table)
                             (declare (xargs :guard ,(if key-recognizer
                                                         `(and (,key-recognizer ,key)
                                                               (,recognizer ,hash-table))
                                                         `(,recognizer ,hash-table))))
                             (let (,@(and key-fixer
                                          `((,key (,key-fixer ,key))))
                                   (,hash-table (,fixer ,hash-table)))
                               (,contents-boundp ,key (cdr ,hash-table))))))

                  (defun ,contents-getp (,key ,contents)
                    (declare (xargs :guard ,(if key-recognizer
                                                `(and (,key-recognizer ,key)
                                                      (,contents-recognizer ,contents))
                                                `(,contents-recognizer ,contents))))
                    (let (,@(and key-fixer
                                 `((,key (,key-fixer ,key))))
                          (,contents (,contents-fixer ,contents)))
                      (mv (,contents-accessor ,key ,contents)
                          (,contents-boundp ,key ,contents))))

                  ,@(and copyable
                         `((defun ,getp (,key ,hash-table)
                             (declare (xargs :guard ,(if key-recognizer
                                                         `(and (,key-recognizer ,key)
                                                               (,recognizer ,hash-table))
                                                         `(,recognizer ,hash-table))))
                             (let (,@(and key-fixer
                                          `((,key (,key-fixer ,key))))
                                   (,hash-table (,fixer ,hash-table)))
                               (,contents-getp ,key (cdr ,hash-table))))))

                  (defun ,contents-remover (,key ,contents)
                    (declare (xargs :guard ,(if key-recognizer
                                                `(and (,key-recognizer ,key)
                                                      (,contents-recognizer ,contents))
                                                `(,contents-recognizer ,contents))
                                    :measure (len ,contents)))
                    (let (,@(and key-fixer
                                 `((,key (,key-fixer ,key))))
                          (,contents (,contents-fixer ,contents)))
                      (cond
                        ((endp ,contents)
                         (,contents-creator))
                        ((<< ,key (caar ,contents))
                         ,contents)
                        ((equal ,key (caar ,contents))
                         (cdr ,contents))
                        (t
                         (cons (car ,contents)
                               (,contents-remover ,key (cdr ,contents)))))))

                  ,@(and copyable
                         `((defun ,remover (,key ,hash-table)
                             (declare (xargs :guard ,(if key-recognizer
                                                         `(and (,key-recognizer ,key)
                                                               (,recognizer ,hash-table))
                                                         `(,recognizer ,hash-table))))
                             (let (,@(and key-fixer
                                          `((,key (,key-fixer ,key))))
                                   (,hash-table (,fixer ,hash-table)))
                               (cons (car ,hash-table)
                                     (,contents-remover ,key (cdr ,hash-table)))))))

                  (defun ,contents-count (,contents)
                    (declare (xargs :guard (,contents-recognizer ,contents)))
                    (let ((,contents (,contents-fixer ,contents)))
                      (if (consp ,contents)
                          (1+ (,contents-count (cdr ,contents)))
                          0)))

                  ,@(and copyable
                         `((defun ,count (,hash-table)
                             (declare (xargs :guard (,recognizer ,hash-table)))
                             (let ((,hash-table (,fixer ,hash-table)))
                               (,contents-count (cdr ,hash-table))))))

                  (defun ,contents-clear (,contents)
                    (declare (xargs :guard (,contents-recognizer ,contents))
                             (ignore ,contents))
                    (,contents-creator))

                  ,@(and copyable
                         `((defun ,clear (,hash-table)
                             (declare (xargs :guard (,recognizer ,hash-table))
                                      (ignore ,hash-table))
                             (,creator))))

                  (defun ,contents-init (ht-size rehash-size rehash-threshold ,contents)
                    (declare (xargs :guard (and (,contents-recognizer ,contents)
                                                (or (natp ht-size)
                                                    (not ht-size))
                                                (or (and (rationalp rehash-size)
                                                         (<= 1 rehash-size))
                                                    (not rehash-size))
                                                (or (and (rationalp rehash-threshold)
                                                         (<= 0 rehash-threshold)
                                                         (<= rehash-threshold 1))
                                                    (not rehash-threshold))))
                             (ignore ht-size rehash-size rehash-threshold ,contents))
                    (,contents-creator))

                  ,@(and copyable
                         `((defun ,init (ht-size rehash-size rehash-threshold ,hash-table)
                             (declare (xargs :guard (and (,recognizer ,hash-table)
                                                         (or (natp ht-size)
                                                             (not ht-size))
                                                         (or (and (rationalp rehash-size)
                                                                  (<= 1 rehash-size))
                                                             (not rehash-size))
                                                         (or (and (rationalp rehash-threshold)
                                                                  (<= 0 rehash-threshold)
                                                                  (<= rehash-threshold 1))
                                                             (not rehash-threshold))))
                                      (ignore ht-size rehash-size rehash-threshold ,hash-table))
                             (,creator))))

                  ,@(and copyable
                         `((defun ,keys (,hash-table)
                             (declare (xargs :guard (,recognizer ,hash-table)))
                             (let ((,hash-table (,fixer ,hash-table)))
                               (car ,hash-table)))))

                  ,@(and copyable
                         `((defun ,keys-set (,set ,hash-table)
                             (declare (xargs :guard (and (,keysp ,set)
                                                         (,recognizer ,hash-table))))
                             (let ((,set (,keys-fix ,set))
                                   (,hash-table (,fixer ,hash-table)))
                               (cons ,set (cdr ,hash-table))))))

                  (local
                    ;; This is a hack.
                    (defthm null-contents
                      (not (,contents-remover ,key nil))))

                  (defthm ,hash-table-constraints
                    (and (equal (,contents-recognizer ,contents)
                                (if (consp ,contents)
                                    (if (consp (car ,contents))
                                        ,(cond
                                           ((and key-recognizer
                                                 val-recognizer)
                                            `(if (,key-recognizer (car (car ,contents)))
                                                 (if (,val-recognizer (cdr (car ,contents)))
                                                     (if (null (cdr ,contents))
                                                         (null (cdr ,contents))
                                                         (if (consp (cdr ,contents))
                                                             (if (consp (car (cdr ,contents)))
                                                                 (if (<< (car (car ,contents))
                                                                         (car (car (cdr ,contents))))
                                                                     (,contents-recognizer (cdr ,contents))
                                                                     'nil)
                                                                 'nil)
                                                             'nil))
                                                     'nil)
                                                 'nil))
                                           (key-recognizer
                                            `(if (,key-recognizer (car (car ,contents)))
                                                 (if (null (cdr ,contents))
                                                     (null (cdr ,contents))
                                                     (if (consp (cdr ,contents))
                                                         (if (consp (car (cdr ,contents)))
                                                             (if (<< (car (car ,contents))
                                                                     (car (car (cdr ,contents))))
                                                                 (,contents-recognizer (cdr ,contents))
                                                                 'nil)
                                                             'nil)
                                                         'nil))
                                                 'nil))
                                           (val-recognizer
                                            `(if (,val-recognizer (cdr (car ,contents)))
                                                 (if (null (cdr ,contents))
                                                     (null (cdr ,contents))
                                                     (if (consp (cdr ,contents))
                                                         (if (consp (car (cdr ,contents)))
                                                             (if (<< (car (car ,contents))
                                                                     (car (car (cdr ,contents))))
                                                                 (,contents-recognizer (cdr ,contents))
                                                                 'nil)
                                                             'nil)
                                                         'nil))
                                                 'nil))
                                           (t
                                            `(if (null (cdr ,contents))
                                                 (null (cdr ,contents))
                                                 (if (consp (cdr ,contents))
                                                     (if (consp (car (cdr ,contents)))
                                                         (if (<< (car (car ,contents))
                                                                 (car (car (cdr ,contents))))
                                                             (,contents-recognizer (cdr ,contents))
                                                             'nil)
                                                         'nil)
                                                     'nil))))
                                        'nil)
                                    (null ,contents)))
                         (equal (,contents-creator)
                                'nil)
                         (equal (,contents-fixer ,contents)
                                (if (,contents-recognizer ,contents)
                                    ,contents
                                    (,contents-creator)))
                         (equal (,equiv ,%hash-table ,hash-table)
                                (equal (,fixer ,%hash-table)
                                       (,fixer ,hash-table)))
                         (equal (,contents-accessor ,key ,contents)
                                ((lambda (,key ,contents)
                                   (if (if (endp ,contents)
                                           (endp ,contents)
                                           (<< ,key (car (car ,contents))))
                                       ,default-val
                                       (if (equal ,key (car (car ,contents)))
                                           ,(if val-fixer
                                                `(,val-fixer (cdr (car ,contents)))
                                                `(cdr (car ,contents)))
                                           (,contents-accessor ,key (cdr ,contents)))))
                                 ,(if key-fixer
                                      `(,key-fixer ,key)
                                      key)
                                 (,contents-fixer ,contents)))
                         (equal (,contents-updater ,key ,val ,contents)
                                ((lambda (,key ,val ,contents)
                                   (if (endp ,contents)
                                       (cons (cons ,key ,val) 'nil)
                                       (if (<< ,key (car (car ,contents)))
                                           (cons (cons ,key ,val) ,contents)
                                           (if (equal ,key (car (car ,contents)))
                                               (cons (cons ,key ,val) (cdr ,contents))
                                               (cons (car ,contents)
                                                     (,contents-updater ,key ,val (cdr ,contents)))))))
                                 ,(if key-fixer
                                      `(,key-fixer ,key)
                                      key)
                                 ,(if val-fixer
                                      `(,val-fixer ,val)
                                      val)
                                 (,contents-fixer ,contents)))
                         (equal (,contents-boundp ,key ,contents)
                                ((lambda (,key ,contents)
                                   (if (if (endp ,contents)
                                           (endp ,contents)
                                           (<< ,key (car (car ,contents))))
                                       'nil
                                       (if (equal ,key (car (car ,contents)))
                                           't
                                           (,contents-boundp ,key (cdr ,contents)))))
                                 ,(if key-fixer
                                      `(,key-fixer ,key)
                                      key)
                                 (,contents-fixer ,contents)))
                         (equal (,contents-getp ,key ,contents)
                                ((lambda (,key ,contents)
                                   (cons (,contents-accessor ,key ,contents)
                                         (cons (,contents-boundp ,key ,contents)
                                               'nil)))
                                 ,(if key-fixer
                                      `(,key-fixer ,key)
                                      key)
                                 (,contents-fixer ,contents)))
                         (equal (,contents-remover ,key ,contents)
                                ((lambda (,key ,contents)
                                   (if (endp ,contents)
                                       'nil
                                       (if (<< ,key (car (car ,contents)))
                                           ,contents
                                           (if (equal ,key (car (car ,contents)))
                                               (cdr ,contents)
                                               (cons (car ,contents)
                                                     (,contents-remover ,key (cdr ,contents)))))))
                                 ,(if key-fixer
                                      `(,key-fixer ,key)
                                      key)
                                 (,contents-fixer ,contents)))
                         (equal (,contents-count ,contents)
                                ((lambda (,contents)
                                   (if (consp ,contents)
                                       (binary-+ '1
                                                 (,contents-count (cdr ,contents)))
                                       '0))
                                 (,contents-fixer ,contents)))
                         (equal (,contents-clear ,contents)
                                (,contents-creator))
                         (equal (,contents-init ht-size rehash-size rehash-threshold ,contents)
                                (,contents-creator))
                         ,@(and copyable
                                `((equal (,keysp ,set)
                                         (if (consp ,set)
                                             ,(if key-recognizer
                                                  `(if (,key-recognizer (car ,set))
                                                       (if (null (cdr ,set))
                                                           (null (cdr ,set))
                                                           (if (consp (cdr ,set))
                                                               (if (<< (car ,set) (car (cdr ,set)))
                                                                   (,keysp (cdr ,set))
                                                                   'nil)
                                                               'nil))
                                                       'nil)
                                                  `(if (null (cdr ,set))
                                                       (null (cdr ,set))
                                                       (if (consp (cdr ,set))
                                                           (if (<< (car ,set) (car (cdr ,set)))
                                                               (,keysp (cdr ,set))
                                                               'nil)
                                                           'nil)))
                                             (null ,set)))
                                  (equal (,keys-fix ,set)
                                         (if (,keysp ,set) ,set 'nil))
                                  (equal (,keys-equiv ,%set ,set)
                                         (equal (,keys-fix ,%set) (,keys-fix ,set)))
                                  (equal (,recognizer hash-table)
                                         (if (consp hash-table)
                                             (if (,keysp (car hash-table))
                                                 (,contents-recognizer (cdr hash-table))
                                                 'nil)
                                             'nil))
                                  (equal (,creator)
                                         (cons 'nil (,contents-creator)))
                                  (equal (,fixer hash-table)
                                         (if (,recognizer hash-table)
                                             hash-table
                                             (,creator)))
                                  (equal (,accessor ,key hash-table)
                                         ((lambda (,key hash-table)
                                            (,contents-accessor ,key (cdr hash-table)))
                                          ,(if key-fixer
                                               `(,key-fixer ,key)
                                               key)
                                          (,fixer hash-table)))
                                  (equal (,updater ,key ,val hash-table)
                                         ((lambda (,key ,val hash-table)
                                            (cons (car hash-table)
                                                  (,contents-updater ,key ,val (cdr hash-table))))
                                          ,(if key-fixer
                                               `(,key-fixer ,key)
                                               key)
                                          ,(if val-fixer
                                               `(,val-fixer ,val)
                                               val)
                                          (,fixer hash-table)))
                                  (equal (,boundp ,key hash-table)
                                         ((lambda (,key hash-table)
                                            (,contents-boundp ,key (cdr hash-table)))
                                          ,(if key-fixer
                                               `(,key-fixer ,key)
                                               key)
                                          (,fixer hash-table)))
                                  (equal (,getp ,key hash-table)
                                         ((lambda (,key hash-table)
                                            (,contents-getp ,key (cdr hash-table)))
                                          ,(if key-fixer
                                               `(,key-fixer ,key)
                                               key)
                                          (,fixer hash-table)))
                                  (equal (,remover ,key hash-table)
                                         ((lambda (,key hash-table)
                                            (cons (car hash-table)
                                                  (,contents-remover ,key (cdr hash-table))))
                                          ,(if key-fixer
                                               `(,key-fixer ,key)
                                               key)
                                          (,fixer hash-table)))
                                  (equal (,count hash-table)
                                         ((lambda (hash-table)
                                            (,contents-count (cdr hash-table)))
                                          (,fixer hash-table)))
                                  (equal (,clear hash-table)
                                         (,creator))
                                  (equal (,init ht-size
                                                rehash-size rehash-threshold hash-table)
                                         (,creator))
                                  (equal (,keys hash-table)
                                         ((lambda (hash-table) (car hash-table))
                                          (,fixer hash-table)))
                                  (equal (,keys-set ,set hash-table)
                                         ((lambda (,set hash-table)
                                            (cons ,set (cdr hash-table)))
                                          (,keys-fix ,set)
                                          (,fixer hash-table))))))
                    :rule-classes
                    ((:definition :corollary
                         (equal (,contents-recognizer ,contents)
                                (if (consp ,contents)
                                    (if (consp (car ,contents))
                                        ,(cond
                                           ((and key-recognizer
                                                 val-recognizer)
                                            `(if (,key-recognizer (car (car ,contents)))
                                                 (if (,val-recognizer (cdr (car ,contents)))
                                                     (if (null (cdr ,contents))
                                                         (null (cdr ,contents))
                                                         (if (consp (cdr ,contents))
                                                             (if (consp (car (cdr ,contents)))
                                                                 (if (<< (car (car ,contents))
                                                                         (car (car (cdr ,contents))))
                                                                     (,contents-recognizer (cdr ,contents))
                                                                     'nil)
                                                                 'nil)
                                                             'nil))
                                                     'nil)
                                                 'nil))
                                           (key-recognizer
                                            `(if (,key-recognizer (car (car ,contents)))
                                                 (if (null (cdr ,contents))
                                                     (null (cdr ,contents))
                                                     (if (consp (cdr ,contents))
                                                         (if (consp (car (cdr ,contents)))
                                                             (if (<< (car (car ,contents))
                                                                     (car (car (cdr ,contents))))
                                                                 (,contents-recognizer (cdr ,contents))
                                                                 'nil)
                                                             'nil)
                                                         'nil))
                                                 'nil))
                                           (val-recognizer
                                            `(if (,val-recognizer (cdr (car ,contents)))
                                                 (if (null (cdr ,contents))
                                                     (null (cdr ,contents))
                                                     (if (consp (cdr ,contents))
                                                         (if (consp (car (cdr ,contents)))
                                                             (if (<< (car (car ,contents))
                                                                     (car (car (cdr ,contents))))
                                                                 (,contents-recognizer (cdr ,contents))
                                                                 'nil)
                                                             'nil)
                                                         'nil))
                                                 'nil))
                                           (t
                                            `(if (null (cdr ,contents))
                                                 (null (cdr ,contents))
                                                 (if (consp (cdr ,contents))
                                                     (if (consp (car (cdr ,contents)))
                                                         (if (<< (car (car ,contents))
                                                                 (car (car (cdr ,contents))))
                                                             (,contents-recognizer (cdr ,contents))
                                                             'nil)
                                                         'nil)
                                                     'nil))))
                                        'nil)
                                    (null ,contents))))
                     (:definition :corollary
                         (equal (,contents-creator)
                                'nil))
                     (:definition :corollary
                         (equal (,contents-fixer ,contents)
                                (if (,contents-recognizer ,contents)
                                    ,contents
                                    (,contents-creator))))
                     (:definition :corollary
                         (equal (,equiv ,%hash-table ,hash-table)
                                (equal (,fixer ,%hash-table)
                                       (,fixer ,hash-table))))
                     (:definition :corollary
                         (equal (,contents-accessor ,key ,contents)
                                ((lambda (,key ,contents)
                                   (if (if (endp ,contents)
                                           (endp ,contents)
                                           (<< ,key (car (car ,contents))))
                                       ,default-val
                                       (if (equal ,key (car (car ,contents)))
                                           ,(if val-fixer
                                                `(,val-fixer (cdr (car ,contents)))
                                                `(cdr (car ,contents)))
                                           (,contents-accessor ,key (cdr ,contents)))))
                                 ,(if key-fixer
                                      `(,key-fixer ,key)
                                      key)
                                 (,contents-fixer ,contents))))
                     (:definition :corollary
                         (equal (,contents-updater ,key ,val ,contents)
                                ((lambda (,key ,val ,contents)
                                   (if (endp ,contents)
                                       (cons (cons ,key ,val) 'nil)
                                       (if (<< ,key (car (car ,contents)))
                                           (cons (cons ,key ,val) ,contents)
                                           (if (equal ,key (car (car ,contents)))
                                               (cons (cons ,key ,val) (cdr ,contents))
                                               (cons (car ,contents)
                                                     (,contents-updater ,key ,val (cdr ,contents)))))))
                                 ,(if key-fixer
                                      `(,key-fixer ,key)
                                      key)
                                 ,(if val-fixer
                                      `(,val-fixer ,val)
                                      val)
                                 (,contents-fixer ,contents))))
                     (:definition :corollary
                         (equal (,contents-boundp ,key ,contents)
                                ((lambda (,key ,contents)
                                   (if (if (endp ,contents)
                                           (endp ,contents)
                                           (<< ,key (car (car ,contents))))
                                       'nil
                                       (if (equal ,key (car (car ,contents)))
                                           't
                                           (,contents-boundp ,key (cdr ,contents)))))
                                 ,(if key-fixer
                                      `(,key-fixer ,key)
                                      key)
                                 (,contents-fixer ,contents))))
                     (:definition :corollary
                         (equal (,contents-getp ,key ,contents)
                                ((lambda (,key ,contents)
                                   (cons (,contents-accessor ,key ,contents)
                                         (cons (,contents-boundp ,key ,contents)
                                               'nil)))
                                 ,(if key-fixer
                                      `(,key-fixer ,key)
                                      key)
                                 (,contents-fixer ,contents))))
                     (:definition :corollary
                         (equal (,contents-remover ,key ,contents)
                                ((lambda (,key ,contents)
                                   (if (endp ,contents)
                                       'nil
                                       (if (<< ,key (car (car ,contents)))
                                           ,contents
                                           (if (equal ,key (car (car ,contents)))
                                               (cdr ,contents)
                                               (cons (car ,contents)
                                                     (,contents-remover ,key (cdr ,contents)))))))
                                 ,(if key-fixer
                                      `(,key-fixer ,key)
                                      key)
                                 (,contents-fixer ,contents))))
                     (:definition :corollary
                         (equal (,contents-count ,contents)
                                ((lambda (,contents)
                                   (if (consp ,contents)
                                       (binary-+ '1
                                                 (,contents-count (cdr ,contents)))
                                       '0))
                                 (,contents-fixer ,contents))))
                     (:definition :corollary
                         (equal (,contents-clear ,contents)
                                (,contents-creator)))
                     (:definition :corollary
                         (equal (,contents-init ht-size rehash-size rehash-threshold ,contents)
                                (,contents-creator)))
                     ,@(and copyable
                            `((:definition :corollary
                                  (equal (,keysp ,set)
                                         (if (consp ,set)
                                             ,(if key-recognizer
                                                  `(if (,key-recognizer (car ,set))
                                                       (if (null (cdr ,set))
                                                           (null (cdr ,set))
                                                           (if (consp (cdr ,set))
                                                               (if (<< (car ,set) (car (cdr ,set)))
                                                                   (,keysp (cdr ,set))
                                                                   'nil)
                                                               'nil))
                                                       'nil)
                                                  `(if (null (cdr ,set))
                                                       (null (cdr ,set))
                                                       (if (consp (cdr ,set))
                                                           (if (<< (car ,set) (car (cdr ,set)))
                                                               (,keysp (cdr ,set))
                                                               'nil)
                                                           'nil)))
                                             (null ,set))))
                              (:definition :corollary
                                  (equal (,keys-fix ,set)
                                         (if (,keysp ,set) ,set 'nil)))
                              (:definition :corollary
                                  (equal (,keys-equiv ,%set ,set)
                                         (equal (,keys-fix ,%set) (,keys-fix ,set))))
                              (:definition :corollary
                                  (equal (,recognizer hash-table)
                                         (if (consp hash-table)
                                             (if (,keysp (car hash-table))
                                                 (,contents-recognizer (cdr hash-table))
                                                 'nil)
                                             'nil)))
                              (:definition :corollary
                                  (equal (,creator)
                                         (cons 'nil (,contents-creator))))
                              (:definition :corollary
                                  (equal (,fixer hash-table)
                                         (if (,recognizer hash-table)
                                             hash-table
                                             (,creator))))
                              (:definition :corollary
                                  (equal (,accessor ,key hash-table)
                                         ((lambda (,key hash-table)
                                            (,contents-accessor ,key (cdr hash-table)))
                                          ,(if key-fixer
                                               `(,key-fixer ,key)
                                               key)
                                          (,fixer hash-table))))
                              (:definition :corollary
                                  (equal (,updater ,key ,val hash-table)
                                         ((lambda (,key ,val hash-table)
                                            (cons (car hash-table)
                                                  (,contents-updater ,key ,val (cdr hash-table))))
                                          ,(if key-fixer
                                               `(,key-fixer ,key)
                                               key)
                                          ,(if val-fixer
                                               `(,val-fixer ,val)
                                               val)
                                          (,fixer hash-table))))
                              (:definition :corollary
                                  (equal (,boundp ,key hash-table)
                                         ((lambda (,key hash-table)
                                            (,contents-boundp ,key (cdr hash-table)))
                                          ,(if key-fixer
                                               `(,key-fixer ,key)
                                               key)
                                          (,fixer hash-table))))
                              (:definition :corollary
                                  (equal (,getp ,key hash-table)
                                         ((lambda (,key hash-table)
                                            (,contents-getp ,key (cdr hash-table)))
                                          ,(if key-fixer
                                               `(,key-fixer ,key)
                                               key)
                                          (,fixer hash-table))))
                              (:definition :corollary
                                  (equal (,remover ,key hash-table)
                                         ((lambda (,key hash-table)
                                            (cons (car hash-table)
                                                  (,contents-remover ,key (cdr hash-table))))
                                          ,(if key-fixer
                                               `(,key-fixer ,key)
                                               key)
                                          (,fixer hash-table))))
                              (:definition :corollary
                                  (equal (,count hash-table)
                                         ((lambda (hash-table)
                                            (,contents-count (cdr hash-table)))
                                          (,fixer hash-table))))
                              (:definition :corollary
                                  (equal (,clear hash-table)
                                         (,creator)))
                              (:definition :corollary
                                  (equal (,init ht-size
                                                rehash-size rehash-threshold hash-table)
                                         (,creator)))
                              (:definition :corollary
                                  (equal (,keys hash-table)
                                         ((lambda (hash-table) (car hash-table))
                                          (,fixer hash-table))))
                              (:definition :corollary
                                  (equal (,keys-set ,set hash-table)
                                         ((lambda (,set hash-table)
                                            (cons ,set (cdr hash-table)))
                                          (,keys-fix ,set)
                                          (,fixer hash-table)))))))
                    :hints
                    (("Goal"
                      :do-not-induct t
                      ,@(and (eq keysp 'set::setp)
                             `(:in-theory (enable set::setp
                                                  set::sfix
                                                  set::equiv
                                                  set::emptyp))))))

                  (local
                    (in-theory
                      (disable ,@(and copyable
                                      key-recognizer
                                      (list keysp
                                            keys-fix
                                            keys-equiv))
                               ,contents-recognizer
                               ,contents-creator
                               ,contents-fixer
                               ,equiv
                               ,contents-accessor
                               ,contents-updater
                               ,contents-boundp
                               ,contents-getp
                               ,contents-remover
                               ,contents-count
                               ,contents-clear
                               ,contents-init
                               ,@(and copyable
                                      (list keys
                                            keys-set
                                            recognizer
                                            creator
                                            fixer
                                            accessor
                                            updater
                                            boundp
                                            getp
                                            remover
                                            count
                                            clear
                                            init)))))

                  ;; `KEYSP'
                  ,@(and copyable
                         key-recognizer
                         `((defthm ,keysp-tp
                             (booleanp (,keysp ,set))
                             :rule-classes :type-prescription
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keysp-tp
                                    ,@fi-bindings))))

                           (defthm ,keysp-cr
                             (implies (,keysp ,set)
                                      (true-listp ,set))
                             :rule-classes :compound-recognizer
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keysp-cr
                                    ,@fi-bindings))))

                           (defthmd ,keysp-def
                             (equal (,keysp ,set)
                                    (and (set::setp ,set)
                                         (or (set::emptyp ,set)
                                             (and (,key-recognizer (set::head ,set))
                                                  (,keysp (set::tail ,set))))))
                             :rule-classes
                             ((:definition :controller-alist ((,keysp t))))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keysp-def
                                    ,@fi-bindings))))

                           (defthm ,setp-when-keysp
                             (implies (,keysp ,set)
                                      (set::setp ,set))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::setp-when-keysp
                                    ,@fi-bindings))))

                           (defthmd ,keysp-when-emptyp
                             (implies (set::emptyp ,set)
                                      (equal (,keysp ,set)
                                             (set::setp ,set)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keysp-when-emptyp
                                    ,@fi-bindings))))

                           (defthm ,keysp-of-keys-fix
                             (,keysp (,keys-fix ,set))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keysp-of-keys-fix
                                    ,@fi-bindings))))

                           (defthm ,keysp-of-keys
                             (,keysp (,keys ,hash-table))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keysp-of-keys
                                    ,@fi-bindings))))

                           (defthm ,keysp-of-sfix
                             (equal (,keysp (set::sfix set))
                                    (or (set::emptyp set)
                                        (,keysp set)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keysp-of-sfix
                                    ,@fi-bindings))))

                           (defthm ,key-recognizer-of-head-when-keysp
                             (implies (and (not (set::emptyp ,set))
                                           (,keysp ,set))
                                      (,key-recognizer (set::head ,set)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::key-recognizer-of-head-when-keysp
                                    ,@fi-bindings))))

                           (defthm ,keysp-of-tail-when-keysp
                             (implies (and (not (set::emptyp ,set))
                                           (,keysp ,set))
                                      (,keysp (set::tail ,set)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keysp-of-tail-when-keysp
                                    ,@fi-bindings))))


                           (defthm ,keysp-of-insert
                             (equal (,keysp (set::insert key set))
                                    (and (,key-recognizer key)
                                         (or (set::emptyp set)
                                             (,keysp set))))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keysp-of-insert
                                    ,@fi-bindings))))

                           (defthmd ,in-when-keysp-split
                             (implies (and (,keysp ,set)
                                           (not (,key-recognizer ,key)))
                                      (not (set::in ,key ,set)))
                             :rule-classes
                             ((:rewrite :corollary
                                        (implies (and (,keysp ,set)
                                                      (not (case-split (,key-recognizer ,key))))
                                                 (not (set::in ,key ,set)))))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::in-when-keysp
                                    ,@fi-bindings))))

                           (defthm ,in-when-keysp
                             (implies (and (,keysp ,set)
                                           (not (,key-recognizer ,key)))
                                      (not (set::in ,key ,set)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::in-when-keysp
                                    ,@fi-bindings))))

                           (defthmd ,subset-when-keysp
                             (implies (and (not (,keysp ,%set))
                                           (,keysp ,set))
                                      (equal (set::subset ,%set ,set)
                                             (set::emptyp ,%set)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::subset-when-keysp
                                    ,@fi-bindings))))

                           (defthm ,keysp-of-delete
                             (implies (,keysp ,set)
                                      (,keysp (set::delete ,key ,set)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keysp-of-delete
                                    ,@fi-bindings))))

                           (defthm ,keysp-of-union
                             (implies (and (not (set::emptyp ,%set))
                                           (not (set::emptyp ,set)))
                                      (equal (,keysp (set::union ,%set ,set))
                                             (and (,keysp ,%set)
                                                  (,keysp ,set))))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keysp-of-union
                                    ,@fi-bindings))))

                           (defthm ,keysp-of-intersect
                             (implies (or (,keysp ,%set)
                                          (,keysp ,set))
                                      (,keysp (set::intersect ,%set ,set)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keysp-of-intersect
                                    ,@fi-bindings))))

                           (defthm ,keysp-of-difference
                             (implies (,keysp ,%set)
                                      (,keysp (set::difference ,%set ,set)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keysp-of-difference
                                    ,@fi-bindings))))))

                  ;; `KEYS-FIX'
                  ,@(and copyable
                         key-recognizer
                         `((defthm ,keys-fix-tp
                             (true-listp (,keys-fix ,set))
                             :rule-classes :type-prescription
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keys-fix-tp
                                    ,@fi-bindings))))

                           (defthm ,keys-fix-when-keysp
                             (implies (,keysp ,set)
                                      (equal (,keys-fix ,set)
                                             ,set))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keys-fix-when-keysp
                                    ,@fi-bindings))))

                           (defthm ,keys-fix-when-not-keysp
                             (implies (not (,keysp ,set))
                                      (not (,keys-fix ,set)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keys-fix-when-not-keysp
                                    ,@fi-bindings))))))

                  ;; `KEYS-EQUIV'
                  ,@(and copyable
                         key-recognizer
                         `((defthm ,keys-equiv-tp
                             (booleanp (,keys-equiv ,%set ,set))
                             :rule-classes :type-prescription
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keys-equiv-tp
                                    ,@fi-bindings))))

                           (defequiv ,keys-equiv
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keys-equiv-is-an-equivalence
                                    ,@fi-bindings))))

                           (defcong ,keys-equiv equal (,keys-fix ,set) 1
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keys-equiv-implies-equal-keys-fix-1
                                    ,@fi-bindings))))

                           (defthm ,keys-fix-mod-keys-equiv
                             (,keys-equiv (,keys-fix ,set) ,set)
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keys-fix-mod-keys-equiv
                                    ,@fi-bindings))))

                           (defthm ,keys-equiv-when-not-keysp
                             (implies (not (,keysp ,set))
                                      (,keys-equiv ,set ()))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keys-equiv-when-not-keysp
                                    ,@fi-bindings))))))

                  ;; `RECOGNIZER'
                  (defthm ,recognizer-tp
                    (booleanp (,recognizer ,hash-table))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::recognizer/copyable-tp
                                'lem-hash-table$a::recognizer/unique-tp)
                           ,@fi-bindings))))

                  (defthm ,recognizer-cr
                    (implies (,recognizer ,hash-table)
                             ,(if copyable
                                  `(and (consp ,hash-table)
                                        (true-listp ,hash-table))
                                  `(true-listp ,hash-table)))
                    :rule-classes :compound-recognizer
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::recognizer/copyable-cr
                                'lem-hash-table$a::recognizer/unique-cr)
                           ,@fi-bindings))))

                  (defthm ,recognizer-of-creator
                    (,recognizer (,creator))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::recognizer/copyable-of-creator/copyable
                                'lem-hash-table$a::recognizer/unique-of-creator/unique)
                           ,@fi-bindings))))

                  (defthm ,recognizer-of-fixer
                    (,recognizer (,fixer ,hash-table))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::recognizer/copyable-of-fixer/copyable
                                'lem-hash-table$a::recognizer/unique-of-fixer/unique)
                           ,@fi-bindings))))

                  (defthm ,recognizer-of-updater
                    (,recognizer (,updater ,key ,val ,hash-table))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::recognizer/copyable-of-updater/copyable
                                'lem-hash-table$a::recognizer/unique-of-updater/unique)
                           ,@fi-bindings))))

                  (defthm ,recognizer-of-remover
                    (,recognizer (,remover ,key ,hash-table))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::recognizer/copyable-of-remover/copyable
                                'lem-hash-table$a::recognizer/unique-of-remover/unique)
                           ,@fi-bindings))))

                  ,@(and copyable
                         `((defthm ,recognizer-of-keys-set
                             (,recognizer (,keys-set ,set ,hash-table))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::recognizer/copyable-of-keys-set
                                    ,@fi-bindings))))))

                  ;; `FIXER'
                  (defthm ,fixer-tp
                    ,(if copyable
                         `(and (consp (,fixer ,hash-table))
                               (true-listp (,fixer ,hash-table)))
                         `(true-listp (,fixer ,hash-table)))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::fixer/copyable-tp
                                'lem-hash-table$a::fixer/unique-tp)
                           ,@fi-bindings))))

                  (defthm ,fixer-when-recognizer
                    (implies (,recognizer ,hash-table)
                             (equal (,fixer ,hash-table)
                                    ,hash-table))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::fixer/copyable-when-recognizer/copyable
                                'lem-hash-table$a::fixer/unique-when-recognizer/unique)
                           ,@fi-bindings))))

                  (defthm ,fixer-when-not-recognizer
                    (implies (not (,recognizer ,hash-table))
                             (equal (,fixer ,hash-table)
                                    (,creator)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::fixer/copyable-when-not-recognizer/copyable
                                'lem-hash-table$a::fixer/unique-when-not-recognizer/unique)
                           ,@fi-bindings))))

                  ;; `EQUIV'
                  (defthm ,equiv-tp
                    (booleanp (,equiv ,%hash-table ,hash-table))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::equiv/copyable-tp
                                'lem-hash-table$a::equiv/unique-tp)
                           ,@fi-bindings))))

                  (defequiv ,equiv
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::equiv/copyable-is-an-equivalence
                                'lem-hash-table$a::equiv/unique-is-an-equivalence)
                           ,@fi-bindings))))

                  (defcong ,equiv equal (,fixer ,hash-table) 1
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::equiv/copyable-implies-equal-fixer/copyable-1
                                'lem-hash-table$a::equiv/unique-implies-equal-fixer/unique-1)
                           ,@fi-bindings))))

                  (defthm ,fixer-mod-equiv
                    (,equiv (,fixer ,hash-table) ,hash-table)
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::fixer/copyable-mod-equiv/copyable
                                'lem-hash-table$a::fixer/unique-mod-equiv/unique)
                           ,@fi-bindings))))

                  (defthm ,equiv-when-not-recognizer
                    (implies (not (,recognizer ,hash-table))
                             (,equiv ,hash-table (,creator)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::equiv/copyable-when-not-recognizer/copyable
                                'lem-hash-table$a::equiv/unique-when-not-recognizer/unique)
                           ,@fi-bindings))))

                  ;; `ACCESSOR'
                  ,@(and val-recognizer
                         `((defthm ,val-recognizer-of-accessor
                             (,val-recognizer (,accessor ,key ,hash-table))
                             :rule-classes
                             (:rewrite
                              :type-prescription)
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    ,(if copyable
                                         'lem-hash-table$a::val-recognizer-of-accessor/copyable
                                         'lem-hash-table$a::val-recognizer-of-accessor/unique)
                                    ,@fi-bindings))))))

                  ,@(and key-recognizer
                         key-fixer
                         (not (eq key-equiv 'equal))
                         `((defcong ,key-equiv equal (,accessor ,key ,hash-table) 1
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    ,(if copyable
                                         'lem-hash-table$a::key-equiv-implies-equal-accessor/copyable-1
                                         'lem-hash-table$a::key-equiv-implies-equal-accessor/unique-1)
                                    ,@fi-bindings))))))

                  (defcong ,equiv equal (,accessor ,key ,hash-table) 2
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::equiv/copyable-implies-equal-accessor/copyable-2
                                'lem-hash-table$a::equiv/unique-implies-equal-accessor/unique-2)
                           ,@fi-bindings))))

                  ,@(and key-recognizer
                         `((defthmd ,accessor-when-not-key-recognizer
                             (implies (not (,key-recognizer ,key))
                                      (equal (,accessor ,key ,hash-table)
                                             (,accessor ,default-key ,hash-table)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    ,(if copyable
                                         'lem-hash-table$a::accessor/copyable-when-not-key-recognizer
                                         'lem-hash-table$a::accessor/unique-when-not-key-recognizer)
                                    ,@fi-bindings))))))

                  (defthmd ,accessor-when-not-recognizer
                    (implies (not (,recognizer ,hash-table))
                             (equal (,accessor ,key ,hash-table)
                                    ,default-val))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::accessor/copyable-when-not-recognizer/copyable
                                'lem-hash-table$a::accessor/unique-when-not-recognizer/unique)
                           ,@fi-bindings))))

                  (defthm ,accessor-of-creator
                    (equal (,accessor ,key (,creator))
                           ,default-val)
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::accessor/copyable-of-creator/copyable
                                'lem-hash-table$a::accessor/unique-of-creator/unique)
                           ,@fi-bindings))))

                  (defthmd ,accessor-of-updater
                    (equal (,accessor ,%key (,updater ,key ,val ,hash-table))
                           (if (,key-equiv ,%key ,key)
                               ,(if val-fixer
                                    `(,val-fixer ,val)
                                    val)
                               (,accessor ,%key ,hash-table)))
                    :rule-classes
                    ((:rewrite :corollary
                               (equal (,accessor ,%key (,updater ,key ,val ,hash-table))
                                      (if (,key-equiv ,%key ,(if (eq key-equiv 'equal)
                                                                 key
                                                                 `(double-rewrite ,key)))
                                          ,(if val-fixer
                                               `(,val-fixer (double-rewrite ,val))
                                               val)
                                          (,accessor ,%key (double-rewrite ,hash-table))))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::accessor/copyable-of-updater/copyable
                                'lem-hash-table$a::accessor/unique-of-updater/unique)
                           ,@fi-bindings))))

                  (defthm ,accessor-of-updater-same
                    (implies (,key-equiv ,%key ,key)
                             (equal (,accessor ,%key (,updater ,key ,val ,hash-table))
                                    ,(if val-fixer
                                         `(,val-fixer ,val)
                                         val)))
                    :rule-classes
                    ((:rewrite :corollary
                               (implies (,key-equiv ,%key ,(if (eq key-equiv 'equal)
                                                               key
                                                               `(double-rewrite ,key)))
                                        (equal (,accessor ,%key (,updater ,key ,val ,hash-table))
                                               ,(if val-fixer
                                                    `(,val-fixer (double-rewrite ,val))
                                                    val)))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::accessor/copyable-of-updater/copyable-same
                                'lem-hash-table$a::accessor/unique-of-updater/unique-same)
                           ,@fi-bindings))))

                  (defthm ,accessor-of-updater-diff
                    (implies (not (,key-equiv ,%key ,key))
                             (equal (,accessor ,%key (,updater ,key ,val ,hash-table))
                                    (,accessor ,%key ,hash-table)))
                    :rule-classes
                    ((:rewrite :corollary
                               (implies (not (,key-equiv ,%key ,(if (eq key-equiv 'equal)
                                                                    key
                                                                    `(double-rewrite ,key))))
                                        (equal (,accessor ,%key (,updater ,key ,val ,hash-table))
                                               (,accessor ,%key (double-rewrite ,hash-table))))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::accessor/copyable-of-updater/copyable-diff
                                'lem-hash-table$a::accessor/unique-of-updater/unique-diff)
                           ,@fi-bindings))))

                  (defthmd ,accessor-when-not-boundp
                    (implies (not (,boundp ,key ,hash-table))
                             (equal (,accessor ,key ,hash-table)
                                    ,default-val))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::accessor/copyable-when-not-boundp/copyable
                                'lem-hash-table$a::accessor/unique-when-not-boundp/unique)
                           ,@fi-bindings))))

                  (defthmd ,accessor-of-remover
                    (equal (,accessor ,%key (,remover ,key ,hash-table))
                           (if (,key-equiv ,%key ,key)
                               ,default-val
                               (,accessor ,%key ,hash-table)))
                    :rule-classes
                    ((:rewrite :corollary
                               (equal (,accessor ,%key (,remover ,key ,hash-table))
                                      (if (,key-equiv ,%key ,(if (eq key-equiv 'equal)
                                                                 key
                                                                 `(double-rewrite ,key)))
                                          ,default-val
                                          (,accessor ,%key (double-rewrite ,hash-table))))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::accessor/copyable-of-remover/copyable
                                'lem-hash-table$a::accessor/unique-of-remover/unique)
                           ,@fi-bindings))))

                  (defthm ,accessor-of-remover-same
                    (implies (,key-equiv ,%key ,key)
                             (equal (,accessor ,%key (,remover ,key ,hash-table))
                                    ,default-val))
                    :rule-classes
                    ((:rewrite :corollary
                               (implies (,key-equiv ,%key ,(if (eq key-equiv 'equal)
                                                               key
                                                               `(double-rewrite ,key)))
                                        (equal (,accessor ,%key (,remover ,key ,hash-table))
                                               ,default-val))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::accessor/copyable-of-remover/copyable-same
                                'lem-hash-table$a::accessor/unique-of-remover/unique-same)
                           ,@fi-bindings))))

                  (defthm ,accessor-of-remover-diff
                    (implies (not (,key-equiv ,%key ,key))
                             (equal (,accessor ,%key (,remover ,key ,hash-table))
                                    (,accessor ,%key ,hash-table)))
                    :rule-classes
                    ((:rewrite :corollary
                               (implies (not (,key-equiv ,%key ,(if (eq key-equiv 'equal)
                                                                    key
                                                                    `(double-rewrite ,key))))
                                        (equal (,accessor ,%key (,remover ,key ,hash-table))
                                               (,accessor ,%key (double-rewrite ,hash-table))))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::accessor/copyable-of-remover/copyable-diff
                                'lem-hash-table$a::accessor/unique-of-remover/unique-diff)
                           ,@fi-bindings))))

                  ,@(and copyable
                         `((defthm ,accessor-of-keys-set
                             (equal (,accessor ,key (,keys-set ,set ,hash-table))
                                    (,accessor ,key ,hash-table))
                             :rule-classes
                             ((:rewrite :corollary
                                        (equal (,accessor ,key (,keys-set ,set ,hash-table))
                                               (,accessor ,key (double-rewrite ,hash-table)))))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::accessor/copyable-of-keys-set
                                    ,@fi-bindings))))))

                  (defthmd ,accessor-when-count-is-zero
                    (implies (equal (,count ,hash-table) 0)
                             (equal (,accessor ,key ,hash-table)
                                    ,default-val))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::accessor/copyable-when-count/copyable-is-zero
                                'lem-hash-table$a::accessor/unique-when-count/unique-is-zero)
                           ,@fi-bindings))))

                  ;; `UPDATER'
                  (defthm ,updater-tp
                    ,(if copyable
                         `(and (consp (,updater ,key ,val ,hash-table))
                               (true-listp (,updater ,key ,val ,hash-table)))
                         `(true-listp (,updater ,key ,val ,hash-table)))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::updater/copyable-tp
                                'lem-hash-table$a::updater/unique-tp)
                           ,@fi-bindings))))

                  ,@(and key-recognizer
                         key-fixer
                         (not (eq key-equiv 'equal))
                         `((defcong ,key-equiv equal (,updater ,key ,val ,hash-table) 1
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    ,(if copyable
                                         'lem-hash-table$a::key-equiv-implies-equal-updater/copyable-1
                                         'lem-hash-table$a::key-equiv-implies-equal-updater/unique-1)
                                    ,@fi-bindings))))))

                  ,@(and val-recognizer
                         val-fixer
                         (not (eq val-equiv 'equal))
                         `((defcong ,val-equiv equal (,updater ,key ,val ,hash-table) 2
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    ,(if copyable
                                         'lem-hash-table$a::val-equiv-implies-equal-updater/copyable-2
                                         'lem-hash-table$a::val-equiv-implies-equal-updater/unique-2)
                                    ,@fi-bindings))))))

                  (defcong ,equiv equal (,updater ,key ,val ,hash-table) 3
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::equiv/copyable-implies-equal-updater/copyable-3
                                'lem-hash-table$a::equiv/unique-implies-equal-updater/unique-3)
                           ,@fi-bindings))))

                  ,@(and key-recognizer
                         `((defthmd ,updater-when-not-key-recognizer
                             (implies (not (,key-recognizer ,key))
                                      (equal (,updater ,key ,val ,hash-table)
                                             (,updater ,default-key ,val ,hash-table)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    ,(if copyable
                                         'lem-hash-table$a::updater/copyable-when-not-key-recognizer
                                         'lem-hash-table$a::updater/unique-when-not-key-recognizer)
                                    ,@fi-bindings))))))

                  ,@(and val-recognizer
                         `((defthmd ,updater-when-not-val-recognizer
                             (implies (not (,val-recognizer ,val))
                                      (equal (,updater ,key ,val ,hash-table)
                                             (,updater ,key ,default-val ,hash-table)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    ,(if copyable
                                         'lem-hash-table$a::updater/copyable-when-not-val-recognizer
                                         'lem-hash-table$a::updater/unique-when-not-val-recognizer)
                                    ,@fi-bindings))))))

                  (defthmd ,updater-when-not-recognizer
                    (implies (not (,recognizer ,hash-table))
                             (equal (,updater ,key ,val ,hash-table)
                                    (,updater ,key ,val (,creator))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::updater/copyable-when-not-recognizer/copyable
                                'lem-hash-table$a::updater/unique-when-not-recognizer/unique)
                           ,@fi-bindings))))

                  (defthmd ,updater-of-accessor-when-boundp-free
                    (implies (and (,boundp ,key ,hash-table)
                                  (,val-equiv ,val (,accessor ,key ,hash-table)))
                             (equal (,updater ,key ,val ,hash-table)
                                    (,fixer ,hash-table)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::updater/copyable-of-accessor/copyable-when-boundp/copyable-free
                                'lem-hash-table$a::updater/unique-of-accessor/unique-when-boundp/unique-free)
                           ,@fi-bindings))))

                  (defthmd ,updater-of-accessor
                    (implies (,key-equiv ,%key ,key)
                             (equal (,updater ,%key (,accessor ,key ,hash-table) ,hash-table)
                                    (if (,boundp ,%key ,hash-table)
                                        (,fixer ,hash-table)
                                        (,updater ,%key ,default-val ,hash-table))))
                    :rule-classes
                    ((:rewrite :corollary
                               (implies (case-split (,key-equiv ,%key ,key))
                                        (equal (,updater ,%key (,accessor ,key ,hash-table) ,hash-table)
                                               (if (,boundp ,%key ,hash-table)
                                                   (,fixer ,hash-table)
                                                   (,updater ,%key ,default-val ,hash-table))))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::updater/copyable-of-accessor/copyable
                                'lem-hash-table$a::updater/unique-of-accessor/unique)
                           ,@fi-bindings))))

                  (defthm ,updater-of-accessor-when-boundp
                    (implies (and (,boundp ,%key ,hash-table)
                                  (,key-equiv ,%key ,key)
                                  (,equiv ,%hash-table ,hash-table))
                             (equal (,updater ,%key (,accessor ,key ,%hash-table) ,hash-table)
                                    (,fixer ,hash-table)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::updater/copyable-of-accessor/copyable-when-boundp/copyable
                                'lem-hash-table$a::updater/unique-of-accessor/unique-when-boundp/unique)
                           ,@fi-bindings))))

                  (defthm ,updater-of-accessor-when-not-boundp
                    (implies (and (not (,boundp ,%key ,hash-table))
                                  (,key-equiv ,%key ,key))
                             (equal (,updater ,%key (,accessor ,key ,hash-table) ,hash-table)
                                    (,updater ,%key ,default-val ,hash-table)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::updater/copyable-of-accessor/copyable-when-not-boundp/copyable
                                'lem-hash-table$a::updater/unique-of-accessor/unique-when-not-boundp/unique)
                           ,@fi-bindings))))

                  (defthmd ,updater-of-updater
                    (equal (,updater ,%key ,%val (,updater ,key ,val ,hash-table))
                           (if (,key-equiv ,%key ,key)
                               (,updater ,%key ,%val ,hash-table)
                               (,updater ,key ,val (,updater ,%key ,%val ,hash-table))))
                    :rule-classes
                    ((:rewrite :loop-stopper ((,%key ,key ,updater))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::updater/copyable-of-updater/copyable
                                'lem-hash-table$a::updater/unique-of-updater/unique)
                           ,@fi-bindings))))

                  (defthm ,updater-of-updater-same
                    (implies (,key-equiv ,%key ,key)
                             (equal (,updater ,%key ,%val (,updater ,key ,val ,hash-table))
                                    (,updater ,%key ,%val ,hash-table)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::updater/copyable-of-updater/copyable-same
                                'lem-hash-table$a::updater/unique-of-updater/unique-same)
                           ,@fi-bindings))))

                  (defthm ,updater-of-updater-diff
                    (implies (not (,key-equiv ,%key ,key))
                             (equal (,updater ,%key ,%val (,updater ,key ,val ,hash-table))
                                    (,updater ,key ,val (,updater ,%key ,%val ,hash-table))))
                    :rule-classes
                    ((:rewrite :loop-stopper ((,%key ,key ,updater))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::updater/copyable-of-updater/copyable-diff
                                'lem-hash-table$a::updater/unique-of-updater/unique-diff)
                           ,@fi-bindings))))

                  (defthm ,updater-of-remover-same
                    (implies (,key-equiv ,%key ,key)
                             (equal (,updater ,%key ,val (,remover ,key ,hash-table))
                                    (,updater ,%key ,val ,hash-table)))
                    :rule-classes
                    ((:rewrite :corollary
                               (implies (,key-equiv ,%key ,(if (eq key-equiv 'equal)
                                                               key
                                                               `(double-rewrite ,key)))
                                        (equal (,updater ,%key ,val (,remover ,key ,hash-table))
                                               (,updater ,%key ,val (double-rewrite ,hash-table))))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::updater/copyable-of-remover/copyable-same
                                'lem-hash-table$a::updater/unique-of-remover/unique-same)
                           ,@fi-bindings))))

                  ;; `BOUNDP'
                  (defthm ,boundp-tp
                    (booleanp (,boundp ,key ,hash-table))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::boundp/copyable-tp
                                'lem-hash-table$a::boundp/unique-tp)
                           ,@fi-bindings))))

                  ,@(and key-recognizer
                         key-fixer
                         (not (eq key-equiv 'equal))
                         `((defcong ,key-equiv equal (,boundp ,key ,hash-table) 1
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    ,(if copyable
                                         'lem-hash-table$a::key-equiv-implies-equal-boundp/copyable-1
                                         'lem-hash-table$a::key-equiv-implies-equal-boundp/unique-1)
                                    ,@fi-bindings))))))

                  (defcong ,equiv equal (,boundp ,key ,hash-table) 2
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::equiv/copyable-implies-equal-boundp/copyable-2
                                'lem-hash-table$a::equiv/unique-implies-equal-boundp/unique-2)
                           ,@fi-bindings))))

                  ,@(and key-recognizer
                         `((defthmd ,boundp-when-not-key-recognizer
                             (implies (not (,key-recognizer ,key))
                                      (equal (,boundp ,key ,hash-table)
                                             (,boundp ,default-key ,hash-table)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    ,(if copyable
                                         'lem-hash-table$a::boundp/copyable-when-not-key-recognizer
                                         'lem-hash-table$a::boundp/unique-when-not-key-recognizer)
                                    ,@fi-bindings))))))

                  (defthmd ,boundp-when-not-recognizer
                    (implies (not (,recognizer ,hash-table))
                             (not (,boundp ,key ,hash-table)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::boundp/copyable-when-not-recognizer/copyable
                                'lem-hash-table$a::boundp/unique-when-not-recognizer/unique)
                           ,@fi-bindings))))

                  (defthm ,boundp-of-creator
                    (not (,boundp ,key (,creator)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::boundp/copyable-of-creator/copyable
                                'lem-hash-table$a::boundp/unique-of-creator/unique)
                           ,@fi-bindings))))

                  (defthmd ,boundp-of-updater
                    (equal (,boundp ,%key (,updater ,key ,val ,hash-table))
                           (if (,key-equiv ,%key ,key)
                               t
                               (,boundp ,%key ,hash-table)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::boundp/copyable-of-updater/copyable
                                'lem-hash-table$a::boundp/unique-of-updater/unique)
                           ,@fi-bindings))))

                  (defthm ,boundp-of-updater-same
                    (implies (,key-equiv ,%key ,key)
                             (equal (,boundp ,%key (,updater ,key ,val ,hash-table))
                                    t))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::boundp/copyable-of-updater/copyable-same
                                'lem-hash-table$a::boundp/unique-of-updater/unique-same)
                           ,@fi-bindings))))

                  (defthm ,boundp-of-updater-diff
                    (implies (not (,key-equiv ,%key ,key))
                             (equal (,boundp ,%key (,updater ,key ,val ,hash-table))
                                    (,boundp ,%key ,hash-table)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::boundp/copyable-of-updater/copyable-diff
                                'lem-hash-table$a::boundp/unique-of-updater/unique-diff)
                           ,@fi-bindings))))

                  (defthmd ,boundp-of-remover
                    (equal (,boundp ,%key (,remover ,key ,hash-table))
                           (if (,key-equiv ,%key ,key)
                               nil
                               (,boundp ,%key ,hash-table)))
                    :rule-classes
                    ((:rewrite :corollary
                               (equal (,boundp ,%key (,remover ,key ,hash-table))
                                      (if (,key-equiv ,%key ,(if (eq key-equiv 'equal)
                                                                 key
                                                                 `(double-rewrite ,key)))
                                          nil
                                          (,boundp ,%key (double-rewrite ,hash-table))))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::boundp/copyable-of-remover/copyable
                                'lem-hash-table$a::boundp/unique-of-remover/unique)
                           ,@fi-bindings))))

                  (defthm ,boundp-of-remover-same
                    (implies (,key-equiv ,%key ,key)
                             (not (,boundp ,%key (,remover ,key ,hash-table))))
                    :rule-classes
                    ((:rewrite :corollary
                               (implies (,key-equiv ,%key ,(if (eq key-equiv 'equal)
                                                               key
                                                               `(double-rewrite ,key)))
                                        (not (,boundp ,%key (,remover ,key ,hash-table))))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::boundp/copyable-of-remover/copyable-same
                                'lem-hash-table$a::boundp/unique-of-remover/unique-same)
                           ,@fi-bindings))))

                  (defthm ,boundp-of-remover-diff
                    (implies (not (,key-equiv ,%key ,key))
                             (equal (,boundp ,%key (,remover ,key ,hash-table))
                                    (,boundp ,%key ,hash-table)))
                    :rule-classes
                    ((:rewrite :corollary
                               (implies (not (,key-equiv ,%key ,(if (eq key-equiv 'equal)
                                                                    key
                                                                    `(double-rewrite ,key))))
                                        (equal (,boundp ,%key (,remover ,key ,hash-table))
                                               (,boundp ,%key (double-rewrite ,hash-table))))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::boundp/copyable-of-remover/copyable-diff
                                'lem-hash-table$a::boundp/unique-of-remover/unique-diff)
                           ,@fi-bindings))))

                  ,@(and copyable
                         `((defthm ,boundp-of-keys-set
                             (equal (,boundp ,key (,keys-set ,set ,hash-table))
                                    (,boundp ,key ,hash-table))
                             :rule-classes
                             ((:rewrite :corollary
                                        (equal (,boundp ,key (,keys-set ,set ,hash-table))
                                               (,boundp ,key (double-rewrite ,hash-table)))))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::boundp/copyable-of-keys-set
                                    ,@fi-bindings))))))

                  (defthmd ,boundp-when-count-is-zero
                    (implies (equal (,count ,hash-table) 0)
                             (not (,boundp ,key ,hash-table)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::boundp/copyable-when-count/copyable-is-zero
                                'lem-hash-table$a::boundp/unique-when-count/unique-is-zero)
                           ,@fi-bindings))))

                  ;; `GETP'
                  (defthm ,getp-tp
                    (and (consp (,getp ,key ,hash-table))
                         (true-listp (,getp ,key ,hash-table)))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::getp/copyable-tp
                                'lem-hash-table$a::getp/unique-tp)
                           ,@fi-bindings))))

                  (defthm ,getp-rw
                    (mv-let (v0 v1)
                            (,getp ,key ,hash-table)
                      (and (equal v0 (,accessor ,key ,hash-table))
                           (equal v1 (,boundp ,key ,hash-table))))
                    :rule-classes
                    ((:rewrite :corollary
                               (mv-let (v0 v1)
                                       (,getp ,key ,hash-table)
                                 (and (equal v0 (,accessor (double-rewrite ,key) (double-rewrite ,hash-table)))
                                      (equal v1 (,boundp (double-rewrite ,key) (double-rewrite ,hash-table)))))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::getp/copyable-rw
                                'lem-hash-table$a::getp/unique-rw)
                           ,@fi-bindings))))

                  ;; `REMOVER'
                  (defthm ,remover-tp
                    ,(if copyable
                         `(and (consp (,remover ,key ,hash-table))
                               (true-listp (,remover ,key ,hash-table)))
                         `(true-listp (,remover ,key ,hash-table)))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::remover/copyable-tp
                                'lem-hash-table$a::remover/unique-tp)
                           ,@fi-bindings))))

                  ,@(and key-recognizer
                         key-fixer
                         (not (eq key-equiv 'equal))
                         `((defcong ,key-equiv equal (,remover ,key ,hash-table) 1
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    ,(if copyable
                                         'lem-hash-table$a::key-equiv-implies-equal-remover/copyable-1
                                         'lem-hash-table$a::key-equiv-implies-equal-remover/unique-1)
                                    ,@fi-bindings))))))

                  (defcong ,equiv equal (,remover ,key ,hash-table) 2
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::equiv/copyable-implies-equal-remover/copyable-2
                                'lem-hash-table$a::equiv/unique-implies-equal-remover/unique-2)
                           ,@fi-bindings))))

                  ,@(and key-recognizer
                         `((defthmd ,remover-when-not-key-recognizer
                             (implies (not (,key-recognizer ,key))
                                      (equal (,remover ,key ,hash-table)
                                             (,remover ,default-key ,hash-table)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    ,(if copyable
                                         'lem-hash-table$a::remover/copyable-when-not-key-recognizer
                                         'lem-hash-table$a::remover/unique-when-not-key-recognizer)
                                    ,@fi-bindings))))))

                  (defthmd ,remover-when-not-recognizer
                    (implies (not (,recognizer ,hash-table))
                             (equal (,remover ,key ,hash-table)
                                    (,creator)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::remover/copyable-when-not-recognizer/copyable
                                'lem-hash-table$a::remover/unique-when-not-recognizer/unique)
                           ,@fi-bindings))))

                  (defthm ,remover-of-creator
                    (equal (,remover ,key (,creator))
                           (,creator))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::remover/copyable-of-creator/copyable
                                'lem-hash-table$a::remover/unique-of-creator/unique)
                           ,@fi-bindings))))

                  (defthmd ,remover-of-updater
                    (equal (,remover ,%key (,updater ,key ,val ,hash-table))
                           (if (,key-equiv ,%key ,key)
                               (,remover ,%key ,hash-table)
                               (,updater ,key ,val (,remover ,%key ,hash-table))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::remover/copyable-of-updater/copyable
                                'lem-hash-table$a::remover/unique-of-updater/unique)
                           ,@fi-bindings))))

                  (defthm ,remover-of-updater-same
                    (implies (,key-equiv ,%key ,key)
                             (equal (,remover ,%key (,updater ,key ,val ,hash-table))
                                    (,remover ,%key ,hash-table)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::remover/copyable-of-updater/copyable-same
                                'lem-hash-table$a::remover/unique-of-updater/unique-same)
                           ,@fi-bindings))))

                  (defthm ,remover-of-updater-diff
                    (implies (not (,key-equiv ,%key ,key))
                             (equal (,remover ,%key (,updater ,key ,val ,hash-table))
                                    (,updater ,key ,val (,remover ,%key ,hash-table))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::remover/copyable-of-updater/copyable-diff
                                'lem-hash-table$a::remover/unique-of-updater/unique-diff)
                           ,@fi-bindings))))

                  (defthmd ,remover-when-not-boundp
                    (implies (not (,boundp ,key ,hash-table))
                             (equal (,remover ,key ,hash-table)
                                    (,fixer ,hash-table)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::remover/copyable-when-not-boundp/copyable
                                'lem-hash-table$a::remover/unique-when-not-boundp/unique)
                           ,@fi-bindings))))

                  (defthmd ,remover-of-remover
                    (equal (,remover ,%key (,remover ,key ,hash-table))
                           (if (,key-equiv ,%key ,key)
                               (,remover ,%key ,hash-table)
                               (,remover ,key (,remover ,%key ,hash-table))))
                    :rule-classes
                    ((:rewrite :loop-stopper ((,%key ,key ,remover))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::remover/copyable-of-remover/copyable
                                'lem-hash-table$a::remover/unique-of-remover/unique)
                           ,@fi-bindings))))

                  (defthm ,remover-of-remover-same
                    (implies (,key-equiv ,%key ,key)
                             (equal (,remover ,%key (,remover ,key ,hash-table))
                                    (,remover ,%key ,hash-table)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::remover/copyable-of-remover/copyable-same
                                'lem-hash-table$a::remover/unique-of-remover/unique-same)
                           ,@fi-bindings))))

                  (defthm ,remover-of-remover-diff
                    (implies (not (,key-equiv ,%key ,key))
                             (equal (,remover ,%key (,remover ,key ,hash-table))
                                    (,remover ,key (,remover ,%key ,hash-table))))
                    :rule-classes
                    ((:rewrite :loop-stopper ((,%key ,key ,remover))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::remover/copyable-of-remover/copyable-diff
                                'lem-hash-table$a::remover/unique-of-remover/unique-diff)
                           ,@fi-bindings))))

                  (defthmd ,remover-when-count-is-zero
                    (implies (equal (,count ,hash-table) 0)
                             (equal (,remover ,key ,hash-table)
                                    ,(if copyable
                                         `(,keys-set (,keys ,hash-table)
                                                     (,creator))
                                         `(,creator))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::remover/copyable-when-count/copyable-is-zero
                                'lem-hash-table$a::remover/unique-when-count/unique-is-zero)
                           ,@fi-bindings))))

                  ;; `COUNT'
                  (defthm ,count-tp
                    (natp (,count ,hash-table))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::count/copyable-tp
                                'lem-hash-table$a::count/unique-tp)
                           ,@fi-bindings))))

                  (defcong ,equiv equal (,count ,hash-table) 1
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::equiv/copyable-implies-equal-count/copyable-1
                                'lem-hash-table$a::equiv/unique-implies-equal-count/unique-1)
                           ,@fi-bindings))))

                  (defthmd ,count-when-not-recognizer
                    (implies (not (,recognizer ,hash-table))
                             (equal (,count ,hash-table)
                                    0))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::count/copyable-when-not-recognizer/copyable
                                'lem-hash-table$a::count/unique-when-not-recognizer/unique)
                           ,@fi-bindings))))

                  (defthm ,count-of-creator
                    (equal (,count (,creator))
                           0)
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::count/copyable-of-creator/copyable
                                'lem-hash-table$a::count/unique-of-creator/unique)
                           ,@fi-bindings))))

                  (defthmd ,count-of-updater
                    (equal (,count (,updater ,key ,val ,hash-table))
                           (if (,boundp ,key ,hash-table)
                               (,count ,hash-table)
                               (1+ (,count ,hash-table))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::count/copyable-of-updater/copyable
                                'lem-hash-table$a::count/unique-of-updater/unique)
                           ,@fi-bindings))))

                  (defthm ,count-of-updater-when-boundp
                    (implies (,boundp ,key ,hash-table)
                             (equal (,count (,updater ,key ,val ,hash-table))
                                    (,count ,hash-table)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::count/copyable-of-updater/copyable-when-boundp/copyable
                                'lem-hash-table$a::count/unique-of-updater/unique-when-boundp/unique)
                           ,@fi-bindings))))

                  (defthm ,count-of-updater-when-not-boundp
                    (implies (not (,boundp ,key ,hash-table))
                             (equal (,count (,updater ,key ,val ,hash-table))
                                    (1+ (,count ,hash-table))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::count/copyable-of-updater/copyable-when-not-boundp/copyable
                                'lem-hash-table$a::count/unique-of-updater/unique-when-not-boundp/unique)
                           ,@fi-bindings))))

                  (defthmd ,count-when-boundp
                    (implies (,boundp ,key ,hash-table)
                             (posp (,count ,hash-table)))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::count/copyable-when-boundp/copyable
                                'lem-hash-table$a::count/unique-when-boundp/unique)
                           ,@fi-bindings))))

                  (defthmd ,count-of-remover
                    (equal (,count (,remover ,key ,hash-table))
                           (if (,boundp ,key ,hash-table)
                               (1- (,count ,hash-table))
                               (,count ,hash-table)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::count/copyable-of-remover/copyable
                                'lem-hash-table$a::count/unique-of-remover/unique)
                           ,@fi-bindings))))

                  (defthm ,count-of-remover-when-boundp
                    (implies (,boundp ,key ,hash-table)
                             (equal (,count (,remover ,key ,hash-table))
                                    (1- (,count ,hash-table))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::count/copyable-of-remover/copyable-when-boundp/copyable
                                'lem-hash-table$a::count/unique-of-remover/unique-when-boundp/unique)
                           ,@fi-bindings))))

                  (defthm ,count-of-remover-when-not-boundp
                    (implies (not (,boundp ,key ,hash-table))
                             (equal (,count (,remover ,key ,hash-table))
                                    (,count ,hash-table)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::count/copyable-of-remover/copyable-when-not-boundp/copyable
                                'lem-hash-table$a::count/unique-of-remover/unique-when-not-boundp/unique)
                           ,@fi-bindings))))

                  ,@(and copyable
                         `((defthm ,count-of-keys-set
                             (equal (,count (,keys-set ,set ,hash-table))
                                    (,count ,hash-table))
                             :rule-classes
                             ((:rewrite :corollary
                                        (equal (,count (,keys-set ,set ,hash-table))
                                               (,count (double-rewrite ,hash-table)))))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::count/copyable-of-keys-set
                                    ,@fi-bindings))))))

                  (defthm ,creator-when-count-is-zero
                    (implies ,(if copyable
                                  `(and (set::emptyp (,keys ,hash-table))
                                        (equal (,count ,hash-table) 0))
                                  `(equal (,count ,hash-table) 0))
                             (,equiv ,hash-table (,creator)))
                    :rule-classes
                    ((:forward-chaining :trigger-terms
                                        ((,count ,hash-table)
                                         ,@(and copyable
                                                `((set::emptyp (,keys ,hash-table)))))
                                        :corollary
                                        (implies t
                                                 (implies ,(if copyable
                                                               `(and (set::emptyp (,keys ,hash-table))
                                                                     (equal (,count ,hash-table) 0))
                                                               `(equal (,count ,hash-table) 0))
                                                          (,equiv ,hash-table (,creator))))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::creator/copyable-when-count/copyable-is-zero
                                'lem-hash-table$a::creator/unique-when-count/unique-is-zero)
                           ,@fi-bindings))))

                  ;; `CLEAR'
                  (defthm ,clear-tp
                    ,(if copyable
                         `(and (consp (,clear ,hash-table))
                               (true-listp (,clear ,hash-table)))
                         `(true-listp (,clear ,hash-table)))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::clear/copyable-tp
                                'lem-hash-table$a::clear/unique-tp)
                           ,@fi-bindings))))

                  (defthm ,clear-rw
                    (equal (,clear ,hash-table)
                           (,creator))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::clear/copyable-rw
                                'lem-hash-table$a::clear/unique-rw)
                           ,@fi-bindings))))

                  ;; `INIT'
                  (defthm ,init-tp
                    ,(if copyable
                         `(and (consp (,init ht-size rehash-size rehash-threshold ,hash-table))
                               (true-listp (,init ht-size rehash-size rehash-threshold ,hash-table)))
                         `(true-listp (,init ht-size rehash-size rehash-threshold ,hash-table)))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::init/copyable-tp
                                'lem-hash-table$a::init/unique-tp)
                           ,@fi-bindings))))

                  (defthm ,init-rw
                    (equal (,init ht-size rehash-size rehash-threshold ,hash-table)
                           (,creator))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::init/copyable-rw
                                'lem-hash-table$a::init/unique-rw)
                           ,@fi-bindings))))

                  ;; `KEYS'
                  ,@(and copyable
                         `((defthm ,keys-tp
                             (true-listp (,keys ,hash-table))
                             :rule-classes :type-prescription
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keys-tp
                                    ,@fi-bindings))))

                           (defcong ,equiv equal (,keys ,hash-table) 1
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::equiv/copyable-implies-equal-keys-1
                                    ,@fi-bindings))))

                           (defthmd ,keys-when-not-recognizer
                             (implies (not (,recognizer ,hash-table))
                                      (not (,keys ,hash-table)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keys-when-not-recognizer/copyable
                                    ,@fi-bindings))))

                           (defthm ,keys-of-creator
                             (not (,keys (,creator)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keys-of-creator/copyable
                                    ,@fi-bindings))))

                           (defthm ,keys-of-updater
                             (equal (,keys (,updater ,key ,val ,hash-table))
                                    (,keys ,hash-table))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keys-of-updater/copyable
                                    ,@fi-bindings))))

                           (defthm ,keys-of-remover
                             (equal (,keys (,remover ,key ,hash-table))
                                    (,keys ,hash-table))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keys-of-remover/copyable
                                    ,@fi-bindings))))

                           (defthm ,keys-of-keys-set
                             (equal (,keys (,keys-set ,set ,hash-table))
                                    (,keys-fix ,set))
                             :rule-classes
                             ((:rewrite :corollary
                                        (equal (,keys (,keys-set ,set ,hash-table))
                                               (,keys-fix ,(if (eq keysp 'set::setp)
                                                               set
                                                               `(double-rewrite ,set))))))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keys-of-keys-set
                                    ,@fi-bindings))))))

                  ;; `KEYS-SET'
                  ,@(and copyable
                         `((defthm ,keys-set-tp
                             (and (consp (,keys-set ,set ,hash-table))
                                  (true-listp (,keys-set ,set ,hash-table)))
                             :rule-classes :type-prescription
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keys-set-tp
                                    ,@fi-bindings))))

                           ,@(and (not (eq keys-equiv 'equal))
                                  `((defcong ,keys-equiv equal (,keys-set ,set ,hash-table) 1)))

                           (defcong ,equiv equal (,keys-set ,set ,hash-table) 2)

                           (defthmd ,keys-set-when-not-keysp
                             (implies (not (,keysp ,set))
                                      (equal (,keys-set ,set ,hash-table)
                                             (,keys-set '() ,hash-table)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keys-set-when-not-keysp
                                    ,@fi-bindings))))

                           (defthmd ,keys-set-when-not-recognizer
                             (implies (not (,recognizer ,hash-table))
                                      (equal (,keys-set ,set ,hash-table)
                                             (,keys-set ,set (,creator))))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keys-set-when-not-recognizer/copyable
                                    ,@fi-bindings))))

                           (defthm ,keys-set-of-creator
                             (implies (set::emptyp ,set)
                                      (equal (,keys-set ,set (,creator))
                                             (,creator)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keys-set-of-creator/copyable
                                    ,@fi-bindings))))

                           (defthm ,keys-set-of-updater
                             (equal (,keys-set ,set (,updater ,key ,val ,hash-table))
                                    (,updater ,key ,val (,keys-set ,set ,hash-table)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keys-set-of-updater/copyable
                                    ,@fi-bindings))))

                           (defthm ,keys-set-of-remover
                             (equal (,keys-set ,set (,remover ,key ,hash-table))
                                    (,remover ,key (,keys-set ,set ,hash-table)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keys-set-of-remover/copyable
                                    ,@fi-bindings))))

                           (defthmd ,keys-set-of-keys-free
                             (implies (,keys-equiv ,set (,keys ,hash-table))
                                      (equal (,keys-set ,set ,hash-table)
                                             (,fixer ,hash-table)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keys-set-of-keys-free
                                    ,@fi-bindings))))

                           (defthm ,keys-set-of-keys
                             (implies (,equiv ,%hash-table ,hash-table)
                                      (equal (,keys-set (,keys ,%hash-table) ,hash-table)
                                             (,fixer ,hash-table)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keys-set-of-keys
                                    ,@fi-bindings))))

                           (defthm ,keys-set-of-keys-set
                             (equal (,keys-set ,%set (,keys-set ,set ,hash-table))
                                    (,keys-set ,%set ,hash-table))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keys-set-of-keys-set
                                    ,@fi-bindings))))))

                  ;; `HASH-TABLE-EQUAL'
                  (defun-sk ,keys-equal (,%hash-table ,hash-table)
                    (declare (xargs :guard (and (,recognizer ,%hash-table)
                                                (,recognizer ,hash-table))
                                    :verify-guards nil))
                    (forall ,key
                      (equal (,boundp ,key ,%hash-table)
                             (,boundp ,key ,hash-table)))
                    :rewrite :direct)

                  (defun-sk ,vals-equal (,%hash-table ,hash-table)
                    (declare (xargs :guard (and (,recognizer ,%hash-table)
                                                (,recognizer ,hash-table))
                                    :verify-guards nil))
                    (forall ,key
                      (equal (,accessor ,key ,%hash-table)
                             (,accessor ,key ,hash-table)))
                    :rewrite :direct)

                  (defun-nx ,hash-table-equal (,%hash-table ,hash-table)
                    (declare (xargs :guard t
                                    :verify-guards nil))
                    (and (,recognizer ,%hash-table)
                         (,recognizer ,hash-table)
                         ,@(and copyable
                                `((equal (,keys ,%hash-table)
                                         (,keys ,hash-table))))
                         (= (,count ,%hash-table)
                            (,count ,hash-table))
                         (,keys-equal ,%hash-table ,hash-table)
                         (,vals-equal ,%hash-table ,hash-table)))

                  (table equality ',hash-table ',hash-table-equal)

                  (local
                    (in-theory
                      (disable ,hash-table-constraints)))

                  (defthm ,hash-table-equal-constraints
                    (and (equal (,keys-equal ,%hash-table ,hash-table)
                                ((lambda (,key ,hash-table ,%hash-table)
                                   (equal (,boundp ,key ,%hash-table)
                                          (,boundp ,key ,hash-table)))
                                 (,keys-equal-witness ,%hash-table ,hash-table)
                                 ,hash-table ,%hash-table))
                         (implies (,keys-equal ,%hash-table ,hash-table)
                                  (equal (,boundp ,key ,%hash-table)
                                         (,boundp ,key ,hash-table)))
                         (equal (,vals-equal ,%hash-table ,hash-table)
                                ((lambda (,key ,hash-table ,%hash-table)
                                   (equal (,accessor ,key ,%hash-table)
                                          (,accessor ,key ,hash-table)))
                                 (,vals-equal-witness ,%hash-table ,hash-table)
                                 ,hash-table ,%hash-table))
                         (implies (,vals-equal ,%hash-table ,hash-table)
                                  (equal (,accessor ,key ,%hash-table)
                                         (,accessor ,key ,hash-table)))
                         (equal (,hash-table-equal ,%hash-table ,hash-table)
                                (if (,recognizer ,%hash-table)
                                    (if (,recognizer ,hash-table)
                                        ,(if copyable
                                             `(if (equal (,keys ,%hash-table)
                                                         (,keys ,hash-table))
                                                  (if (equal (,count ,%hash-table)
                                                             (,count ,hash-table))
                                                      (if (,keys-equal ,%hash-table ,hash-table)
                                                          (,vals-equal ,%hash-table ,hash-table)
                                                          'nil)
                                                      'nil)
                                                  'nil)
                                             `(if (equal (,count ,%hash-table)
                                                         (,count ,hash-table))
                                                  (if (,keys-equal ,%hash-table ,hash-table)
                                                      (,vals-equal ,%hash-table ,hash-table)
                                                      'nil)
                                                  'nil))
                                        'nil)
                                    'nil)))
                    :rule-classes
                    ((:definition :corollary
                         (equal (,keys-equal ,%hash-table ,hash-table)
                                ((lambda (,key ,hash-table ,%hash-table)
                                   (equal (,boundp ,key ,%hash-table)
                                          (,boundp ,key ,hash-table)))
                                 (,keys-equal-witness ,%hash-table ,hash-table)
                                 ,hash-table ,%hash-table)))
                     (:rewrite :corollary
                               (implies (,keys-equal ,%hash-table ,hash-table)
                                        (equal (,boundp ,key ,%hash-table)
                                               (,boundp ,key ,hash-table))))
                     (:definition :corollary
                         (equal (,vals-equal ,%hash-table ,hash-table)
                                ((lambda (,key ,hash-table ,%hash-table)
                                   (equal (,accessor ,key ,%hash-table)
                                          (,accessor ,key ,hash-table)))
                                 (,vals-equal-witness ,%hash-table ,hash-table)
                                 ,hash-table ,%hash-table)))
                     (:rewrite :corollary
                               (implies (,vals-equal ,%hash-table ,hash-table)
                                        (equal (,accessor ,key ,%hash-table)
                                               (,accessor ,key ,hash-table))))
                     (:definition :corollary
                         (equal (,hash-table-equal ,%hash-table ,hash-table)
                                (if (,recognizer ,%hash-table)
                                    (if (,recognizer ,hash-table)
                                        ,(if copyable
                                             `(if (equal (,keys ,%hash-table)
                                                         (,keys ,hash-table))
                                                  (if (equal (,count ,%hash-table)
                                                             (,count ,hash-table))
                                                      (if (,keys-equal ,%hash-table ,hash-table)
                                                          (,vals-equal ,%hash-table ,hash-table)
                                                          'nil)
                                                      'nil)
                                                  'nil)
                                             `(if (equal (,count ,%hash-table)
                                                         (,count ,hash-table))
                                                  (if (,keys-equal ,%hash-table ,hash-table)
                                                      (,vals-equal ,%hash-table ,hash-table)
                                                      'nil)
                                                  'nil))
                                        'nil)
                                    'nil))))
                    :hints
                    (("Goal"
                      :in-theory (disable ,keys-equal-necc
                                          ,vals-equal-necc)
                      :use ((:instance ,keys-equal-necc)
                            (:instance ,vals-equal-necc)))))

                  (local
                    (in-theory
                      (disable ,keys-equal
                               ,vals-equal
                               ,hash-table-equal
                               (:definition ,hash-table-equal-constraints . 1)
                               (:definition ,hash-table-equal-constraints . 2))))

                  (defthm ,hash-table-equal-fc
                    (implies (,hash-table-equal ,%hash-table ,hash-table)
                             (equal ,%hash-table ,hash-table))
                    :rule-classes
                    ((:forward-chaining :trigger-terms
                                        ((,hash-table-equal ,%hash-table ,hash-table))
                                        :corollary
                                        (implies t
                                                 (implies (,hash-table-equal ,%hash-table ,hash-table)
                                                          (equal ,%hash-table ,hash-table)))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::equal/copyable-fc
                                'lem-hash-table$a::equal/unique-fc)
                           ,@fi-bindings-with-skolem))
                     ("Subgoal 3"
                      :in-theory (enable (:definition ,hash-table-equal-constraints . 2)))
                     ("Subgoal 1"
                      :in-theory (enable (:definition ,hash-table-equal-constraints . 1)))))))

              (stobj$a-property `(,hash-table (,recognizer
                                               ,creator
                                               ,fixer
                                               ,equiv)
                                              ((,key
                                                ,key-recognizer
                                                ,default-key-name
                                                ,key-fixer
                                                ,key-equiv)
                                               (,val
                                                ,val-recognizer
                                                ,(and (not stobj-property)
                                                      default-val-name)
                                                ,val-fixer
                                                ,val-equiv)
                                               (,test
                                                ,copyable)
                                               (,accessor
                                                ,updater
                                                ,boundp
                                                ,getp
                                                ,remover
                                                ,count
                                                ,clear
                                                ,init
                                                ;; HERE: update accesses to these
                                                ,@(and copyable
                                                       `((,keys
                                                          ,keys-set
                                                          ,keysp
                                                          ,keys-fix
                                                          ,keys-equiv))))))))

         `(progn
            ,@prologue

            ,body

            ,@epilogue

            (table stobj$a-property ',hash-table ',stobj$a-property)

            (table package-witness ',hash-table ',package-witness))))))
