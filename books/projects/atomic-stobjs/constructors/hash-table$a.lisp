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
(include-book "../lemmas/hash-table$a")
||#

(include-book "std/osets/top" :dir :system)

(include-book "../utilities/top")


;;;; `DEFINE-HASH-TABLE$A'
(defmacro define-hash-table$a
    (hash-table test
     &key
       (key-recognizer 'nil)
       (key-fixer 'nil)
       (key 'nil)
       (%key 'nil)
       (default-key 'nil)
       (val-recognizer 'nil)
       (val-fixer 'nil)
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
       (keys 'nil)
       (keys-set 'nil)

       (debug 'nil))

  (declare (xargs :guard (and (symbolp hash-table)
                              (symbolp test)
                              (member test '(eq eql hons-equal equal) :test 'eq)
                              (symbol-listp (list key-recognizer
                                                  key-fixer
                                                  key
                                                  val-recognizer
                                                  val-fixer
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
                                                  keys
                                                  keys-set))
                              (or copyable
                                  (and (not keysp)
                                       (not keys-fix)
                                       (not keys)
                                       (not keys-set)))
                              (booleanp debug))))

  `(with-output
     ,@(and (not debug)
            *constructor-output*)

     (make-event
       (let* ((hash-table ',hash-table)
              (%hash-table (symbolicate hash-table "%" hash-table))
              (test ',test)

              (key (or ',key
                       (symbolicate hash-table "K")))
              (%key (or ',%key
                        (symbolicate key "%" key)))
              (key-recognizer ',key-recognizer)
              (key-fixer ',key-fixer)
              (default-key-name (symbolicate hash-table "*" hash-table "-DEFAULT-KEY*"))
              (default-key default-key-name)

              (val (or ',val
                       (symbolicate hash-table "V")))
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
              (default-val-name (symbolicate hash-table "*" hash-table "-DEFAULT-VAL*"))
              (default-val (if val-creator
                               `(,val-creator)
                               default-val-name))
              (set (or ',set
                       (symbolicate hash-table "S")))
              (%set (or ',%set
                        (symbolicate set "%" set)))
              (copyable ',copyable)

              (contents ',contents)
              (recognizer ',recognizer)
              (creator ',creator)
              (fixer ',fixer)
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
              (keys ',keys)
              (keys-set ',keys-set)

              ;; Interface Symbols
              (recognizer (or recognizer
                              (symbolicate hash-table hash-table (make-predicate-suffix hash-table))))
              (creator (or creator
                           (symbolicate hash-table "CREATE-" hash-table)))
              (fixer (or fixer
                         (symbolicate hash-table hash-table "-FIX")))
              (accessor (or accessor
                            (symbolicate hash-table hash-table "-GET")))
              (updater (or updater
                           (symbolicate hash-table hash-table "-PUT")))
              (boundp (or boundp
                          (symbolicate hash-table hash-table "-BOUNDP")))
              (getp (or getp
                        (symbolicate hash-table hash-table "-GETP")))
              (remover (or remover
                           (symbolicate hash-table hash-table "-REM")))
              (count (or count
                         (symbolicate hash-table hash-table "-COUNT")))
              (clear (or clear
                         (symbolicate hash-table hash-table "-CLEAR")))
              (init (or init
                        (symbolicate hash-table hash-table "-INIT")))
              (keysp (or keysp
                         (symbolicate hash-table hash-table "-KEYS-P")))
              (keys-fix (or keys-fix
                            (symbolicate hash-table hash-table "-KEYS-FIX")))
              (keys (or keys
                        (symbolicate hash-table hash-table "-KEYS")))
              (keys-set (or keys-set
                            (symbolicate hash-table hash-table "-KEYS-SET")))
              (contents (if copyable
                            (or contents
                                (symbolicate hash-table hash-table "-CONTENTS"))
                            hash-table))
              (contents-recognizer (if copyable
                                       (symbolicate hash-table contents "-P")
                                       recognizer))
              (contents-creator (if copyable
                                    (symbolicate hash-table "CREATE-" contents)
                                    creator))
              (contents-fixer (if copyable
                                  (symbolicate hash-table contents "-FIX")
                                  fixer))
              (contents-accessor (if copyable
                                     (symbolicate hash-table contents "-GET")
                                     accessor))
              (contents-updater (if copyable
                                    (symbolicate hash-table contents "-PUT")
                                    updater))
              (contents-boundp (if copyable
                                   (symbolicate hash-table contents "-BOUNDP")
                                   boundp))
              (contents-getp (if copyable
                                 (symbolicate hash-table contents "-GETP")
                                 getp))
              (contents-remover (if copyable
                                    (symbolicate hash-table contents "-REM")
                                    remover))
              (contents-count (if copyable
                                  (symbolicate hash-table contents "-COUNT")
                                  count))
              (contents-clear (if copyable
                                  (symbolicate hash-table contents "-CLEAR")
                                  clear))
              (contents-init (if copyable
                                 (symbolicate hash-table contents "-INIT")
                                 init))

              ;; Prologue
              (hash-table-begin (symbolicate hash-table hash-table "-BEGIN"))
              (hash-table-end (symbolicate hash-table hash-table "-END"))
              (prologue
               `((deflabel ,hash-table-begin)

                 (defconst ,default-key-name ',',default-key)

                 ,@(and (not stobj-property)
                        `((defconst ,default-val-name ',',default-val)))))

              ;; Theorem Names
              (key-fixer{rewrite} (symbolicate "ATOMIC-STOBJS" key-fixer "{REWRITE}-1"))
              (val-fixer{rewrite} (symbolicate "ATOMIC-STOBJS" val-fixer "{REWRITE}-2"))

              (recognizer{type-prescription} (symbolicate hash-table recognizer "{TYPE-PRESCRIPTION}"))
              (recognizer{compound-recognizer} (symbolicate hash-table recognizer "{COMPOUND-RECOGNIZER}"))
              (recognizer-of-creator (symbolicate hash-table recognizer "-OF-" creator))
              (recognizer-of-fixer (symbolicate hash-table recognizer "-OF-" fixer))
              (recognizer-of-updater (symbolicate hash-table recognizer "-OF-" updater))
              (recognizer-of-remover (symbolicate hash-table recognizer "-OF-" remover))
              (recognizer-of-keys-set (symbolicate hash-table recognizer "-OF-" keys-set))

              (fixer{type-prescription} (symbolicate hash-table fixer "{TYPE-PRESCRIPTION}"))
              (fixer-when-recognizer (symbolicate hash-table fixer "-WHEN-" recognizer))
              (fixer-when-not-recognizer (symbolicate hash-table fixer "-WHEN-NOT-" recognizer))

              (val-recognizer-of-accessor (symbolicate hash-table val-recognizer "-OF-" accessor))
              (accessor-when-not-key-recognizer (symbolicate hash-table accessor "-WHEN-NOT-" key-recognizer))
              (accessor-when-not-recognizer (symbolicate hash-table accessor "-WHEN-NOT-" recognizer))
              (accessor-of-creator (symbolicate hash-table accessor "-OF-" creator))
              (accessor-of-key-fixer (symbolicate hash-table accessor "-OF-" key-fixer))
              (accessor-of-fixer (symbolicate hash-table accessor "-OF-" fixer))
              (accessor-of-updater (symbolicate hash-table accessor "-OF-" updater))
              (accessor-of-updater-same (symbolicate hash-table accessor-of-updater "-SAME"))
              (accessor-of-updater-diff (symbolicate hash-table accessor-of-updater "-DIFF"))
              (accessor-when-not-boundp (symbolicate hash-table accessor "-WHEN-NOT-" boundp))
              (accessor-of-remover (symbolicate hash-table accessor "-OF-" remover))
              (accessor-of-remover-same (symbolicate hash-table accessor-of-remover "-SAME"))
              (accessor-of-remover-diff (symbolicate hash-table accessor-of-remover "-DIFF"))
              (accessor-of-keys-set (symbolicate hash-table accessor "-OF-" keys-set))

              (updater{type-prescription} (symbolicate hash-table updater "{TYPE-PRESCRIPTION}"))
              (updater-when-not-key-recognizer (symbolicate hash-table updater "-WHEN-NOT-" key-recognizer))
              (updater-when-not-val-recognizer (symbolicate hash-table updater "-WHEN-NOT-" val-recognizer))
              (updater-when-not-key-recognizer (if (eq updater-when-not-key-recognizer updater-when-not-val-recognizer)
                                                   (symbolicate hash-table updater-when-not-key-recognizer "-1")
                                                   updater-when-not-key-recognizer))
              (updater-when-not-val-recognizer (if (eq updater-when-not-key-recognizer updater-when-not-val-recognizer)
                                                   (symbolicate hash-table updater-when-not-val-recognizer "-2")
                                                   updater-when-not-val-recognizer))
              (updater-when-not-recognizer (symbolicate hash-table updater "-WHEN-NOT-" recognizer))
              (updater-of-key-fixer (symbolicate hash-table updater "-OF-" key-fixer))
              (updater-of-val-fixer (symbolicate hash-table updater "-OF-" val-fixer))
              (updater-of-key-fixer (if (eq updater-of-key-fixer updater-of-val-fixer)
                                        (symbolicate hash-table updater-of-key-fixer "-1")
                                        updater-of-key-fixer))
              (updater-of-val-fixer (if (eq updater-of-key-fixer updater-of-val-fixer)
                                        (symbolicate hash-table updater-of-val-fixer "-2")
                                        updater-of-val-fixer))
              (updater-of-fixer (symbolicate hash-table updater "-OF-" fixer))
              (updater-of-accessor (symbolicate hash-table updater "-OF-" accessor))
              (updater-of-accessor-when-boundp (symbolicate hash-table updater-of-accessor "-WHEN-" boundp))
              (updater-of-accessor-when-not-boundp (symbolicate hash-table updater-of-accessor "-WHEN-NOT-" boundp))
              (updater-of-accessor-when-boundp-free (symbolicate hash-table updater-of-accessor-when-boundp "-FREE"))
              (updater-of-updater (symbolicate hash-table updater "-OF-" updater))
              (updater-of-updater-same (symbolicate hash-table updater-of-updater "-SAME"))
              (updater-of-updater-diff (symbolicate hash-table updater-of-updater "-DIFF"))
              (updater-of-remover-same (symbolicate hash-table updater "-OF-" remover "-SAME"))

              (boundp{type-prescription} (symbolicate hash-table boundp "{TYPE-PRESCRIPTION}"))
              (boundp-when-not-key-recognizer (symbolicate hash-table boundp "-WHEN-NOT-" key-recognizer))
              (boundp-when-not-recognizer (symbolicate hash-table boundp "-WHEN-NOT-" recognizer))
              (boundp-of-creator (symbolicate hash-table boundp "-OF-" creator))
              (boundp-of-key-fixer (symbolicate hash-table boundp "-OF-" key-fixer))
              (boundp-of-fixer (symbolicate hash-table boundp "-OF-" fixer))
              (boundp-of-updater (symbolicate hash-table boundp "-OF-" updater))
              (boundp-of-updater-same (symbolicate hash-table boundp-of-updater "-SAME"))
              (boundp-of-updater-diff (symbolicate hash-table boundp-of-updater "-DIFF"))
              (boundp-of-remover (symbolicate hash-table boundp "-OF-" remover))
              (boundp-of-remover-same (symbolicate hash-table boundp-of-remover "-SAME"))
              (boundp-of-remover-diff (symbolicate hash-table boundp-of-remover "-DIFF"))
              (boundp-when-zp-count (symbolicate hash-table boundp "-WHEN-ZP-" count))
              (boundp-of-keys-set (symbolicate hash-table boundp "-OF-" keys-set))

              (getp{type-prescription} (symbolicate hash-table getp "{TYPE-PRESCRIPTION}"))
              (getp{rewrite} (symbolicate hash-table getp "{REWRITE}"))

              (remover{type-prescription} (symbolicate hash-table remover "{TYPE-PRESCRIPTION}"))
              (remover-when-not-key-recognizer (symbolicate hash-table remover "-WHEN-NOT-" key-recognizer))
              (remover-when-not-recognizer (symbolicate hash-table remover "-WHEN-NOT-" recognizer))
              (remover-of-creator (symbolicate hash-table remover "-OF-" creator))
              (remover-of-key-fixer (symbolicate hash-table remover "-OF-" key-fixer))
              (remover-of-fixer (symbolicate hash-table remover "-OF-" fixer))
              (remover-of-updater (symbolicate hash-table remover "-OF-" updater))
              (remover-of-updater-same (symbolicate hash-table remover-of-updater "-SAME"))
              (remover-of-updater-diff (symbolicate hash-table remover-of-updater "-DIFF"))
              (remover-when-not-boundp (symbolicate hash-table remover "-WHEN-NOT-" boundp))
              (remover-of-remover (symbolicate hash-table remover "-OF-" remover))
              (remover-of-remover-same (symbolicate hash-table remover-of-remover "-SAME"))
              (remover-of-remover-diff (symbolicate hash-table remover-of-remover "-DIFF"))

              (count{type-prescription} (symbolicate hash-table count "{TYPE-PRESCRIPTION}"))
              (count-when-not-recognizer (symbolicate hash-table count "-WHEN-NOT-" recognizer))
              (count-of-creator (symbolicate hash-table count "-OF-" creator))
              (count-of-fixer (symbolicate hash-table count "-OF-" fixer))
              (count-of-updater (symbolicate hash-table count "-OF-" updater))
              (count-of-updater-when-boundp (symbolicate hash-table count-of-updater "-WHEN-" boundp))
              (count-of-updater-when-not-boundp (symbolicate hash-table count-of-updater "-WHEN-NOT-" boundp))
              (count-when-boundp (symbolicate hash-table count "-WHEN-" boundp))
              (count-of-remover (symbolicate hash-table count "-OF-" remover))
              (count-of-remover-when-boundp (symbolicate hash-table count-of-remover "-WHEN-" boundp))
              (count-of-remover-when-not-boundp (symbolicate hash-table count-of-remover "-WHEN-NOT-" boundp))
              (count-of-keys-set (symbolicate hash-table count "-OF-" keys-set))

              (clear{type-prescription} (symbolicate hash-table clear "{TYPE-PRESCRIPTION}"))
              (clear{rewrite} (symbolicate hash-table clear "{REWRITE}"))

              (init{type-prescription} (symbolicate hash-table init "{TYPE-PRESCRIPTION}"))
              (init{rewrite} (symbolicate hash-table init "{REWRITE}"))

              (keysp{type-prescription} (symbolicate hash-table keysp "{TYPE-PRESCRIPTION}"))
              (keysp{compound-recognizer} (symbolicate hash-table keysp "{COMPOUND-RECOGNIZER}"))
              (keysp{definition} (symbolicate hash-table keysp "{DEFINITION}"))
              (keysp-when-emptyp (symbolicate hash-table keysp "-WHEN-EMPTYP"))
              (keysp-of-keys-fix (symbolicate hash-table keysp "-OF-" keys-fix))
              (setp-when-keysp (symbolicate hash-table "SETP-WHEN-" keysp))
              (key-recognizer-of-head-when-keysp (symbolicate hash-table key-recognizer "-OF-HEAD-WHEN-" keysp))
              (keysp-of-tail-when-keysp (symbolicate hash-table keysp "-OF-TAIL-WHEN-" keysp))
              (in-when-keysp (symbolicate hash-table "IN-WHEN-" keysp))
              (in-when-keysp{case-split} (symbolicate hash-table in-when-keysp "{CASE-SPLIT}"))
              (keysp-when-subset (symbolicate hash-table keysp "-WHEN-SUBSET"))
              (keysp-of-insert (symbolicate hash-table keysp "-OF-INSERT"))
              (keysp-of-delete (symbolicate hash-table keysp "-OF-DELETE"))

              (keys-fix{type-prescription} (symbolicate hash-table keys-fix "{TYPE-PRESCRIPTION}"))
              (keys-fix-when-keysp (symbolicate hash-table keys-fix "-WHEN-" keysp))
              (keys-fix-when-not-keysp (symbolicate hash-table keys-fix "-WHEN-NOT-" keysp))

              (keys{type-prescription} (symbolicate hash-table keys "{TYPE-PRESCRIPTION}"))
              (keysp-of-keys (symbolicate hash-table (if key-recognizer keysp "SETP") "-OF-" keys))
              (keys-when-not-recognizer (symbolicate hash-table keys "-WHEN-NOT-" recognizer))
              (keys-of-creator (symbolicate hash-table keys "-OF-" creator))
              (keys-of-fixer (symbolicate hash-table keys "-OF-" fixer))
              (keys-of-updater (symbolicate hash-table keys "-OF-" updater))
              (keys-of-remover (symbolicate hash-table keys "-OF-" remover))
              (keys-of-keys-set (symbolicate hash-table keys "-OF-" keys-set))

              (keys-set{type-prescription} (symbolicate hash-table keys-set "{TYPE-PRESCRIPTION}"))
              (keys-set-when-not-keysp (symbolicate hash-table keys-set "-WHEN-NOT-" (if key-recognizer keysp "SETP")))
              (keys-set-when-not-recognizer (symbolicate hash-table keys-set "-WHEN-NOT-" recognizer))
              (keys-set-of-creator (symbolicate hash-table keys-set "-OF-" creator))
              (keys-set-of-keys-fix (symbolicate hash-table keys-set "-OF-" (if key-recognizer keys-fix "SFIX")))
              (keys-set-of-fixer (symbolicate hash-table keys-set "-OF-" fixer))
              (keys-set-of-updater (symbolicate hash-table keys-set "-OF-" updater))
              (keys-set-of-remover (symbolicate hash-table keys-set "-OF-" remover))
              (keys-set-of-keys (symbolicate hash-table keys-set "-OF-" keys))
              (keys-set-of-keys-free (symbolicate hash-table keys-set-of-keys "-FREE"))
              (keys-set-of-keys-set (symbolicate hash-table keys-set "-OF-" keys-set))

              (keys-equal (symbolicate hash-table hash-table "-KEYS-EQUAL"))
              (keys-equal-necc (symbolicate hash-table keys-equal "-NECC"))
              (keys-equal-witness (symbolicate hash-table keys-equal "-WITNESS"))
              (vals-equal (symbolicate hash-table hash-table "-VALS-EQUAL"))
              (vals-equal-necc (symbolicate hash-table vals-equal "-NECC"))
              (vals-equal-witness (symbolicate hash-table vals-equal "-WITNESS"))
              (hash-table-equal (symbolicate hash-table hash-table "-EQUAL"))
              (hash-table-equal{forward-chaining} (symbolicate hash-table hash-table-equal "{FORWARD-CHAINING}"))

              ;; Epilogue
              (hash-table-theorems (symbolicate hash-table hash-table "-THEOREMS"))
              (hash-table-definitions (symbolicate hash-table hash-table "-DEFINITIONS"))
              (hash-table-aggressive (symbolicate hash-table hash-table "-AGGRESSIVE"))
              (epilogue
               `((deflabel ,hash-table-end)

                 (deftheory-static ,hash-table-definitions
                   ',(append
                      (list contents-recognizer
                            contents-creator
                            contents-fixer
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
                           key-recognizer
                           (list keysp
                                 keys-fix))
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
                                 keys-set))))

                 (deftheory-static ,hash-table-theorems
                   (set-difference-theories
                    (set-difference-theories
                     (current-theory ',hash-table-end)
                     (current-theory ',hash-table-begin))
                    (theory ',hash-table-definitions)))

                 (deftheory-static ,hash-table-aggressive
                   ',(append
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
                           (list keys-fix
                                 in-when-keysp{case-split}))
                      (list fixer
                            accessor-when-not-recognizer
                            accessor-of-updater
                            accessor-when-not-boundp
                            accessor-of-remover
                            updater-when-not-recognizer
                            updater-of-accessor-when-boundp-free
                            updater-of-accessor
                            updater-of-updater
                            boundp-when-not-recognizer
                            boundp-of-updater
                            boundp-of-remover
                            boundp-when-zp-count
                            remover-when-not-recognizer
                            remover-of-updater
                            remover-when-not-boundp
                            remover-of-remover
                            count-when-not-recognizer
                            count-of-updater
                            count-of-remover)))

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
                (list `(lem-hash-table$a::keysp ,(if (and copyable
                                                          key-recognizer)
                                                     keysp
                                                     'set::setp))
                      `(lem-hash-table$a::keys-fix ,(if (and copyable
                                                             key-recognizer)
                                                        keys-fix
                                                        'set::sfix))
                      `(lem-hash-table$a::key-recognizer ,(or key-recognizer
                                                              '(lambda (key)
                                                                t)))
                      `(lem-hash-table$a::default-key (lambda ()
                                                        ,default-key-name))
                      `(lem-hash-table$a::key-fixer ,(or key-fixer
                                                         '(lambda (key)
                                                           key)))
                      `(lem-hash-table$a::val-recognizer ,(or val-recognizer
                                                              '(lambda (val)
                                                                t)))
                      `(lem-hash-table$a::default-val ,(or val-creator
                                                           `(lambda ()
                                                              ,default-val-name)))
                      `(lem-hash-table$a::val-fixer ,(or val-fixer
                                                         '(lambda (val)
                                                           val)))
                      `(lem-hash-table$a::recognizer/unique ,contents-recognizer)
                      `(lem-hash-table$a::creator/unique ,contents-creator)
                      `(lem-hash-table$a::fixer/unique ,contents-fixer)
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
               `(with-books (("projects/atomic-stobjs/lemmas/hash-table$a" :dir :system))

                  ,@(and key-fixer
                         key-recognizer
                         `((local
                             (defthm ,key-fixer{rewrite}
                               (equal (,key-fixer ,key)
                                      (if (,key-recognizer ,key)
                                          ,key
                                          ,default-key))))))

                  ,@(and val-fixer
                         val-recognizer
                         `((local
                             (defthm ,val-fixer{rewrite}
                               (equal (,val-fixer ,val)
                                      (if (,val-recognizer ,val)
                                          ,val
                                          ,default-val))))))

                  (local
                    (in-theory
                      (union-theories (current-theory 'acl2::ground-zero)
                                      (set-difference-theories
                                       (universal-theory :here)
                                       (universal-theory ',hash-table-begin)))))

                  ,@(and absstobj-info
                         `((local
                             (in-theory
                               (enable ,@(strip-cars (cdr absstobj-info)))))))

                  (local
                    (in-theory
                      (enable acl2::fast-<<-is-<<)))

                  ,@(and key-recognizer
                         key-fixer
                         `((local
                             (in-theory
                               (enable (:e ,key-recognizer)
                                       (:e ,key-fixer))))))

                  ,@(and val-recognizer
                         val-fixer
                         `((local
                             (in-theory
                               (enable (:e ,val-recognizer)
                                       (:e ,val-fixer))))))

                  ,@(and copyable
                         key-recognizer
                         `((defun ,keysp (,set)
                             (declare (xargs :guard t))
                             (if (atom ,set)
                                 (null ,set)
                                 (and (,key-recognizer (car ,set))
                                      (or (null (cdr ,set))
                                          (and (consp (cdr ,set))
                                               (<< (car ,set)
                                                   (cadr ,set))
                                               (,keysp (cdr ,set)))))))

                           (defun-inline ,keys-fix (,set)
                             (declare (xargs :guard (,keysp ,set)))
                             (mbe :logic (if (,keysp ,set)
                                             ,set
                                             ())
                                  :exec ,set))))

; If hash-table isn't copyable, then all "CONTENTS"-prefixed symbols refer to
; their non-prefixed base.
                  (defun ,contents-recognizer (,contents)
                    (declare (xargs :guard t))
                    (if (atom ,contents)
                        (null ,contents)
                        (and (consp (car ,contents))
                             ,@(and key-recognizer
                                    `((,key-recognizer (caar ,contents))))
                             ,@(and val-recognizer
                                    `((,val-recognizer (cdar ,contents))))
                             (or (null (cdr ,contents))
                                 (and (consp (cdr ,contents))
                                      (consp (cadr ,contents))
                                      (<< (caar ,contents) (caadr ,contents))
                                      (,contents-recognizer (cdr ,contents)))))))

                  ,@(and copyable
                         `((defun ,recognizer (,hash-table)
                             (declare (xargs :guard t))
                             (and (consp ,hash-table)
                                  ,(if key-recognizer
                                       `(,keysp (car ,hash-table))
                                       `(set::setp (car ,hash-table)))
                                  (,contents-recognizer (cdr ,hash-table))))))

                  (defun ,contents-creator ()
                    (declare (xargs :guard t))
                    '())

                  (in-theory
                    (disable (:e ,contents-creator)))

                  ,@(and copyable
                         `((defun ,creator ()
                             (declare (xargs :guard t))
                             (cons '() (,contents-creator)))

                           (in-theory
                             (disable (:e ,creator)))))

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
                        ((or (atom ,contents)
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
                        ((atom ,contents)
                         (list (cons ,key ,val)))
                        ((<< ,key (caar ,contents))
                         (cons (cons ,key ,val)
                               ,contents))
                        ((equal ,key (caar ,contents))
                         (cons (cons ,key ,val)
                               (cdr ,contents)))
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
                        ((or (atom ,contents)
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
                        ((atom ,contents)
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
                      (if (atom ,contents)
                          0
                          (1+ (,contents-count (cdr ,contents))))))

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
                             (declare (xargs :guard (and ,(if key-recognizer
                                                              `(,keysp ,set)
                                                              `(set::setp ,set))
                                                         (,recognizer ,hash-table))))
                             (let ((,set ,(if key-recognizer
                                              `(,keys-fix ,set)
                                              `(set::sfix ,set)))
                                   (,hash-table (,fixer ,hash-table)))
                               (cons ,set (cdr ,hash-table))))))

                  ;; `RECOGNIZER'
                  (defthm ,recognizer{type-prescription}
                    (booleanp (,recognizer ,hash-table))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      ,@(and (not key-recognizer)
                             `(:in-theory (enable set::setp
                                                  set::sfix
                                                  set::emptyp)))
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::recognizer/copyable{type-prescription}
                                'lem-hash-table$a::recognizer/unique{type-prescription})
                           ,@fi-bindings))))

                  (defthm ,recognizer{compound-recognizer}
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
                                'lem-hash-table$a::recognizer/copyable{compound-recognizer}
                                'lem-hash-table$a::recognizer/unique{compound-recognizer})
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
                               ,@(and (not key-recognizer)
                                      `(:in-theory (enable set::setp
                                                           set::sfix
                                                           set::emptyp)))
                               :by (:functional-instance
                                    lem-hash-table$a::recognizer/copyable-of-keys-set
                                    ,@fi-bindings))))))

                  ;; `FIXER'
                  (defthm ,fixer{type-prescription}
                    ,(if copyable
                         `(and (consp (,fixer ,hash-table))
                               (true-listp (,fixer ,hash-table)))
                         `(true-listp (,fixer ,hash-table)))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::fixer/copyable{type-prescription}
                                'lem-hash-table$a::fixer/unique{type-prescription})
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

                  ;; `ACCESSOR'
                  ,@(and val-recognizer
                         `((defthm ,val-recognizer-of-accessor
                             (,val-recognizer (,accessor ,key ,hash-table))
                             :rule-classes
                             (:rewrite
                              :type-prescription)
                             :hints
                             (("Goal"
                               ,@(and val-creator
                                      `(:in-theory (enable (:e ,val-creator))))
                               :by (:functional-instance
                                    ,(if copyable
                                         'lem-hash-table$a::val-recognizer-of-accessor/copyable
                                         'lem-hash-table$a::val-recognizer-of-accessor/unique)
                                    ,@fi-bindings))))))

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

                  ,@(and key-fixer
                         `((defthm ,accessor-of-key-fixer
                             (equal (,accessor (,key-fixer ,key) ,hash-table)
                                    (,accessor ,key ,hash-table))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    ,(if copyable
                                         'lem-hash-table$a::accessor/copyable-of-key-fixer
                                         'lem-hash-table$a::accessor/unique-of-key-fixer)
                                    ,@fi-bindings))))))

                  (defthm ,accessor-of-fixer
                    (equal (,accessor ,key (,fixer ,hash-table))
                           (,accessor ,key ,hash-table))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::accessor/copyable-of-fixer/copyable
                                'lem-hash-table$a::accessor/unique-of-fixer/unique)
                           ,@fi-bindings))))

                  (defthmd ,accessor-of-updater
                    (equal (,accessor ,%key (,updater ,key ,val ,hash-table))
                           (if (equal ,(if key-fixer
                                           `(,key-fixer ,%key)
                                           %key)
                                      ,(if key-fixer
                                           `(,key-fixer ,key)
                                           key))
                               ,(if val-fixer
                                    `(,val-fixer ,val)
                                    val)
                               (,accessor ,%key ,hash-table)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::accessor/copyable-of-updater/copyable
                                'lem-hash-table$a::accessor/unique-of-updater/unique)
                           ,@fi-bindings))))

                  (defthm ,accessor-of-updater-same
                    (implies (equal ,(if key-fixer
                                         `(,key-fixer ,%key)
                                         %key)
                                    ,(if key-fixer
                                         `(,key-fixer ,key)
                                         key))
                             (equal (,accessor ,%key (,updater ,key ,val ,hash-table))
                                    ,(if val-fixer
                                         `(,val-fixer ,val)
                                         val)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::accessor/copyable-of-updater/copyable-same
                                'lem-hash-table$a::accessor/unique-of-updater/unique-same)
                           ,@fi-bindings))))

                  (defthm ,accessor-of-updater-diff
                    (implies (not (equal ,(if key-fixer
                                              `(,key-fixer ,%key)
                                              %key)
                                         ,(if key-fixer
                                              `(,key-fixer ,key)
                                              key)))
                             (equal (,accessor ,%key (,updater ,key ,val ,hash-table))
                                    (,accessor ,%key ,hash-table)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::accessor/copyable-of-updater/copyable-diff
                                'lem-hash-table$a::accessor/unique-of-updater/unique-diff)
                           ,@fi-bindings))))

                  (defthmd , accessor-when-not-boundp
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
                           (if (equal ,(if key-fixer
                                           `(,key-fixer ,%key)
                                           %key)
                                      ,(if key-fixer
                                           `(,key-fixer ,key)
                                           key))
                               ,default-val
                               (,accessor ,%key ,hash-table)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::accessor/copyable-of-remover/copyable
                                'lem-hash-table$a::accessor/unique-of-remover/unique)
                           ,@fi-bindings))))

                  (defthm ,accessor-of-remover-same
                    (implies (equal ,(if key-fixer
                                         `(,key-fixer ,%key)
                                         %key)
                                    ,(if key-fixer
                                         `(,key-fixer ,key)
                                         key))
                             (equal (,accessor ,%key (,remover ,key ,hash-table))
                                    ,default-val))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::accessor/copyable-of-remover/copyable-same
                                'lem-hash-table$a::accessor/unique-of-remover/unique-same)
                           ,@fi-bindings))))

                  (defthm ,accessor-of-remover-diff
                    (implies (not (equal ,(if key-fixer
                                              `(,key-fixer ,%key)
                                              %key)
                                         ,(if key-fixer
                                              `(,key-fixer ,key)
                                              key)))
                             (equal (,accessor ,%key (,remover ,key ,hash-table))
                                    (,accessor ,%key ,hash-table)))
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
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::accessor/copyable-of-keys-set
                                    ,@fi-bindings))))))

                  ;; `UPDATER'
                  (defthm ,updater{type-prescription}
                    ,(if copyable
                         `(and (consp (,updater ,key ,val ,hash-table))
                               (true-listp (,updater ,key ,val ,hash-table)))
                         `(true-listp (,updater ,key ,val ,hash-table)))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::updater/copyable{type-prescription}
                                'lem-hash-table$a::updater/unique{type-prescription})
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

                  ,@(and key-fixer
                         `((defthm ,updater-of-key-fixer
                             (equal (,updater (,key-fixer ,key) ,val ,hash-table)
                                    (,updater ,key ,val ,hash-table))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    ,(if copyable
                                         'lem-hash-table$a::updater/copyable-of-key-fixer
                                         'lem-hash-table$a::updater/unique-of-key-fixer)
                                    ,@fi-bindings))))))

                  ,@(and val-fixer
                         `((defthm ,updater-of-val-fixer
                             (equal (,updater ,key (,val-fixer ,val) ,hash-table)
                                    (,updater ,key ,val ,hash-table))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    ,(if copyable
                                         'lem-hash-table$a::updater/copyable-of-val-fixer
                                         'lem-hash-table$a::updater/unique-of-val-fixer)
                                    ,@fi-bindings))))))

                  (defthm ,updater-of-fixer
                    (equal (,updater ,key ,val (,fixer ,hash-table))
                           (,updater ,key ,val ,hash-table))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::updater/copyable-of-fixer/copyable
                                'lem-hash-table$a::updater/unique-of-fixer/unique)
                           ,@fi-bindings))))

                  (defthmd ,updater-of-accessor-when-boundp-free
                    (implies (and (,boundp ,key ,hash-table)
                                  (equal ,(if val-fixer
                                              `(,val-fixer ,val)
                                              val)
                                         (,accessor ,key ,hash-table)))
                             (equal (,updater ,key ,val ,hash-table)
                                    (,fixer ,hash-table)))
                    :rule-classes
                    ((:rewrite :corollary
                               (implies (and (,boundp ,key ,hash-table)
                                             (case-split (equal ,(if val-fixer
                                                                     `(,val-fixer ,val)
                                                                     val)
                                                                (,accessor ,key ,hash-table))))
                                        (equal (,updater ,key ,val ,hash-table)
                                               (,fixer ,hash-table)))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::updater/copyable-of-accessor/copyable-when-boundp/copyable-free
                                'lem-hash-table$a::updater/unique-of-accessor/unique-when-boundp/unique-free)
                           ,@fi-bindings))))

                  (defthmd ,updater-of-accessor
                    (implies (equal ,(if key-fixer
                                         `(,key-fixer ,%key)
                                         %key)
                                    ,(if key-fixer
                                         `(,key-fixer ,key)
                                         key))
                             (equal (,updater ,%key (,accessor ,key ,hash-table) ,hash-table)
                                    (if (,boundp ,%key ,hash-table)
                                        (,fixer ,hash-table)
                                        (,updater ,%key ,default-val ,hash-table))))
                    :rule-classes
                    ((:rewrite :corollary
                               (implies (case-split (equal ,(if key-fixer
                                                                `(,key-fixer ,%key)
                                                                %key)
                                                           ,(if key-fixer
                                                                `(,key-fixer ,key)
                                                                key)))
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
                                  (equal ,(if key-fixer
                                              `(,key-fixer ,%key)
                                              %key)
                                         ,(if key-fixer
                                              `(,key-fixer ,key)
                                              key)))
                             (equal (,updater ,%key (,accessor ,key ,hash-table) ,hash-table)
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
                                  (equal ,(if key-fixer
                                              `(,key-fixer ,%key)
                                              %key)
                                         ,(if key-fixer
                                              `(,key-fixer ,key)
                                              key)))
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
                           (if (equal ,(if key-fixer
                                           `(,key-fixer ,%key)
                                           %key)
                                      ,(if key-fixer
                                           `(,key-fixer ,key)
                                           key))
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
                    (implies (equal ,(if key-fixer
                                         `(,key-fixer ,%key)
                                         %key)
                                    ,(if key-fixer
                                         `(,key-fixer ,key)
                                         key))
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
                    (implies (not (equal ,(if key-fixer
                                              `(,key-fixer ,%key)
                                              %key)
                                         ,(if key-fixer
                                              `(,key-fixer ,key)
                                              key)))
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
                    (implies (equal ,(if key-fixer
                                         `(,key-fixer ,%key)
                                         %key)
                                    ,(if key-fixer
                                         `(,key-fixer ,key)
                                         key))
                             (equal (,updater ,%key ,val (,remover ,key ,hash-table))
                                    (,updater ,%key ,val ,hash-table)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::updater/copyable-of-remover/copyable-same
                                'lem-hash-table$a::updater/unique-of-remover/unique-same)
                           ,@fi-bindings))))

                  ;; `BOUNDP'
                  (defthm ,boundp{type-prescription}
                    (booleanp (,boundp ,key ,hash-table))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::boundp/copyable{type-prescription}
                                'lem-hash-table$a::boundp/unique{type-prescription})
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

                  ,@(and key-fixer
                         `((defthm ,boundp-of-key-fixer
                             (equal (,boundp (,key-fixer ,key) ,hash-table)
                                    (,boundp ,key ,hash-table))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    ,(if copyable
                                         'lem-hash-table$a::boundp/copyable-of-key-fixer
                                         'lem-hash-table$a::boundp/unique-of-key-fixer)
                                    ,@fi-bindings))))))

                  (defthm ,boundp-of-fixer
                    (equal (,boundp ,key (,fixer ,hash-table))
                           (,boundp ,key ,hash-table))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::boundp/copyable-of-fixer/copyable
                                'lem-hash-table$a::boundp/unique-of-fixer/unique)
                           ,@fi-bindings))))

                  (defthmd ,boundp-of-updater
                    (equal (,boundp ,%key (,updater ,key ,val ,hash-table))
                           (if (equal ,(if key-fixer
                                           `(,key-fixer ,%key)
                                           %key)
                                      ,(if key-fixer
                                           `(,key-fixer ,key)
                                           key))
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
                    (implies (equal ,(if key-fixer
                                         `(,key-fixer ,%key)
                                         %key)
                                    ,(if key-fixer
                                         `(,key-fixer ,key)
                                         key))
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
                    (implies (not (equal ,(if key-fixer
                                              `(,key-fixer ,%key)
                                              %key)
                                         ,(if key-fixer
                                              `(,key-fixer ,key)
                                              key)))
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
                           (if (equal ,(if key-fixer
                                           `(,key-fixer ,%key)
                                           %key)
                                      ,(if key-fixer
                                           `(,key-fixer ,key)
                                           key))
                               nil
                               (,boundp ,%key ,hash-table)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::boundp/copyable-of-remover/copyable
                                'lem-hash-table$a::boundp/unique-of-remover/unique)
                           ,@fi-bindings))))

                  (defthm ,boundp-of-remover-same
                    (implies (equal ,(if key-fixer
                                         `(,key-fixer ,%key)
                                         %key)
                                    ,(if key-fixer
                                         `(,key-fixer ,key)
                                         key))
                             (not (,boundp ,%key (,remover ,key ,hash-table))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::boundp/copyable-of-remover/copyable-same
                                'lem-hash-table$a::boundp/unique-of-remover/unique-same)
                           ,@fi-bindings))))

                  (defthm ,boundp-of-remover-diff
                    (implies (not (equal ,(if key-fixer
                                              `(,key-fixer ,%key)
                                              %key)
                                         ,(if key-fixer
                                              `(,key-fixer ,key)
                                              key)))
                             (equal (,boundp ,%key (,remover ,key ,hash-table))
                                    (,boundp ,%key ,hash-table)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::boundp/copyable-of-remover/copyable-diff
                                'lem-hash-table$a::boundp/unique-of-remover/unique-diff)
                           ,@fi-bindings))))

                  (defthmd ,boundp-when-zp-count
                    (implies (zp (,count ,hash-table))
                             (not (,boundp ,key ,hash-table)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::boundp/copyable-when-zp-count/copyable
                                'lem-hash-table$a::boundp/unique-when-zp-count/unique)
                           ,@fi-bindings))))

                  ,@(and copyable
                         `((defthm ,boundp-of-keys-set
                             (equal (,boundp ,key (,keys-set ,set ,hash-table))
                                    (,boundp ,key ,hash-table))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::boundp/copyable-of-keys-set
                                    ,@fi-bindings))))))

                  ;; `GETP'
                  (defthm ,getp{type-prescription}
                    (and (consp (,getp ,key ,hash-table))
                         (true-listp (,getp ,key ,hash-table)))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::getp/copyable{type-prescription}
                                'lem-hash-table$a::getp/unique{type-prescription})
                           ,@fi-bindings))))

                  (defthm ,getp{rewrite}
                    (mv-let (v0 v1)
                            (,getp ,key ,hash-table)
                      (and (equal v0 (,accessor ,key ,hash-table))
                           (equal v1 (,boundp ,key ,hash-table))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::getp/copyable{rewrite}
                                'lem-hash-table$a::getp/unique{rewrite})
                           ,@fi-bindings))))

                  ;; `REMOVER'
                  (defthm ,remover{type-prescription}
                    ,(if copyable
                         `(and (consp (,remover ,key ,hash-table))
                               (true-listp (,remover ,key ,hash-table)))
                         `(true-listp (,remover ,key ,hash-table)))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::remover/copyable{type-prescription}
                                'lem-hash-table$a::remover/unique{type-prescription})
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

                  ,@(and key-fixer
                         `((defthm ,remover-of-key-fixer
                             (equal (,remover (,key-fixer ,key) ,hash-table)
                                    (,remover ,key ,hash-table))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    ,(if copyable
                                         'lem-hash-table$a::remover/copyable-of-key-fixer
                                         'lem-hash-table$a::remover/unique-of-key-fixer)
                                    ,@fi-bindings))))))

                  (defthm ,remover-of-fixer
                    (equal (,remover ,key (,fixer ,hash-table))
                           (,remover ,key ,hash-table))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::remover/copyable-of-fixer/copyable
                                'lem-hash-table$a::remover/unique-of-fixer/unique)
                           ,@fi-bindings))))

                  (defthmd ,remover-of-updater
                    (equal (,remover ,%key (,updater ,key ,val ,hash-table))
                           (if (equal ,(if key-fixer
                                           `(,key-fixer ,%key)
                                           %key)
                                      ,(if key-fixer
                                           `(,key-fixer ,key)
                                           key))
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
                    (implies (equal ,(if key-fixer
                                         `(,key-fixer ,%key)
                                         %key)
                                    ,(if key-fixer
                                         `(,key-fixer ,key)
                                         key))
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
                    (implies (not (equal ,(if key-fixer
                                              `(,key-fixer ,%key)
                                              %key)
                                         ,(if key-fixer
                                              `(,key-fixer ,key)
                                              key)))
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
                           (if (equal ,(if key-fixer
                                           `(,key-fixer ,%key)
                                           %key)
                                      ,(if key-fixer
                                           `(,key-fixer ,key)
                                           key))
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
                    (implies (equal ,(if key-fixer
                                         `(,key-fixer ,%key)
                                         %key)
                                    ,(if key-fixer
                                         `(,key-fixer ,key)
                                         key))
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
                    (implies (not (equal ,(if key-fixer
                                              `(,key-fixer ,%key)
                                              %key)
                                         ,(if key-fixer
                                              `(,key-fixer ,key)
                                              key)))
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

                  ;; `COUNT'
                  (defthm ,count{type-prescription}
                    (natp (,count ,hash-table))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::count/copyable{type-prescription}
                                'lem-hash-table$a::count/unique{type-prescription})
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

                  (defthm ,count-of-fixer
                    (equal (,count (,fixer ,hash-table))
                           (,count ,hash-table))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::count/copyable-of-fixer/copyable
                                'lem-hash-table$a::count/unique-of-fixer/unique)
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

                  (defthm ,count-when-boundp
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
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::count/copyable-of-keys-set
                                    ,@fi-bindings))))))

                  ;; `CLEAR'
                  (defthm ,clear{type-prescription}
                    ,(if copyable
                         `(and (consp (,clear ,hash-table))
                               (true-listp (,clear ,hash-table)))
                         `(true-listp (,clear ,hash-table)))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::clear/copyable{type-prescription}
                                'lem-hash-table$a::clear/unique{type-prescription})
                           ,@fi-bindings))))

                  (defthm ,clear{rewrite}
                    (equal (,clear ,hash-table)
                           (,creator))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::clear/copyable{rewrite}
                                'lem-hash-table$a::clear/unique{rewrite})
                           ,@fi-bindings))))

                  ;; `INIT'
                  (defthm ,init{type-prescription}
                    ,(if copyable
                         `(and (consp (,init ht-size rehash-size rehash-threshold ,hash-table))
                               (true-listp (,init ht-size rehash-size rehash-threshold ,hash-table)))
                         `(true-listp (,init ht-size rehash-size rehash-threshold ,hash-table)))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::init/copyable{type-prescription}
                                'lem-hash-table$a::init/unique{type-prescription})
                           ,@fi-bindings))))

                  (defthm ,init{rewrite}
                    (equal (,init ht-size rehash-size rehash-threshold ,hash-table)
                           (,creator))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::init/copyable{rewrite}
                                'lem-hash-table$a::init/unique{rewrite})
                           ,@fi-bindings))))

                  ;; `KEYSP'
                  ,@(and copyable
                         key-recognizer
                         `((defthm ,keysp{type-prescription}
                             (booleanp (,keysp ,set))
                             :rule-classes :type-prescription
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keysp{type-prescription}
                                    ,@fi-bindings))))

                           (defthm ,keysp{compound-recognizer}
                             (implies (,keysp ,set)
                                      (true-listp ,set))
                             :rule-classes :compound-recognizer
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keysp{compound-recognizer}
                                    ,@fi-bindings))))

                           (defthmd ,keysp{definition}
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
                                    lem-hash-table$a::keysp{definition}
                                    ,@fi-bindings))))

                           (defthm ,keysp-when-emptyp
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

                           (defthm ,setp-when-keysp
                             (implies (,keysp ,set)
                                      (set::setp ,set))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::setp-when-keysp
                                    ,@fi-bindings))))

                           (defthm ,key-recognizer-of-head-when-keysp
                             (implies (and (,keysp ,set)
                                           (not (set::emptyp ,set)))
                                      (,key-recognizer (set::head ,set)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::key-recognizer-of-head-when-keysp
                                    ,@fi-bindings))))

                           (defthm ,keysp-of-tail-when-keysp
                             (implies (and (,keysp ,set)
                                           (not (set::emptyp ,set)))
                                      (,keysp (set::tail ,set)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keysp-of-tail-when-keysp
                                    ,@fi-bindings))))

                           (defthmd ,in-when-keysp{case-split}
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

                           (defthm ,keysp-when-subset
                             (implies (and (not (,keysp ,%set))
                                           (,keysp ,set))
                                      (equal (set::subset ,%set ,set)
                                             (set::emptyp ,%set)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keysp-when-subset
                                    ,@fi-bindings))))


                           (defthm ,keysp-of-insert
                             (implies (,keysp set)
                                      (equal (,keysp (set::insert key set))
                                             (,key-recognizer key)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keysp-of-insert
                                    ,@fi-bindings))))

                           (defthm ,keysp-of-delete
                             (implies (,keysp ,set)
                                      (,keysp (set::delete ,key ,set)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keysp-of-delete
                                    ,@fi-bindings))))))

                  ;; `KEYS-FIX'
                  ,@(and copyable
                         key-recognizer
                         `((defthm ,keys-fix{type-prescription}
                             (true-listp (,keys-fix ,set))
                             :rule-classes :type-prescription
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keys-fix{type-prescription}
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

                  ;; `KEYS'
                  ,@(and copyable
                         `((defthm ,keys{type-prescription}
                             (true-listp (,keys ,hash-table))
                             :rule-classes :type-prescription
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keys{type-prescription}
                                    ,@fi-bindings))))

                           (defthm ,keysp-of-keys
                             ,(if key-recognizer
                                  `(,keysp (,keys ,hash-table))
                                  `(set::setp (,keys ,hash-table)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keysp-of-keys
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

                           (defthm ,keys-of-fixer
                             (equal (,keys (,fixer ,hash-table))
                                    (,keys ,hash-table))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keys-of-fixer/copyable
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
                                    ,(if key-recognizer
                                         `(,keys-fix ,set)
                                         `(set::sfix ,set)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keys-of-keys-set
                                    ,@fi-bindings))))))

                  ;; `KEYS-SET'
                  ,@(and copyable
                         `((defthm ,keys-set{type-prescription}
                             (and (consp (,keys-set ,set ,hash-table))
                                  (true-listp (,keys-set ,set ,hash-table)))
                             :rule-classes :type-prescription
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keys-set{type-prescription}
                                    ,@fi-bindings))))

                           (defthmd ,keys-set-when-not-keysp
                             (implies (not ,(if key-recognizer
                                                `(,keysp ,set)
                                                `(set::setp ,set)))
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

                           (defthm ,keys-set-of-keys-fix
                             (equal (,keys-set ,(if key-recognizer
                                                    `(,keys-fix ,set)
                                                    `(set::sfix ,set))
                                               ,hash-table)
                                    (,keys-set ,set ,hash-table))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keys-set-of-keys-fix
                                    ,@fi-bindings))))

                           (defthm ,keys-set-of-fixer
                             (equal (,keys-set ,set (,fixer ,hash-table))
                                    (,keys-set ,set ,hash-table))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keys-set-of-fixer/copyable
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
                             (implies (equal ,(if key-recognizer
                                                  `(,keys-fix ,set)
                                                  `(set::sfix ,set))
                                             (,keys ,hash-table))
                                      (equal (,keys-set ,set ,hash-table)
                                             (,fixer ,hash-table)))
                             :rule-classes
                             ((:rewrite :corollary
                                        (implies (case-split (equal ,(if key-recognizer
                                                                         `(,keys-fix ,set)
                                                                         `(set::sfix ,set))
                                                                    (,keys ,hash-table)))
                                                 (equal (,keys-set ,set ,hash-table)
                                                        (,fixer ,hash-table)))))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$a::keys-set-of-keys-free
                                    ,@fi-bindings))))

                           (defthm ,keys-set-of-keys
                             (equal (,keys-set (,keys ,hash-table) ,hash-table)
                                    (,fixer ,hash-table))
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
                      ,(if key-recognizer
                           `(implies (,key-recognizer ,key)
                                     (equal (,boundp ,key ,%hash-table)
                                            (,boundp ,key ,hash-table)))
                           `(equal (,boundp ,key ,%hash-table)
                                   (,boundp ,key ,hash-table))))
                    :rewrite :direct)

                  (defun-sk ,vals-equal (,%hash-table ,hash-table)
                    (declare (xargs :guard (and (,recognizer ,%hash-table)
                                                (,recognizer ,hash-table))
                                    :verify-guards nil))
                    (forall ,key
                      ,(if key-recognizer
                           `(implies (,key-recognizer ,key)
                                     (equal (,accessor ,key ,%hash-table)
                                            (,accessor ,key ,hash-table)))
                           `(equal (,accessor ,key ,%hash-table)
                                   (,accessor ,key ,hash-table))))
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

                  (defthm ,hash-table-equal{forward-chaining}
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
                      :in-theory (disable ,recognizer
                                          ,creator
                                          ,fixer
                                          ,accessor
                                          ,updater
                                          ,boundp
                                          ,getp
                                          ,remover
                                          ,count
                                          ,clear
                                          ,init
                                          ,@(and copyable
                                                 (list keys
                                                       keys-set))
                                          ,keys-equal
                                          ,keys-equal-necc
                                          ,vals-equal
                                          ,vals-equal-necc)
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$a::equal/copyable{forward-chaining}
                                'lem-hash-table$a::equal/unique{forward-chaining})
                           ,@fi-bindings-with-skolem))
                     ("Subgoal 4"
                      :use ((:instance ,vals-equal-necc
                                       (,%hash-table lem-hash-table$a::%hash-table)
                                       (,hash-table lem-hash-table$a::hash-table)
                                       (,key lem-hash-table$a::key))))
                     ("Subgoal 3"
                      :expand (:free (,%hash-table ,hash-table)
                                     (,vals-equal ,%hash-table ,hash-table)))
                     ("Subgoal 2"
                      :use ((:instance ,keys-equal-necc
                                       (,%hash-table lem-hash-table$a::%hash-table)
                                       (,hash-table lem-hash-table$a::hash-table)
                                       (,key lem-hash-table$a::key))))
                     ("Subgoal 1"
                      :expand (:free (,%hash-table ,hash-table)
                                     (,keys-equal ,%hash-table ,hash-table)))))))

              (stobj$a-property `(,hash-table (,recognizer
                                               ,creator
                                               ,fixer)
                                              ((,key
                                                ,key-recognizer
                                                ,default-key-name
                                                ,key-fixer)
                                               (,val
                                                ,val-recognizer
                                                ,(and (not stobj-property)
                                                      default-val-name)
                                                ,val-fixer)
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
                                                ,@(and copyable
                                                       (list (if key-recognizer
                                                                 keysp
                                                                 'set::setp)
                                                             (if key-recognizer
                                                                 keys-fix
                                                                 'set::sfix)
                                                             keys
                                                             keys-set)))))))

         `(progn
            ,@prologue

            ,body

            ,@epilogue

            (table stobj$a-property ',hash-table ',stobj$a-property))))))
