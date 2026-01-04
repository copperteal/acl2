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

#|
(include-book "../lemmas/hash-table-c")
|#

(include-book "../type-spec")
(include-book "../utilities/top")


;;;; `DEFINE-HASH-TABLE$C'
(defmacro define-hash-table$c
    (hash-table test
     &key
       (size 'nil)
       (element-type 't)
       (default-value 'nil)
       (copyable 't)

       (inline 't)
       (memoizable 'nil)
       (executable 'nil)

       (contents 'nil)
       (contents-recognizer 'nil)
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
       (keys 'nil)
       (keys-set 'nil)

       (package-witness 'nil package-witness-supplied-p)
       (debug 'nil))

  (declare (xargs :guard (and (symbolp hash-table)
                              (symbolp test)
                              (member test '(eq eql hons-equal equal) :test 'eq)
                              (or (null size)
                                  (natp size))
                              (if (acl2-type-spec-p element-type)
                                  (typep$ default-value element-type)
                                  (symbolp element-type))
                              (boolean-listp (list copyable
                                                   inline
                                                   memoizable
                                                   executable))
                              (symbol-listp (list contents
                                                  contents-recognizer
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
                                                  init
                                                  keys
                                                  keys-set))
                              (or copyable
                                  (and (not keys)
                                       (not keys-set)))
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
              (size ',size)

              (element-type ',element-type)
              (stobj-property (and (symbolp element-type)
                                   (getpropc element-type 'acl2::stobj)))
              (absstobj-info (and stobj-property
                                  (getpropc element-type 'acl2::absstobj-info)))
              (stobj$a-property (and (symbolp element-type)
                                     (cdr (assoc element-type (table-alist 'stobj$a-property (w state))))))
              (stobj-recognizer (cond
                                  (stobj$a-property
                                   (first (second stobj$a-property)))
                                  (stobj-property
                                   (caadr stobj-property))))
              (stobj-creator (cond
                               (stobj$a-property
                                (second (second stobj$a-property)))
                               (stobj-property
                                (cdadr stobj-property))))
              (default-value ',default-value)
              (default-value-name (symbolicate package-witness "*" hash-table "-DEFAULT-VALUE*"))
              (copyable ',copyable)

              (inline ',inline)
              (memoizable ',memoizable)
              (executable ',executable)

              (contents ',contents)
              (contents-recognizer ',contents-recognizer)
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
              (keys ',keys)
              (keys-set ',keys-set)

              ;; Interface Symbols
              (contents (or contents
                            (symbolicate package-witness hash-table "-CONTENTS")))
              (contents-recognizer-stobj-default (symbolicate package-witness contents "P"))
              (contents-recognizer (or contents-recognizer
                                       (symbolicate package-witness contents (make-predicate-suffix contents))))
              (recognizer-stobj-default (symbolicate package-witness hash-table "P"))
              (recognizer (or recognizer
                              (symbolicate package-witness hash-table (make-predicate-suffix hash-table))))
              (creator-stobj-default (symbolicate package-witness "CREATE-" hash-table))
              (creator (or creator
                           (symbolicate package-witness "CREATE-" hash-table)))
              (fixer (or fixer
                         (symbolicate package-witness hash-table "-FIX")))
              (accessor-stobj-default (symbolicate package-witness contents "-GET"))
              (accessor (or accessor
                            (symbolicate package-witness hash-table "-GET")))
              (updater-stobj-default (symbolicate package-witness contents "-PUT"))
              (updater (or updater
                           (symbolicate package-witness hash-table "-PUT")))
              (boundp-stobj-default (symbolicate package-witness contents "-BOUNDP"))
              (boundp (or boundp
                          (symbolicate package-witness hash-table "-BNDP")))
              (getp-stobj-default (symbolicate package-witness contents "-GET?"))
              (getp (or getp
                        (symbolicate package-witness hash-table "-GETP")))
              (remover-stobj-default (symbolicate package-witness contents "-REM"))
              (remover (or remover
                           (symbolicate package-witness hash-table "-REM")))
              (count-stobj-default (symbolicate package-witness contents "-COUNT"))
              (count (or count
                         (symbolicate package-witness hash-table "-CNT")))
              (clear-stobj-default (symbolicate package-witness contents "-CLEAR"))
              (clear (or clear
                         (symbolicate package-witness hash-table "-CLR")))
              (%clear (if copyable
                          (symbolicate package-witness hash-table "-%CLEAR")
                          clear))
              (init-stobj-default (symbolicate package-witness contents "-INIT"))
              (init (or init
                        (symbolicate package-witness hash-table "-INIT")))
              (%init (if copyable
                         (symbolicate package-witness hash-table "-%INIT")
                         init))
              (keys (or keys
                        (symbolicate package-witness hash-table "-KEYS")))
              (keys-set-stobj-default (symbolicate package-witness "UPDATE-" keys))
              (keys-set (or keys-set
                            (symbolicate package-witness keys "-SET")))

              ;; Make Doublets
              (doublets (append (and (not (eq contents-recognizer contents-recognizer-stobj-default))
                                     `((,contents-recognizer-stobj-default ,contents-recognizer)))
                                (and (not (eq recognizer recognizer-stobj-default))
                                     `((,recognizer-stobj-default ,recognizer)))
                                (and (not (eq creator creator-stobj-default))
                                     `((,creator-stobj-default ,creator)))
                                (and (not (eq accessor accessor-stobj-default))
                                     `((,accessor-stobj-default ,accessor)))
                                (and (not (eq updater updater-stobj-default))
                                     `((,updater-stobj-default ,updater)))
                                (and (not (eq boundp boundp-stobj-default))
                                     `((,boundp-stobj-default ,boundp)))
                                (and (not (eq getp getp-stobj-default))
                                     `((,getp-stobj-default ,getp)))
                                (and (not (eq remover remover-stobj-default))
                                     `((,remover-stobj-default ,remover)))
                                (and (not (eq count count-stobj-default))
                                     `((,count-stobj-default ,count)))
                                (and (not (eq clear clear-stobj-default))
                                     `((,clear-stobj-default ,%clear)))
                                (and (not (eq init init-stobj-default))
                                     `((,init-stobj-default ,%init)))
                                (and copyable
                                     (not (eq keys-set keys-set-stobj-default))
                                     `((,keys-set-stobj-default ,keys-set)))))

              ;; Prologue
              (hash-table-begin (symbolicate package-witness hash-table "-BEGIN"))
              (hash-table-end (symbolicate package-witness hash-table "-END"))
              (prologue
               `((deflabel ,hash-table-begin)

                 ,@(and (not stobj-property)
                        `((defconst ,default-value-name ',default-value)))

                 (defstobj ,hash-table
                   (,contents :type (acl2::hash-table ,test ,size ,element-type)
                              ,@(and (not stobj-property)
                                     `(:initially ,default-value)))
                   ,@(and ',copyable
                          `((,keys)))
                   :renaming ,doublets
                   :inline ,inline
                   :non-memoizable ,(not memoizable)
                   :non-executable ,(not executable))))

              ;; Theorem Names
              (stobj-recognizer-of-stobj-creator (symbolicate "ATOMIC-STOBJS" stobj-recognizer "-OF-" stobj-creator))

              (contents-recognizer-tp (symbolicate package-witness contents-recognizer "-TP"))

              (recognizer-tp (symbolicate package-witness recognizer "-TP"))
              (recognizer-cr (symbolicate package-witness recognizer "-CR"))
              (recognizer-of-creator (symbolicate package-witness recognizer "-OF-" creator))
              (recognizer-of-updater (symbolicate package-witness recognizer "-OF-" updater))
              (recognizer-of-remover (symbolicate package-witness recognizer "-OF-" remover))
              (recognizer-of-%clear (symbolicate package-witness recognizer "-OF-" %clear))
              (recognizer-of-%init (symbolicate package-witness recognizer "-OF-" %init))
              (recognizer-of-keys-set (symbolicate package-witness recognizer "-OF-" keys-set))

              (typep$-of-accessor (symbolicate package-witness "TYPEP$-OF-" accessor))
              (accessor-of-creator (symbolicate package-witness accessor "-OF-" creator))
              (accessor-of-updater (symbolicate package-witness accessor "-OF-" updater))
              (accessor-of-updater-same (symbolicate package-witness accessor-of-updater "-SAME"))
              (accessor-of-updater-diff (symbolicate package-witness accessor-of-updater "-DIFF"))
              (accessor-of-remover (symbolicate package-witness accessor "-OF-" remover))
              (accessor-of-remover-same (symbolicate package-witness accessor-of-remover "-SAME"))
              (accessor-of-remover-diff (symbolicate package-witness accessor-of-remover "-DIFF"))
              (accessor-of-keys-set (symbolicate package-witness accessor "-OF-" keys-set))

              (updater-tp (symbolicate package-witness updater "-TP"))

              (boundp-tp (symbolicate package-witness boundp "-TP"))
              (boundp-of-creator (symbolicate package-witness boundp "-OF-" creator))
              (boundp-of-updater (symbolicate package-witness boundp "-OF-" updater))
              (boundp-of-updater-same (symbolicate package-witness boundp-of-updater "-SAME"))
              (boundp-of-updater-diff (symbolicate package-witness boundp-of-updater "-DIFF"))
              (boundp-of-remover (symbolicate package-witness boundp "-OF-" remover))
              (boundp-of-remover-same (symbolicate package-witness boundp-of-remover "-SAME"))
              (boundp-of-remover-diff (symbolicate package-witness boundp-of-remover "-DIFF"))
              (boundp-of-keys-set (symbolicate package-witness boundp "-OF-" keys-set))

              (getp-tp (symbolicate package-witness getp "-TP"))
              (getp-rw (symbolicate package-witness getp "-RW"))

              (remover-tp (symbolicate package-witness remover "-TP"))
              (remover-of-creator (symbolicate package-witness remover "-OF-" creator))
              (remover-of-updater (symbolicate package-witness remover "-OF-" updater))
              (remover-of-updater-same (symbolicate package-witness remover-of-updater "-SAME"))
              (remover-of-updater-diff (symbolicate package-witness remover-of-updater "-DIFF"))
              (remover-of-remover (symbolicate package-witness remover "-OF-" remover))
              (remover-of-remover-same (symbolicate package-witness remover-of-remover "-SAME"))
              (remover-of-remover-diff (symbolicate package-witness remover-of-remover "-DIFF"))

              (count-tp (symbolicate package-witness count "-TP"))
              (count-of-creator (symbolicate package-witness count "-OF-" creator))
              (count-of-updater (symbolicate package-witness count "-OF-" updater))
              (count-of-updater-when-boundp (symbolicate package-witness count-of-updater "-WHEN-" boundp))
              (count-of-updater-when-not-boundp (symbolicate package-witness count-of-updater "-WHEN-NOT-" boundp))
              (count-of-remover (symbolicate package-witness count "-OF-" remover))
              (count-of-remover-when-boundp (symbolicate package-witness count-of-remover "-WHEN-" boundp))
              (count-of-remover-when-not-boundp (symbolicate package-witness count-of-remover "-WHEN-NOT-" boundp))
              (count-of-keys-set (symbolicate package-witness count "-OF-" keys-set))

              (%clear-tp (symbolicate package-witness %clear "-TP"))
              (%clear-rw (symbolicate package-witness %clear "-RW"))

              (%init-tp (symbolicate package-witness %init "-TP"))
              (%init-rw (symbolicate package-witness %init "-RW"))

              (keys-of-creator (symbolicate package-witness keys "-OF-" creator))
              (keys-of-updater (symbolicate package-witness keys "-OF-" updater))
              (keys-of-remover (symbolicate package-witness keys "-OF-" remover))
              (keys-of-keys-set (symbolicate package-witness keys "-OF-" keys-set))

              (keys-set-tp (symbolicate package-witness keys-set "-TP"))
              (keys-set-of-updater (symbolicate package-witness keys-set "-OF-" updater))
              (keys-set-of-remover (symbolicate package-witness keys-set "-OF-" remover))
              (keys-set-of-keys-set (symbolicate package-witness keys-set "-OF-" keys-set))

              (fixer-tp (symbolicate package-witness fixer "-TP"))
              (recognizer-of-fixer (symbolicate package-witness recognizer "-OF-" fixer))
              (fixer-when-recognizer (symbolicate package-witness fixer "-WHEN-" recognizer))
              (fixer-when-not-recognizer (symbolicate package-witness fixer "-WHEN-NOT-" recognizer))

              (clear-tp (symbolicate package-witness clear "-TP"))
              (clear-rw (symbolicate package-witness clear "-RW"))

              (init-tp (symbolicate package-witness init "-TP"))
              (init-rw (symbolicate package-witness init "-RW"))

              ;; Epilogue
              (hash-table-theorems (symbolicate package-witness hash-table "-THEOREMS"))
              (epilogue
               `((deflabel ,hash-table-end)

                 (deftheory-static ,hash-table-theorems
                   (set-difference-theories
                    (set-difference-theories
                     (current-theory ',hash-table-end)
                     (current-theory ',hash-table-begin))
                    ',(append
                       (list contents-recognizer
                             recognizer
                             creator
                             accessor
                             updater
                             boundp
                             getp
                             remover
                             count
                             %clear
                             %init
                             fixer)
                       (and copyable
                            (list keys
                                  keys-set
                                  clear
                                  init)))))

                 (in-theory
                   (union-theories (current-theory ',hash-table-begin)
                                   (theory ',hash-table-theorems)))))

              ;; Functional Instantiation
              (fi-bindings
               (append
                (list `(lem-hash-table$c::key-guard ,(case test
                                                       (eq
                                                        'symbolp)
                                                       (eql
                                                        'eqlablep)
                                                       (t
                                                        `(lambda (key)
                                                           t))))
                      `(lem-hash-table$c::element-recognizer ,(or stobj-recognizer
                                                                  `(lambda (value)
                                                                     ,(typep$transform 'value element-type))))
                      `(lem-hash-table$c::default-value ,(or stobj-creator
                                                             `(lambda ()
                                                                ,default-value-name)))
                      `(lem-hash-table$c::contents-recognizer ,contents-recognizer)
                      (if copyable
                          `(lem-hash-table$c::recognizer/copyable ,recognizer)
                          `(lem-hash-table$c::recognizer/unique ,recognizer))
                      (if copyable
                          `(lem-hash-table$c::creator/copyable ,creator)
                          `(lem-hash-table$c::creator/unique ,creator))
                      `(lem-hash-table$c::accessor ,accessor)
                      `(lem-hash-table$c::updater ,updater)
                      `(lem-hash-table$c::boundp ,boundp)
                      `(lem-hash-table$c::getp ,getp)
                      `(lem-hash-table$c::remover ,remover)
                      `(lem-hash-table$c::count ,count)
                      `(lem-hash-table$c::%clear ,%clear)
                      `(lem-hash-table$c::%init ,%init))
                (and copyable
                     (list `(lem-hash-table$c::keys ,keys)
                           `(lem-hash-table$c::keys-set ,keys-set)))))
              (fi-bindings-with-fixer
               (cons (if copyable
                         `(lem-hash-table$c::fixer/copyable ,fixer)
                         `(lem-hash-table$c::fixer/unique ,fixer))
                     fi-bindings))
              (fi-bindings-with-fixer-and-clear
               (cons `(lem-hash-table$c::clear ,clear)
                     fi-bindings-with-fixer))
              (fi-bindings-with-fixer-and-clear-and-init
               (cons `(lem-hash-table$c::init ,init)
                     fi-bindings-with-fixer-and-clear))

              (body
               `(encapsulate ()

                  ,@(and stobj-property
                         `((local
                             (defthm ,stobj-recognizer-of-stobj-creator
                               (,stobj-recognizer (,stobj-creator))))))

                  (local
                    (deflabel end-of-prologue))

                  (local
                    (include-book "projects/atomic-stobjs/lemmas/hash-table-c" :dir :system))

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

                  (local
                    (in-theory
                      (enable type-spec-theory)))

                  ;; `CONTENTS-RECOGNIZER'
                  (defthm ,contents-recognizer-tp
                    (booleanp (,contents-recognizer ,contents))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-hash-table$c::contents-recognizer-tp
                           ,@fi-bindings))))

                  ;; `RECOGNIZER'
                  (defthm ,recognizer-tp
                    (booleanp (,recognizer ,hash-table))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$c::recognizer/copyable-tp
                                'lem-hash-table$c::recognizer/unique-tp)
                           ,@fi-bindings))))

                  (defthm ,recognizer-cr
                    (implies (,recognizer ,hash-table)
                             (and (consp ,hash-table)
                                  (true-listp ,hash-table)))
                    :rule-classes :compound-recognizer
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$c::recognizer/copyable-cr
                                'lem-hash-table$c::recognizer/unique-cr)
                           ,@fi-bindings))))

                  (defthm ,recognizer-of-creator
                    (,recognizer (,creator))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$c::recognizer/copyable-of-creator/copyable
                                'lem-hash-table$c::recognizer/unique-of-creator/unique)
                           ,@fi-bindings))))

                  (defthm ,recognizer-of-updater
                    (implies ,(if (eq element-type t)
                                  `(,recognizer ,hash-table)
                                  `(and (,recognizer ,hash-table)
                                        ,(if stobj-recognizer
                                             `(,stobj-recognizer value)
                                             (typep$transform 'value element-type))))
                             (,recognizer (,updater key value ,hash-table)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$c::recognizer/copyable-of-updater
                                'lem-hash-table$c::recognizer/unique-of-updater)
                           ,@fi-bindings))))

                  (defthm ,recognizer-of-remover
                    (implies (,recognizer ,hash-table)
                             (,recognizer (,remover key ,hash-table)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$c::recognizer/copyable-of-remover
                                'lem-hash-table$c::recognizer/unique-of-remover)
                           ,@fi-bindings))))

                  (defthm ,recognizer-of-%clear
                    (implies (,recognizer ,hash-table)
                             (,recognizer (,%clear ,hash-table)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$c::recognizer/copyable-of-%clear
                                'lem-hash-table$c::recognizer/unique-of-%clear)
                           ,@fi-bindings))))

                  (defthm ,recognizer-of-%init
                    (implies (,recognizer ,hash-table)
                             (,recognizer (,%init ht-size rehash-size rehash-threshold ,hash-table)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$c::recognizer/copyable-of-%init
                                'lem-hash-table$c::recognizer/unique-of-%init)
                           ,@fi-bindings))))

                  ,@(and copyable
                         `((defthm ,recognizer-of-keys-set
                             (implies (,recognizer ,hash-table)
                                      (,recognizer (,keys-set set ,hash-table)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$c::recognizer/copyable-of-keys-set
                                    ,@fi-bindings))))))

                  ;; `ACCESSOR'
                  ,@(and (not (eq element-type t))
                         `((defthm ,typep$-of-accessor
                             (implies (,recognizer ,hash-table)
                                      ,(if stobj-recognizer
                                           `(,stobj-recognizer (,accessor key ,hash-table))
                                           (typep$transform `(,accessor key ,hash-table) element-type)))
                             :rule-classes
                             (:rewrite
                              :type-prescription)
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    ,(if copyable
                                         'lem-hash-table$c::element-recognizer-of-accessor/copyable
                                         'lem-hash-table$c::element-recognizer-of-accessor/unique)
                                    ,@fi-bindings))))))

                  (defthm ,accessor-of-creator
                    (equal (,accessor key (,creator))
                           ,(if stobj-creator
                                `(,stobj-creator)
                                default-value-name))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$c::accessor-of-creator/copyable
                                'lem-hash-table$c::accessor-of-creator/unique)
                           ,@fi-bindings))))

                  (defthm ,accessor-of-updater-same
                    (implies (equal %key key)
                             (equal (,accessor %key (,updater key value ,hash-table))
                                    value))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-hash-table$c::accessor-of-updater-same
                           ,@fi-bindings))))

                  (defthm ,accessor-of-updater-diff
                    (implies (not (equal %key key))
                             (equal (,accessor %key (,updater key value ,hash-table))
                                    (,accessor %key ,hash-table)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-hash-table$c::accessor-of-updater-diff
                           ,@fi-bindings))))

                  (defthm ,accessor-of-remover-same
                    (implies (equal %key key)
                             (equal (,accessor %key (,remover key ,hash-table))
                                    ,(if stobj-creator
                                         `(,stobj-creator)
                                         default-value-name)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-hash-table$c::accessor-of-remover-same
                           ,@fi-bindings))))

                  (defthm ,accessor-of-remover-diff
                    (implies (not (equal %key key))
                             (equal (,accessor %key (,remover key ,hash-table))
                                    (,accessor %key ,hash-table)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-hash-table$c::accessor-of-remover-diff
                           ,@fi-bindings))))

                  ,@(and copyable
                         `((defthm ,accessor-of-keys-set
                             (equal (,accessor key (,keys-set set ,hash-table))
                                    (,accessor key ,hash-table))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$c::accessor-of-keys-set
                                    ,@fi-bindings))))))

                  ;; `UPDATER'
                  (defthm ,updater-tp
                    (implies (,recognizer ,hash-table)
                             (and (consp (,updater key value ,hash-table))
                                  (true-listp (,updater key value ,hash-table))))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$c::updater/copyable-tp
                                'lem-hash-table$c::updater/unique-tp)
                           ,@fi-bindings))))

                  ;; `BOUNDP'
                  (defthm ,boundp-tp
                    (booleanp (,boundp key ,hash-table))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-hash-table$c::boundp-tp
                           ,@fi-bindings))))

                  (defthm ,boundp-of-creator
                    (not (,boundp key (,creator)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$c::boundp-of-creator/copyable
                                'lem-hash-table$c::boundp-of-creator/unique)
                           ,@fi-bindings))))

                  (defthm ,boundp-of-updater-same
                    (implies (equal %key key)
                             (equal (,boundp %key (,updater key value ,hash-table))
                                    t))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-hash-table$c::boundp-of-updater-same
                           ,@fi-bindings))))

                  (defthm ,boundp-of-updater-diff
                    (implies (not (equal %key key))
                             (equal (,boundp %key (,updater key value ,hash-table))
                                    (,boundp %key ,hash-table)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-hash-table$c::boundp-of-updater-diff
                           ,@fi-bindings))))

                  (defthm ,boundp-of-remover-same
                    (implies (equal %key key)
                             (not (,boundp %key (,remover key ,hash-table))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-hash-table$c::boundp-of-remover-same
                           ,@fi-bindings))))

                  (defthm ,boundp-of-remover-diff
                    (implies (not (equal %key key))
                             (equal (,boundp %key (,remover key ,hash-table))
                                    (,boundp %key ,hash-table)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-hash-table$c::boundp-of-remover-diff
                           ,@fi-bindings))))

                  ,@(and copyable
                         `((defthm ,boundp-of-keys-set
                             (equal (,boundp key (,keys-set set ,hash-table))
                                    (,boundp key ,hash-table))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$c::boundp-of-keys-set
                                    ,@fi-bindings))))))

                  ;; `GETP'
                  (defthm ,getp-tp
                    (and (consp (,getp key ,hash-table))
                         (true-listp (,getp key ,hash-table)))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-hash-table$c::getp-tp
                           ,@fi-bindings))))

                  (defthm ,getp-rw
                    (mv-let (v0 v1)
                            (,getp key ,hash-table)
                      (and (equal v0 (,accessor key ,hash-table))
                           (equal v1 (,boundp key ,hash-table))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-hash-table$c::getp-rw
                           ,@fi-bindings))))

                  ;; `REMOVER'
                  (defthm ,remover-tp
                    (implies (,recognizer ,hash-table)
                             (and (consp (,remover key ,hash-table))
                                  (true-listp (,remover key ,hash-table))))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$c::remover/copyable-tp
                                'lem-hash-table$c::remover/unique-tp)
                           ,@fi-bindings))))

                  (defthm ,remover-of-creator
                    (equal (,remover key (,creator))
                           (,creator))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$c::remover-of-creator/copyable
                                'lem-hash-table$c::remover-of-creator/unique)
                           ,@fi-bindings))))

                  (defthm ,remover-of-updater-same
                    (implies (equal %key key)
                             (equal (,remover %key (,updater key value ,hash-table))
                                    (,remover %key ,hash-table)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-hash-table$c::remover-of-updater-same
                           ,@fi-bindings))))

                  (defthm ,remover-of-updater-diff
                    (implies (not (equal %key key))
                             (equal (,remover %key (,updater key value ,hash-table))
                                    (,updater key value (,remover %key ,hash-table))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-hash-table$c::remover-of-updater-diff
                           ,@fi-bindings))))

                  (defthm ,remover-of-remover-same
                    (implies (equal %key key)
                             (equal (,remover %key (,remover key ,hash-table))
                                    (,remover %key ,hash-table)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-hash-table$c::remover-of-remover-same
                           ,@fi-bindings))))

                  (defthm ,remover-of-remover-diff
                    (implies (not (equal %key key))
                             (equal (,remover %key (,remover key ,hash-table))
                                    (,remover key (,remover %key ,hash-table))))
                    :rule-classes
                    ((:rewrite :loop-stopper ((%key key ,remover))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-hash-table$c::remover-of-remover-diff
                           ,@fi-bindings))))

                  ;; `COUNT'
                  (defthm ,count-tp
                    (natp (,count ,hash-table))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-hash-table$c::count-tp
                           ,@fi-bindings))))

                  (defthm ,count-of-creator
                    (equal (,count (,creator)) 0)
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$c::count-of-creator/copyable
                                'lem-hash-table$c::count-of-creator/unique)
                           ,@fi-bindings))))

                  (defthm ,count-of-updater-when-boundp
                    (implies (,boundp key ,hash-table)
                             (equal (,count (,updater key value ,hash-table))
                                    (,count ,hash-table)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-hash-table$c::count-of-updater-when-boundp
                           ,@fi-bindings))))

                  (defthm ,count-of-updater-when-not-boundp
                    (implies (not (,boundp key ,hash-table))
                             (equal (,count (,updater key value ,hash-table))
                                    (1+ (,count ,hash-table))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-hash-table$c::count-of-updater-when-not-boundp
                           ,@fi-bindings))))

                  (defthm ,count-of-remover-when-boundp
                    (implies (,boundp key ,hash-table)
                             (equal (,count (,remover key ,hash-table))
                                    (1- (,count ,hash-table))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-hash-table$c::count-of-remover-when-boundp
                           ,@fi-bindings))))

                  (defthm ,count-of-remover-when-not-boundp
                    (implies (not (,boundp key ,hash-table))
                             (equal (,count (,remover key ,hash-table))
                                    (,count ,hash-table)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-hash-table$c::count-of-remover-when-not-boundp
                           ,@fi-bindings))))

                  ,@(and copyable
                         `((defthm ,count-of-keys-set
                             (equal (,count (,keys-set set ,hash-table))
                                    (,count ,hash-table))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$c::count-of-keys-set
                                    ,@fi-bindings))))))

                  ;; `%CLEAR'
                  (defthm ,%clear-tp
                    (implies (,recognizer ,hash-table)
                             (and (consp (,%clear ,hash-table))
                                  (true-listp (,%clear ,hash-table))))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$c::%clear/copyable-tp
                                'lem-hash-table$c::%clear/unique-tp)
                           ,@fi-bindings))))

                  (defthm ,%clear-rw
                    (implies (,recognizer ,hash-table)
                             (equal (,%clear ,hash-table)
                                    ,(if copyable
                                         `(,keys-set (,keys ,hash-table) (,creator))
                                         `(,creator))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$c::%clear/copyable-rw
                                'lem-hash-table$c::%clear/unique-rw)
                           ,@fi-bindings))))

                  ;; `%INIT'
                  (defthm ,%init-tp
                    (implies (,recognizer ,hash-table)
                             (and (consp (,%init ht-size rehash-size rehash-threshold ,hash-table))
                                  (true-listp (,%init ht-size rehash-size rehash-threshold ,hash-table))))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$c::%init/copyable-tp
                                'lem-hash-table$c::%init/unique-tp)
                           ,@fi-bindings))))

                  (defthm ,%init-rw
                    (implies (,recognizer ,hash-table)
                             (equal (,%init ht-size rehash-size rehash-threshold ,hash-table)
                                    ,(if copyable
                                         `(,keys-set (,keys ,hash-table) (,creator))
                                         `(,creator))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$c::%init/copyable-rw
                                'lem-hash-table$c::%init/unique-rw)
                           ,@fi-bindings))))

                  ;; `KEYS'
                  ,@(and copyable
                         `((defthm ,keys-of-creator
                             (not (,keys (,creator)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$c::keys-of-creator/copyable
                                    ,@fi-bindings))))

                           (defthm ,keys-of-updater
                             (equal (,keys (,updater key value ,hash-table))
                                    (,keys ,hash-table))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$c::keys-of-updater
                                    ,@fi-bindings))))

                           (defthm ,keys-of-remover
                             (equal (,keys (,remover key ,hash-table))
                                    (,keys ,hash-table))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$c::keys-of-remover
                                    ,@fi-bindings))))

                           (defthm ,keys-of-keys-set
                             (equal (,keys (,keys-set set ,hash-table))
                                    set)
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$c::keys-of-keys-set
                                    ,@fi-bindings))))))

                  ;; `KEYS-SET'
                  ,@(and copyable
                         `((defthm ,keys-set-tp
                             (implies (,recognizer ,hash-table)
                                      (and (consp (,keys-set set ,hash-table))
                                           (true-listp (,keys-set set ,hash-table))))
                             :rule-classes :type-prescription
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$c::keys-set-tp
                                    ,@fi-bindings))))

                           (defthm ,keys-set-of-updater
                             (equal (,keys-set set (,updater key value ,hash-table))
                                    (,updater key value (,keys-set set ,hash-table)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$c::keys-set-of-updater
                                    ,@fi-bindings))))

                           (defthm ,keys-set-of-remover
                             (equal (,keys-set set (,remover key ,hash-table))
                                    (,remover key (,keys-set set ,hash-table)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$c::keys-set-of-remover
                                    ,@fi-bindings))))

                           (defthm ,keys-set-of-keys-set
                             (equal (,keys-set %set (,keys-set set ,hash-table))
                                    (,keys-set %set ,hash-table))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$c::keys-set-of-keys-set
                                    ,@fi-bindings))))))

                  ;; `FIXER'
                  (defun-inline ,fixer (,hash-table)
                    (declare (xargs :stobjs ,hash-table))
                    (mbe :logic (if (,recognizer ,hash-table)
                                    ,hash-table
                                    (,creator))
                         :exec ,hash-table))

                  (table fixer ',hash-table ',fixer)

                  (defthm ,fixer-tp
                    (and (consp (,fixer ,hash-table))
                         (true-listp (,fixer ,hash-table)))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$c::fixer/copyable-tp
                                'lem-hash-table$c::fixer/unique-tp)
                           ,@fi-bindings-with-fixer))))

                  (defthm ,recognizer-of-fixer
                    (,recognizer (,fixer ,hash-table))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$c::recognizer/copyable-of-fixer/copyable
                                'lem-hash-table$c::recognizer/unique-of-fixer/unique)
                           ,@fi-bindings-with-fixer))))

                  (defthm ,fixer-when-recognizer
                    (implies (,recognizer ,hash-table)
                             (equal (,fixer ,hash-table)
                                    ,hash-table))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$c::fixer/copyable-when-recognizer/copyable
                                'lem-hash-table$c::fixer/unique-when-recognizer/unique)
                           ,@fi-bindings-with-fixer))))

                  (defthm ,fixer-when-not-recognizer
                    (implies (not (,recognizer ,hash-table))
                             (equal (,fixer ,hash-table)
                                    (,creator)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if copyable
                                'lem-hash-table$c::fixer/copyable-when-not-recognizer/copyable
                                'lem-hash-table$c::fixer/unique-when-not-recognizer/unique)
                           ,@fi-bindings-with-fixer))))

                  ;; `CLEAR'
                  ,@(and copyable
                         `((defun ,clear (,hash-table)
                             (declare (xargs :stobjs ,hash-table))
                             (let* ((,hash-table (mbe :logic (,fixer ,hash-table)
                                                      :exec ,hash-table))
                                    (,hash-table (,keys-set '() ,hash-table)))
                               (,%clear ,hash-table)))

                           (table clear ',hash-table ',clear)

                           (defthm ,clear-tp
                             (implies (,recognizer ,hash-table)
                                      (and (consp (,clear ,hash-table))
                                           (true-listp (,clear ,hash-table))))
                             :rule-classes :type-prescription
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$c::clear-tp
                                    ,@fi-bindings-with-fixer-and-clear))))

                           (defthm ,clear-rw
                             (implies (,recognizer ,hash-table)
                                      (equal (,clear ,hash-table)
                                             (,creator)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$c::clear-rw
                                    ,@fi-bindings-with-fixer-and-clear))))))

                  ;; `INIT'
                  ,@(and copyable
                         `((defun ,init (ht-size rehash-size rehash-threshold ,hash-table)
                             (declare (xargs :stobjs ,hash-table
                                             :guard (and (or (natp ht-size)
                                                             (not ht-size))
                                                         (or (and (rationalp rehash-size)
                                                                  (<= 1 rehash-size))
                                                             (not rehash-size))
                                                         (or (and (rationalp rehash-threshold)
                                                                  (<= 0 rehash-threshold)
                                                                  (<= rehash-threshold 1))
                                                             (not rehash-threshold)))))
                             (let* ((,hash-table (mbe :logic (,fixer ,hash-table)
                                                      :exec ,hash-table))
                                    (,hash-table (,keys-set '() ,hash-table)))
                               (,%init ht-size rehash-size rehash-threshold ,hash-table)))

                           (table init ',hash-table ',init)

                           (defthm ,init-tp
                             (implies (,recognizer ,hash-table)
                                      (and (consp (,init ht-size rehash-size rehash-threshold ,hash-table))
                                           (true-listp (,init ht-size rehash-size rehash-threshold ,hash-table))))
                             :rule-classes :type-prescription
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$c::init-tp
                                    ,@fi-bindings-with-fixer-and-clear-and-init))))

                           (defthm ,init-rw
                             (implies (,recognizer ,hash-table)
                                      (equal (,init ht-size rehash-size rehash-threshold ,hash-table)
                                             (,creator)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-hash-table$c::init-rw
                                    ,@fi-bindings-with-fixer-and-clear-and-init)))))))))

         `(progn
            ,@prologue

            ,body

            ,@epilogue

            (table package-witness ',hash-table ',package-witness))))))
