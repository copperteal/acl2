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
(include-book "../lemmas/hash-table$c")
||#

(include-book "../type-spec")
(include-book "../utilities/top")


;;;; `HASH-TABLE' Guard Predicates
(defun valid-hash-table-test-p (test)
  (declare (xargs :guard t))
; TODO: refactor into separate file
;
; TODO: use memberp. library wide check member usage
  (and (member test '(eq eql hons-equal equal))
       t))

(defthm valid-hash-table-test-p{compound-recognizer}
; TODO: Is this theorem useful?
  (implies (valid-hash-table-test-p test)
           (and (symbolp test)
                (not (booleanp test))))
  :rule-classes :compound-recognizer)

(defun valid-hash-table-size-p (size)
  (declare (xargs :guard t))
; TODO: refactor into separate file
  (or (null size)
      (natp size)))

(defthm valid-hash-table-size-p{compound-recognizer}
; TODO: Is this theorem useful?
  (implies (valid-hash-table-size-p size)
           (or (null size)
               (natp size)))
  :rule-classes :compound-recognizer)


;;;; `DEFINE-HASH-TABLE$C'
(defmacro define-hash-table$c
    (hash-table test
     &key
       (size 'nil)
       (element-type 't)
       (default-value 'nil)
       (copyable 't)

       (inline 'nil)
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

       (debug 'nil))

  (declare (xargs :guard (and (symbolp hash-table)
                              (valid-hash-table-test-p test)
                              (valid-hash-table-size-p size)
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
                              (booleanp debug))))

  (let* (
; TODO: enable defined constant size
         (contents (or contents
                       (symbolicate hash-table hash-table "-CONTENTS")))
         (contents-recognizer-stobj-default (symbolicate hash-table contents "P"))
         (contents-recognizer (or contents-recognizer
                                  (symbolicate hash-table contents (make-predicate-suffix contents))))
         (recognizer-stobj-default (symbolicate hash-table hash-table "P"))
         (recognizer (or recognizer
                         (symbolicate hash-table hash-table (make-predicate-suffix hash-table))))
         (creator-stobj-default (symbolicate hash-table "CREATE-" hash-table))
         (creator (or creator
                      (symbolicate hash-table "CREATE-" hash-table)))
         (fixer (or fixer
                    (symbolicate hash-table hash-table "-FIX")))
         (accessor-stobj-default (symbolicate hash-table contents "-GET"))
         (accessor (or accessor
                       (symbolicate hash-table hash-table "-GET")))
         (updater-stobj-default (symbolicate hash-table contents "-PUT"))
         (updater (or updater
                      (symbolicate hash-table hash-table "-PUT")))
         (boundp-stobj-default (symbolicate hash-table contents "-BOUNDP"))
         (boundp (or boundp
                     (symbolicate hash-table hash-table "-BOUNDP")))
         (getp-stobj-default (symbolicate hash-table contents "-GET?"))
         (getp (or getp
                   (symbolicate hash-table hash-table "-GETP")))
         (remover-stobj-default (symbolicate hash-table contents "-REM"))
         (remover (or remover
                      (symbolicate hash-table hash-table "-REM")))
         (count-stobj-default (symbolicate hash-table contents "-COUNT"))
         (count (or count
                    (symbolicate hash-table hash-table "-COUNT")))
         (clear-stobj-default (symbolicate hash-table contents "-CLEAR"))
         (clear (or clear
                    (symbolicate hash-table hash-table "-CLEAR")))
         (%clear (if copyable
                     (symbolicate hash-table hash-table "-%CLEAR")
                     clear))
         (init-stobj-default (symbolicate hash-table contents "-INIT"))
         (init (or init
                   (symbolicate hash-table hash-table "-INIT")))
         (%init (if copyable
                    (symbolicate hash-table hash-table "-%INIT")
                    init))
         (keys (or keys
                   (symbolicate hash-table hash-table "-KEYS")))
         (keys-set-stobj-default (symbolicate hash-table "UPDATE-" keys))
         (keys-set (or keys-set
                       (symbolicate hash-table keys "-SET")))

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
                                `((,keys-set-stobj-default ,keys-set))))))

    `(with-output
       ,@(and (not debug)
              '#!acl2(:off (warning! observation prove event history proof-tree)
                           :summary-off (rules)
                           :gag-mode t))

       (make-event
         (let* ((hash-table ',hash-table)
                (test ',test)
                (size ',size)

                (element-type ',element-type)
                (stobj-property (and (symbolp element-type)
                                     (getpropc element-type 'stobj)))
                (absstobj-info (and (symbolp element-type)
                                    (getpropc element-type 'absstobj-info)))
                (stobj$a-property (and (symbolp element-type)
                                       (cdr (assoc element-type (table-alist 'stobj$a-property (w state))))))
                (element-recognizer (cond
                                      (stobj$a-property
                                       (first (second stobj$a-property)))
                                      (absstobj-info
                                       (second (second absstobj-info)))
                                      (stobj-property
                                       (caadr stobj-property))))
                (element-creator (cond
                                   (stobj$a-property
                                    (second (second stobj$a-property)))
                                   (absstobj-info
                                    (second (third absstobj-info)))
                                   (stobj-property
                                    (cdadr stobj-property))))
                (default-value ',default-value)
                (default-value-name (symbolicate hash-table "*" hash-table "-DEFAULT-VALUE*"))
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
                (%clear ',%clear)
                (clear ',clear)
                (%init ',%init)
                (init ',init)
                (keys ',keys)
                (keys-set ',keys-set)

                (hash-table-begin (symbolicate hash-table hash-table "-BEGIN"))
                (hash-table-end (symbolicate hash-table hash-table "-END"))
                (prologue
                 `((deflabel ,hash-table-begin)

                   ,@(and (not stobj-property)
                          `((defconst ,default-value-name ',default-value)))

                   (defstobj ,hash-table
                     (,contents :type (hash-table ,test ,size ,element-type)
                                ,@(and (not stobj-property)
                                       `(:initially ,default-value)))
                     ,@(and ',copyable
                            `((,keys)))
                     :renaming ,',doublets
                     :inline ,inline
                     :non-memoizable ,(not memoizable)
                     :non-executable ,(not executable))))

                (contents-recognizer{type-prescription} (symbolicate hash-table contents-recognizer "{TYPE-PRESCRIPTION}"))

                (recognizer{type-prescription} (symbolicate hash-table recognizer "{TYPE-PRESCRIPTION}"))
                (recognizer{compound-recognizer} (symbolicate hash-table recognizer "{COMPOUND-RECOGNIZER}"))
                (recognizer-of-creator (symbolicate hash-table recognizer "-OF-" creator))
                (recognizer-of-updater (symbolicate hash-table recognizer "-OF-" updater))
                (recognizer-of-remover (symbolicate hash-table recognizer "-OF-" remover))
                (recognizer-of-%clear (symbolicate hash-table recognizer "-OF-" %clear))
                (recognizer-of-%init (symbolicate hash-table recognizer "-OF-" %init))
                (recognizer-of-keys-set (symbolicate hash-table recognizer "-OF-" keys-set))

                (typep$-of-accessor (symbolicate hash-table "TYPEP$-OF-" accessor))
                (accessor-of-creator (symbolicate hash-table accessor "-OF-" creator))
                (accessor-of-updater (symbolicate hash-table accessor "-OF-" updater))
                (accessor-of-updater-same (symbolicate hash-table accessor-of-updater "-SAME"))
                (accessor-of-updater-diff (symbolicate hash-table accessor-of-updater "-DIFF"))
                (accessor-when-not-boundp (symbolicate hash-table accessor "-WHEN-NOT-" boundp))
                (accessor-of-remover (symbolicate hash-table accessor "-OF-" remover))
                (accessor-of-remover-same (symbolicate hash-table accessor-of-remover "-SAME"))
                (accessor-of-remover-diff (symbolicate hash-table accessor-of-remover "-DIFF"))
                (accessor-of-keys-set (symbolicate hash-table accessor "-OF-" keys-set))

                (updater{type-prescription} (symbolicate hash-table updater "{TYPE-PRESCRIPTION}"))

                (boundp{type-prescription} (symbolicate hash-table boundp "{TYPE-PRESCRIPTION}"))
                (boundp-of-creator (symbolicate hash-table boundp "-OF-" creator))
                (boundp-of-updater (symbolicate hash-table boundp "-OF-" updater))
                (boundp-of-updater-same (symbolicate hash-table boundp-of-updater "-SAME"))
                (boundp-of-updater-diff (symbolicate hash-table boundp-of-updater "-DIFF"))
                (boundp-of-remover (symbolicate hash-table boundp "-OF-" remover))
                (boundp-of-remover-same (symbolicate hash-table boundp-of-remover "-SAME"))
                (boundp-of-remover-diff (symbolicate hash-table boundp-of-remover "-DIFF"))
                (boundp-of-keys-set (symbolicate hash-table boundp "-OF-" keys-set))

                (getp{type-prescription} (symbolicate hash-table getp "{TYPE-PRESCRIPTION}"))
                (getp{rewrite} (symbolicate hash-table getp "{REWRITE}"))

                (remover{type-prescription} (symbolicate hash-table remover "{TYPE-PRESCRIPTION}"))
                (remover-of-creator (symbolicate hash-table remover "-OF-" creator))
                (remover-of-updater (symbolicate hash-table remover "-OF-" updater))
                (remover-of-updater-same (symbolicate hash-table remover-of-updater "-SAME"))
                (remover-of-updater-diff (symbolicate hash-table remover-of-updater "-DIFF"))
                (remover-of-remover (symbolicate hash-table remover "-OF-" remover))
                (remover-of-remover-same (symbolicate hash-table remover-of-remover "-SAME"))
                (remover-of-remover-diff (symbolicate hash-table remover-of-remover "-DIFF"))

                (count{type-prescription} (symbolicate hash-table count "{TYPE-PRESCRIPTION}"))
                (count-of-creator (symbolicate hash-table count "-OF-" creator))
                (count-of-updater (symbolicate hash-table count "-OF-" updater))
                (count-of-updater-when-boundp (symbolicate hash-table count-of-updater "-WHEN-" boundp))
                (count-of-updater-when-not-boundp (symbolicate hash-table count-of-updater "-WHEN-NOT-" boundp))
                (count-when-boundp (symbolicate hash-table count "-WHEN-" boundp))
                (count-of-remover (symbolicate hash-table count "-OF-" remover))
                (count-of-remover-when-boundp (symbolicate hash-table count-of-remover "-WHEN-" boundp))
                (count-of-remover-when-not-boundp (symbolicate hash-table count-of-remover "-WHEN-NOT-" boundp))
                (count-of-keys-set (symbolicate hash-table count "-OF-" keys-set))

                (%clear{type-prescription} (symbolicate hash-table %clear "{TYPE-PRESCRIPTION}"))
                (%clear{rewrite} (symbolicate hash-table %clear "{REWRITE}"))

                (%init{type-prescription} (symbolicate hash-table %init "{TYPE-PRESCRIPTION}"))
                (%init{rewrite} (symbolicate hash-table %init "{REWRITE}"))

                (keys-of-creator (symbolicate hash-table keys "-OF-" creator))
                (keys-of-updater (symbolicate hash-table keys "-OF-" updater))
                (keys-of-remover (symbolicate hash-table keys "-OF-" remover))
                (keys-of-keys-set (symbolicate hash-table keys "-OF-" keys-set))

                (keys-set{type-prescription} (symbolicate hash-table keys-set "{TYPE-PRESCRIPTION}"))
                (keys-set-of-updater (symbolicate hash-table keys-set "-OF-" updater))
                (keys-set-of-remover (symbolicate hash-table keys-set "-OF-" remover))
                (keys-set-of-keys-set (symbolicate hash-table keys-set "-OF-" keys-set))

                (fixer{type-prescription} (symbolicate hash-table fixer "{TYPE-PRESCRIPTION}"))
                (recognizer-of-fixer (symbolicate hash-table recognizer "-OF-" fixer))
                (fixer-when-recognizer (symbolicate hash-table fixer "-WHEN-" recognizer))
                (fixer-when-not-recognizer (symbolicate hash-table fixer "-WHEN-NOT-" recognizer))

                (clear{type-prescription} (symbolicate hash-table clear "{TYPE-PRESCRIPTION}"))
                (clear{rewrite} (symbolicate hash-table clear "{REWRITE}"))

                (init{type-prescription} (symbolicate hash-table init "{TYPE-PRESCRIPTION}"))
                (init{rewrite} (symbolicate hash-table init "{REWRITE}"))

                (hash-table-theorems (symbolicate hash-table hash-table "-THEOREMS"))
                (epilogue
                 `((deflabel ,hash-table-end)

                   (deftheory-static ,hash-table-theorems
                     (set-difference-theories
                      (set-difference-theories
                       (current-theory ',hash-table-end)
                       (current-theory ',hash-table-begin))
                      (function-theory ',hash-table-end)))

                   (in-theory
                     (union-theories (current-theory ',hash-table-begin)
                                     (theory ',hash-table-theorems)))))

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
                        `(lem-hash-table$c::element-recognizer ,(or element-recognizer
                                                                    `(lambda (value)
                                                                       ,(typep$transform 'value element-type))))
                        `(lem-hash-table$c::default-value ,(or element-creator
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
                 `(with-books (("projects/atomic-stobjs/lemmas/hash-table$c" :dir :system))
                    ;; `CONTENTS-RECOGNIZER'
                    (defthm ,contents-recognizer{type-prescription}
                      (booleanp (,contents-recognizer ,contents))
                      :rule-classes :type-prescription
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             lem-hash-table$c::contents-recognizer{type-prescription}
                             ,@fi-bindings))))

                    ;; `RECOGNIZER'
                    (defthm ,recognizer{type-prescription}
                      (booleanp (,recognizer ,hash-table))
                      :rule-classes :type-prescription
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if copyable
                                  'lem-hash-table$c::recognizer/copyable{type-prescription}
                                  'lem-hash-table$c::recognizer/unique{type-prescription})
                             ,@fi-bindings))))

                    (defthm ,recognizer{compound-recognizer}
                      (implies (,recognizer ,hash-table)
                               (and (consp ,hash-table)
                                    (true-listp ,hash-table)))
                      :rule-classes :compound-recognizer
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if copyable
                                  'lem-hash-table$c::recognizer/copyable{compound-recognizer}
                                  'lem-hash-table$c::recognizer/unique{compound-recognizer})
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
                                          ,(if element-recognizer
                                               `(,element-recognizer value)
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
                                      ,(if copyable
                                           'lem-hash-table$c::recognizer/copyable-of-keys-set
                                           'lem-hash-table$c::recognizer/unique-of-keys-set)
                                      ,@fi-bindings))))))

                    ;; `ACCESSOR'
                    ,@(and (not (eq element-type t))
                           `((defthm ,typep$-of-accessor
                               (implies (,recognizer ,hash-table)
                                        ,(if element-recognizer
                                             `(,element-recognizer (,accessor key ,hash-table))
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
                             ,(if element-creator
                                  `(,element-creator)
                                  default-value-name))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if copyable
                                  'lem-hash-table$c::accessor-of-creator/copyable
                                  'lem-hash-table$c::accessor-of-creator/unique)
                             ,@fi-bindings))))

                    (defthmd ,accessor-of-updater
                      (equal (,accessor %key (,updater key value ,hash-table))
                             (if (equal %key key)
                                 value
                                 (,accessor %key ,hash-table)))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             lem-hash-table$c::accessor-of-updater
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

                    (defthmd ,accessor-when-not-boundp
                      (implies (not (,boundp key ,hash-table))
                               (equal (,accessor key ,hash-table)
                                      ,(if element-creator
                                           `(,element-creator)
                                           default-value-name)))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             lem-hash-table$c::accessor-when-not-boundp
                             ,@fi-bindings))))

                    (defthmd ,accessor-of-remover
                      (equal (,accessor %key (,remover key ,hash-table))
                             (if (equal %key key)
                                 ,(if element-creator
                                      `(,element-creator)
                                      default-value-name)
                                 (,accessor %key ,hash-table)))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             lem-hash-table$c::accessor-of-remover
                             ,@fi-bindings))))

                    (defthm ,accessor-of-remover-same
                      (implies (equal %key key)
                               (equal (,accessor %key (,remover key ,hash-table))
                                      ,(if element-creator
                                           `(,element-creator)
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
                    (defthm ,updater{type-prescription}
                      (implies (,recognizer ,hash-table)
                               (and (consp (,updater key value ,hash-table))
                                    (true-listp (,updater key value ,hash-table))))
                      :rule-classes :type-prescription
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if copyable
                                  'lem-hash-table$c::updater{type-prescription}/copyable
                                  'lem-hash-table$c::updater{type-prescription}/unique)
                             ,@fi-bindings))))

                    ;; `BOUNDP'
                    (defthm ,boundp{type-prescription}
                      (booleanp (,boundp key ,hash-table))
                      :rule-classes :type-prescription
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             lem-hash-table$c::boundp{type-prescription}
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

                    (defthmd ,boundp-of-updater
                      (equal (,boundp %key (,updater key value ,hash-table))
                             (or (equal %key key)
                                 (,boundp %key ,hash-table)))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             lem-hash-table$c::boundp-of-updater
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

                    (defthmd ,boundp-of-remover
                      (equal (,boundp %key (,remover key ,hash-table))
                             (if (equal %key key)
                                 nil
                                 (,boundp %key ,hash-table)))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             lem-hash-table$c::boundp-of-remover
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
                    (defthm ,getp{type-prescription}
                      (and (consp (,getp key ,hash-table))
                           (true-listp (,getp key ,hash-table)))
                      :rule-classes :type-prescription
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             lem-hash-table$c::getp{type-prescription}
                             ,@fi-bindings))))

                    (defthm ,getp{rewrite}
                      (mv-let (v0 v1)
                              (,getp key ,hash-table)
                        (and (equal v0 (,accessor key ,hash-table))
                             (equal v1 (,boundp key ,hash-table))))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             lem-hash-table$c::getp{rewrite}
                             ,@fi-bindings))))

                    ;; `REMOVER'
                    (defthm ,remover{type-prescription}
                      (implies (,recognizer ,hash-table)
                               (and (consp (,remover key ,hash-table))
                                    (true-listp (,remover key ,hash-table))))
                      :rule-classes :type-prescription
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if copyable
                                  'lem-hash-table$c::remover{type-prescription}/copyable
                                  'lem-hash-table$c::remover{type-prescription}/unique)
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

                    (defthmd ,remover-of-updater
                      (equal (,remover %key (,updater key value ,hash-table))
                             (if (equal %key key)
                                 (,remover %key ,hash-table)
                                 (,updater key value (,remover %key ,hash-table))))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             lem-hash-table$c::remover-of-updater
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
                    (defthm ,count{type-prescription}
                      (natp (,count ,hash-table))
                      :rule-classes :type-prescription
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             lem-hash-table$c::count{type-prescription}
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

                    (defthmd ,count-of-updater
                      (equal (,count (,updater key value ,hash-table))
                             (if (,boundp key ,hash-table)
                                 (,count ,hash-table)
                                 (1+ (,count ,hash-table))))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             lem-hash-table$c::count-of-updater
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

                    (defthm ,count-when-boundp
                      (implies (,boundp key ,hash-table)
                               (posp (,count ,hash-table)))
                      :rule-classes :type-prescription
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             lem-hash-table$c::count-when-boundp
                             ,@fi-bindings))))

                    (defthmd ,count-of-remover
                      (equal (,count (,remover key ,hash-table))
                             (if (,boundp key ,hash-table)
                                 (1- (,count ,hash-table))
                                 (,count ,hash-table)))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             lem-hash-table$c::count-of-remover
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
                    (defthm ,%clear{type-prescription}
                      (implies (,recognizer ,hash-table)
                               (and (consp (,%clear ,hash-table))
                                    (true-listp (,%clear ,hash-table))))
                      :rule-classes :type-prescription
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if copyable
                                  'lem-hash-table$c::%clear{type-prescription}/copyable
                                  'lem-hash-table$c::%clear{type-prescription}/unique)
                             ,@fi-bindings))))

                    (defthm ,%clear{rewrite}
                      (implies (,recognizer ,hash-table)
                               (equal (,%clear ,hash-table)
                                      ,(if copyable
                                           `(,keys-set (,keys ,hash-table) (,creator))
                                           `(,creator))))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if copyable
                                  'lem-hash-table$c::%clear{rewrite}/copyable
                                  'lem-hash-table$c::%clear{rewrite}/unique)
                             ,@fi-bindings))))

                    ;; `%INIT'
                    (defthm ,%init{type-prescription}
                      (implies (,recognizer ,hash-table)
                               (and (consp (,%init ht-size rehash-size rehash-threshold ,hash-table))
                                    (true-listp (,%init ht-size rehash-size rehash-threshold ,hash-table))))
                      :rule-classes :type-prescription
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if copyable
                                  'lem-hash-table$c::%init{type-prescription}/copyable
                                  'lem-hash-table$c::%init{type-prescription}/unique)
                             ,@fi-bindings))))

                    (defthm ,%init{rewrite}
                      (implies (,recognizer ,hash-table)
                               (equal (,%init ht-size rehash-size rehash-threshold ,hash-table)
                                      ,(if copyable
                                           `(,keys-set (,keys ,hash-table) (,creator))
                                           `(,creator))))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if copyable
                                  'lem-hash-table$c::%init{rewrite}/copyable
                                  'lem-hash-table$c::%init{rewrite}/unique)
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
                           `((defthm ,keys-set{type-prescription}
                               (implies (,recognizer ,hash-table)
                                        (and (consp (,keys-set set ,hash-table))
                                             (true-listp (,keys-set set ,hash-table))))
                               :rule-classes :type-prescription
                               :hints
                               (("Goal"
                                 :by (:functional-instance
                                      lem-hash-table$c::keys-set{type-prescription}
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

                    (defthm ,fixer{type-prescription}
                      (and (consp (,fixer ,hash-table))
                           (true-listp (,fixer ,hash-table)))
                      :rule-classes :type-prescription
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if copyable
                                  'lem-hash-table$c::fixer/copyable{type-prescription}
                                  'lem-hash-table$c::fixer/unique{type-prescription})
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
                               (let* ((,hash-table (,fixer ,hash-table))
                                      (,hash-table (,keys-set '() ,hash-table)))
                                 (,%clear ,hash-table)))

                             (defthm ,clear{type-prescription}
                               (implies (,recognizer ,hash-table)
                                        (and (consp (,clear ,hash-table))
                                             (true-listp (,clear ,hash-table))))
                               :rule-classes :type-prescription
                               :hints
                               (("Goal"
                                 :by (:functional-instance
                                      lem-hash-table$c::clear{type-prescription}
                                      ,@fi-bindings-with-fixer-and-clear))))

                             (defthm ,clear{rewrite}
                               (implies (,recognizer ,hash-table)
                                        (equal (,clear ,hash-table)
                                               (,creator)))
                               :hints
                               (("Goal"
                                 :by (:functional-instance
                                      lem-hash-table$c::clear{rewrite}
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
                               (let* ((,hash-table (,fixer ,hash-table))
                                      (,hash-table (,keys-set '() ,hash-table)))
                                 (,%init ht-size rehash-size rehash-threshold ,hash-table)))

                             (defthm ,init{type-prescription}
                               (implies (,recognizer ,hash-table)
                                        (and (consp (,init ht-size rehash-size rehash-threshold ,hash-table))
                                             (true-listp (,init ht-size rehash-size rehash-threshold ,hash-table))))
                               :rule-classes :type-prescription
                               :hints
                               (("Goal"
                                 :by (:functional-instance
                                      lem-hash-table$c::init{type-prescription}
                                      ,@fi-bindings-with-fixer-and-clear-and-init))))

                             (defthm ,init{rewrite}
                               (implies (,recognizer ,hash-table)
                                        (equal (,init ht-size rehash-size rehash-threshold ,hash-table)
                                               (,creator)))
                               :hints
                               (("Goal"
                                 :by (:functional-instance
                                      lem-hash-table$c::init{rewrite}
                                      ,@fi-bindings-with-fixer-and-clear-and-init)))))))))

           `(progn
              ,@prologue

              ,body

              ,@epilogue))))))
