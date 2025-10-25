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
(include-book "../lemmas/vector$c")
||#

(include-book "../type-spec")
(include-book "../utilities/top")


;;;; `VECTOR' Guard Predicates
(defun valid-vector-dimensions-p (dimensions)
; TODO: refactor into separate file
  (declare (xargs :guard t))
  (or (and (consp dimensions)
           (natp (car dimensions))
           (null (cdr dimensions)))
      (natp dimensions)))

(defthm valid-vector-dimensions-p{compound-recognizer}
; TODO: Is this theorem useful?
  (implies (valid-vector-dimensions-p dimensions)
           (or (natp dimensions)
               (and (consp dimensions)
                    (true-listp dimensions))))
  :rule-classes :compound-recognizer)


;;;; `DEFINE-VECTOR$C'
(defmacro define-vector$c
    (vector dimensions
     &key
       (element-type 't)
       (specialize-element-type 'nil)
       (initial-element 'nil)
       (resizable 'nil)

       (inline 'nil)
       (memoizable 'nil)
       (executable 'nil)

       (contents 'nil)
       (contents-recognizer 'nil)
       (recognizer 'nil)
       (creator 'nil)
       (fixer 'nil)
       (length 'nil)
       (resizer 'nil)
       (accessor 'nil)
       (updater 'nil)

       (debug 'nil))

  (declare (xargs :guard (and (symbolp vector)
                              (valid-vector-dimensions-p dimensions)
                              (if (acl2-type-spec-p element-type)
                                  (typep$ initial-element element-type)
; TODO: What's the best macro-guard for a value that is expected to be a stobj
; name?  We cannot actually check if it is a stobj name until we are within an
; event's scope.  However, it is desirable to reject the value eagerly if
; possible.
                                  (symbolp element-type))
                              (boolean-listp (list specialize-element-type
                                                   resizable
                                                   inline
                                                   memoizable
                                                   executable))
                              (symbol-listp (list contents
                                                  contents-recognizer
                                                  recognizer
                                                  creator
                                                  fixer
                                                  length
                                                  resizer
                                                  accessor
                                                  updater))
                              (booleanp debug))))

  (let* (
; TODO: Enable defined constant default length via the `CONST' property and move
; this into `MAKE-EVENT'
         (dimensions (if (consp dimensions)
                         dimensions
                         (list dimensions)))

         (contents (or contents
                       (symbolicate vector vector "-CONTENTS")))
         (contents-recognizer-stobj-default (symbolicate vector contents "P"))
         (contents-recognizer (or contents-recognizer
                                  (symbolicate vector contents (make-predicate-suffix contents))))
         (recognizer-stobj-default (symbolicate vector vector "P"))
         (recognizer (or recognizer
                         (symbolicate vector vector (make-predicate-suffix vector))))
         (creator-stobj-default (symbolicate vector "CREATE-" vector))
         (creator (or creator
                      (symbolicate vector "CREATE-" vector)))
         (fixer (or fixer
                    (symbolicate vector vector "-FIX")))
         (length-stobj-default (symbolicate vector contents "-LENGTH"))
         (length (or length
                     (symbolicate vector vector "-LENGTH")))
         (resizer-stobj-default (symbolicate vector "RESIZE-" contents))
         (resizer (or resizer
                      (symbolicate vector vector "-RESIZE")))
         (accessor-stobj-default (symbolicate vector contents "I"))
         (accessor (or accessor
                       (symbolicate vector vector "-REF")))
         (updater-stobj-default (symbolicate vector "UPDATE-" contents "I"))
         (updater (or updater
                      (symbolicate vector vector "-SET")))

         (doublets (append (and (not (eq contents-recognizer contents-recognizer-stobj-default))
                                `((,contents-recognizer-stobj-default ,contents-recognizer)))
                           (and (not (eq recognizer recognizer-stobj-default))
                                `((,recognizer-stobj-default ,recognizer)))
                           (and (not (eq creator creator-stobj-default))
                                `((,creator-stobj-default ,creator)))
                           (and (not (eq length length-stobj-default))
                                `((,length-stobj-default ,length)))
                           (and (not (eq resizer resizer-stobj-default))
                                `((,resizer-stobj-default ,resizer)))
                           (and (not (eq accessor accessor-stobj-default))
                                `((,accessor-stobj-default ,accessor)))
                           (and (not (eq updater updater-stobj-default))
                                `((,updater-stobj-default ,updater))))))

    `(with-output
; TODO: Refactor `WITH-OUTPUT' options.  Do for all constructors.
       ,@(and (not debug)
              '#!acl2(:off (warning! observation prove event history proof-tree)
                           :summary-off (rules)
                           :gag-mode t))

       (make-event
         (let* ((vector ',vector)
                (dimensions ',dimensions)
                (default-length (car dimensions))
                (default-length-name (symbolicate vector "*" vector "-DEFAULT-LENGTH*"))

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
                (specialize-element-type ',specialize-element-type)
                (initial-element ',initial-element)
                (initial-element-name (symbolicate vector "*" vector "-INITIAL-ELEMENT*"))
                (resizable ',resizable)

                (inline ',inline)
                (memoizable ',memoizable)
                (executable ',executable)

                (contents ',contents)
                (contents-recognizer ',contents-recognizer)
                (recognizer ',recognizer)
                (creator ',creator)
                (fixer ',fixer)
                (length ',length)
                (resizer ',resizer)
                (accessor ',accessor)
                (updater ',updater)

                (vector-begin (symbolicate vector vector "-BEGIN"))
                (vector-end (symbolicate vector vector "-END"))
                (prologue
                 `((deflabel ,vector-begin)

                   (defconst ,default-length-name ',default-length)

                   ,@(and (not stobj-property)
                          `((defconst ,initial-element-name ',initial-element)))

                   (defstobj ,vector
                     (,contents :type (array ,element-type ,dimensions)
                                ,@(and (not stobj-property)
                                       `(:element-type
                                         ,(if specialize-element-type
                                              element-type
                                              t)
                                         :initially ,initial-element))
                                :resizable ,resizable)
                     :renaming ,',doublets
                     :inline ,inline
                     :non-memoizable ,(not memoizable)
                     :non-executable ,(not executable))))

                (contents-recognizer{type-prescription} (symbolicate vector contents-recognizer "{TYPE-PRESCRIPTION}"))
                (contents-recognizer{compound-recognizer} (symbolicate vector contents-recognizer "{COMPOUND-RECOGNIZER}"))

                (recognizer{type-prescription} (symbolicate vector recognizer "{TYPE-PRESCRIPTION}"))
                (recognizer{compound-recognizer} (symbolicate vector recognizer "{COMPOUND-RECOGNIZER}"))
                (recognizer-of-creator (symbolicate vector recognizer "-OF-" creator))
                (recognizer-of-resizer (symbolicate vector recognizer "-OF-" resizer))
                (recognizer-of-updater (symbolicate vector recognizer "-OF-" updater))

                (length{type-prescription} (symbolicate vector length "{TYPE-PRESCRIPTION}"))
                (length-of-creator (symbolicate vector length "-OF-" creator))
                (length-of-resizer (symbolicate vector length "-OF-" resizer))
                (length-of-updater (symbolicate vector length "-OF-" updater))
                (length{rewrite} (symbolicate vector length "{REWRITE}"))

                (resizer{type-prescription} (symbolicate vector resizer "{TYPE-PRESCRIPTION}"))
                (resizer-of-creator (symbolicate vector resizer "-OF-" creator))
                (resizer-of-length (symbolicate vector resizer "-OF-" length))
                (resizer-of-length-free (symbolicate vector resizer-of-length "-FREE"))
                (resizer-of-resizer (symbolicate vector resizer "-OF-" resizer))
                (resizer-of-updater (symbolicate vector resizer "-OF-" updater))
                (resizer-of-updater-keep (symbolicate vector resizer-of-updater "-KEEP"))
                (resizer-of-updater-drop (symbolicate vector resizer-of-updater "-DROP"))
                (resizer{rewrite} (symbolicate vector resizer "{REWRITE}"))

; TODO: Unfold type spec to name `TYPEP$-OF-ACCESSOR'
                (typep$-of-accessor (symbolicate vector (or element-recognizer "TYPEP$") "-OF-" accessor))
                (accessor-of-creator (symbolicate vector accessor "-OF-" creator))
                (accessor-of-resizer (symbolicate vector accessor "-OF-" resizer))
                (accessor-of-resizer-inner (symbolicate vector accessor-of-resizer "-INNER"))
                (accessor-of-resizer-outer (symbolicate vector accessor-of-resizer "-OUTER"))
                (accessor-of-updater (symbolicate vector accessor "-OF-" updater))
                (accessor-of-updater-same (symbolicate vector accessor-of-updater "-SAME"))
                (accessor-of-updater-diff (symbolicate vector accessor-of-updater "-DIFF"))

                (updater{type-prescription} (symbolicate vector updater "{TYPE-PRESCRIPTION}"))
                (updater-of-creator (symbolicate vector updater "-OF-" creator))
                (updater-of-resizer (symbolicate vector updater "-OF-" resizer))
                (updater-of-resizer-inner (symbolicate vector updater-of-resizer "-INNER"))
                (updater-of-resizer-outer (symbolicate vector updater-of-resizer "-OUTER"))
                (updater-of-accessor (symbolicate vector updater "-OF-" accessor))
                (updater-of-accessor-free (symbolicate vector updater-of-accessor "-FREE"))
                (updater-of-updater (symbolicate vector updater "-OF-" updater))
                (updater-of-updater-same (symbolicate vector updater-of-updater "-SAME"))
                (updater-of-updater-diff (symbolicate vector updater-of-updater "-DIFF"))

                (fixer{type-prescription} (symbolicate vector fixer "{TYPE-PRESCRIPTION}"))
                (recognizer-of-fixer (symbolicate vector recognizer "-OF-" fixer))
                (fixer-when-recognizer (symbolicate vector fixer "-WHEN-" recognizer))
                (fixer-when-not-recognizer (symbolicate vector fixer "-WHEN-NOT-" recognizer))

                (vector-theorems (symbolicate vector vector "-THEOREMS"))
                (epilogue
                 `((deflabel ,vector-end)

                   (deftheory-static ,vector-theorems
                     (set-difference-theories
                      (set-difference-theories
                       (current-theory ',vector-end)
                       (current-theory ',vector-begin))
                      (function-theory ',vector-end)))

                   (in-theory
                     (union-theories (current-theory ',vector-begin)
                                     (theory ',vector-theorems)))))

                (fi-bindings
                 (list `(lem-vector$c::default-length (lambda ()
                                                        ,default-length))
                       `(lem-vector$c::element-recognizer ,(or element-recognizer
                                                               `(lambda (value)
                                                                  ,(typep$transform 'value element-type))))
                       `(lem-vector$c::initial-element ,(or element-creator
                                                            `(lambda ()
                                                               ,initial-element-name)))
                       `(lem-vector$c::contents-recognizer ,contents-recognizer)
                       (if resizable
                           `(lem-vector$c::recognizer/resizable ,recognizer)
                           `(lem-vector$c::recognizer/fixed ,recognizer))
                       `(lem-vector$c::creator ,creator)
                       (if resizable
                           `(lem-vector$c::length/resizable ,length)
                           `(lem-vector$c::length/fixed ,length))
                       (if resizable
                           `(lem-vector$c::resizer/resizable ,resizer)
                           `(lem-vector$c::resizer/fixed ,resizer))
                       `(lem-vector$c::accessor ,accessor)
                       `(lem-vector$c::updater ,updater)))
                (fi-bindings-with-fixer
                 (cons (if resizable
                           `(lem-vector$c::fixer/resizable ,fixer)
                           `(lem-vector$c::fixer/fixed ,fixer))
                       fi-bindings))

                (body
                 `(with-books (("projects/atomic-stobjs/lemmas/vector$c" :dir :system))
                    ;; `CONTENTS-RECOGNIZER'
                    (defthm ,contents-recognizer{type-prescription}
                      (booleanp (,contents-recognizer ,contents))
                      :rule-classes :type-prescription
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             lem-vector$c::contents-recognizer{type-prescription}
                             ,@fi-bindings))))

                    (defthm ,contents-recognizer{compound-recognizer}
                      (implies (,contents-recognizer ,contents)
                               (true-listp ,contents))
                      :rule-classes :compound-recognizer
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             lem-vector$c::contents-recognizer{compound-recognizer}
                             ,@fi-bindings))))

                    ;; `RECOGNIZER'
                    (defthm ,recognizer{type-prescription}
                      (booleanp (,recognizer ,vector))
                      :rule-classes :type-prescription
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$c::recognizer/resizable{type-prescription}
                                  'lem-vector$c::recognizer/fixed{type-prescription})
                             ,@fi-bindings))))

                    (defthm ,recognizer{compound-recognizer}
                      (implies (,recognizer ,vector)
                               (and (consp ,vector)
                                    (true-listp ,vector)))
                      :rule-classes :compound-recognizer
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$c::recognizer/resizable{compound-recognizer}
                                  'lem-vector$c::recognizer/fixed{compound-recognizer})
                             ,@fi-bindings))))

                    (defthm ,recognizer-of-creator
                      (,recognizer (,creator))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$c::recognizer/resizable-of-creator
                                  'lem-vector$c::recognizer/fixed-of-creator)
                             ,@fi-bindings))))

                    ,@(and resizable
                           `((defthm ,recognizer-of-resizer
                               (implies (,recognizer ,vector)
                                        (,recognizer (,resizer length ,vector)))
                               :hints
                               (("Goal"
                                 :by (:functional-instance
                                      lem-vector$c::recognizer/resizable-of-resizer/resizable
                                      ,@fi-bindings))))))

                    (defthm ,recognizer-of-updater
                      (implies (and (natp index)
                                    (< index ,(if resizable
                                                  `(,length ,vector)
                                                  default-length-name))
                                    ,@(and (not (eq element-type t))
                                           (if element-recognizer
                                               `((,element-recognizer value))
                                               `(,(typep$transform 'value element-type))))
                                    (,recognizer ,vector))
                               (,recognizer (,updater index value ,vector)))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$c::recognizer/resizable-of-updater
                                  'lem-vector$c::recognizer/fixed-of-updater)
                             ,@fi-bindings))))

                    ;; `LENGTH'
                    (defthm ,length{type-prescription}
                      (natp (,length ,vector))
                      :rule-classes :type-prescription
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$c::length/resizable{type-prescription}
                                  'lem-vector$c::length/fixed{type-prescription})
                             ,@fi-bindings))))

                    ,@(if resizable
                          `((defthm ,length-of-creator
                              (equal (,length (,creator))
                                     ,default-length-name)
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$c::length/resizable-of-creator
                                     ,@fi-bindings))))

                            (defthm ,length-of-resizer
                              (implies (natp length)
                                       (equal (,length (,resizer length ,vector))
                                              length))
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$c::length/resizable-of-resizer/resizable
                                     ,@fi-bindings))))

                            (defthm ,length-of-updater
                              (implies (and (natp index)
                                            (< index (,length ,vector)))
                                       (equal (,length (,updater index value ,vector))
                                              (,length ,vector)))
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$c::length/resizable-of-updater
                                     ,@fi-bindings)))))

                          `((defthm ,length{rewrite}
                              (equal (,length ,vector)
                                     ,default-length-name)
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$c::length/fixed{rewrite}
                                     ,@fi-bindings))))))

                    ;; `RESIZER'
                    (defthm ,resizer{type-prescription}
                      (implies (,recognizer ,vector)
                               (and (consp (,resizer length ,vector))
                                    (true-listp (,resizer length ,vector))))
                      :rule-classes :type-prescription
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$c::resizer/resizable{type-prescription}
                                  'lem-vector$c::resizer/fixed{type-prescription})
                             ,@fi-bindings))))

                    ,@(if resizable
                          `((defthm ,resizer-of-creator
                              (implies (equal length ,default-length-name)
                                       (equal (,resizer length (,creator))
                                              (,creator)))
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$c::resizer/resizable-of-creator
                                     ,@fi-bindings))))

; TODO: Make a theory to allow enabling or disabling the vector$c theorems that
; are initially disabled.  Call it aggressive in analogy with the vector$a
; aggressive theory.  Note that the concrete interface only needs to be strong
; enough to allow users to pass the proof obligations to create custom abstract
; stobjs.  Make the theory name accessible from a table or property.

                            (defthmd ,resizer-of-length-free
                              (implies (and (equal length (,length ,vector))
                                            (,recognizer ,vector))
                                       (equal (,resizer length ,vector)
                                              ,vector))
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$c::resizer/resizable-of-length/resizable-free
                                     ,@fi-bindings))))

                            (defthm ,resizer-of-length
                              (implies (,recognizer ,vector)
                                       (equal (,resizer (,length ,vector) ,vector)
                                              ,vector))
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$c::resizer/resizable-of-length/resizable
                                     ,@fi-bindings))))

                            (defthm ,resizer-of-resizer
                              (implies (and (natp %length)
                                            (natp length)
                                            (or (<= %length length)
                                                (<= (,length ,vector) length))
                                            (,recognizer ,vector))
                                       (equal (,resizer %length (,resizer length ,vector))
                                              (,resizer %length ,vector)))
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$c::resizer/resizable-of-resizer/resizable
                                     ,@fi-bindings))))

                            (defthmd ,resizer-of-updater
                              (implies (and (natp index)
                                            (natp length)
                                            (< index (,length ,vector)))
                                       (equal (,resizer length (,updater index value ,vector))
                                              (if (< index length)
                                                  (,updater index value (,resizer length ,vector))
                                                  (,resizer length ,vector))))
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$c::resizer/resizable-of-updater
                                     ,@fi-bindings))))

                            (defthm ,resizer-of-updater-keep
                              (implies (and (natp index)
                                            (natp length)
                                            (< index length)
                                            (< index (,length ,vector)))
                                       (equal (,resizer length (,updater index value ,vector))
                                              (,updater index value (,resizer length ,vector))))
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$c::resizer/resizable-of-updater-keep
                                     ,@fi-bindings))))

                            (defthm ,resizer-of-updater-drop
                              (implies (and (natp index)
                                            (natp length)
                                            (<= length index)
                                            (< index (,length ,vector)))
                                       (equal (,resizer length (,updater index value ,vector))
                                              (,resizer length ,vector)))
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$c::resizer/resizable-of-updater-drop
                                     ,@fi-bindings)))))

                          `((defthm ,resizer{rewrite}
                              (equal (,resizer length ,vector)
                                     ,vector)
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$c::resizer/fixed{rewrite}
                                     ,@fi-bindings))))))

                    ;; `ACCESSOR'
                    ,@(and (not (eq element-type t))
                           `((defthm ,typep$-of-accessor
                               (implies (and (natp index)
                                             (< index ,(if resizable
                                                           `(,length ,vector)
                                                           default-length-name))
                                             (,recognizer ,vector))
                                        ,(if element-recognizer
                                             `(,element-recognizer (,accessor index ,vector))
; TODO: Check if `TYPEP$-OF-ACCESSOR' fails for member, unsigned-byte, or
; signed-byte.
                                             (typep$transform `(,accessor index ,vector) element-type)))
                               :rule-classes
                               (:rewrite
                                :type-prescription)
                               :hints
                               (("Goal"
                                 :by (:functional-instance
                                      ,(if resizable
                                           'lem-vector$c::element-recognizer-of-accessor/resizable
                                           'lem-vector$c::element-recognizer-of-accessor/fixed)
                                      ,@fi-bindings))))))

                    (defthm ,accessor-of-creator
                      (implies (and (natp index)
                                    (< index ,default-length-name))
                               (equal (,accessor index (,creator))
                                      ,(if element-creator
                                           `(,element-creator)
                                           initial-element-name)))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             lem-vector$c::accessor-of-creator
                             ,@fi-bindings))))

                    ,@(and resizable
                           `((defthmd ,accessor-of-resizer
                               (implies (and (natp index)
                                             (natp length)
                                             (< index length))
                                        (equal (,accessor index (,resizer length ,vector))
                                               (if (< index (,length ,vector))
                                                   (,accessor index ,vector)
                                                   ,(if element-creator
                                                        `(,element-creator)
                                                        initial-element-name))))
                               :hints
                               (("Goal"
                                 :by (:functional-instance
                                      lem-vector$c::accessor-of-resizer/resizable
                                      ,@fi-bindings))))

                             (defthm ,accessor-of-resizer-inner
                               (implies (and (natp index)
                                             (natp length)
                                             (< index length)
                                             (< index (,length ,vector)))
                                        (equal (,accessor index (,resizer length ,vector))
                                               (,accessor index ,vector)))
                               :hints
                               (("Goal"
                                 :by (:functional-instance
                                      lem-vector$c::accessor-of-resizer/resizable-inner
                                      ,@fi-bindings))))

                             (defthm ,accessor-of-resizer-outer
                               (implies (and (natp index)
                                             (natp length)
                                             (< index length)
                                             (<= (,length ,vector) index))
                                        (equal (,accessor index (,resizer length ,vector))
                                               ,(if element-creator
                                                    `(,element-creator)
                                                    initial-element-name)))
                               :hints
                               (("Goal"
                                 :by (:functional-instance
                                      lem-vector$c::accessor-of-resizer/resizable-outer
                                      ,@fi-bindings))))))

                    (defthmd ,accessor-of-updater
                      (implies (and (natp %index)
                                    (natp index))
                               (equal (,accessor %index (,updater index value ,vector))
                                      (if (equal %index index)
                                          value
                                          (,accessor %index ,vector))))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             lem-vector$c::accessor-of-updater
                             ,@fi-bindings))))

                    (defthm ,accessor-of-updater-same
                      (implies (equal %index index)
                               (equal (,accessor %index (,updater index value ,vector))
                                      value))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             lem-vector$c::accessor-of-updater-same
                             ,@fi-bindings))))

                    (defthm ,accessor-of-updater-diff
                      (implies (and (not (equal %index index))
                                    (natp %index)
                                    (natp index))
                               (equal (,accessor %index (,updater index value ,vector))
                                      (,accessor %index ,vector)))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             lem-vector$c::accessor-of-updater-diff
                             ,@fi-bindings))))

                    ;; `UPDATER'
                    (defthm ,updater{type-prescription}
                      (implies (,recognizer ,vector)
                               (and (consp (,updater index value ,vector))
                                    (true-listp (,updater index value ,vector))))
                      :rule-classes :type-prescription
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$c::updater{type-prescription}/resizable
                                  'lem-vector$c::updater{type-prescription}/fixed)
                             ,@fi-bindings))))

                    (defthm ,updater-of-creator
                      (implies (and (equal value ,(if element-creator
                                                      `(,element-creator)
                                                      initial-element-name))
                                    (natp index)
                                    (< index ,default-length-name))
                               (equal (,updater index value (,creator))
                                      (,creator)))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             lem-vector$c::updater-of-creator
                             ,@fi-bindings))))

                    ,@(and resizable
                           `((defthmd ,updater-of-resizer
                               (implies (and (natp index)
                                             (natp length)
                                             (< index length)
                                             (equal value (if (< index (,length ,vector))
                                                              (,accessor index ,vector)
                                                              ,(if element-creator
                                                                   `(,element-creator)
                                                                   initial-element-name))))
                                        (equal (,updater index value (,resizer length ,vector))
                                               (,resizer length ,vector)))
                               :hints
                               (("Goal"
                                 :by (:functional-instance
                                      lem-vector$c::updater-of-resizer/resizable
                                      ,@fi-bindings))))

                             (defthm ,updater-of-resizer-inner
                               (implies (and (equal value (,accessor index ,vector))
                                             (natp index)
                                             (natp length)
                                             (< index length)
                                             (< index (,length ,vector)))
                                        (equal (,updater index value (,resizer length ,vector))
                                               (,resizer length ,vector)))
                               :hints
                               (("Goal"
                                 :by (:functional-instance
                                      lem-vector$c::updater-of-resizer/resizable-inner
                                      ,@fi-bindings))))

                             (defthm ,updater-of-resizer-outer
                               (implies (and (equal value ,(if element-creator
                                                               `(,element-creator)
                                                               initial-element-name))
                                             (natp index)
                                             (natp length)
                                             (< index length)
                                             (<= (,length ,vector) index))
                                        (equal (,updater index value (,resizer length ,vector))
                                               (,resizer length ,vector)))
                               :hints
                               (("Goal"
                                 :by (:functional-instance
                                      lem-vector$c::updater-of-resizer/resizable-outer
                                      ,@fi-bindings))))))

                    (defthmd ,updater-of-accessor-free
                      (implies (and (equal value (,accessor index ,vector))
                                    (natp index)
                                    (< index ,(if resizable
                                                  `(,length ,vector)
                                                  default-length-name))
                                    (,recognizer ,vector))
                               (equal (,updater index value ,vector)
                                      ,vector))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$c::updater-of-accessor-free/resizable
                                  'lem-vector$c::updater-of-accessor-free/fixed)
                             ,@fi-bindings))))

                    (defthm ,updater-of-accessor
                      (implies (and (equal %index index)
                                    (natp %index)
                                    (< %index ,(if resizable
                                                   `(,length ,vector)
                                                   default-length-name))
                                    (,recognizer ,vector))
                               (equal (,updater %index (,accessor index ,vector) ,vector)
                                      ,vector))
                      :hints
                      (("Goal"
                        :in-theory (disable ,updater-of-accessor-free)
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$c::updater-of-accessor/resizable
                                  'lem-vector$c::updater-of-accessor/fixed)
                             ,@fi-bindings))))

                    (defthm ,updater-of-updater-same
                      (implies (equal %index index)
                               (equal (,updater %index %value (,updater index value ,vector))
                                      (,updater %index %value ,vector)))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             lem-vector$c::updater-of-updater-same
                             ,@fi-bindings))))

                    (defthm ,updater-of-updater-diff
                      (implies (and (not (equal %index index))
                                    (natp %index)
                                    (natp index))
                               (equal (,updater %index %value (,updater index value ,vector))
                                      (,updater index value (,updater %index %value ,vector))))
                      :rule-classes
                      ((:rewrite :loop-stopper ((%index index ,updater))))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             lem-vector$c::updater-of-updater-diff
                             ,@fi-bindings))))

                    ;; `FIXER'
                    (defun-inline ,fixer (,vector)
                      (declare (xargs :stobjs ,vector))
                      (mbe :logic (if (,recognizer ,vector)
                                      ,vector
                                      (,creator))
                           :exec ,vector))

                    (table fixer ',vector ',fixer)

                    (defthm ,fixer{type-prescription}
                      (and (consp (,fixer ,vector))
                           (true-listp (,fixer ,vector)))
                      :rule-classes :type-prescription
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$c::fixer/resizable{type-prescription}
                                  'lem-vector$c::fixer/fixed{type-prescription})
                             ,@fi-bindings-with-fixer))))

                    (defthm ,recognizer-of-fixer
                      (,recognizer (,fixer ,vector))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$c::recognizer/resizable-of-fixer/resizable
                                  'lem-vector$c::recognizer/fixed-of-fixer/fixed)
                             ,@fi-bindings-with-fixer))))

                    (defthm ,fixer-when-recognizer
                      (implies (,recognizer ,vector)
                               (equal (,fixer ,vector)
                                      ,vector))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$c::fixer/resizable-when-recognizer/resizable
                                  'lem-vector$c::fixer/fixed-when-recognizer/fixed)
                             ,@fi-bindings-with-fixer))))

                    (defthm ,fixer-when-not-recognizer
                      (implies (not (,recognizer ,vector))
                               (equal (,fixer ,vector) (,creator)))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$c::fixer/resizable-when-not-recognizer/resizable
                                  'lem-vector$c::fixer/fixed-when-not-recognizer/fixed)
                             ,@fi-bindings-with-fixer)))))))
           `(progn
              ,@prologue

              ,body

              ,@epilogue))))))
