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
(include-book "../lemmas/vector$a")
||#

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


;;;; `DEFINE-VECTOR$A'
(defmacro define-vector$a
    (vector dimensions
     &key
       (index 'nil)
       (%index 'nil)
       (element-recognizer 'nil element-recognizer-supplied-p)
       (element-fixer 'nil element-fixer-supplied-p)
       (element 'nil)
       (%element 'nil)
       (initial-element 'nil)
       (resizable 'nil)

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
                              (symbol-listp (list index
                                                  %index
                                                  element-recognizer
                                                  element-fixer
                                                  element
                                                  %element))
                              (or (and (not element-recognizer)
                                       (not element-fixer))
                                  (and element-recognizer
                                       element-fixer))
                              (booleanp resizable)
                              (symbol-listp (list recognizer
                                                  creator
                                                  fixer
                                                  length
                                                  resizer
                                                  accessor
                                                  updater))
                              (booleanp debug))))

  (let* (
; TODO: allow defined constant default length, move to inner `LET*'
         (default-length (if (consp dimensions)
                             (car dimensions)
                             dimensions))

         (recognizer (or recognizer
                         (symbolicate vector vector (make-predicate-suffix vector))))
         (creator (or creator
                      (symbolicate vector "CREATE-" vector)))
         (fixer (or fixer
                    (symbolicate vector vector "-FIX")))
         (length (or length
                     (symbolicate vector vector "-LENGTH")))
         (resizer (or resizer
                      (symbolicate vector vector "-RESIZE")))
         (accessor (or accessor
                       (symbolicate vector vector "-REF")))
         (updater (or updater
                      (symbolicate vector vector "-SET"))))

    `(with-output
       ,@(and (not debug)
              '#!acl2(:off (warning! observation prove event history proof-tree)
                           :summary-off (rules)
                           :gag-mode t))

       (make-event
         (let* ((vector ',vector)
                (default-length ',default-length)
                (default-length-name (symbolicate vector "*" vector "-DEFAULT-LENGTH*"))

                (index (or ',index
                           (symbolicate "LEM-VECTOR$A" "I")))
                (%index (or ',%index
                            (symbolicate index "%" index)))
                (element (or ',element
                             (symbolicate "LEM-VECTOR$A" "V")))
                (%element (or ',%element
                              (symbolicate element "%" element)))
                (stobj-property (getpropc element 'stobj))
                (absstobj-info (getpropc element 'absstobj-info))
                (stobj$a-property (cdr (assoc element (table-alist 'stobj$a-property (w state)))))
                (element-recognizer (cond
                                      (',element-recognizer-supplied-p
                                       ',element-recognizer)
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
                (element-fixer (cond
                                 (',element-fixer-supplied-p
                                  ',element-fixer)
                                 (stobj$a-property
                                  (third (second stobj$a-property)))
                                 (t
                                  (cdr (assoc element (table-alist 'fixer (w state)))))))
                (initial-element-name (symbolicate vector "*" vector "-INITIAL-ELEMENT*"))
                (initial-element (if element-creator
                                     `(,element-creator)
                                     initial-element-name))
                (resizable ',resizable)

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
                          `((defconst ,initial-element-name ',',initial-element)))))

                (recognizer-aux (symbolicate vector vector "-AUX-P"))
                (recognizer-aux{type-prescription} (symbolicate vector recognizer-aux "{TYPE-PRESCRIPTION}"))
                (recognizer-aux{compound-recognizer} (symbolicate vector recognizer-aux "{COMPOUND-RECOGNIZER}"))

                (recognizer{type-prescription} (symbolicate vector recognizer "{TYPE-PRESCRIPTION}"))
                (recognizer{compound-recognizer} (symbolicate vector recognizer "{COMPOUND-RECOGNIZER}"))
                (recognizer-of-creator (symbolicate vector recognizer "-OF-" creator))
                (recognizer-of-fixer (symbolicate vector recognizer "-OF-" fixer))
                (recognizer-of-resizer (symbolicate vector recognizer "-OF-" resizer))
                (recognizer-of-updater (symbolicate vector recognizer "-OF-" updater))

                (fixer{type-prescription} (symbolicate vector fixer "{TYPE-PRESCRIPTION}"))
                (fixer-when-recognizer (symbolicate vector fixer "-WHEN-" recognizer))
                (fixer-when-not-recognizer (symbolicate vector fixer "-WHEN-NOT-" recognizer))

                (length{type-prescription} (symbolicate vector length "{TYPE-PRESCRIPTION}"))
                (length-when-not-recognizer (symbolicate vector length "-WHEN-NOT-" recognizer))
                (length-of-creator (symbolicate vector length "-OF-" creator))
                (length-of-fixer (symbolicate vector length "-OF-" fixer))
                (length-of-resizer (symbolicate vector length "-OF-" resizer))
                (length-of-updater (symbolicate vector length "-OF-" updater))
                (length{rewrite} (symbolicate vector length "{REWRITE}"))

                (resizer{type-prescription} (symbolicate vector resizer "{TYPE-PRESCRIPTION}"))
                (resizer-when-not-natp (symbolicate vector resizer "-WHEN-NOT-NATP"))
                (resizer-when-not-recognizer (symbolicate vector resizer "-WHEN-NOT-" recognizer))
                (resizer-of-creator (symbolicate vector resizer "-OF-" creator))
                (resizer-of-nfix (symbolicate vector resizer "-OF-NFIX"))
                (resizer-of-fixer (symbolicate vector resizer "-OF-" fixer))
                (resizer-of-length (symbolicate vector resizer "-OF-" length))
                (resizer-of-length-free (symbolicate vector resizer-of-length "-FREE"))
                (resizer-of-resizer (symbolicate vector resizer "-OF-" resizer))
                (resizer-of-resizer{case-split} (symbolicate vector resizer-of-resizer "{CASE-SPLIT}"))
                (resizer-of-updater (symbolicate vector resizer "-OF-" updater))
                (resizer-of-updater-keep (symbolicate vector resizer-of-updater "-KEEP"))
                (resizer-of-updater-drop (symbolicate vector resizer-of-updater "-DROP"))
                (resizer{rewrite} (symbolicate vector resizer "{REWRITE}"))

                (element-recognizer-of-accessor (symbolicate vector element-recognizer "-OF-" accessor))
                (accessor-when-large (symbolicate vector accessor "-WHEN-LARGE"))
                (accessor-when-not-natp (symbolicate vector accessor "-WHEN-NOT-NATP"))
                (accessor-when-not-recognizer (symbolicate vector accessor "-WHEN-NOT-" recognizer))
                (accessor-of-creator (symbolicate vector accessor "-OF-" creator))
                (accessor-of-nfix (symbolicate vector accessor "-OF-NFIX"))
                (accessor-of-fixer (symbolicate vector accessor "-OF-" fixer))
                (accessor-of-resizer (symbolicate vector accessor "-OF-" resizer))
                (accessor-of-resizer{case-split} (symbolicate vector accessor-of-resizer "{CASE-SPLIT}"))
                (accessor-of-updater (symbolicate vector accessor "-OF-" updater))
                (accessor-of-updater-same (symbolicate vector accessor-of-updater "-SAME"))
                (accessor-of-updater-diff (symbolicate vector accessor-of-updater "-DIFF"))

                (updater{type-prescription} (symbolicate vector updater "{TYPE-PRESCRIPTION}"))
                (updater-when-large (symbolicate vector updater "-WHEN-LARGE"))
                (updater-when-not-natp (symbolicate vector updater "-WHEN-NOT-NATP"))
                (updater-when-not-element-recognizer (symbolicate vector updater "-WHEN-NOT-" element-recognizer))
                (updater-when-not-natp (if (eq updater-when-not-natp updater-when-not-element-recognizer)
                                           (symbolicate vector updater-when-not-natp "-1")
                                           updater-when-not-natp))
                (updater-when-not-element-recognizer (if (eq updater-when-not-natp updater-when-not-element-recognizer)
                                                         (symbolicate vector updater-when-not-natp "-2")
                                                         updater-when-not-element-recognizer))
                (updater-when-not-recognizer (symbolicate vector updater "-WHEN-NOT-" recognizer))
                (updater-of-creator (symbolicate vector updater "-OF-" creator))
                (updater-of-nfix (symbolicate vector updater "-OF-NFIX"))
                (updater-of-element-fixer (symbolicate vector updater "-OF-" element-fixer))
                (updater-of-nfix (if (eq updater-of-nfix updater-of-element-fixer)
                                     (symbolicate vector updater-of-nfix "-1")
                                     updater-of-nfix))
                (updater-of-element-fixer (if (eq updater-of-nfix updater-of-element-fixer)
                                              (symbolicate vector updater-of-nfix "-2")
                                              updater-of-element-fixer))
                (updater-of-fixer (symbolicate vector updater "-OF-" fixer))
                (updater-of-resizer (symbolicate vector updater "-OF-" resizer))
                (updater-of-resizer{case-split} (symbolicate vector updater-of-resizer "{CASE-SPLIT}"))
                (updater-of-accessor (symbolicate vector updater "-OF-" accessor))
                (updater-of-accessor-free (symbolicate vector updater-of-accessor "-FREE"))
                (updater-of-updater (symbolicate vector updater "-OF-" updater))
                (updater-of-updater-same (symbolicate vector updater-of-updater "-SAME"))
                (updater-of-updater-diff (symbolicate vector updater-of-updater "-DIFF"))

                (%vector (symbolicate vector "%" vector))
                (contents-equal (symbolicate vector vector "-CONTENTS-EQUAL"))
                (contents-equal-witness (symbolicate vector contents-equal "-WITNESS"))
                (contents-equal-necc (symbolicate vector contents-equal "-NECC"))
                (vector-equal (symbolicate vector vector "-EQUAL"))
                (vector-equal{forward-chaining} (symbolicate vector vector-equal "{FORWARD-CHAINING}"))

                (vector-theorems (symbolicate vector vector "-THEOREMS"))
                (vector-definitions (symbolicate vector vector "-DEFINITIONS"))
                (vector-aggressive (symbolicate vector vector "-AGGRESSIVE"))
                (epilogue
                 `((deflabel ,vector-end)

                   (deftheory-static ,vector-theorems
                     (set-difference-theories
                      (set-difference-theories
                       (current-theory ',vector-end)
                       (current-theory ',vector-begin))
                      (union-theories (function-theory ',vector-end)
                                      '(,@(and element-recognizer
                                               `((:i ,(if resizable
                                                          recognizer
                                                          recognizer-aux))))))))

                   (deftheory-static ,vector-definitions
                     (set-difference-theories
                      (set-difference-theories
                       (set-difference-theories
                        (current-theory ',vector-end)
                        (current-theory ',vector-begin))
                       (theory ',vector-theorems))
                      '(,contents-equal)))

                   (deftheory-static ,vector-aggressive
                     ',(append (list fixer
                                     accessor-when-large
                                     accessor-when-not-natp
                                     accessor-when-not-recognizer
                                     accessor-of-updater
                                     updater-when-large
                                     updater-when-not-natp
                                     updater-when-not-recognizer
                                     updater-of-accessor-free
                                     updater-of-updater)
                               (and resizable
                                    (list length-when-not-recognizer
                                          resizer-when-not-natp
                                          resizer-when-not-recognizer
                                          resizer-of-length-free
                                          resizer-of-resizer{case-split}
                                          resizer-of-updater
                                          accessor-of-resizer{case-split}
                                          updater-of-resizer{case-split}))
                               (and element-recognizer
                                    (list updater-when-not-element-recognizer))))

                   (in-theory
                     (union-theories (current-theory ',vector-begin)
                                     (theory ',vector-theorems)))
                   (in-theory
                     ;; Ensure `:USE' `VECTOR-EQUAL' automagically works.
                     (enable ,contents-equal))))

                (fi-bindings
                 (list `(lem-vector$a::default-length (lambda ()
                                                        ,default-length-name))
                       `(lem-vector$a::element-recognizer ,(or element-recognizer
                                                               '(lambda (element)
                                                                 t)))
                       `(lem-vector$a::initial-element ,(or element-creator
                                                            `(lambda ()
                                                               ,initial-element-name)))
                       `(lem-vector$a::element-fixer ,(or element-fixer
                                                          '(lambda (element)
                                                            element)))
                       `(lem-vector$a::contents-recognizer ,(if element-recognizer
                                                                (if resizable
                                                                    recognizer
                                                                    recognizer-aux)
                                                                'true-listp))
                       (if resizable
                           `(lem-vector$a::recognizer/resizable ,recognizer)
                           `(lem-vector$a::recognizer/fixed ,recognizer))
                       `(lem-vector$a::creator ,creator)
                       (if resizable
                           `(lem-vector$a::fixer/resizable ,fixer)
                           `(lem-vector$a::fixer/fixed ,fixer))
                       (if resizable
                           `(lem-vector$a::length/resizable ,length)
                           `(lem-vector$a::length/fixed ,length))
                       (if resizable
                           `(lem-vector$a::resizer/resizable ,resizer)
                           `(lem-vector$a::resizer/fixed ,resizer))
                       (if resizable
                           `(lem-vector$a::accessor/resizable ,accessor)
                           `(lem-vector$a::accessor/fixed ,accessor))
                       (if resizable
                           `(lem-vector$a::updater/resizable ,updater)
                           `(lem-vector$a::updater/fixed ,updater))))
                (fi-bindings-with-skolem
                 (list* (if resizable
                            `(lem-vector$a::contents-equal/resizable ,contents-equal)
                            `(lem-vector$a::contents-equal/fixed ,contents-equal))
                        (if resizable
                            `(lem-vector$a::equal/resizable ,vector-equal)
                            `(lem-vector$a::equal/fixed ,vector-equal))
                        (if resizable
                            `(lem-vector$a::contents-equal/resizable-witness ,contents-equal-witness)
                            `(lem-vector$a::contents-equal/fixed-witness ,contents-equal-witness))
                        fi-bindings))

                (body
                 `(with-books (("projects/atomic-stobjs/lemmas/vector$a" :dir :system))
; Fixed-length vectors with specialized elements need a predicate to check
; element-wise validity.
                    ,@(and (not resizable)
                           element-recognizer
                           `((defun ,recognizer-aux (,vector)
                               (declare (xargs :guard t))
                               (if (atom ,vector)
                                   (eq ,vector nil)
                                   (and (,element-recognizer (car ,vector))
                                        (,recognizer-aux (cdr ,vector)))))))

                    (defun ,recognizer (,vector)
                      (declare (xargs :guard t))
                      ,(if resizable
                           (if element-recognizer
                               `(if (atom ,vector)
                                    (eq ,vector nil)
                                    (and (,element-recognizer (car ,vector))
                                         (,recognizer (cdr ,vector))))
                               `(true-listp ,vector))
                           (if element-recognizer
                               `(and (= (len ,vector) ,default-length-name)
                                     (,recognizer-aux ,vector))
                               `(and (= (len ,vector) ,default-length-name)
                                     (true-listp ,vector)))))

                    (defun ,creator ()
                      (declare (xargs :guard t))
                      (make-list ,default-length-name
                                 :initial-element ,initial-element))

                    (local
                      (in-theory
                        (disable make-list-ac
                                 (:e make-list-ac))))

; We don't want to frequently allocate large list literals in proofs.
                    (in-theory
                      (disable (:e ,creator)))

                    (defun ,fixer (,vector)
                      (declare (xargs :guard (,recognizer ,vector)))
                      (if (,recognizer ,vector)
                          ,vector
                          (,creator)))

                    (defun ,length (,vector)
                      (declare (xargs :guard (,recognizer ,vector))
                               ,@(and (not resizable)
                                      `((ignore ,vector))))
                      ,(if resizable
                           `(len (,fixer ,vector))
                           default-length-name))

                    (defun ,resizer (length ,vector)
                      (declare (xargs :guard (and (natp length)
                                                  (,recognizer ,vector)))
                               ,@(and (not resizable)
                                      `((ignore length))))
                      ,(if resizable
                           `(let ((,vector (,fixer ,vector))
                                  (length (nfix length)))
                              (resize-list ,vector length ,initial-element))
                           `(,fixer ,vector)))

                    (defun ,accessor (,index ,vector)
                      (declare (xargs :guard (and (natp ,index)
                                                  (,recognizer ,vector)
                                                  (< ,index ,(if resizable
                                                                 `(,length ,vector)
                                                                 default-length-name)))))
                      (let ((,index (nfix ,index))
                            (,vector (,fixer ,vector)))
                        (if (< ,index ,(if resizable
                                           `(,length ,vector)
                                           default-length-name))
                            ,(if element-fixer
                                 `(,element-fixer (nth ,index ,vector))
                                 `(nth ,index ,vector))
                            ,initial-element)))

                    (defun ,updater (,index ,element ,vector)
                      (declare (xargs :guard (and (natp ,index)
                                                  ,@(and element-recognizer
                                                         `((,element-recognizer ,element)))
                                                  (,recognizer ,vector)
                                                  (< ,index ,(if resizable
                                                                 `(,length ,vector)
                                                                 default-length-name)))))
                      (let ((,index (nfix ,index))
                            ,@(and element-fixer
                                   `((,element (,element-fixer ,element))))
                            (,vector (,fixer ,vector)))
                        (if (< ,index ,(if resizable
                                           `(,length ,vector)
                                           default-length-name))
                            (update-nth ,index ,element ,vector)
                            ,vector)))

                    ;; `RECOGNIZER-AUX'
                    ,@(and (not resizable)
                           element-recognizer
                           `((defthm ,recognizer-aux{type-prescription}
                               (booleanp (,recognizer-aux ,vector))
                               :rule-classes :type-prescription
                               :hints
                               (("Goal"
                                 :by (:functional-instance
                                      lem-vector$a::contents-recognizer{type-prescription}
                                      ,@fi-bindings))))

                             (defthm ,recognizer-aux{compound-recognizer}
                               (implies (,recognizer-aux ,vector)
                                        (true-listp ,vector))
                               :rule-classes :compound-recognizer
                               :hints
                               (("Goal"
                                 :by (:functional-instance
                                      lem-vector$a::contents-recognizer{compound-recognizer}
                                      ,@fi-bindings))))))

                    (defthm ,recognizer{type-prescription}
                      (booleanp (,recognizer ,vector))
                      :rule-classes :type-prescription
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$a::recognizer/resizable{type-prescription}
                                  'lem-vector$a::recognizer/fixed{type-prescription})
                             ,@fi-bindings))))

                    ;; TODO: for fixed-length vectors of positive length, add
                    ;; consp conjunct
                    (defthm ,recognizer{compound-recognizer}
                      (implies (,recognizer ,vector)
                               (true-listp ,vector))
                      :rule-classes :compound-recognizer
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$a::recognizer/resizable{compound-recognizer}
                                  'lem-vector$a::recognizer/fixed{compound-recognizer})
                             ,@fi-bindings))))

                    (defthm ,recognizer-of-creator
                      (,recognizer (,creator))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$a::recognizer/resizable-of-creator
                                  'lem-vector$a::recognizer/fixed-of-creator)
                             ,@fi-bindings))))

                    (defthm ,recognizer-of-fixer
                      (,recognizer (,fixer ,vector))
                      :hints
                      (("Goal"
                        :in-theory (disable ,creator
                                            (:e ,creator))
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$a::recognizer/resizable-of-fixer/resizable
                                  'lem-vector$a::recognizer/fixed-of-fixer/fixed)
                             ,@fi-bindings))))

                    ,@(and resizable
                           `((defthm ,recognizer-of-resizer
                               (,recognizer (,resizer length ,vector))
                               :hints
                               (("Goal"
                                 :by (:functional-instance
                                      lem-vector$a::recognizer/resizable-of-resizer/resizable
                                      ,@fi-bindings))))))

                    (defthm ,recognizer-of-updater
                      (,recognizer (,updater ,index ,element ,vector))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$a::recognizer/resizable-of-updater/resizable
                                  'lem-vector$a::recognizer/fixed-of-updater/fixed)
                             ,@fi-bindings))))

                    ;; `CREATOR'
                    ;; TODO: add type prescription rule

                    ;; `FIXER'
                    (defthm ,fixer{type-prescription}
                      (true-listp (,fixer ,vector))
                      :rule-classes :type-prescription
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$a::fixer/resizable{type-prescription}
                                  'lem-vector$a::fixer/fixed{type-prescription})
                             ,@fi-bindings))))

; While the fixer is disabled by default, it is enabled in the aggressive
; theory.  You can see from its definition that this does not break abstraction.

                    (defthm ,fixer-when-recognizer
                      (implies (,recognizer ,vector)
                               (equal (,fixer ,vector)
                                      ,vector))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$a::fixer/resizable-when-recognizer/resizable
                                  'lem-vector$a::fixer/fixed-when-recognizer/fixed)
                             ,@fi-bindings))))

                    (defthm ,fixer-when-not-recognizer
                      (implies (not (,recognizer ,vector))
                               (equal (,fixer ,vector)
                                      (,creator)))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$a::fixer/resizable-when-not-recognizer/resizable
                                  'lem-vector$a::fixer/fixed-when-not-recognizer/fixed)
                             ,@fi-bindings))))

                    ;; `LENGTH'
                    (defthm ,length{type-prescription}
                      (natp (,length ,vector))
                      :rule-classes :type-prescription
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$a::length/resizable{type-prescription}
                                  'lem-vector$a::length/fixed{type-prescription})
                             ,@fi-bindings))))

; Resizable vector length is characterized by a short list of composition
; identities.
;
; Non-resizable vector length is characterized entirely by `LENGTH{REWRITE}'.

                    ,@(if resizable
                          `((defthmd ,length-when-not-recognizer
                              (implies (not (,recognizer ,vector))
                                       (equal (,length ,vector)
                                              ,default-length-name))
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$a::length/resizable-when-not-recognizer/resizable
                                     ,@fi-bindings))))

                            (defthm ,length-of-creator
                              (equal (,length (,creator))
                                     ,default-length-name)
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$a::length/resizable-of-creator
                                     ,@fi-bindings))))

                            (defthm ,length-of-fixer
                              (equal (,length (,fixer ,vector))
                                     (,length ,vector))
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$a::length/resizable-of-fixer/resizable
                                     ,@fi-bindings))))

                            (defthm ,length-of-resizer
                              (equal (,length (,resizer length ,vector))
                                     (nfix length))
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$a::length/resizable-of-resizer/resizable
                                     ,@fi-bindings))))

                            (defthm ,length-of-updater
                              (equal (,length (,updater ,index ,element ,vector))
                                     (,length ,vector))
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$a::length/resizable-of-updater/resizable
                                     ,@fi-bindings)))))

                          `((defthm ,length{rewrite}
                              (equal (,length ,vector)
                                     ,default-length-name)
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$a::length/fixed{rewrite}
                                     ,@fi-bindings))))))

                    ;; `RESIZER'
                    (defthm ,resizer{type-prescription}
                      (true-listp (,resizer length ,vector))
                      :rule-classes :type-prescription
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$a::resizer/resizable{type-prescription}
                                  'lem-vector$a::resizer/fixed{type-prescription})
                             ,@fi-bindings))))


; Resizable vector resizer is characterized by a short list of composition
; identities.
;
; Non-resizable vector resizer is characterized entirely by `RESIZER{REWRITE}'.

                    ,@(if resizable
                          `((defthmd ,resizer-when-not-natp
                              (implies (not (natp length))
                                       (equal (,resizer length ,vector)
                                              (,resizer 0 ,vector)))
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$a::resizer/resizable-when-not-natp
                                     ,@fi-bindings))))

                            (defthmd ,resizer-when-not-recognizer
                              (implies (not (,recognizer ,vector))
                                       (equal (,resizer length ,vector)
                                              (,resizer length (,creator))))
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$a::resizer/resizable-when-not-recognizer/resizable
                                     ,@fi-bindings))))

                            (defthm ,resizer-of-creator
                              (implies (equal length ,default-length-name)
                                       (equal (,resizer length (,creator))
                                              (,creator)))
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$a::resizer/resizable-of-creator
                                     ,@fi-bindings))))

                            (defthm ,resizer-of-nfix
                              (equal (,resizer (nfix length) ,vector)
                                     (,resizer length ,vector))
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$a::resizer/resizable-of-nfix
                                     ,@fi-bindings))))

                            (defthm ,resizer-of-fixer
                              (equal (,resizer length (,fixer ,vector))
                                     (,resizer length ,vector))
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$a::resizer/resizable-of-fixer/resizable
                                     ,@fi-bindings))))

                            (defthmd ,resizer-of-length-free
                              (implies (equal (nfix length) (,length ,vector))
                                       (equal (,resizer length ,vector)
                                              (,fixer ,vector)))
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$a::resizer/resizable-of-length/resizable-free
                                     ,@fi-bindings))))

                            (defthm ,resizer-of-length
                              (equal (,resizer (,length ,vector) ,vector)
                                     (,fixer ,vector))
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$a::resizer/resizable-of-length/resizable
                                     ,@fi-bindings))))

                            (defthm ,resizer-of-resizer
; If you resize a vector and then shrink it, the result is equivalent to a
; single resize.  If you extend a vector and then resize it, the result is
; equivalent to a single resize. If you shrink a vector and then extend it, this
; is not equivalent to a single resize.
                              (implies (or (<= (nfix %length) (nfix length))
                                           (<= (,length ,vector) (nfix length)))
                                       (equal (,resizer %length (,resizer length ,vector))
                                              (,resizer %length ,vector)))
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$a::resizer/resizable-of-resizer/resizable
                                     ,@fi-bindings))))

                            (defthmd ,resizer-of-resizer{case-split}
                              (implies (or (<= (nfix %length) (nfix length))
                                           (<= (,length ,vector) (nfix length)))
                                       (equal (,resizer %length (,resizer length ,vector))
                                              (,resizer %length ,vector)))
                              :rule-classes
                              ((:rewrite :corollary
                                         (implies (case-split (or (<= (nfix %length) (nfix length))
                                                                  (<= (,length ,vector) (nfix length))))
                                                  (equal (,resizer %length (,resizer length ,vector))
                                                         (,resizer %length ,vector)))))
                              :hints
                              (("Goal"
                                :by ,resizer-of-resizer)))

                            (defthmd ,resizer-of-updater
                              (implies (< (nfix ,index) (,length ,vector))
                                       (equal (,resizer length (,updater ,index ,element ,vector))
                                              (if (< (nfix ,index) (nfix length))
                                                  (,updater ,index ,element (,resizer length ,vector))
                                                  (,resizer length ,vector))))
                              :rule-classes
                              ((:rewrite :corollary
                                         (implies (case-split (< (nfix ,index) (,length ,vector)))
                                                  (equal (,resizer length (,updater ,index ,element ,vector))
                                                         (if (< (nfix ,index) (nfix length))
                                                             (,updater ,index ,element (,resizer length ,vector))
                                                             (,resizer length ,vector))))))
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$a::resizer/resizable-of-updater/resizable
                                     ,@fi-bindings))))

                            (defthm ,resizer-of-updater-keep
                              (implies (and (< (nfix ,index) (,length ,vector))
                                            (< (nfix ,index) (nfix length)))
                                       (equal (,resizer length (,updater ,index ,element ,vector))
                                              (,updater ,index ,element (,resizer length ,vector))))
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$a::resizer/resizable-of-updater/resizable-keep
                                     ,@fi-bindings))))

                            (defthm ,resizer-of-updater-drop
                              (implies (and (< (nfix ,index) (,length ,vector))
                                            (<= (nfix length) (nfix ,index)))
                                       (equal (,resizer length (,updater ,index ,element ,vector))
                                              (,resizer length ,vector)))
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$a::resizer/resizable-of-updater/resizable-drop
                                     ,@fi-bindings)))))

                          `((defthm ,resizer{rewrite}
                              (equal (,resizer length ,vector)
                                     (,fixer ,vector))
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$a::resizer/fixed{rewrite}
                                     ,@fi-bindings))))))

                    ;; `ACCESSOR'
                    ,@(and element-recognizer
                           `((defthm ,element-recognizer-of-accessor
                               (,element-recognizer (,accessor ,index ,vector))
                               :rule-classes
                               (:rewrite
                                :type-prescription)
                               :hints
                               (("Goal"
                                 :by (:functional-instance
                                      ,(if resizable
                                           'lem-vector$a::element-recognizer-of-accessor/resizable
                                           'lem-vector$a::element-recognizer-of-accessor/fixed)
                                      ,@fi-bindings))))))

                    (defthmd ,accessor-when-large
                      (implies (<= ,(if resizable
                                        `(,length ,vector)
                                        default-length-name)
                                   (nfix ,index))
                               (equal (,accessor ,index ,vector)
                                      ,initial-element))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$a::accessor/resizable-when-large
                                  'lem-vector$a::accessor/fixed-when-large)
                             ,@fi-bindings))))

                    (defthmd ,accessor-when-not-natp
                      (implies (not (natp ,index))
                               (equal (,accessor ,index ,vector)
                                      (,accessor 0 ,vector)))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$a::accessor/resizable-when-not-natp
                                  'lem-vector$a::accessor/fixed-when-not-natp)
                             ,@fi-bindings))))

                    (defthmd ,accessor-when-not-recognizer
                      (implies (not (,recognizer ,vector))
                               (equal (,accessor ,index ,vector)
                                      ,initial-element))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$a::accessor/resizable-when-not-recognizer/resizable
                                  'lem-vector$a::accessor/fixed-when-not-recognizer/fixed)
                             ,@fi-bindings))))

                    (defthm ,accessor-of-creator
                      (equal (,accessor ,index (,creator))
                             ,initial-element)
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$a::accessor/resizable-of-creator
                                  'lem-vector$a::accessor/fixed-of-creator)
                             ,@fi-bindings))))

                    (defthm ,accessor-of-nfix
                      (equal (,accessor (nfix ,index) ,vector)
                             (,accessor ,index ,vector))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$a::accessor/resizable-of-nfix
                                  'lem-vector$a::accessor/fixed-of-nfix)
                             ,@fi-bindings))))

                    (defthm ,accessor-of-fixer
                      (equal (,accessor ,index (,fixer ,vector))
                             (,accessor ,index ,vector))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$a::accessor/resizable-of-fixer/resizable
                                  'lem-vector$a::accessor/fixed-of-fixer/fixed)
                             ,@fi-bindings))))

                    ,@(and resizable
                           `((defthm ,accessor-of-resizer
                               (implies (< (nfix ,index) (nfix length))
                                        (equal (,accessor ,index (,resizer length ,vector))
                                               (,accessor ,index ,vector)))
                               :hints
                               (("Goal"
                                 :by (:functional-instance
                                      ,(if resizable
                                           'lem-vector$a::accessor/resizable-of-resizer/resizable
                                           'lem-vector$a::accessor/fixed-of-resizer/fixed)
                                      ,@fi-bindings))))

                             (defthmd ,accessor-of-resizer{case-split}
                               (implies (< (nfix ,index) (nfix length))
                                        (equal (,accessor ,index (,resizer length ,vector))
                                               (,accessor ,index ,vector)))
                               :rule-classes
                               ((:rewrite :corollary
                                          (implies (case-split (< (nfix ,index) (nfix length)))
                                                   (equal (,accessor ,index (,resizer length ,vector))
                                                          (,accessor ,index ,vector)))))
                               :hints
                               (("Goal"
                                 :by ,accessor-of-resizer)))))

                    (defthmd ,accessor-of-updater
                      (implies (< (nfix ,%index)
                                  ,(if resizable
                                       `(,length ,vector)
                                       default-length-name))
                               (equal (,accessor ,%index (,updater ,index ,element ,vector))
                                      (if (equal (nfix ,%index) (nfix ,index))
                                          ,(if element-fixer
                                               `(,element-fixer ,element)
                                               element)
                                          (,accessor ,%index ,vector))))
                      :rule-classes
                      ((:rewrite :corollary
                                 (implies (case-split (< (nfix ,%index)
                                                         ,(if resizable
                                                              `(,length ,vector)
                                                              default-length-name)))
                                          (equal (,accessor ,%index (,updater ,index ,element ,vector))
                                                 (if (equal (nfix ,%index) (nfix ,index))
                                                     ,(if element-fixer
                                                          `(,element-fixer ,element)
                                                          element)
                                                     (,accessor ,%index ,vector))))))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$a::accessor/resizable-of-updater/resizable
                                  'lem-vector$a::accessor/fixed-of-updater/fixed)
                             ,@fi-bindings))))

                    (defthm ,accessor-of-updater-same
                      (implies (and (< (nfix ,%index)
                                       ,(if resizable
                                            `(,length ,vector)
                                            default-length-name))
                                    (equal (nfix ,%index) (nfix ,index)))
                               (equal (,accessor ,%index (,updater ,index ,element ,vector))
                                      ,(if element-fixer
                                           `(,element-fixer ,element)
                                           element)))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$a::accessor/resizable-of-updater/resizable-same
                                  'lem-vector$a::accessor/fixed-of-updater/fixed-same)
                             ,@fi-bindings))))

                    (defthm ,accessor-of-updater-diff
                      (implies (and (< (nfix ,%index)
                                       ,(if resizable
                                            `(,length ,vector)
                                            default-length-name))
                                    (not (equal (nfix ,%index) (nfix ,index))))
                               (equal (,accessor ,%index (,updater ,index ,element ,vector))
                                      (,accessor ,%index ,vector)))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$a::accessor/resizable-of-updater/resizable-diff
                                  'lem-vector$a::accessor/fixed-of-updater/fixed-diff)
                             ,@fi-bindings))))

                    ;; `UPDATER'
                    (defthm ,updater{type-prescription}
                      (true-listp (,updater ,index ,element ,vector))
                      :rule-classes :type-prescription
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$a::updater/resizable{type-prescription}
                                  'lem-vector$a::updater/fixed{type-prescription})
                             ,@fi-bindings))))

                    (defthmd ,updater-when-large
                      (implies (<= ,(if resizable
                                        `(,length ,vector)
                                        default-length-name)
                                   (nfix ,index))
                               (equal (,updater ,index ,element ,vector)
                                      (,fixer ,vector)))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$a::updater/resizable-when-large
                                  'lem-vector$a::updater/fixed-when-large)
                             ,@fi-bindings))))

                    (defthmd ,updater-when-not-natp
                      (implies (not (natp ,index))
                               (equal (,updater ,index ,element ,vector)
                                      (,updater 0 ,element ,vector)))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$a::updater/resizable-when-not-natp
                                  'lem-vector$a::updater/fixed-when-not-natp)
                             ,@fi-bindings))))

                    ,@(and element-recognizer
                           `((defthmd ,updater-when-not-element-recognizer
                               (implies (not (,element-recognizer ,element))
                                        (equal (,updater ,index ,element ,vector)
                                               (,updater ,index ,initial-element ,vector)))
                               :hints
                               (("Goal"
                                 :by (:functional-instance
                                      ,(if resizable
                                           'lem-vector$a::updater/resizable-when-not-element-recognizer
                                           'lem-vector$a::updater/fixed-when-not-element-recognizer)
                                      ,@fi-bindings))))))

                    (defthmd ,updater-when-not-recognizer
                      (implies (not (,recognizer ,vector))
                               (equal (,updater ,index ,element ,vector)
                                      (,updater ,index ,element (,creator))))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$a::updater/resizable-when-not-recognizer/resizable
                                  'lem-vector$a::updater/fixed-when-not-recognizer/fixed)
                             ,@fi-bindings))))

                    (defthm ,updater-of-creator
                      (implies (equal ,(if element-fixer
                                           `(,element-fixer ,element)
                                           element)
                                      ,initial-element)
                               (equal (,updater ,index ,element (,creator))
                                      (,creator)))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$a::updater/resizable-of-creator
                                  'lem-vector$a::updater/fixed-of-creator)
                             ,@fi-bindings))))

                    (defthm ,updater-of-nfix
                      (equal (,updater (nfix ,index) ,element ,vector)
                             (,updater ,index ,element ,vector))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$a::updater/resizable-of-nfix
                                  'lem-vector$a::updater/fixed-of-nfix)
                             ,@fi-bindings))))

                    ,@(and element-fixer
                           `((defthm ,updater-of-element-fixer
                               (equal (,updater ,index (,element-fixer ,element) ,vector)
                                      (,updater ,index ,element ,vector))
                               :hints
                               (("Goal"
                                 :by (:functional-instance
                                      ,(if resizable
                                           'lem-vector$a::updater/resizable-of-element-fixer
                                           'lem-vector$a::updater/fixed-of-element-fixer)
                                      ,@fi-bindings))))))

                    (defthm ,updater-of-fixer
                      (equal (,updater ,index ,element (,fixer ,vector))
                             (,updater ,index ,element ,vector))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$a::updater/resizable-of-fixer/resizable
                                  'lem-vector$a::updater/fixed-of-fixer/fixed)
                             ,@fi-bindings))))

                    ,@(and resizable
                           `((defthm ,updater-of-resizer
                               (implies (and (< (nfix ,index)
                                                (nfix length))
                                             (equal ,(if element-fixer
                                                         `(,element-fixer ,element)
                                                         element)
                                                    (,accessor ,index ,vector)))
                                        (equal (,updater ,index ,element (,resizer length ,vector))
                                               (,resizer length ,vector)))
                               :hints
                               (("Goal"
                                 :by (:functional-instance
                                      ,(if resizable
                                           'lem-vector$a::updater/resizable-of-resizer/resizable
                                           'lem-vector$a::updater/fixed-of-resizer/fixed)
                                      ,@fi-bindings))))

                             (defthmd ,updater-of-resizer{case-split}
                               (implies (and (< (nfix ,index)
                                                (nfix length))
                                             (equal ,(if element-fixer
                                                         `(,element-fixer ,element)
                                                         element)
                                                    (,accessor ,index ,vector)))
                                        (equal (,updater ,index ,element (,resizer length ,vector))
                                               (,resizer length ,vector)))
                               :rule-classes
                               ((:rewrite :corollary
                                          (implies (and (case-split (< (nfix ,index) (nfix length)))
                                                        (equal ,(if element-fixer
                                                                    `(,element-fixer ,element)
                                                                    element)
                                                               (,accessor ,index ,vector)))
                                                   (equal (,updater ,index ,element (,resizer length ,vector))
                                                          (,resizer length ,vector)))))
                               :hints
                               (("Goal"
                                 :by ,updater-of-resizer)))))

                    (defthmd ,updater-of-accessor-free
                      (implies (equal ,(if element-fixer
                                           `(,element-fixer ,element)
                                           element)
                                      (,accessor ,index ,vector))
                               (equal (,updater ,index ,element ,vector)
                                      (,fixer ,vector)))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$a::updater/resizable-of-accessor/resizable-free
                                  'lem-vector$a::updater/fixed-of-accessor/fixed-free)
                             ,@fi-bindings))))

                    (defthm ,updater-of-accessor
                      (implies (equal (nfix ,%index) (nfix ,index))
                               (equal (,updater ,%index (,accessor ,index ,vector) ,vector)
                                      (,fixer ,vector)))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$a::updater/resizable-of-accessor/resizable
                                  'lem-vector$a::updater/fixed-of-accessor/fixed)
                             ,@fi-bindings))))

                    (defthmd ,updater-of-updater
                      (equal (,updater ,%index ,%element (,updater ,index ,element ,vector))
                             (if (equal (nfix ,%index) (nfix ,index))
                                 (,updater ,%index ,%element ,vector)
                                 (,updater ,index ,element (,updater ,%index ,%element ,vector))))
                      :rule-classes
                      ((:rewrite :loop-stopper ((,%index ,index ,updater))))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$a::updater/resizable-of-updater/resizable
                                  'lem-vector$a::updater/fixed-of-updater/fixed)
                             ,@fi-bindings))))

                    (defthm ,updater-of-updater-same
                      (implies (equal (nfix ,%index) (nfix ,index))
                               (equal (,updater ,%index ,%element (,updater ,index ,element ,vector))
                                      (,updater ,%index ,%element ,vector)))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$a::updater/resizable-of-updater/resizable-same
                                  'lem-vector$a::updater/fixed-of-updater/fixed-same)
                             ,@fi-bindings))))

                    (defthm ,updater-of-updater-diff
                      (implies (not (equal (nfix ,%index) (nfix ,index)))
                               (equal (,updater ,%index ,%element (,updater ,index ,element ,vector))
                                      (,updater ,index ,element (,updater ,%index ,%element ,vector))))
                      :rule-classes
                      ((:rewrite :loop-stopper ((,%index ,index ,updater))))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$a::updater/resizable-of-updater/resizable-diff
                                  'lem-vector$a::updater/fixed-of-updater/fixed-diff)
                             ,@fi-bindings))))

                    ;; `VECTOR-EQUAL'
                    (defun-sk ,contents-equal (,%vector ,vector)
                      (declare (xargs :guard (and (,recognizer ,%vector)
                                                  (,recognizer ,vector))
                                      :verify-guards nil))
                      (forall ,index
                        (implies (and (natp ,index)
                                      (< ,index (,length ,%vector))
                                      (< ,index (,length ,vector)))
                                 (equal (,accessor ,index ,%vector)
                                        (,accessor ,index ,vector))))
                      :rewrite :direct)

                    (defun-nx ,vector-equal (,%vector ,vector)
                      (declare (xargs :guard (and (,recognizer ,%vector)
                                                  (,recognizer ,vector))
                                      :verify-guards nil))
                      (and (,recognizer ,%vector)
                           (,recognizer ,vector)
                           ,@(and resizable
                                  `((= (,length ,%vector)
                                       (,length ,vector))))
                           (,contents-equal ,%vector ,vector)))

; If you pass an instance of `VECTOR-EQUAL' in a `USE' hint, then
; `VECTOR-EQUAL{FORWARD-CHAINING}' ensures true equality is proven if both
; arguments are vectors of the same length with the same elements.

                    (defthm ,vector-equal{forward-chaining}
                      (implies (,vector-equal ,%vector ,vector)
                               (equal ,%vector ,vector))
                      :rule-classes
                      ((:forward-chaining :trigger-terms
                                          ((,vector-equal ,%vector ,vector))
                                          :corollary
                                          (implies t
                                                   (implies (,vector-equal ,%vector ,vector)
                                                            (equal ,%vector ,vector)))))
                      :hints
                      (("Goal"
                        :in-theory (disable ,recognizer
                                            ,creator
                                            ,fixer
                                            ,length
                                            ,accessor
                                            ,contents-equal
                                            ,contents-equal-necc)
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$a::equal/resizable{forward-chaining}
                                  'lem-vector$a::equal/fixed{forward-chaining})
                             ,@fi-bindings-with-skolem))
                       ("Subgoal 2"
                        :use ((:instance ,contents-equal-necc
                                         (,%vector lem-vector$a::%vector)
                                         (,vector lem-vector$a::vector)
                                         (,index lem-vector$a::index))))
                       ("Subgoal 1"
                        :expand (:free (,%vector ,vector)
                                       (,contents-equal ,%vector ,vector)))))))

; TODO: Compare `STOBJ$A-PROPERTY' with `STOBJ-PROPERTY' and `ABSSTOBJ-INFO' to
; see if there's a more intuitive layout.  Also compare with frame and
; hash-table.  Maybe `RECOGNIZER-AUX' should be made available?  Should theory
; names be accessible from a property or table?

; TODO: Make `VECTOR-EQUAL' and `CONTENTS-EQUAL' user nameable.

                (stobj$a-property `(stobj$a-property (,recognizer
                                                      ,creator
                                                      ,fixer
; TODO: Track `VECTOR-EQUAL' and `CONTENTS-EQUAL' in their own table.
                                                      ,vector-equal)
                                                     ((,element
                                                       ,element-recognizer
                                                       ,(and (not stobj-property)
                                                             initial-element-name)
                                                       ,element-fixer)
                                                      (,resizable
                                                       ,default-length-name)
                                                      (,length
                                                       ,resizer
                                                       ,accessor
                                                       ,updater)))))

           `(progn
              ,@prologue

              ,body

              ,@epilogue

              (table stobj$a-property ',vector ',stobj$a-property)))))))
