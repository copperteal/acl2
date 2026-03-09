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
(include-book "../lemmas/vector-a")
|#

(include-book "../utilities/top")


;;;; `DEFINE-VECTOR$A'
(defmacro define-vector$a
    (vector dimensions
     &key
       (index 'nil)
       (%index 'nil)
       (element-recognizer 'nil)
       (element-fixer 'nil)
       (element-equiv 'nil)
       (element 'nil)
       (%element 'nil)
       (initial-element 'nil)
       (resizable 't)

       (recognizer 'nil)
       (creator 'nil)
       (fixer 'nil)
       (equiv 'nil)
       (length 'nil)
       (resizer 'nil)
       (accessor 'nil)
       (updater 'nil)

       (package-witness 'nil package-witness-supplied-p)
       (debug 'nil))

  (declare (xargs :guard (and (symbolp vector)
                              (or (and (consp dimensions)
                                       (natp (car dimensions))
                                       (null (cdr dimensions)))
                                  (natp dimensions))
                              (symbol-listp (list index
                                                  %index
                                                  element-recognizer
                                                  element-fixer
                                                  element-equiv
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
                                                  equiv
                                                  length
                                                  resizer
                                                  accessor
                                                  updater))
                              (package-witness-p package-witness)
                              (booleanp debug))))

  `(with-output
     ,@(and (not debug)
            *constructor-output*)

     (make-event
       (let* ((vector ',vector)
              (package-witness (if ',package-witness-supplied-p
                                   ',package-witness
                                   (current-package state)))
              (dimensions ',dimensions)
              (default-length (if (consp dimensions)
                                  (car dimensions)
                                  dimensions))
              (default-length-name (symbolicate package-witness "*" vector "-DEFAULT-LENGTH*"))

              (index (or ',index
                         (symbolicate package-witness "I")))
              (%index (or ',%index
                          (symbolicate index "%" index)))
              (element (or ',element
                           (symbolicate package-witness "V")))
              (%element (or ',%element
                            (symbolicate package-witness "%" element)))
              (world (w state))
              (stobj-property (getpropc element 'acl2::stobj))
              (absstobj-info (and stobj-property
                                  (getpropc element 'acl2::absstobj-info)))
              (stobj$a-property (cdr (assoc element (table-alist 'stobj$a-property world))))
              (element-recognizer (cond
                                    (',element-recognizer)
                                    (stobj$a-property
                                     (first (second stobj$a-property)))))
              (guard-element-recognizer (if stobj-property
                                            (caadr stobj-property)
                                            element-recognizer))
              (element-creator (cond
                                 (stobj$a-property
                                  (second (second stobj$a-property)))))
              (element-fixer (cond
                               (',element-fixer)
                               (stobj$a-property
                                (third (second stobj$a-property)))
                               (t
                                (cdr (assoc element (table-alist 'fixer world))))))
              (element-equiv (cond
                               (',element-equiv)
                               (stobj$a-property
                                (fourth (second stobj$a-property)))
                               (t
                                'equal)))
              (initial-element-name (and (not stobj-property)
                                         (symbolicate package-witness "*" vector "-INITIAL-ELEMENT*")))
              (initial-element (if element-creator
                                   `(,element-creator)
                                   initial-element-name))
              (resizable ',resizable)

              (recognizer ',recognizer)
              (creator ',creator)
              (fixer ',fixer)
              (equiv ',equiv)
              (length ',length)
              (resizer ',resizer)
              (accessor ',accessor)
              (updater ',updater)

              ;; Interface symbols
              (recognizer (or recognizer
                              (symbolicate package-witness vector (make-predicate-suffix vector))))
              (creator (or creator
                           (symbolicate package-witness "CREATE-" vector)))
              (fixer (or fixer
                         (symbolicate package-witness vector "-FIX")))
              (equiv (or equiv
                         (symbolicate package-witness vector "-EQUIV")))
              (length (or length
                          (symbolicate package-witness vector "-LEN")))
              (resizer (or resizer
                           (symbolicate package-witness vector "-RSZ")))
              (accessor (or accessor
                            (symbolicate package-witness vector "-REF")))
              (updater (or updater
                           (symbolicate package-witness vector "-SET")))

              ;; Prologue
              (vector-begin (symbolicate package-witness vector "-BEGIN"))
              (vector-end (symbolicate package-witness vector "-END"))
              (prologue
               `((deflabel ,vector-begin)

                 (defconst ,default-length-name ',default-length)

                 ,@(and initial-element-name
                        `((defconst ,initial-element-name ',',initial-element)))))

              ;; Theorem Names
              (element-recognizer-constraints (symbolicate "ATOMIC-STOBJS" element-recognizer "-CONSTRAINTS"))
              (element-fixer-constraints (symbolicate "ATOMIC-STOBJS" element-fixer "-CONSTRAINTS"))
              (element-equiv-constraints (symbolicate "ATOMIC-STOBJS" element-equiv "-CONSTRAINTS"))

              (recognizer-aux (symbolicate package-witness vector "-AUX-P"))
              (recognizer-aux-tp (symbolicate "ATOMIC-STOBJS" recognizer-aux "-TP"))
              (recognizer-aux-cr (symbolicate "ATOMIC-STOBJS" recognizer-aux "-CR"))
              (element-recognizer-of-nth-when-recognizer-aux (symbolicate "ATOMIC-STOBJS"
                                                                          element-recognizer
                                                                          "-OF-NTH-WHEN-"
                                                                          recognizer-aux))

              (vector-constraints (symbolicate package-witness vector "-CONSTRAINTS"))

              (recognizer-tp (symbolicate package-witness recognizer "-TP"))
              (recognizer-cr (symbolicate package-witness recognizer "-CR"))
              (recognizer-of-creator (symbolicate package-witness recognizer "-OF-" creator))
              (recognizer-of-fixer (symbolicate package-witness recognizer "-OF-" fixer))
              (recognizer-of-resizer (symbolicate package-witness recognizer "-OF-" resizer))
              (recognizer-of-updater (symbolicate package-witness recognizer "-OF-" updater))

              (fixer-tp (symbolicate package-witness fixer "-TP"))
              (fixer-when-recognizer (symbolicate package-witness fixer "-WHEN-" recognizer))
              (fixer-when-not-recognizer (symbolicate package-witness fixer "-WHEN-NOT-" recognizer))

              (equiv-tp (symbolicate package-witness equiv "-TP"))
              (fixer-mod-equiv (symbolicate package-witness fixer "-MOD-" equiv))
              (equiv-when-not-recognizer (symbolicate package-witness equiv "-WHEN-NOT-" recognizer))

              (length-tp (symbolicate package-witness length "-TP"))
              (length-when-not-recognizer (symbolicate package-witness length "-WHEN-NOT-" recognizer))
              (length-of-creator (symbolicate package-witness length "-OF-" creator))
              (length-of-resizer (symbolicate package-witness length "-OF-" resizer))
              (length-of-updater (symbolicate package-witness length "-OF-" updater))
              (length-rw (symbolicate package-witness length "-RW"))

              (resizer-tp (symbolicate package-witness resizer "-TP"))
              (resizer-when-not-natp (symbolicate package-witness resizer "-WHEN-NOT-NATP"))
              (resizer-when-not-recognizer (symbolicate package-witness resizer "-WHEN-NOT-" recognizer))
              (resizer-of-creator (symbolicate package-witness resizer "-OF-" creator))
              (resizer-of-length (symbolicate package-witness resizer "-OF-" length))
              (resizer-of-length-free (symbolicate package-witness resizer-of-length "-FREE"))
              (resizer-of-resizer (symbolicate package-witness resizer "-OF-" resizer))
              (resizer-of-resizer-split (symbolicate package-witness resizer-of-resizer "-SPLIT"))
              (resizer-of-updater (symbolicate package-witness resizer "-OF-" updater))
              (resizer-of-updater-keep (symbolicate package-witness resizer-of-updater "-KEEP"))
              (resizer-of-updater-drop (symbolicate package-witness resizer-of-updater "-DROP"))
              (resizer-rw (symbolicate package-witness resizer "-RW"))

              (element-recognizer-of-accessor (symbolicate package-witness element-recognizer "-OF-" accessor))
              (accessor-when-large (symbolicate package-witness accessor "-WHEN-LARGE"))
              (accessor-when-not-natp (symbolicate package-witness accessor "-WHEN-NOT-NATP"))
              (accessor-when-not-recognizer (symbolicate package-witness accessor "-WHEN-NOT-" recognizer))
              (accessor-of-creator (symbolicate package-witness accessor "-OF-" creator))
              (accessor-of-resizer (symbolicate package-witness accessor "-OF-" resizer))
              (accessor-of-resizer-wh (symbolicate package-witness accessor-of-resizer "-WH"))
              (accessor-of-updater (symbolicate package-witness accessor "-OF-" updater))
              (accessor-of-updater-same (symbolicate package-witness accessor-of-updater "-SAME"))
              (accessor-of-updater-diff (symbolicate package-witness accessor-of-updater "-DIFF"))

              (updater-tp (symbolicate package-witness updater "-TP"))
              (updater-when-large (symbolicate package-witness updater "-WHEN-LARGE"))
              (updater-when-not-natp (symbolicate package-witness updater "-WHEN-NOT-NATP"))
              (updater-when-not-element-recognizer (symbolicate package-witness updater "-WHEN-NOT-" element-recognizer))
              (updater-when-not-natp (if (eq updater-when-not-natp updater-when-not-element-recognizer)
                                         (symbolicate package-witness updater-when-not-natp "-1")
                                         updater-when-not-natp))
              (updater-when-not-element-recognizer (if (eq updater-when-not-natp updater-when-not-element-recognizer)
                                                       (symbolicate package-witness updater-when-not-natp "-2")
                                                       updater-when-not-element-recognizer))
              (updater-when-not-recognizer (symbolicate package-witness updater "-WHEN-NOT-" recognizer))
              (updater-of-creator (symbolicate package-witness updater "-OF-" creator))
              (updater-of-resizer (symbolicate package-witness updater "-OF-" resizer))
              (updater-of-accessor (symbolicate package-witness updater "-OF-" accessor))
              (updater-of-accessor-free (symbolicate package-witness updater-of-accessor "-FREE"))
              (updater-of-updater (symbolicate package-witness updater "-OF-" updater))
              (updater-of-updater-same (symbolicate package-witness updater-of-updater "-SAME"))
              (updater-of-updater-diff (symbolicate package-witness updater-of-updater "-DIFF"))

              (%vector (symbolicate package-witness "%" vector))
              (contents-equal (symbolicate package-witness vector "-CONTENTS-EQUAL"))
              (contents-equal-witness (symbolicate package-witness contents-equal "-WITNESS"))
              (vector-equal (symbolicate package-witness vector "-EQUAL"))
              (vector-equal-constraints (symbolicate package-witness vector-equal "-CONSTRAINTS"))
              (vector-equal-fc (symbolicate package-witness vector-equal "-FC"))

              ;; Epilogue
              (vector-theorems (symbolicate package-witness vector "-THEOREMS"))
              (vector-aggressive (symbolicate package-witness vector "-AGGRESSIVE"))
              (epilogue
               `((deflabel ,vector-end)

                 (deftheory-static ,vector-theorems
                   (set-difference-theories
                    (set-difference-theories
                     (current-theory ',vector-end)
                     (current-theory ',vector-begin))
                    ',(append (and (not resizable)
                                   element-recognizer
                                   (list recognizer-aux))
                              (list recognizer
                                    creator
                                    fixer
                                    equiv
                                    length
                                    resizer
                                    accessor
                                    updater
                                    vector-equal))))

                 (deftheory-static ,vector-aggressive
                   ',(append
                      (list accessor-when-large
                            accessor-when-not-natp
                            accessor-when-not-recognizer
                            accessor-of-updater
                            updater-when-large
                            updater-when-not-natp
                            updater-when-not-recognizer
                            updater-of-accessor-free
                            updater-of-updater)
                      (and element-recognizer
                           (list updater-when-not-element-recognizer))
                      (and resizable
                           (list length-when-not-recognizer
                                 resizer-when-not-natp
                                 resizer-when-not-recognizer
                                 resizer-of-length-free
                                 resizer-of-resizer-split
                                 resizer-of-updater
                                 accessor-of-resizer))))

                 (in-theory
                   (union-theories (current-theory ',vector-begin)
                                   (theory ',vector-theorems)))
                 (in-theory
                   ;; Ensure `:USE' `VECTOR-EQUAL' automagically works.
                   (enable ,contents-equal))))

              ;; Functional Instantiation
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
                     `(lem-vector$a::element-equiv ,element-equiv)

                     `(lem-vector$a::recognizer-aux ,(if element-recognizer
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
                         `(lem-vector$a::equiv/resizable ,equiv)
                         `(lem-vector$a::equiv/fixed ,equiv))
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
               `(encapsulate ()

                  ,@(and element-fixer
                         element-recognizer
                         (not (eq element-equiv 'equal))
                         `((local
                             (defthm ,element-recognizer-constraints
                               (and (booleanp (,element-recognizer ,element))
                                    (,element-recognizer ,initial-element))
                               :rule-classes
                               ((:rewrite :corollary
                                          (booleanp (,element-recognizer ,element)))
                                ,@(and (not initial-element-name)
                                       `((:rewrite :corollary
                                                   (,element-recognizer ,initial-element)))))))

                           (local
                             (defthm ,element-fixer-constraints
                               (equal (,element-fixer ,element)
                                      (if (,element-recognizer ,element)
                                          ,element
                                          ,initial-element))))

                           (local
                             (defthm ,element-equiv-constraints
                               (equal (,element-equiv ,%element ,element)
                                      (equal (,element-fixer ,%element)
                                             (,element-fixer ,element)))
                               :rule-classes
                               ((:rewrite :match-free :all))
                               :hints
                               (("Goal"
                                 :in-theory (enable ,element-equiv)))))))

                  (local
                    (deflabel end-of-prologue))

                  (local
                    (include-book "projects/atomic-stobjs/lemmas/vector-a" :dir :system))

                  (local
                    (table acl2::theory-invariant-table nil nil :clear))

                  (local
                    (in-theory
                      (union-theories (current-theory 'acl2::ground-zero)
                                      (set-difference-theories
                                       (universal-theory 'end-of-prologue)
                                       (universal-theory ',vector-begin)))))

                  ,@(and absstobj-info
                         `((local
                             (in-theory
                               (enable ,@(strip-cars (cdr absstobj-info)))))))

                  (local
                    (in-theory
                      (disable make-list-ac
                               (:e make-list-ac))))

                  ,@(and element-recognizer
                         `((local
                             (in-theory
                               (enable (:e ,element-recognizer))))))

                  ;; Fixed-length vectors with specialized elements need a
                  ;; predicate to check element-wise validity.
                  ,@(and (not resizable)
                         element-recognizer
                         `((defun ,recognizer-aux (,vector)
                             (declare (xargs :guard t))
                             (if (consp ,vector)
                                 (and (,element-recognizer (car ,vector))
                                      (,recognizer-aux (cdr ,vector)))
                                 (null ,vector)))

                           (local
                             (defthm ,recognizer-aux-tp
                               (booleanp (,recognizer-aux ,vector))
                               :rule-classes :type-prescription
                               :hints
                               (("Goal"
                                 :by (:functional-instance lem-vector$a::recognizer-aux-tp
                                                           (lem-vector$a::recognizer-aux ,recognizer-aux)
                                                           (lem-vector$a::element-recognizer ,element-recognizer))))))

                           (local
                             (defthm ,recognizer-aux-cr
                               (implies (,recognizer-aux ,vector)
                                        (true-listp ,vector))
                               :rule-classes :compound-recognizer
                               :hints
                               (("Goal"
                                 :by (:functional-instance lem-vector$a::recognizer-aux-cr
                                                           (lem-vector$a::recognizer-aux ,recognizer-aux)
                                                           (lem-vector$a::element-recognizer ,element-recognizer))))))

                           (local
                             (defthm ,element-recognizer-of-nth-when-recognizer-aux
                               (implies (and (,recognizer-aux ,vector)
                                             (natp ,index)
                                             (< ,index (len ,vector)))
                                        (,element-recognizer (nth ,index ,vector)))
                               :hints
                               (("Goal"
                                 :by (:functional-instance lem-vector$a::element-recognizer-of-nth-when-recognizer-aux
                                                           (lem-vector$a::recognizer-aux ,recognizer-aux)
                                                           (lem-vector$a::element-recognizer ,element-recognizer))))))))

                  (defun ,recognizer (,vector)
                    (declare (xargs :guard t))
                    ,(if resizable
                         (if element-recognizer
                             `(if (consp ,vector)
                                  (and (,element-recognizer (car ,vector))
                                       (,recognizer (cdr ,vector)))
                                  (null ,vector))
                             `(true-listp ,vector))
                         (if element-recognizer
                             `(and (= (len ,vector) ,default-length-name)
                                   (,recognizer-aux ,vector))
                             `(and (= (len ,vector) ,default-length-name)
                                   (true-listp ,vector)))))

                  (defun-nx ,creator ()
                    ;; We don't want to frequently allocate large list literals
                    ;; in proofs.
                    (declare (xargs :guard t))
                    (make-list ,default-length-name
                               :initial-element ,initial-element))

                  (defun ,fixer (,vector)
                    (declare (xargs :guard (,recognizer ,vector)))
                    (if (,recognizer ,vector)
                        ,vector
                        (,creator)))

                  (defun ,equiv (,%vector ,vector)
                    (declare (xargs :guard (and (,recognizer ,%vector)
                                                (,recognizer ,vector))))
                    (equal (,fixer ,%vector)
                           (,fixer ,vector)))

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
                         `(let ((length (nfix length))
                                (,vector (,fixer ,vector)))
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
                                                ,@(and guard-element-recognizer
                                                       `((,guard-element-recognizer ,element)))
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

                  (local
                    (defthm ,vector-constraints
                      (and ,@(and (not resizable)
                                  element-recognizer
                                  `((equal (,recognizer-aux ,vector)
                                           (if (consp ,vector)
                                               (if (,element-recognizer (car ,vector))
                                                   (,recognizer-aux (cdr ,vector))
                                                   'nil)
                                               (null ,vector)))))
                           (equal (,creator)
                                  (make-list-ac ,default-length ,initial-element 'nil))
                           (equal (,recognizer ,vector)
                                  ,(cond
                                     ((and (not resizable)
                                           element-recognizer)
                                      `(if (equal (len ,vector) ,default-length)
                                           (,recognizer-aux ,vector)
                                           'nil))
                                     ((not resizable)
                                      `(if (equal (len ,vector) ,default-length)
                                           (true-listp ,vector)
                                           'nil))
                                     (element-recognizer
                                      `(if (consp ,vector)
                                           (if (,element-recognizer (car ,vector))
                                               (,recognizer (cdr ,vector))
                                               'nil)
                                           (null ,vector)))
                                     (t
                                      `(true-listp ,vector))))
                           (equal (,fixer ,vector)
                                  (if (,recognizer ,vector)
                                      ,vector
                                      (,creator)))
                           (equal (,equiv ,%vector ,vector)
                                  (equal (,fixer ,%vector)
                                         (,fixer ,vector)))
                           (equal (,length ,vector)
                                  ,(if resizable
                                       `(len (,fixer ,vector))
                                       default-length-name))
                           (equal (,resizer length ,vector)
                                  ,(if resizable
                                       `((lambda (length ,vector)
                                           (resize-list ,vector length ,initial-element))
                                         (nfix length)
                                         (,fixer ,vector))
                                       `(,fixer ,vector)))
                           (equal (,accessor ,index ,vector)
                                  ((lambda (,index ,vector)
                                     (if (< ,index ,(if resizable
                                                        `(,length ,vector)
                                                        default-length-name))
                                         ,(if element-fixer
                                              `(,element-fixer (nth ,index ,vector))
                                              `(nth ,index ,vector))
                                         ,initial-element))
                                   (nfix ,index)
                                   (,fixer ,vector)))
                           (equal (,updater ,index ,element ,vector)
                                  ((lambda (,index ,element ,vector)
                                     (if (< ,index ,(if resizable
                                                        `(,length ,vector)
                                                        default-length-name))
                                         (update-nth ,index ,element ,vector)
                                         ,vector))
                                   (nfix ,index)
                                   ,(if element-fixer
                                        `(,element-fixer ,element)
                                        element)
                                   (,fixer ,vector))))
                      :rule-classes ()
                      :hints
                      (("Goal"
                        :do-not-induct t
                        :use (:functional-instance
                              ,(if resizable
                                   'lem-vector$a::vector-constraints/resizable
                                   'lem-vector$a::vector-constraints/fixed)
                              ,@fi-bindings)))))

                  (local
                    (in-theory
                      (disable ,@(and (not resizable)
                                      element-recognizer
                                      (list recognizer-aux))
                               ,recognizer
                               ,creator
                               ,fixer
                               ,equiv
                               ,length
                               ,resizer
                               ,accessor
                               ,updater)))

                  ;; `RECOGNIZER'
                  (defthm ,recognizer-tp
                    (booleanp (,recognizer ,vector))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if resizable
                                'lem-vector$a::recognizer/resizable-tp
                                'lem-vector$a::recognizer/fixed-tp)
                           ,@fi-bindings))))

                  (defthm ,recognizer-cr
                    (implies (,recognizer ,vector)
                             (true-listp ,vector))
                    :rule-classes :compound-recognizer
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if resizable
                                'lem-vector$a::recognizer/resizable-cr
                                'lem-vector$a::recognizer/fixed-cr)
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
                      :by (:functional-instance
                           ,(if resizable
                                'lem-vector$a::recognizer/resizable-of-fixer/resizable
                                'lem-vector$a::recognizer/fixed-of-fixer/fixed)
                           ,@fi-bindings))))

                  ,@(and resizable
                         ;; The resizer of a fixed-length vector is always rewritten.
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

                  ;; `FIXER'
                  (defthm ,fixer-tp
                    (true-listp (,fixer ,vector))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if resizable
                                'lem-vector$a::fixer/resizable-tp
                                'lem-vector$a::fixer/fixed-tp)
                           ,@fi-bindings))))

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

                  ;; `EQUIV'
                  (defthm ,equiv-tp
                    (booleanp (,equiv ,%vector ,vector))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if resizable
                                'lem-vector$a::equiv/resizable-tp
                                'lem-vector$a::equiv/fixed-tp)
                           ,@fi-bindings))))

                  (defequiv ,equiv
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if resizable
                                'lem-vector$a::equiv/resizable-is-an-equivalence
                                'lem-vector$a::equiv/fixed-is-an-equivalence)
                           ,@fi-bindings))))

                  (defcong ,equiv equal (,fixer ,vector) 1
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if resizable
                                'lem-vector$a::equiv/resizable-implies-equal-fixer/resizable-1
                                'lem-vector$a::equiv/fixed-implies-equal-fixer/fixed-1)
                           ,@fi-bindings))))

                  (defthm ,fixer-mod-equiv
                    (,equiv (,fixer ,vector) ,vector)
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if resizable
                                'lem-vector$a::fixer/resizable-mod-equiv/resizable
                                'lem-vector$a::fixer/fixed-mod-equiv/fixed)
                           ,@fi-bindings))))

                  (defthm ,equiv-when-not-recognizer
                    (implies (not (,recognizer ,vector))
                             (,equiv ,vector (,creator)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if resizable
                                'lem-vector$a::equiv/resizable-when-not-recognizer/resizable
                                'lem-vector$a::equiv/fixed-when-not-recognizer/fixed)
                           ,@fi-bindings))))

                  ;; `LENGTH'
                  (defthm ,length-tp
                    (natp (,length ,vector))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if resizable
                                'lem-vector$a::length/resizable-tp
                                'lem-vector$a::length/fixed-tp)
                           ,@fi-bindings))))

                  ,@(if resizable
                        `((defcong ,equiv equal (,length ,vector) 1
                            :hints
                            (("Goal"
                              :by (:functional-instance
                                   lem-vector$a::equiv/resizable-implies-equal-length/resizable-1
                                   ,@fi-bindings))))

                          (defthmd ,length-when-not-recognizer
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

                          (defthm ,length-of-resizer
                            (equal (,length (,resizer length ,vector))
                                   (nfix length))
                            :rule-classes
                            ((:rewrite :corollary
                                       (equal (,length (,resizer length ,vector))
                                              (nfix (double-rewrite length)))))
                            :hints
                            (("Goal"
                              :by (:functional-instance
                                   lem-vector$a::length/resizable-of-resizer/resizable
                                   ,@fi-bindings))))

                          (defthm ,length-of-updater
                            (equal (,length (,updater ,index ,element ,vector))
                                   (,length ,vector))
                            :rule-classes
                            ((:rewrite :corollary
                                       (equal (,length (,updater ,index ,element ,vector))
                                              (,length (double-rewrite ,vector)))))
                            :hints
                            (("Goal"
                              :by (:functional-instance
                                   lem-vector$a::length/resizable-of-updater/resizable
                                   ,@fi-bindings)))))

                        `((defthm ,length-rw
                            (equal (,length ,vector)
                                   ,default-length-name)
                            :hints
                            (("Goal"
                              :by (:functional-instance
                                   lem-vector$a::length/fixed-rw
                                   ,@fi-bindings))))))

                  ;; `RESIZER'
                  (defthm ,resizer-tp
                    (true-listp (,resizer length ,vector))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if resizable
                                'lem-vector$a::resizer/resizable-tp
                                'lem-vector$a::resizer/fixed-tp)
                           ,@fi-bindings))))

                  ,@(if resizable
                        ;; TODO: generate `LENGTH' in current package
                        `((defcong nat-equiv equal (,resizer length ,vector) 1
                            :hints
                            (("Goal"
                              :by (:functional-instance
                                   lem-vector$a::nat-equiv-implies-equal-resizer/resizable-1
                                   ,@fi-bindings))))

                          (defcong ,equiv equal (,resizer length ,vector) 2
                            :hints
                            (("Goal"
                              :by (:functional-instance
                                   lem-vector$a::equiv/resizable-implies-equal-resizer/resizable-2
                                   ,@fi-bindings))))

                          (defthmd ,resizer-when-not-natp
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
                            (implies (nat-equiv length ,default-length-name)
                                     (equal (,resizer length (,creator))
                                            (,creator)))
                            :hints
                            (("Goal"
                              :by (:functional-instance
                                   lem-vector$a::resizer/resizable-of-creator
                                   ,@fi-bindings))))

                          (defthmd ,resizer-of-length-free
                            (implies (nat-equiv length (,length ,vector))
                                     (equal (,resizer length ,vector)
                                            (,fixer ,vector)))
                            :hints
                            (("Goal"
                              :by (:functional-instance
                                   lem-vector$a::resizer/resizable-of-length/resizable-free
                                   ,@fi-bindings))))

                          (defthm ,resizer-of-length
                            (implies (,equiv ,%vector ,vector)
                                     (equal (,resizer (,length ,%vector) ,vector)
                                            (,fixer ,vector)))
                            :hints
                            (("Goal"
                              :by (:functional-instance
                                   lem-vector$a::resizer/resizable-of-length/resizable
                                   ,@fi-bindings))))

                          (defthmd ,resizer-of-resizer-split
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
                              :by (:functional-instance
                                   lem-vector$a::resizer/resizable-of-resizer/resizable
                                   ,@fi-bindings))))

                          (defthm ,resizer-of-resizer
                            (implies (or (<= (nfix %length) (nfix length))
                                         (<= (,length ,vector) (nfix length)))
                                     (equal (,resizer %length (,resizer length ,vector))
                                            (,resizer %length ,vector)))
                            :hints
                            (("Goal"
                              :by (:functional-instance
                                   lem-vector$a::resizer/resizable-of-resizer/resizable
                                   ,@fi-bindings))))

                          (defthmd ,resizer-of-updater
                            (equal (,resizer length (,updater ,index ,element ,vector))
                                   (if (and (< (nfix ,index) (,length ,vector))
                                            (< (nfix ,index) (nfix length)))
                                       (,updater ,index ,element (,resizer length ,vector))
                                       (,resizer length ,vector)))
                            :rule-classes
                            ((:rewrite :corollary
                                       (equal (,resizer length (,updater ,index ,element ,vector))
                                              (if (and (< (nfix (double-rewrite ,index)) (,length (double-rewrite ,vector)))
                                                       (< (nfix (double-rewrite ,index)) (nfix length)))
                                                  (,updater ,index ,element (,resizer length (double-rewrite ,vector)))
                                                  (,resizer length (double-rewrite ,vector))))))
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
                            :rule-classes
                            ((:rewrite :corollary
                                       (implies (and (< (nfix (double-rewrite ,index)) (,length (double-rewrite ,vector)))
                                                     (< (nfix (double-rewrite ,index)) (nfix length)))
                                                (equal (,resizer length (,updater ,index ,element ,vector))
                                                       (,updater ,index ,element (,resizer length (double-rewrite ,vector)))))))
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
                            :rule-classes
                            ((:rewrite :corollary
                                       (implies (and (< (nfix (double-rewrite ,index)) (,length (double-rewrite ,vector)))
                                                     (<= (nfix length) (nfix (double-rewrite ,index))))
                                                (equal (,resizer length (,updater ,index ,element ,vector))
                                                       (,resizer length (double-rewrite ,vector))))))
                            :hints
                            (("Goal"
                              :by (:functional-instance
                                   lem-vector$a::resizer/resizable-of-updater/resizable-drop
                                   ,@fi-bindings)))))

                        `((defthm ,resizer-rw
                            (equal (,resizer length ,vector)
                                   (,fixer ,vector))
                            :rule-classes
                            ((:rewrite :corollary
                                       (equal (,resizer length ,vector)
                                              (,fixer (double-rewrite ,vector)))))
                            :hints
                            (("Goal"
                              :by (:functional-instance
                                   lem-vector$a::resizer/fixed-rw
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

                  (defcong nat-equiv equal (,accessor ,index ,vector) 1
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if resizable
                                'lem-vector$a::nat-equiv-implies-equal-accessor/resizable-1
                                'lem-vector$a::nat-equiv-implies-equal-accessor/fixed-1)
                           ,@fi-bindings))))

                  (defcong ,equiv equal (,accessor ,index ,vector) 2
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if resizable
                                'lem-vector$a::equiv/resizable-implies-equal-accessor/resizable-2
                                'lem-vector$a::equiv/fixed-implies-equal-accessor/fixed-2)
                           ,@fi-bindings))))

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

                  ,@(and resizable
                         `((defthmd ,accessor-of-resizer
                             (equal (,accessor ,index (,resizer length ,vector))
                                    (if (< (nfix ,index) (nfix length))
                                        (,accessor ,index ,vector)
                                        ,initial-element))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-vector$a::accessor/resizable-of-resizer/resizable
                                    ,@fi-bindings))))

                           (defthm ,accessor-of-resizer-wh
                             (implies (< (nfix ,index) (nfix length))
                                      (equal (,accessor ,index (,resizer length ,vector))
                                             (,accessor ,index ,vector)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-vector$a::accessor/resizable-of-resizer/resizable-wh
                                    ,@fi-bindings))))))

                  (defthmd ,accessor-of-updater
                    (equal (,accessor ,%index (,updater ,index ,element ,vector))
                           (cond
                             ((<= ,(if resizable
                                       `(,length ,vector)
                                       default-length-name)
                                  (nfix ,%index))
                              ,initial-element)
                             ((nat-equiv ,%index ,index)
                              ,(if element-fixer
                                   `(,element-fixer ,element)
                                   element))
                             (t
                              (,accessor ,%index ,vector))))
                    :rule-classes
                    ((:rewrite :corollary
                               (equal (,accessor ,%index (,updater ,index ,element ,vector))
                                      (cond
                                        ((<= ,(if resizable
                                                  `(,length (double-rewrite ,vector))
                                                  default-length-name)
                                             (nfix ,%index))
                                         ,initial-element)
                                        ((nat-equiv ,%index (double-rewrite ,index))
                                         ,(if element-fixer
                                              `(,element-fixer (double-rewrite ,element))
                                              element))
                                        (t
                                         (,accessor ,%index (double-rewrite ,vector)))))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if resizable
                                'lem-vector$a::accessor/resizable-of-updater/resizable
                                'lem-vector$a::accessor/fixed-of-updater/fixed)
                           ,@fi-bindings))))

                  (defthm ,accessor-of-updater-same
                    (implies (and (nat-equiv ,%index ,index)
                                  (< (nfix ,%index)
                                     ,(if resizable
                                          `(,length ,vector)
                                          default-length-name)))
                             (equal (,accessor ,%index (,updater ,index ,element ,vector))
                                    ,(if element-fixer
                                         `(,element-fixer ,element)
                                         element)))
                    :rule-classes
                    ((:rewrite :corollary
                               (implies (and (nat-equiv ,%index (double-rewrite ,index))
                                             (< (nfix ,%index) ,(if resizable
                                                                    `(,length (double-rewrite ,vector))
                                                                    default-length-name)))
                                        (equal (,accessor ,%index (,updater ,index ,element ,vector))
                                               ,(if element-fixer
                                                    `(,element-fixer (double-rewrite ,element))
                                                    element)))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if resizable
                                'lem-vector$a::accessor/resizable-of-updater/resizable-same
                                'lem-vector$a::accessor/fixed-of-updater/fixed-same)
                           ,@fi-bindings))))

                  (defthm ,accessor-of-updater-diff
                    (implies (and (not (nat-equiv ,%index ,index))
                                  (< (nfix ,%index) ,(if resizable
                                                         `(,length ,vector)
                                                         default-length-name)))
                             (equal (,accessor ,%index (,updater ,index ,element ,vector))
                                    (,accessor ,%index ,vector)))
                    :rule-classes
                    ((:rewrite :corollary
                               (implies (and (not (nat-equiv ,%index (double-rewrite ,index)))
                                             (< (nfix ,%index) ,(if resizable
                                                                    `(,length (double-rewrite ,vector))
                                                                    default-length-name)))
                                        (equal (,accessor ,%index (,updater ,index ,element ,vector))
                                               (,accessor ,%index (double-rewrite ,vector))))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if resizable
                                'lem-vector$a::accessor/resizable-of-updater/resizable-diff
                                'lem-vector$a::accessor/fixed-of-updater/fixed-diff)
                           ,@fi-bindings))))

                  ;; `UPDATER'
                  (defthm ,updater-tp
                    (true-listp (,updater ,index ,element ,vector))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if resizable
                                'lem-vector$a::updater/resizable-tp
                                'lem-vector$a::updater/fixed-tp)
                           ,@fi-bindings))))

                  (defcong nat-equiv equal (,updater ,index ,element ,vector) 1
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if resizable
                                'lem-vector$a::nat-equiv-implies-equal-updater/resizable-1
                                'lem-vector$a::nat-equiv-implies-equal-updater/fixed-1)
                           ,@fi-bindings))))

                  ,@(and (not (eq element-equiv 'equal))
                         element-recognizer
                         element-fixer
                         `((defcong ,element-equiv equal (,updater ,index ,element ,vector) 2
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    ,(if resizable
                                         'lem-vector$a::element-equiv-implies-equal-updater/resizable-2
                                         'lem-vector$a::element-equiv-implies-equal-updater/fixed-2)
                                    ,@fi-bindings))))))

                  (defcong ,equiv equal (,updater ,index ,element ,vector) 3
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if resizable
                                'lem-vector$a::equiv/resizable-implies-equal-updater/resizable-3
                                'lem-vector$a::equiv/fixed-implies-equal-updater/fixed-3)
                           ,@fi-bindings))))

                  (defthmd ,updater-when-large
                    (implies (<= ,(if resizable
                                      `(,length ,vector)
                                      default-length-name)
                                 (nfix ,index))
                             (equal (,updater ,index ,element ,vector)
                                    (,fixer ,vector)))
                    :rule-classes
                    ((:rewrite :corollary
                               (implies (<= ,(if resizable
                                                 `(,length (double-rewrite ,vector))
                                                 default-length-name)
                                            (nfix (double-rewrite ,index)))
                                        (equal (,updater ,index ,element ,vector)
                                               (,fixer (double-rewrite ,vector))))))
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
                    (implies (,element-equiv ,element ,initial-element)
                             (equal (,updater ,index ,element (,creator))
                                    (,creator)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if resizable
                                'lem-vector$a::updater/resizable-of-creator
                                'lem-vector$a::updater/fixed-of-creator)
                           ,@fi-bindings))))

                  ,@(and resizable
                         `((defthm ,updater-of-resizer
                             (implies (,element-equiv ,element (,accessor ,index ,vector))
                                      (equal (,updater ,index ,element (,resizer length ,vector))
                                             (,resizer length ,vector)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    ,(if resizable
                                         'lem-vector$a::updater/resizable-of-resizer/resizable
                                         'lem-vector$a::updater/fixed-of-resizer/fixed)
                                    ,@fi-bindings))))))

                  (defthmd ,updater-of-accessor-free
                    (implies (,element-equiv ,element (,accessor ,index ,vector))
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
                    (implies (and (nat-equiv ,%index ,index)
                                  (,equiv ,%vector ,vector))
                             (equal (,updater ,%index (,accessor ,index ,%vector) ,vector)
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
                           (if (nat-equiv ,%index ,index)
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
                    (implies (nat-equiv ,%index ,index)
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
                    (implies (not (nat-equiv ,%index ,index))
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
                      (equal (,accessor ,index ,%vector)
                             (,accessor ,index ,vector)))
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

                  (table equality ',vector ',vector-equal)

                  (local
                    (defthm ,vector-equal-constraints
                      (and (equal (,contents-equal ,%vector ,vector)
                                  ((lambda (,index ,vector ,%vector)
                                     (equal (,accessor ,index ,%vector)
                                            (,accessor ,index ,vector)))
                                   (,contents-equal-witness ,%vector ,vector)
                                   ,vector ,%vector))
                           (implies (,contents-equal ,%vector ,vector)
                                    (equal (,accessor ,index ,%vector)
                                           (,accessor ,index ,vector)))
                           (equal (,vector-equal ,%vector ,vector)
                                  (if (,recognizer ,%vector)
                                      (if (,recognizer ,vector)
                                          ,(if resizable
                                               `(if (equal (,length ,%vector)
                                                           (,length ,vector))
                                                    (,contents-equal ,%vector ,vector)
                                                    'nil)
                                               `(,contents-equal ,%vector ,vector))
                                          'nil)
                                      'nil)))
                      :rule-classes ()
                      :hints
                      (("Goal"
                        :in-theory (disable ,contents-equal)
                        :use (:instance (:functional-instance
                                         ,(if resizable
                                              'lem-vector$a::equal-constraints/resizable
                                              'lem-vector$a::equal-constraints/fixed)
                                         ,@fi-bindings-with-skolem)
                                        (lem-vector$a::index ,index)
                                        (lem-vector$a::%vector ,%vector)
                                        (lem-vector$a::vector ,vector)))
                       ("Subgoal 1"
                        :in-theory (enable ,contents-equal)))))

                  (local
                    (in-theory
                      (disable ,contents-equal
                               ,vector-equal)))

                  (defthm ,vector-equal-fc
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
                      :by (:functional-instance
                           ,(if resizable
                                'lem-vector$a::equal/resizable-fc
                                'lem-vector$a::equal/fixed-fc)
                           ,@fi-bindings-with-skolem))))))

              (stobj$a-property `(,vector (,recognizer
                                           ,creator
                                           ,fixer
                                           ,equiv)
                                          ((,element
                                            ,element-recognizer
                                            ,initial-element-name
                                            ,element-fixer
                                            ,element-equiv)
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

            (table stobj$a-property ',vector ',stobj$a-property)

            (table package-witness ',vector ',package-witness))))))
