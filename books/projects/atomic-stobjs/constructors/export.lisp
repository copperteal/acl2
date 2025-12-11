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
(include-book "../lemmas/hash-table-a")
|#

(include-book "../utilities/top")
(include-book "copy")


;;;; `MAKE-VECTOR-EXPORT-EVENTS'
(defun make-vector-export-events (vector package-witness state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp vector)
                              (package-witness-p package-witness))
                  :verify-guards nil))
  (let* ((%vector (symbolicate package-witness "%" vector))

         (export (symbolicate package-witness vector "-EXPORT"))
         (export-begin (symbolicate package-witness export "-BEGIN"))
         (export-end (symbolicate package-witness export "-END"))
         (export-theory (symbolicate package-witness export "-THEORY"))
         (exportp (symbolicate package-witness export (make-predicate-suffix export)))
         (exportp-rec (symbolicate package-witness exportp "-REC"))
         (export-acc (symbolicate package-witness export "-ACC"))
         (import (symbolicate package-witness vector "-IMPORT"))
         (import-rec (symbolicate package-witness import "-REC"))

         (stobj-property (getpropc vector 'acl2::stobj))
         (creator (cdadr stobj-property))
         (the-vector (symbolicate vector "THE-" vector))
         (length (second (third stobj-property)))
         (resizer (third (third stobj-property)))
         (accessor (fourth (third stobj-property)))
         (updater (fifth (third stobj-property)))

         (world (w state))
         (coupledp (cdr (assoc vector (table-alist 'coupledp world))))

         (stobj$a-property (cdr (assoc vector (table-alist 'stobj$a-property world))))
         (vector$a (first stobj$a-property))
         (recognizer$a-aux (symbolicate vector$a vector$a "-AUX-P"))
         (vector$a-theorems (symbolicate vector$a vector$a "-THEOREMS"))
         (vector$a-aggressive (symbolicate vector$a vector$a "-AGGRESSIVE"))
         (vector$a-constraints (symbolicate vector$a vector$a "-CONSTRAINTS"))
         (recognizer$a (first (second stobj$a-property)))
         (creator$a (second (second stobj$a-property)))
         (fixer$a (third (second stobj$a-property)))
         (length$a (first (third (third stobj$a-property))))
         (resizer$a (second (third (third stobj$a-property))))
         (accessor$a (third (third (third stobj$a-property))))
         (updater$a (fourth (third (third stobj$a-property))))

         (index (symbolicate package-witness "I"))
         (resizable (first (second (third stobj$a-property))))
         (element (first (first (third stobj$a-property))))
         (%element (symbolicate element "%" element))
         (element-stobj-property (getpropc element 'acl2::stobj))
         (element-stobj$a-property (cdr (assoc element (table-alist 'stobj$a-property world))))
         (initial-element-name (third (first (third stobj$a-property))))
         (element-creator (second (second element-stobj$a-property)))
         (initial-element (if element-stobj-property
                              `(,element-creator)
                              initial-element-name))
         (default-length-name (second (second (third stobj$a-property))))
         (element-recognizer (second (first (third stobj$a-property))))
         (element-fixer (fourth (first (third stobj$a-property))))
         (element-equiv (fifth (first (third stobj$a-property))))
         (exportp-rec (if element-recognizer
                          exportp-rec
                          'true-listp))

         (element-coupled-p (cdr (assoc element (table-alist 'coupledp world))))
         (element-export-list (cdr (assoc element (table-alist 'export world))))
         (element-export-p (first element-export-list))
         (element-export (second element-export-list))
         (element-import (third element-export-list))

         ;; Theorem Names
         (element-recognizer-constraints (symbolicate "ATOMIC-STOBJS" element-recognizer "-CONSTRAINTS"))
         (element-fixer-constraints (symbolicate "ATOMIC-STOBJS" element-fixer "-CONSTRAINTS"))
         (element-equiv-constraints (symbolicate "ATOMIC-STOBJS" element-equiv "-CONSTRAINTS"))

         (exportp-tp (symbolicate package-witness exportp "-TP"))
         (exportp-cr (symbolicate package-witness exportp "-CR"))

         (export-tp (symbolicate package-witness export "-TP"))
         (exportp-of-export (symbolicate package-witness exportp "-OF-" export))

         (import-tp (symbolicate package-witness import "-TP"))
         (recognizer$a-of-import (symbolicate package-witness recognizer$a "-OF-" import))
         (coupledp-of-import (symbolicate package-witness coupledp "-OF-" import))
         (import-when-not-exportp (symbolicate package-witness import "-WHEN-NOT-" exportp))
         (import-ignores-2 (symbolicate package-witness import "-IGNORES-2"))
         (length$a-of-import (symbolicate package-witness length$a "-OF-" import))
         (accessor$a-of-import (symbolicate package-witness accessor$a "-OF-" import))

         (export-of-import (symbolicate package-witness export "-OF-" import))
         (import-of-export (symbolicate package-witness import "-OF-" export))

         (fi-bindings
          (list `(lem-vector$a::element-recognizer ,(or element-recognizer
                                                        `(lambda (element)
                                                           t)))
                `(lem-vector$a::element-fixer ,(or element-fixer
                                                   'identity))
                `(lem-vector$a::element-equiv ,(or element-equiv
                                                   'equal))
                `(lem-vector$a::initial-element ,(if element-stobj$a-property
                                                     `(,element-creator)
                                                     `(lambda ()
                                                        ,initial-element-name)))
                `(lem-vector$a::element-coupled-p ,(or element-coupled-p
                                                       `(lambda (element)
                                                          t)))
                `(lem-vector$a::element-export-p ,(or element-export-p
                                                      element-recognizer
                                                      `(lambda ()
                                                         t)))
                `(lem-vector$a::element-export ,(or element-export
                                                    element-fixer
                                                    'identity))
                `(lem-vector$a::element-import ,(or element-import
                                                    `(lambda (export element)
                                                       (,element-fixer export))
                                                    `(lambda (export element)
                                                       export)))

                `(lem-vector$a::name (lambda ()
                                       ',vector))
                `(lem-vector$a::exportp-rec ,exportp-rec)
                (if resizable
                    `(lem-vector$a::exportp/resizable ,exportp)
                    `(lem-vector$a::exportp/fixed ,exportp))

                `(lem-vector$a::default-length (lambda ()
                                                 ,default-length-name))))

         (fi-bindings-post-export
          (append
           (and resizable
                (list `(lem-vector$a::length/resizable ,length$a)
                      `(lem-vector$a::resizer/resizable ,resizer$a)))
           (list* (if resizable
                      `(lem-vector$a::export-acc/resizable ,export-acc)
                      `(lem-vector$a::export-acc/fixed ,export-acc))
                  (if resizable
                      `(lem-vector$a::export/resizable ,export)
                      `(lem-vector$a::export/fixed ,export))

                  `(lem-vector$a::recognizer-aux ,(if element-recognizer
                                                      (if resizable
                                                          recognizer$a
                                                          recognizer$a-aux)
                                                      'true-listp))
                  (if resizable
                      `(lem-vector$a::recognizer/resizable ,recognizer$a)
                      `(lem-vector$a::recognizer/fixed ,recognizer$a))
                  `(lem-vector$a::creator ,creator$a)
                  (if resizable
                      `(lem-vector$a::fixer/resizable ,fixer$a)
                      `(lem-vector$a::fixer/fixed ,fixer$a))
                  (if resizable
                      `(lem-vector$a::accessor/resizable ,accessor$a)
                      `(lem-vector$a::accessor/fixed ,accessor$a))

                  fi-bindings)))

         (fi-bindings-post-import
          (list* (if resizable
                     `(lem-vector$a::coupledp/resizable ,(or coupledp
                                                             `(lambda (vector)
                                                                t)))
                     `(lem-vector$a::coupledp/fixed ,(or coupledp
                                                         `(lambda (vector)
                                                            t))))

                 (if resizable
                     `(lem-vector$a::updater/resizable ,updater$a)
                     `(lem-vector$a::updater/fixed ,updater$a))

                 (if resizable
                     `(lem-vector$a::import-rec/resizable ,import-rec)
                     `(lem-vector$a::import-rec/fixed ,import-rec))
                 (if resizable
                     `(lem-vector$a::import/resizable ,import)
                     `(lem-vector$a::import/fixed ,import))

                 fi-bindings-post-export)))

    `(progn
       (deflabel ,export-begin)

       (encapsulate ()

         (local
           (deflabel prologue-begin))

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
                       ,@(and (not (equal initial-element initial-element-name))
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
                                    (,element-fixer ,element)))))))

         (local
           (deflabel prologue-end))

         (local
           (include-book "projects/atomic-stobjs/lemmas/vector-a" :dir :system))

         (local
           (table acl2::theory-invariant-table nil nil :clear))

         (local
           (in-theory
             (union-theories (theory 'acl2::ground-zero)
                             (set-difference-theories (current-theory 'prologue-end)
                                                      (current-theory 'prologue-begin)))))

         (local
           (in-theory
             (disable make-list-ac
                      (:e make-list-ac))))

         ,@(and element-recognizer
                `((local
                    (in-theory
                      (enable (:e ,element-recognizer))))))

         ,@(and element-stobj-property
                `((local
                    (in-theory
                      (enable ,@(strip-cars (cdr (getpropc element 'acl2::absstobj-info))))))))

         (local
           (in-theory
             (enable ,@(strip-cars (cdr (getpropc vector 'acl2::absstobj-info))))))

         ;; `EXPORTP-REC'
         ,@(and element-recognizer
                `((defun ,exportp-rec (list)
                    (declare (xargs :guard t))
                    (if (consp list)
                        (and (,(or element-export-p
                                   element-recognizer)
                               (car list))
                             (,exportp-rec (cdr list)))
                        (null list)))))

         ;; `EXPORTP'
         (defun ,exportp (export)
           (declare (xargs :guard t))
           (and (consp export)
                (equal (car export) ',vector)
                ;; TODO: `EXPORTP-REC' defaults to `TRUE-LISTP'
                (,exportp-rec (cdr export))
                ,@(and (not resizable)
                       `((= (len (cdr export)) ,default-length-name)))))

         (defthm ,exportp-tp
           (booleanp (,exportp export))
           :rule-classes :type-prescription
           :hints
           (("Goal"
             :by (:functional-instance
                  ,(if resizable
                       'lem-vector$a::exportp/resizable-tp
                       'lem-vector$a::exportp/fixed-tp)
                  ,@fi-bindings))))

         (defthm ,exportp-cr
           (implies (,exportp export)
                    (and (consp export)
                         (true-listp export)))
           :rule-classes :compound-recognizer
           :hints
           (("Goal"
             :by (:functional-instance
                  ,(if resizable
                       'lem-vector$a::exportp/resizable-cr
                       'lem-vector$a::exportp/fixed-cr)
                  ,@fi-bindings))))

         ;; `EXPORT-ACC'
         (defun ,export-acc (,index acc ,vector)
           (declare (xargs :stobjs ,vector
                           :guard (and (natp ,index)
                                       (,exportp-rec acc)
                                       (<= ,index ,(if resizable
                                                       `(,length ,vector)
                                                       default-length-name)))))
           (if (zp ,index)
               (mbe :logic (true-list-fix acc)
                    :exec acc)
               ,(if element-export
                    `(let ((,index (1- ,index)))
                       (stobj-let ((,element (,accessor ,index ,vector) ,updater))
                                  (export)
                                  (,element-export ,element)
                         (,export-acc ,index (cons export acc) ,vector)))
                    `(let* ((,index (1- ,index))
                            (,element (,accessor ,index ,vector)))
                       (,export-acc ,index (cons ,element acc) ,vector)))))

         ;; `EXPORT'
         (defun ,export (,vector)
           (declare (xargs :stobjs ,vector))
           (cons ',vector
                 (,export-acc ,(if resizable
                                   `(,length ,vector)
                                   default-length-name)
                              ()
                              ,vector)))

         (defthm ,export-tp
           (and (consp (,export ,vector))
                (true-listp (,export ,vector)))
           :rule-classes :type-prescription
           :hints
           (("Goal"
             :do-not-induct t
             :in-theory (enable ,vector$a-constraints)
             :by (:functional-instance
                  ,(if resizable
                       'lem-vector$a::export/resizable-tp
                       'lem-vector$a::export/fixed-tp)
                  ,@fi-bindings-post-export))))

         (defthm ,exportp-of-export
           (,exportp (,export ,vector))
           :hints
           (("Goal"
             :by (:functional-instance
                  ,(if resizable
                       'lem-vector$a::exportp/resizable-of-export/resizable
                       'lem-vector$a::exportp/fixed-of-export/fixed)
                  ,@fi-bindings-post-export))))

         ;; `IMPORT-REC'
         (defun ,import-rec (list ,index ,vector)
           (declare (xargs :stobjs ,vector
                           :guard (and (,exportp-rec list)
                                       (natp ,index)
                                       (<= (+ (len list) ,index) ,(if resizable
                                                                      `(,length ,vector)
                                                                      default-length-name)))
                           :guard-hints
                           (("Goal"
                             :in-theory (enable ,vector$a-theorems)))))
           (if (consp list)
               ,(if element-import
                    `(stobj-let ((,element (,accessor ,index ,vector) ,updater))
                                (,element)
                                (,element-import (car list) ,element)
                       (,import-rec (cdr list)
                                    (1+ (mbe :logic (nfix ,index)
                                             :exec ,index))
                                    ,vector))
                    `(let ((,vector (,updater ,index (car list) ,vector)))
                       (,import-rec (cdr list)
                                    (1+ (mbe :logic (nfix ,index)
                                             :exec ,index))
                                    ,vector)))
               (,the-vector ,vector)))

         ;; `IMPORT'
         (defun ,import (export ,vector)
           (declare (xargs :stobjs ,vector
                           :guard (,exportp export)
                           :guard-hints
                           (("Goal"
                             :in-theory (enable ,vector$a-theorems)))))
           (if (mbt (,exportp export))
               (let* ((list (cdr export))
                      ,@(and resizable
                             `((,vector (,resizer (len list) ,vector))))
                      (,vector (,import-rec list 0 ,vector)))
                 ,vector)
               (let ((,vector (,creator)))
                 ,vector)))

         (defthm ,import-tp
           (true-listp (,import export ,vector))
           :rule-classes :type-prescription
           :hints
           (("Goal"
             :do-not-induct t
             :by (:functional-instance
                  ,(if resizable
                       'lem-vector$a::import/resizable-tp
                       'lem-vector$a::import/fixed-tp)
                  ,@fi-bindings-post-import))
            ,@(and resizable
                   `(("Subgoal 3"
                      :in-theory (enable ,vector$a-constraints))))
            ("Subgoal 2"
             :in-theory (enable ,vector$a-aggressive)
             :expand (,import-rec lem-vector$a::list
                                  lem-vector$a::index
                                  lem-vector$a::vector))
            ("Subgoal 1"
             :in-theory (enable ,vector$a-constraints))))

         (defthm ,recognizer$a-of-import
           (,recognizer$a (,import export ,vector))
           :hints
           (("Goal"
             :by (:functional-instance
                  ,(if resizable
                       'lem-vector$a::recognizer/resizable-of-import/resizable
                       'lem-vector$a::recognizer/fixed-of-import/fixed)
                  ,@fi-bindings-post-import))))

         ,@(and coupledp
                `((defthm ,coupledp-of-import
                    (,coupledp (,import export ,vector))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if resizable
                                'lem-vector$a::coupledp/resizable-of-import/resizable
                                'lem-vector$a::coupledp/fixed-of-import/fixed)
                           ,@fi-bindings-post-import))))))

         (defthm ,import-when-not-exportp
           (implies (not (,exportp export))
                    (equal (,import export ,vector)
                           (,creator$a)))
           :hints
           (("Goal"
             :by (:functional-instance
                  ,(if resizable
                       'lem-vector$a::import/resizable-when-not-exportp/resizable
                       'lem-vector$a::import/fixed-when-not-exportp/fixed)
                  ,@fi-bindings-post-import))))

         (defthm ,import-ignores-2
           (equal (,import export ,vector)
                  (,import export (,creator$a)))
           :rule-classes
           ((:rewrite :corollary
                      (implies (syntaxp (not (and (consp ,vector)
                                                  (eq (car ,vector) ',creator$a))))
                               (equal (,import export ,vector)
                                      (,import export (,creator$a))))))
           :hints
           (("Goal"
             :by (:functional-instance
                  ,(if resizable
                       'lem-vector$a::import/resizable-ignores-2
                       'lem-vector$a::import/fixed-ignores-2)
                  ,@fi-bindings-post-import))))

         ,@(and resizable
                `((defthm ,length$a-of-import
                    (equal (,length$a (,import export ,vector))
                           (if (,exportp export)
                               (1- (len export))
                               ,default-length-name))
                    :rule-classes
                    ((:rewrite :corollary
                               (equal (,length$a (,import export ,vector))
                                      (if (,exportp export)
                                          (1- (len (double-rewrite export)))
                                          ,default-length-name))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-vector$a::length/resizable-of-import/resizable
                           ,@fi-bindings-post-import))))))

         (defthm ,accessor$a-of-import
           (equal (,accessor$a ,index (,import export ,vector))
                  (if (and (,exportp export)
                           ,(if resizable
                                `(< (1+ (nfix ,index)) (len export))
                                `(< (nfix ,index) ,default-length-name)))
                      ,@(cond
                          (element-import
                           `((,element-import (nth (1+ (nfix ,index)) export)
                                              (,element-creator))
                             (,element-creator)))
                          (element-fixer
                           `((,element-fixer (nth (1+ (nfix ,index)) export))
                             ,initial-element-name))
                          (t
                           `((nth (1+ (nfix ,index)) export)
                             ,initial-element-name)))))
           :rule-classes
           ((:rewrite :corollary
                      (equal (,accessor$a ,index (,import export vector))
                             (if (and (,exportp export)
                                      ,(if resizable
                                           `(< (1+ (nfix ,index)) (len (double-rewrite export)))
                                           `(< (nfix ,index) ,default-length-name)))
                                 ,@(cond
                                     (element-import
                                      `((,element-import (nth (1+ (nfix ,index)) (double-rewrite export))
                                                         (,element-creator))
                                        (,element-creator)))
                                     (element-fixer
                                      `((,element-fixer (nth (1+ (nfix ,index)) (double-rewrite export)))
                                        ,initial-element-name))
                                     (t
                                      `((nth (1+ (nfix ,index)) (double-rewrite export))
                                        ,initial-element-name)))))))
           :hints
           (("Goal"
             :by (:functional-instance
                  ,(if resizable
                       'lem-vector$a::accessor/resizable-of-import/resizable
                       'lem-vector$a::accessor/fixed-of-import/fixed)
                  ,@fi-bindings-post-import))))

         ;; Composition Theorems
         (defthm ,export-of-import
           (implies (,exportp export)
                    (equal (,export (,import export ,vector))
                           export))
           :hints
           (("Goal"
             :by (:functional-instance
                  ,(if resizable
                       'lem-vector$a::export/resizable-of-import/resizable
                       'lem-vector$a::export/fixed-of-import/fixed)
                  ,@fi-bindings-post-import))))

         (defthm ,import-of-export
           ;; TODO: Remove hypothesis and rewrite to copy of `%VECTOR'
           ,(if coupledp
                `(implies (,coupledp ,%vector)
                          (equal (,import (,export ,%vector) ,vector)
                                 (,fixer$a ,%vector)))
                `(equal (,import (,export ,%vector) ,vector)
                        (,fixer$a ,%vector)))
           :rule-classes
           ((:rewrite :corollary
                      ,(if coupledp
                           `(implies (,coupledp ,%vector)
                                     (equal (,import (,export ,%vector) ,vector)
                                            (,fixer$a (double-rewrite ,%vector))))
                           `(equal (,import (,export ,%vector) ,vector)
                                   (,fixer$a (double-rewrite ,%vector))))))
           :hints
           (("Goal"
             :by (:functional-instance
                  ,(if resizable
                       'lem-vector$a::import/resizable-of-export/resizable
                       'lem-vector$a::import/fixed-of-export/fixed)
                  ,@fi-bindings-post-import)))))

       (deflabel ,export-end)

       (table export ',vector ',(list exportp
                                      export
                                      import))

       (deftheory-static ,export-theory
         (set-difference-theories
          (set-difference-theories (current-theory ',export-end)
                                   (current-theory ',export-begin))
          '(,@(and element-recognizer
                   `(,exportp-rec))
            ,exportp
            ,export-acc
            ,export
            ,import-rec
            ,import)))

       (in-theory
         (union-theories (current-theory ',export-begin)
                         (theory ',export-theory))))))


;;;; `MAKE-HASH-TABLE-EXPORT-EVENTS'
#|(defun make-hash-table-export-events (hash-table package-witness state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp hash-table)
                              (package-witness-p package-witness))
                  :verify-guards nil))
  (let* ()

    `(progn
       (deflabel ,export-begin)

       (encapsulate ()

         (local
           (deflabel prologue-begin))

         (local
           (deflabel prologue-end))

         (local
           (include-book "projects/atomic-stobjs/lemmas/hash-table-a" :dir :system))

         (local
           (table acl2::theory-invariant-table nil nil :clear))

         (local
           (in-theory
             (union-theories
              (union-theories (theory 'acl2::ground-zero))
              (set-difference-theories (current-theory 'prologue-end)
                                       (current-theory 'prologue-begin)))))

         ;; `EXPORTP-REC'
         ,@(and (or key-recognizer
                    val-recognizer)
                `((defun ,exportp-rec (map)
                    (declare (xargs :guard t))
                    (if (consp map)
                        (and (consp (car map))
                             ,@(and key-recognizer
                                    `((,key-recognizer (caar map))))
                             ,@(cond
                                 (val-export-p
                                  `((,val-export-p (cdar map))))
                                 (val-recognizer
                                  `((,val-recognizer (cdar map)))))
                             (or (null (cdr map))
                                 (and (consp (cdr map))
                                      (consp (cadr map))
                                      (<< (caar map) (caadr map))
                                      (exportp-rec (cdr map)))))
                        (null map)))))

         ;; `EXPORTP'
         (defun ,exportp (export)
           (declare (xargs :guard t))
           (and (consp export)
                (equal (car export) ',hash-table)
                ;; TODO: `EXPORTP-REC' defaults to `OMAP::MAPP'
                (,exportp-rec (cdr export))))

         (defthm ,exportp-tp
           (booleanp (,exportp export))
           :rule-classes :type-prescription
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::exportp-tp
                  ,@fi-bindings))))

         (defthm ,exportp-cr
           (implies (,exportp export)
                    (and (consp export)
                         (true-listp export)))
           :rule-classes :compound-recognizer
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::exportp-cr
                  ,@fi-bindings))))

         ;; `EXPORT-ACC'
         (defun ,export-acc (set acc ,hash-table)
           (declare (xargs :stobjs ,hash-table
                           :guard (and (,keysp set)
                                       (,exportp-rec acc))))
           (if (mbe :logic (or (set::emptyp set)
                               (not (keysp set)))
                    :exec (endp set))
               (mbe :logic (omap::mfix acc)
                    :exec acc)
               ,(if val-export
                    `(let ((,key (set::head set)))
                       (stobj-let ((,val (,accessor ,key ,hash-table) ,updater))
                                  (export)
                                  (,val-export ,val)
                         (,export-acc (set::tail set) (omap::update ,key export acc) ,hash-table)))
                    `(let* ((,key (set::head set))
                            (,val (,accessor ,key ,hash-table)))
                       (,export-acc (set::tail set) (omap::update ,key ,val acc) ,hash-table)))))

         ;; `EXPORT'
         (defun ,export (,hash-table)
           (declare (xargs :stobjs ,hash-table))
           (cons ',hash-table
                 (,export-acc (,keys ,hash-table) () ',hash-table)))

         (defthm ,export-tp
           (and (consp (,export ,hash-table))
                (true-listp (,export ,hash-table)))
           :rule-classes :type-prescription
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::export-tp
                  ,@fi-bindings))))

         (defthm ,exportp-of-export
           (,exportp (,export ,hash-table))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::exportp-of-export
                  ,@fi-bindings))))

         ;; `IMPORT-REC'
         (defun ,import-rec (map ,index ,hash-table)
           (declare (xargs :stobjs ,hash-table
                           :guard (,exportp-rec map)))
           (if (mbe :logic (or (omap::emptyp map)
                               (not (exportp-rec map)))
                    :exec (endp map))
               (,the-hash-table ,hash-table)
               (mv-let (,key ,val-export)
                       (omap::head map)
                 ,(if val-import
                      `(stobj-let ((,val (,accessor ,key ,hash-table) ,updater))
                                  (,val)
                                  (,val-import ,val-export ,val)
                         (,import-rec (omap::tail map) ,hash-table))
                      `(let ((,hash-table (,updater ,key ,val-export ,hash-table)))
                         (,import-rec (omap::tail map) ,hash-table))))))

         ;; `IMPORT'
         (defun ,import (export ,hash-table)
           (declare (xargs :stobjs ,hash-table
                           :guard (,exportp export)))
           (if (mbt (,exportp export))
               (let* ((map (cdr export))
                      (count (omap::size map))
                      (,hash-table (,init count nil nil ,hash-table))
                      (,hash-table (,import-rec map ,hash-table))
                      (,hash-table (,keys-set (omap::keys map) ,hash-table)))
                 ,hash-table)
               (let ((,hash-table (,creator)))
                 ,hash-table)))

         (defthm ,import-tp
           (and (consp (,import export ,hash-table))
                (true-listp (,import export ,hash-table)))
           :rule-classes :type-prescription
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::import-tp
                  ,@fi-bindings))))

         (defthm ,recognizer$a-of-import
           (,recognizer$a (,import export ,hash-table))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::recognizer/copyable-of-import
                  ,@fi-bindings))))

         (defthm ,coupledp-of-import
           (,coupledp (,import export ,hash-table))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::coupledp-of-import
                  ,@fi-bindings))))

         (defthm ,import-when-not-exportp
           (implies (not (,exportp export))
                    (equal (,import export ,hash-table)
                           (,creator$a)))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::import-when-not-exportp
                  ,@fi-bindings))))

         (defthm ,import-ignores-2
           (equal (,import export ,hash-table)
                  (,import export (,creator$a)))
           :rule-classes
           ((:rewrite :corollary
                      (implies (syntaxp (not (and (consp ,hash-table)
                                                  (eq (car ,hash-table) ',creator$a))))
                               (equal (,import export ,hash-table)
                                      (,import export (,creator$a))))))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::import-ignores-2
                  ,@fi-bindings))))

         (defthm ,keys$a-of-import
           (equal (,keys$a (,import export ,hash-table))
                  (and (,exportp export)
                       (omap::,keys$a (cdr export))))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::keys-of-import
                  ,@fi-bindings))))

         (defthm ,boundp$a-of-import
           (equal (,boundp$a ,key (,import export ,hash-table))
                  (and (omap::assoc ,(if key-fixer `(,key-fixer ,key) key)
                                    (cdr export))
                       (,exportp export)))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::boundp/copyable-of-import
                  ,@fi-bindings))))

         (defthm ,accessor$a-of-import
           (equal (,accessor$a ,key (,import export ,hash-table))
                  (let ((pair (omap::assoc ,(if key-fixer `(,key-fixer ,key) key)
                                           (cdr export))))
                    ,(if val-import
                         `(if (and (,exportp export)
                                   pair)
                              (,val-import (cdr pair) (,val-creator))
                              (,val-creator))
                         `(if (and (,exportp export)
                                   pair)
                              (cdr pair)
                              ,default-val-name))))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::accessor/copyable-of-import
                  ,@fi-bindings))))

         (defthm ,count$a-of-import
           (equal (,count$a (,import export ,hash-table))
                  (if (,exportp export)
                      (omap::size (cdr export))
                      0))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::count/copyable-of-import
                  ,@fi-bindings))))

         ;; Composition Theorems
         (defthm ,export-of-import
           (implies (,exportp export)
                    (equal (,export (,import export ,hash-table))
                           export))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::export-of-import
                  ,@fi-bindings))))

         (defthm ,import-of-export
           ;; TODO: Remove hypothesis and rewrite to copy of `%HASH-TABLE'
           ,(if coupledp
                `(implies (,coupledp ,%hash-table)
                          (equal (,import (,export ,%hash-table) ,hash-table)
                                 (,fixer$a ,%hash-table)))
                `(equal (,import (,export ,%hash-table) ,hash-table)
                        (,fixer$a ,%hash-table)))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::import-of-export
                  ,@fi-bindings)))))

       (deflabel ,export-end)

       (table export ',hash-table ',(list exportp-rec
                                          exportp
                                          export-acc
                                          export
                                          import-rec
                                          import))

       (deftheory-static ,export-theory
         (set-difference-theories
          (set-different-theories (current-theory ',export-end)
                                  (current-theory ',export-begin))
          '(,@(and (or key-recognizer
                       val-recognizer)
                   `(,exportp-rec))
            ,exportp
            ,export-acc
            ,export
            ,import-rec
            ,import)))

       (in-theory
         (union-theories (current-theory ',export-begin)
                         (theory ',export-theory))))))|#


;;;; `MAKE-FRAME-EXPORT-EVENTS'
#|(defun make-frame-export-events (frame package-witness state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp hash-table)
                              (package-witness-p package-witness))
                  :verify-guards nil))
  (let* ()

    `(progn
       (deflabel ,export-begin)

       (encapsulate ()

         (local
           (deflabel prologue-begin))

         (local
           (deflabel prologue-end))

         (local
           (table acl2::theory-invariant-table nil nil :clear))

         (local
           (in-theory
             (union-theories
              (union-theories (theory 'acl2::ground-zero)
                              (theory ',frame$a-theorems))
              (set-difference-theories (current-theory 'prologue-end)
                                       (current-theory 'prologue-begin)))))

         ;; `EXPORTP'
         (defun ,exportp (export)
           (declare (xargs :guard t))
           (and (consp export)
                (equal (car export) ',frame)
                (true-listp export)
                (= (len export) ,(1+ (* 2 (len fields))))
                ,@(loop$ :for field :in fields
                        :as recognizer :in recognizers
                        :as field-export-p :in field-export-p-list
                        :as i :from 1 :to (len fields)
                        :append `((eq ,(intern (symbol-name field) "KEYWORD")
                                      (nth ,(1- (* 2 i)) export))
                                  (,(or field-export-p recognizer)
                                    (nth ,(* 2 i) export))))))

         (defthm ,exportp-tp
           (booleanp (,exportp export))
           :rule-classes :type-prescription)

         (defthm ,exportp-cr
           (implies (,exportp export)
                    (and (consp export)
                         (true-listp export)))
           :rule-classes :compound-recognizer)

         ;; `EXPORT'
         (defun ,export (,frame)
           (declare (xargs :stobjs ,frame))
           (list ',frame
                 ,@(loop$ :for field :in fields
                         :as accessor :in accessors
                         :append `(,(intern (symbol-name field) "KEYWORD")
                                    (,accessor ,frame)))))

         (defthm ,export-tp
           (and (consp (,export ,frame))
                (true-listp (,export ,frame)))
           :rule-classes :type-prescription)

         (defthm ,exportp-of-export
           (,exportp (,export ,frame)))

         ;; `IMPORT'
         (defun ,import (export ,frame)
           (declare (xargs :stobj ,frame
                           :guard (,exportp export)))
           (if (mbt (,exportp export))
               ;; HERE
               ,(loop$ :with body := `(,the-frame ,frame)
                      :do
                      (progn
                        )
                      #|do-loop that sets every field in frame from the export|#
                      )
               (let ((,frame (,creator)))
                 ,frame)))

         (defthm ,import-tp
           ,(if (consp fields)
                `(and (consp (,import export ,frame))
                      (true-listp (,import export ,frame)))
                `(null (,import export ,frame)))
           :rule-classes :type-prescription)

         (defthm ,recognizer$a-of-import
           (,recognizer$a (,import export ,frame)))

         (defthm ,coupledp-of-import
           (,coupledp (,import export ,frame)))

         (defthm ,import-when-not-exportp
           (implies (not (,exportp export))
                    (equal (,import export ,frame)
                           (,creator$a))))

         (defthm ,import-ignores-2
           (equal (,import export ,frame)
                  (,import export (,creator$a)))
           :rule-classes
           ((:rewrite :corollary
                      (implies (syntaxp (not (and (consp ,frame)
                                                  (eq (car ,frame) ',creator$a))))
                               (equal (,import export ,frame)
                                      (,import export (,creator$a)))))))

         ,@(loop$ :for field :in fields
                 :as field-creator$a :in field-creators$a
                 :as i :from 1 :to (len fields)
                 :as initial-element-name :in initial-element-names
                 :collect `(defthm ,(symbolicate package-witness accessor$a "-OF-" import)
                             (equal (,accessor$a (,import export ,frame))
                                    ,(if field-import
                                         `(if (,exportp export)
                                              (,field-import (nth ,(* 2 i) export)
                                                             (,field-creator$a))
                                              (,field-creator$a))
                                         `(if (,exportp export)
                                              (nth ,(* 2 i) export)
                                              ,initial-element-name)))
                             :rule-classes
                             ((:rewrite :corollary
                                        (equal (,accessor$a (,import export ,frame))
                                               ,(if field-import
                                                    `(if (,exportp export)
                                                         (,field-import (nth ,(* 2 i) (double-rewrite export))
                                                                        (,field-creator$a))
                                                         (,field-creator$a))
                                                    `(if (,exportp export)
                                                         (nth ,(* 2 i) (double-rewrite export))
                                                         ,initial-element-name)))))))

         ;; Composition Theorems
         (defthm ,export-of-import
           (implies (,exportp export)
                    (equal (,export (,import export ,frame))
                           export)))

         (defthm ,import-of-export
           ;; TODO: Remove hypothesis and rewrite to copy of `%FRAME'
           ,(if coupledp
                `(implies (,coupledp ,%frame)
                          (equal (,import (,export ,%frame) ,frame)
                                 (,fixer$a ,%frame)))
                `(equal (,import (,export ,%frame) ,frame)
                        (,fixer$a ,%frame)))))

       (deflabel ,export-end)

       (table export ',frame ',(list exportp
                                     export
                                     import))

       (deftheory-static ,export-theory
         (set-difference-theories
          (set-different-theories (current-theory ',export-end)
                                  (current-theory ',export-begin))
          '(,exportp
            ,export
            ,import)))

       (in-theory
         (union-theories (current-theory ',export-begin)
                         (theory ',export-theory))))))|#


;;;; `DEFINE-EXPORT'
(defmacro define-export (stobj &key
                                 (debug 't)
                                 (package-witness 'nil package-witness-supplied-p))
  (declare (xargs :guard (and (symbolp stobj)
                              (booleanp debug)
                              (package-witness-p package-witness))))
  `(with-output
     ,@(and (not debug)
            *constructor-output*)

     (make-event
       (let* ((stobj ',stobj)
              (world (w state))
              (package-witness-lookup (cdr (assoc stobj (table-alist 'package-witness world))))
              (package-witness (cond
                                 (',package-witness-supplied-p
                                  ',package-witness)
                                 (package-witness-lookup)
                                 (t
                                  (current-package state))))
              (stobj$a-property (cdr (assoc stobj (table-alist 'stobj$a-property world)))))
         (cond
           ((and (= (len stobj$a-property) 3)
                 (= (len (third stobj$a-property)) 3))
            (make-vector-export-events stobj package-witness state))
           #|((and (= (len stobj$a-property) 3)
                 (= (len (third stobj$a-property)) 5))
            (make-hash-table-export-events stobj package-witness state))|#
           #|((and (= (len stobj$a-property) 3)
                 (= (len (third stobj$a-property)) 9))
            (make-frame-export-events stobj package-witness state))|#)))))
