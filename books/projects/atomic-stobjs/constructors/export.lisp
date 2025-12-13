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

(include-book "std/omaps/core" :dir :system)

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
                `(lem-vector$a::element-equiv ,element-equiv)
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

         ,@(and element-recognizer
                `((local
                    (in-theory
                      (disable ,element-recognizer)))))

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
(defun make-hash-table-export-events (hash-table package-witness state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp hash-table)
                              (package-witness-p package-witness))
                  :verify-guards nil))
  (let* ((%hash-table (symbolicate package-witness "%" hash-table))

         (export (symbolicate package-witness hash-table "-EXPORT"))
         (export-begin (symbolicate package-witness export "-BEGIN"))
         (export-end (symbolicate package-witness export "-END"))
         (export-theory (symbolicate package-witness export "-THEORY"))
         (exportp (symbolicate package-witness export (make-predicate-suffix export)))
         (exportp-rec (symbolicate package-witness exportp "-REC"))
         (export-acc (symbolicate package-witness export "-ACC"))
         (import (symbolicate package-witness hash-table "-IMPORT"))
         (import-rec (symbolicate package-witness import "-REC"))

         (stobj-property (getpropc hash-table 'acl2::stobj))
         (creator (cdadr stobj-property))
         (the-hash-table (symbolicate hash-table "THE-" hash-table))
         (accessor (second (third stobj-property)))
         (updater (third (third stobj-property)))
         (init (ninth (third stobj-property)))
         (keys (tenth (third stobj-property)))
         (keys-set (nth 10 (third stobj-property)))

         (world (w state))
         (coupledp (cdr (assoc hash-table (table-alist 'coupledp world))))
         (coupled-keys-p (symbolicate coupledp hash-table "-COUPLED-KEYS-P"))
         (coupled-keys-p-witness (symbolicate coupledp coupled-keys-p "-WITNESS"))
         (coupled-vals-p (symbolicate coupledp hash-table "-COUPLED-VALS-P"))
         (coupledp-constraints (symbolicate coupledp coupledp "-CONSTRAINTS"))

         (copy (cdr (assoc hash-table (table-alist 'copy world))))
         (copy-theory (symbolicate copy copy "-THEORY"))

         (stobj$a-property (cdr (assoc hash-table (table-alist 'stobj$a-property world))))
         (hash-table$a (first stobj$a-property))
         (hash-table$a-theorems (symbolicate hash-table$a hash-table$a "-THEOREMS"))
         (hash-table$a-constraints (symbolicate hash-table$a hash-table$a "-CONSTRAINTS"))
         (recognizer$a (first (second stobj$a-property)))
         (creator$a (second (second stobj$a-property)))
         (fixer$a (third (second stobj$a-property)))
         (accessor$a (first (fourth (third stobj$a-property))))
         (updater$a (second (fourth (third stobj$a-property))))
         (boundp$a (third (fourth (third stobj$a-property))))
         (count$a (sixth (fourth (third stobj$a-property))))
         (init$a (eighth (fourth (third stobj$a-property))))
         (keys$a (first (fifth (third stobj$a-property))))
         (keys$a-set (second (fifth (third stobj$a-property))))
         (keys$ap (third (fifth (third stobj$a-property))))
         (keys$a-fix (fourth (fifth (third stobj$a-property))))

         (contents$a (symbolicate hash-table$a hash-table$a "-CONTENTS"))
         (contents-recognizer$a (symbolicate hash-table$a contents$a "-P"))
         (contents-fixer$a (symbolicate hash-table$a contents$a "-FIX"))
         (contents-accessor$a (symbolicate hash-table$a contents$a "-GET"))
         (contents-updater$a (symbolicate hash-table$a contents$a "-PUT"))
         (contents-boundp$a (symbolicate hash-table$a contents$a "-BNDP"))
         (contents-count$a (symbolicate hash-table$a contents$a "-CNT"))

         (key (first (first (third stobj$a-property))))
         (%key (symbolicate key "%" key))
         (key-recognizer (second (first (third stobj$a-property))))
         (default-key-name (third (first (third stobj$a-property))))
         (key-fixer (fourth (first (third stobj$a-property))))
         (key-equiv (fifth (first (third stobj$a-property))))

         (val (first (second (third stobj$a-property))))
         (%val (symbolicate val "%" val))
         (val-stobj-property (getpropc val 'acl2::stobj))
         (val-stobj$a-property (cdr (assoc val (table-alist 'stobj$a-property world))))
         (val-recognizer (second (second (third stobj$a-property))))
         (default-val-name (third (second (third stobj$a-property))))
         (val-creator (second (second val-stobj$a-property)))
         (default-val (if val-stobj-property
                          `(,val-creator)
                          default-val-name))
         (val-fixer (fourth (second (third stobj$a-property))))
         (val-equiv (fifth (second (third stobj$a-property))))
         (exportp-rec (if (or key-recognizer
                              val-recognizer)
                          exportp-rec
                          'omap::mapp))

         (val-coupled-p (cdr (assoc val (table-alist 'coupledp world))))
         (val-export-list (cdr (assoc val (table-alist 'export world))))
         (val-export-p (first val-export-list))
         (val-export (second val-export-list))
         (val-import (third val-export-list))

         ;; Theorem Names
         (key-recognizer-constraints (symbolicate "ATOMIC-STOBJS" key-recognizer "-CONSTRAINTS"))
         (key-fixer-constraints (symbolicate "ATOMIC-STOBJS" key-fixer "-CONSTRAINTS"))
         (key-equiv-constraints (symbolicate "ATOMIC-STOBJS" key-equiv "-CONSTRAINTS"))

         (val-recognizer-constraints (symbolicate "ATOMIC-STOBJS" val-recognizer "-CONSTRAINTS"))
         (val-fixer-constraints (symbolicate "ATOMIC-STOBJS" val-fixer "-CONSTRAINTS"))
         (val-equiv-constraints (symbolicate "ATOMIC-STOBJS" val-equiv "-CONSTRAINTS"))

         (exportp-tp (symbolicate package-witness exportp "-TP"))
         (exportp-cr (symbolicate package-witness exportp "-CR"))
         (mapp-when-exportp-rec (symbolicate "ATOMIC-STOBJS" "MAPP-WHEN-" exportp-rec))
         (key-recognizer-head-when-exportp-rec (symbolicate "ATOMIC-STOBJS" key-recognizer "-HEAD-WHEN-" exportp-rec))
         (val-export-p-head-when-exportp-rec (symbolicate "ATOMIC-STOBJS"
                                                          (or val-export-p
                                                              val-recognizer)
                                                          "-HEAD-WHEN-"
                                                          exportp-rec))
         (exportp-rec-of-tail (symbolicate "ATOMIC-STOBJS" exportp-rec "-OF-TAIL"))
         (exportp-rec-of-update (symbolicate "ATOMIC-STOBJS" exportp-rec "-OF-UPDATE"))
         (keysp-of-keys-when-exportp-rec (symbolicate "ATOMIC-STOBJS" keys$ap "-OF-KEYS-WHEN-" exportp-rec))

         (export-tp (symbolicate package-witness export "-TP"))
         (exportp-of-export (symbolicate package-witness exportp "-OF-" export))

         (import-tp (symbolicate package-witness import "-TP"))
         (recognizer$a-of-import (symbolicate package-witness recognizer$a "-OF-" import))
         (coupledp-of-import (symbolicate package-witness coupledp "-OF-" import))
         (import-when-not-exportp (symbolicate package-witness import "-WHEN-NOT-" exportp))
         (import-ignores-2 (symbolicate package-witness import "-IGNORES-2"))
         (keys$a-of-import (symbolicate package-witness keys$a "-OF-" import))
         (boundp$a-of-import (symbolicate package-witness boundp$a "-OF-" import))
         (accessor$a-of-import (symbolicate package-witness accessor$a "-OF-" import))
         (count$a-of-import (symbolicate package-witness count$a "-OF-" import))

         (export-of-import (symbolicate package-witness export "-OF-" import))
         (import-of-export (symbolicate package-witness import "-OF-" export))

         (fi-bindings
          (list `(lem-hash-table$a::key-recognizer ,(or key-recognizer
                                                        `(lambda (key)
                                                           t)))
                `(lem-hash-table$a::key-fixer ,(or key-fixer
                                                   'identity))
                `(lem-hash-table$a::default-key (lambda ()
                                                  ,default-key-name))

                `(lem-hash-table$a::val-recognizer ,(or val-recognizer
                                                        `(lambda (val)
                                                           t)))
                `(lem-hash-table$a::val-fixer ,(or val-fixer
                                                   'identity))
                `(lem-hash-table$a::val-equiv ,val-equiv)
                `(lem-hash-table$a::default-val ,(if val-stobj$a-property
                                                     `(,val-creator)
                                                     `(lambda ()
                                                        ,default-val-name)))

                `(lem-hash-table$a::val-coupled-p ,(or val-coupled-p
                                                       `(lambda (val)
                                                          t)))
                `(lem-hash-table$a::val-export-p ,(or val-export-p
                                                      val-recognizer
                                                      `(lambda ()
                                                         t)))
                `(lem-hash-table$a::val-export ,(or val-export
                                                    val-fixer
                                                    'identity))
                `(lem-hash-table$a::val-import ,(or val-import
                                                    `(lambda (export val)
                                                       (,val-fixer export))
                                                    `(lambda (export val)
                                                       export)))

                `(lem-hash-table$a::keysp ,keys$ap)

                `(lem-hash-table$a::name (lambda ()
                                           ',hash-table))
                `(lem-hash-table$a::exportp-rec ,exportp-rec)
                `(lem-hash-table$a::exportp ,exportp)))

         (fi-bindings-post-export
          (list* `(lem-hash-table$a::export-acc ,export-acc)
                 `(lem-hash-table$a::export ,export)

                 `(lem-hash-table$a::recognizer/copyable ,recognizer$a)
                 `(lem-hash-table$a::creator/copyable ,creator$a)
                 `(lem-hash-table$a::fixer/copyable ,fixer$a)
                 `(lem-hash-table$a::accessor/copyable ,accessor$a)
                 `(lem-hash-table$a::keys ,keys$a)

                 `(lem-hash-table$a::recognizer/unique ,contents-recognizer$a)
                 `(lem-hash-table$a::fixer/unique ,contents-fixer$a)
                 `(lem-hash-table$a::accessor/unique ,contents-accessor$a)

                 fi-bindings))

         (fi-bindings-post-import
          (list* `(lem-hash-table$a::coupledp ,coupledp)
                 `(lem-hash-table$a::coupled-keys-p ,coupled-keys-p)
                 `(lem-hash-table$a::coupled-keys-p-witness ,coupled-keys-p-witness)
                 `(lem-hash-table$a::coupled-vals-p ,(if val-coupled-p
                                                         coupled-vals-p
                                                         `(lambda (x)
                                                            t)))

                 `(lem-hash-table$a::import-rec ,import-rec)
                 `(lem-hash-table$a::import ,import)

                 `(lem-hash-table$a::keys-set ,keys$a-set)
                 `(lem-hash-table$a::keys-fix ,keys$a-fix)
                 `(lem-hash-table$a::updater/copyable ,updater$a)
                 `(lem-hash-table$a::updater/unique ,contents-updater$a)
                 `(lem-hash-table$a::boundp/copyable ,boundp$a)
                 `(lem-hash-table$a::boundp/unique ,contents-boundp$a)
                 `(lem-hash-table$a::count/copyable ,count$a)
                 `(lem-hash-table$a::count/unique ,contents-count$a)
                 `(lem-hash-table$a::init/copyable ,init$a)

                 fi-bindings-post-export)))

    `(progn
       (deflabel ,export-begin)

       (encapsulate ()

         (local
           (deflabel prologue-begin))

         ,@(and key-fixer
                key-recognizer
                (not (eq key-equiv 'equal))
                `((local
                    (defthm ,key-recognizer-constraints
                      (and (booleanp (,key-recognizer ,key))
                           (,key-recognizer ,default-key-name))
                      :rule-classes
                      ((:rewrite :corollary
                                 (booleanp (,key-recognizer ,key))))))

                  (local
                    (defthm ,key-fixer-constraints
                      (equal (,key-fixer ,key)
                             (if (,key-recognizer ,key)
                                 ,key
                                 ,default-key-name))))

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
                                 (booleanp (,val-recognizer ,val)))
                       ,@(and (not (equal default-val default-val-name))
                              `((:rewrite :corollary
                                          (,val-recognizer ,default-val)))))))

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
           (deflabel prologue-end))

         (local
           (include-book "projects/atomic-stobjs/lemmas/hash-table-a" :dir :system))

         (local
           (table acl2::theory-invariant-table nil nil :clear))

         (local
           (in-theory
             (union-theories (theory 'acl2::ground-zero)
                             (set-difference-theories (current-theory 'prologue-end)
                                                      (current-theory 'prologue-begin)))))

         ,@(and key-recognizer
                `((local
                    (in-theory
                      (disable ,key-recognizer)))))

         ,@(and (not val-stobj-property)
                `((local
                    (in-theory
                      (disable ,val-recognizer)))))

         (local
           (in-theory
             (e/d ((:e set::emptyp)
                   set::never-in-empty
                   set::setp-type
                   set::sets-are-true-lists-compound-recognizer
                   (:e omap::emptyp)
                   omap::mfix-when-mapp
                   omap::mapp-non-nil-implies-not-emptyp
                   (:e set::cardinality))
                  (mv-nth))))

         ,@(and key-recognizer
                `((local
                    (in-theory
                      (enable (:e ,key-recognizer))))))

         ,@(and val-recognizer
                `((local
                    (in-theory
                      (enable (:e ,val-recognizer))))))

         ,@(and val-stobj-property
                `((local
                    (in-theory
                      (enable ,@(strip-cars (cdr (getpropc val 'acl2::absstobj-info))))))))

         (local
           (in-theory
             (enable ,@(strip-cars (cdr (getpropc hash-table 'acl2::absstobj-info))))))

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
                                      (,exportp-rec (cdr map)))))
                        (null map)))))

         ;; `EXPORTP'
         (defun ,exportp (export)
           (declare (xargs :guard t))
           (and (consp export)
                (equal (car export) ',hash-table)
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

         (local
           (defthm ,mapp-when-exportp-rec
             (implies (,exportp-rec map)
                      (omap::mapp map))
             :hints
             (("Goal"
               :by (:functional-instance
                    lem-hash-table$a::mapp-when-exportp-rec
                    ,@fi-bindings)))))

         ,@(and key-recognizer
                `((local
                    (defthm ,key-recognizer-head-when-exportp-rec
                      (implies (and (not (omap::emptyp map))
                                    (,exportp-rec map))
                               (,key-recognizer (mv-nth 0 (omap::head map))))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             lem-hash-table$a::key-recognizer-head-when-exportp-rec
                             ,@fi-bindings)))))))

         ,@(and val-recognizer
                `((local
                    (defthm ,val-export-p-head-when-exportp-rec
                      (implies (and (not (omap::emptyp map))
                                    (,exportp-rec map))
                               (,(or val-export-p
                                     val-recognizer)
                                 (mv-nth 1 (omap::head map))))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             lem-hash-table$a::val-export-p-head-when-exportp-rec
                             ,@fi-bindings)))))))

         (local
           (defthm ,exportp-rec-of-tail
             (implies (,exportp-rec map)
                      (,exportp-rec (omap::tail map)))
             :hints
             (("Goal"
               :by (:functional-instance
                    lem-hash-table$a::exportp-rec-of-tail
                    ,@fi-bindings)))))

         (local
           (defthm ,exportp-rec-of-update
             (implies (and (,exportp-rec map)
                           ,@(and key-recognizer
                                  `((,key-recognizer key)))
                           ,@(cond
                               (val-export-p
                                `((,val-export-p val)))
                               (val-recognizer
                                `((,val-recognizer val)))))
                      (,exportp-rec (omap::update key val map)))
             :hints
             (("Goal"
               :by (:functional-instance
                    lem-hash-table$a::exportp-rec-of-update
                    ,@fi-bindings)))))

         ,@(and key-recognizer
                `((local
                    (defthm ,keysp-of-keys-when-exportp-rec
                      (implies (,exportp-rec map)
                               (,keys$ap (omap::keys map)))
                      :hints
                      (("Goal"
                        :do-not-induct t
                        :in-theory (enable ,hash-table$a-constraints)
                        :by (:functional-instance
                             lem-hash-table$a::keysp-of-keys-when-exportp-rec
                             ,@fi-bindings)))))))

         ;; `EXPORT-ACC'
         (defun ,export-acc (set acc ,hash-table)
           (declare (xargs :stobjs ,hash-table
                           :guard (and (,keys$ap set)
                                       (,exportp-rec acc))
                           :guard-hints
                           (("Goal"
                             :in-theory (enable ,hash-table$a-theorems
                                                set::emptyp)))
                           :measure (set::cardinality set)
                           :hints
                           (("Goal"
                             :in-theory (enable set::cardinality)))))
           (if (mbe :logic (or (set::emptyp set)
                               (not (,keys$ap set)))
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
                 (,export-acc (,keys ,hash-table) () ,hash-table)))

         (defthm ,export-tp
           (and (consp (,export ,hash-table))
                (true-listp (,export ,hash-table)))
           :rule-classes :type-prescription
           :hints
           (("Goal"
             :do-not-induct t
             :in-theory (enable ,hash-table$a-constraints)
             :by (:functional-instance
                  lem-hash-table$a::export-tp
                  ,@fi-bindings-post-export))))

         (defthm ,exportp-of-export
           (,exportp (,export ,hash-table))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::exportp-of-export
                  ,@fi-bindings-post-export))))

         ;; `IMPORT-REC'
         (defun ,import-rec (map ,hash-table)
           (declare (xargs :stobjs ,hash-table
                           :guard (,exportp-rec map)
                           :guard-hints
                           (("Goal"
                             :in-theory (enable ,hash-table$a-theorems)))
                           :measure (omap::size map)
                           :hints
                           (("Goal"
                             :in-theory (enable omap::size)))))
           (if (mbe :logic (or (omap::emptyp map)
                               (not (,exportp-rec map)))
                    :exec (endp map))
               (,the-hash-table ,hash-table)
               (mv-let (,key val-export)
                       (omap::head map)
                 ,(if val-import
                      `(stobj-let ((,val (,accessor ,key ,hash-table) ,updater))
                                  (,val)
                                  (,val-import val-export ,val)
                         (,import-rec (omap::tail map) ,hash-table))
                      `(let ((,hash-table (,updater ,key val-export ,hash-table)))
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
             :do-not-induct t
             :in-theory (enable ,hash-table$a-theorems)
             :by (:functional-instance
                  lem-hash-table$a::import-tp
                  ,@fi-bindings-post-import))
            ("Subgoal 4"
             :in-theory (enable ,hash-table$a-constraints))
            ("Subgoal 3"
             :in-theory (enable ,hash-table$a-constraints))
            ("Subgoal 2"
             :in-theory (enable ,hash-table$a-constraints))))

         (defthm ,recognizer$a-of-import
           (,recognizer$a (,import export ,hash-table))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::recognizer/copyable-of-import
                  ,@fi-bindings-post-import))))

         (defthm ,coupledp-of-import
           (,coupledp (,import export ,hash-table))
           :hints
           (("Goal"
             :do-not-induct t
             :in-theory (enable ,copy-theory)
             :by (:functional-instance
                  lem-hash-table$a::coupledp-of-import
                  ,@fi-bindings-post-import))
            ("Subgoal 7"
             :in-theory (enable ,coupledp))
            ("Subgoal 5"
             :in-theory (enable ,coupledp-constraints))
            ("Subgoal 4"
             :in-theory (enable ,hash-table$a-constraints))
            ("Subgoal 3"
             :in-theory (enable ,hash-table$a-constraints))
            ("Subgoal 2"
             :in-theory (enable ,hash-table$a-constraints))
            ("Subgoal 1"
             :in-theory (enable ,hash-table$a-constraints))))

         (defthm ,import-when-not-exportp
           (implies (not (,exportp export))
                    (equal (,import export ,hash-table)
                           (,creator$a)))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::import-when-not-exportp
                  ,@fi-bindings-post-import))))

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
                  ,@fi-bindings-post-import))))

         (defthm ,keys$a-of-import
           (equal (,keys$a (,import export ,hash-table))
                  (and (,exportp export)
                       (omap::keys (cdr export))))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::keys-of-import
                  ,@fi-bindings-post-import))))

         (defthm ,boundp$a-of-import
           (equal (,boundp$a ,key (,import export ,hash-table))
                  (and (omap::assoc ,(if key-fixer `(,key-fixer ,key) key)
                                    (cdr export))
                       (,exportp export)))
           :hints
           (("Goal"
             :do-not-induct t
             :in-theory (enable ,hash-table$a-constraints)
             :by (:functional-instance
                  lem-hash-table$a::boundp/copyable-of-import
                  ,@fi-bindings-post-import))))

         (defthm ,accessor$a-of-import
           (equal (,accessor$a ,key (,import export ,hash-table))
                  (let ((pair (omap::assoc ,(if key-fixer `(,key-fixer ,key) key)
                                           (cdr export))))
                    ,(cond
                       (val-import
                        `(if (and (,exportp export)
                                  pair)
                             (,val-import (cdr pair) (,val-creator))
                             (,val-creator)))
                       (val-fixer
                        `(if (and (,exportp export)
                                  pair)
                             (,val-fixer (cdr pair))
                             ,default-val-name))
                       (t
                        `(if (and (,exportp export)
                                  pair)
                             (cdr pair)
                             ,default-val-name)))))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::accessor/copyable-of-import
                  ,@fi-bindings-post-import))))

         (defthm ,count$a-of-import
           (equal (,count$a (,import export ,hash-table))
                  (if (,exportp export)
                      (omap::size (cdr export))
                      0))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::count/copyable-of-import
                  ,@fi-bindings-post-import))))

         ;; Composition Theorems
         (defthm ,export-of-import
           (implies (,exportp export)
                    (equal (,export (,import export ,hash-table))
                           export))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::export-of-import
                  ,@fi-bindings-post-import))))

         (defthm ,import-of-export
           ;; TODO: Remove hypothesis and rewrite to copy of `%HASH-TABLE'
           (implies (,coupledp ,%hash-table)
                    (equal (,import (,export ,%hash-table) ,hash-table)
                           (,fixer$a ,%hash-table)))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::import-of-export
                  ,@fi-bindings-post-import)))))

       (deflabel ,export-end)

       (table export ',hash-table ',(list exportp
                                          export
                                          import))

       (deftheory-static ,export-theory
         (set-difference-theories
          (set-difference-theories (current-theory ',export-end)
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
                         (theory ',export-theory))))))


;;;; `MAKE-FRAME-EXPORT-EVENTS'
(defun make-frame-export-events (frame package-witness state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp frame)
                              (package-witness-p package-witness))
                  :verify-guards nil))
  (let* ((%frame (symbolicate package-witness "%" frame))

         (export (symbolicate package-witness frame "-EXPORT"))
         (export-begin (symbolicate package-witness export "-BEGIN"))
         (export-end (symbolicate package-witness export "-END"))
         (export-theory (symbolicate package-witness export "-THEORY"))
         (exportp (symbolicate package-witness export (make-predicate-suffix export)))
         (import (symbolicate package-witness frame "-IMPORT"))

         (stobj-property (getpropc frame 'acl2::stobj))
         (creator (cdadr stobj-property))
         (the-frame (symbolicate frame "THE-" frame))

         (world (w state))
         (stobj$a-property (cdr (assoc frame (table-alist 'stobj$a-property world))))
         (frame$a (first stobj$a-property))
         (frame$a-equal (cdr (assoc frame$a (table-alist 'equality world))))
         (%frame$a (car (getpropc frame$a-equal 'acl2::formals)))
         (frame$a-theorems (symbolicate frame$a frame$a "-THEOREMS"))
         (recognizer$a (first (second stobj$a-property)))
         (creator$a (second (second stobj$a-property)))
         (fixer$a (third (second stobj$a-property)))

         (fields (first (third stobj$a-property)))
         (%fields (loop$ :for field :in fields
                        :collect (symbolicate field "%" field)))
         (stobjs (sixth (third stobj$a-property)))
         (stobj-property-list (loop$ :for stobj :in stobjs
                                    :collect (and (symbolp stobj)
                                                  (getprop stobj
                                                           'acl2::stobj
                                                           nil
                                                           'acl2::current-acl2-world
                                                           world))))
         (absstobj-info-list (loop$ :for stobj :in stobjs
                                   :collect (and (symbolp stobj)
                                                 (getprop stobj
                                                          'acl2::absstobj-info
                                                          nil
                                                          'acl2::current-acl2-world
                                                          world))))
         (stobj$a-property-alist (table-alist 'stobj$a-property world))
         (stobj$a-property-list (loop$ :for stobj :in stobjs
                                      :collect (and (symbolp stobj)
                                                    (cdr (assoc stobj stobj$a-property-alist)))))
         (recognizers$a (second (third stobj$a-property)))
         (initial-element-names (third (third stobj$a-property)))
         (creators$a (loop$ :for stobj$a-property :in stobj$a-property-list
                           :collect (and stobj$a-property
                                         (second (second stobj$a-property)))))
         (initial-elements (loop$ :for stobj-property :in stobj-property-list
                                 :as stobj$a-property :in stobj$a-property-list
                                 :as initial-element-name :in initial-element-names
                                 :as creator$a :in creators$a
                                 :collect (if stobj-property
                                              `(,creator$a)
                                              initial-element-name)))
         (fixers$a (fourth (third stobj$a-property)))
         (equivs$a (fifth (third stobj$a-property)))
         (accessors$a (seventh (third stobj$a-property)))

         (stobj-count (len (remove nil stobjs)))
         (stobj-accessors-and-updaters (third stobj-property))
         (non-stobj-accessors-and-updaters (nthcdr (1+ (* 2 stobj-count)) stobj-accessors-and-updaters))
         (accessors (loop$ :with stobj-accessors-and-updaters := stobj-accessors-and-updaters
                          :with non-stobj-accessors-and-updaters := non-stobj-accessors-and-updaters
                          :with stobjs := stobjs
                          :with accessors := ()
                          :do
                          (progn
                            (cond
                              ((endp stobjs)
                               (return (reverse accessors)))
                              ((car stobjs)
                               (progn
                                 (setq accessors (cons (car stobj-accessors-and-updaters) accessors))
                                 (setq stobj-accessors-and-updaters (cddr stobj-accessors-and-updaters))))
                              (t
                               (progn
                                 (setq accessors (cons (car non-stobj-accessors-and-updaters) accessors))
                                 (setq non-stobj-accessors-and-updaters (cdr non-stobj-accessors-and-updaters)))))
                            (setq stobjs (cdr stobjs)))))
         (updaters (loop$ :with stobj-accessors-and-updaters := (cdr stobj-accessors-and-updaters)
                         :with non-stobj-accessors-and-updaters := (nthcdr (- (len fields) stobj-count)
                                                                           non-stobj-accessors-and-updaters)
                         :with stobjs := stobjs
                         :with updaters := ()
                         :do
                         (progn
                           (cond
                             ((endp stobjs)
                              (return (reverse updaters)))
                             ((car stobjs)
                              (progn
                                (setq updaters (cons (car stobj-accessors-and-updaters) updaters))
                                (setq stobj-accessors-and-updaters (cddr stobj-accessors-and-updaters))))
                             (t
                              (progn
                                (setq updaters (cons (car non-stobj-accessors-and-updaters) updaters))
                                (setq non-stobj-accessors-and-updaters (cdr non-stobj-accessors-and-updaters)))))
                           (setq stobjs (cdr stobjs)))))

         (export-alist (table-alist 'export world))
         (export-list (loop$ :for stobj :in stobjs
                            :collect (and stobj
                                          (cdr (assoc stobj export-alist)))))
         (coupledp (cdr (assoc frame (table-alist 'coupledp world))))

         ;; Theorem Names
         (len-of-cons (symbolicate "ATOMIC-STOBJS" "LEN-OF-CONS"))
         (nth-of-cons (symbolicate "ATOMIC-STOBJS" "NTH-OF-CONS"))

         (exportp-tp (symbolicate package-witness exportp "-TP"))
         (exportp-cr (symbolicate package-witness exportp "-CR"))

         (export-tp (symbolicate package-witness export "-TP"))
         (exportp-of-export (symbolicate package-witness exportp "-OF-" export))

         (import-tp (symbolicate package-witness import "-TP"))
         (recognizer$a-of-import (symbolicate package-witness recognizer$a "-OF-" import))
         (coupledp-of-import (symbolicate package-witness coupledp "-OF-" import))
         (import-when-not-exportp (symbolicate package-witness import "-WHEN-NOT-" exportp))
         (import-ignores-2 (symbolicate package-witness import "-IGNORES-2"))

         (export-of-import (symbolicate package-witness export "-OF-" import))
         (import-of-export (symbolicate package-witness import "-OF-" export)))

    `(progn
       (deflabel ,export-begin)

       (encapsulate ()

         (local
           (deflabel prologue-begin))

         (local
           (defthm ,len-of-cons
             (equal (len (cons a d))
                    (1+ (len d)))))

         (local
           (defthm ,nth-of-cons
             (equal (nth n (cons a d))
                    (if (zp n)
                        a
                        (nth (1- n) d)))))

         ,@(loop$ :for fixer$a :in fixers$a
                 :as recognizer$a :in recognizers$a
                 :as equiv$a :in equivs$a
                 :as initial-element :in initial-elements
                 :as initial-element-name :in initial-element-names
                 :as field :in fields
                 :as %field :in %fields
                 :as i :from 1 :to (len fields)
                 :when (and fixer$a
                            recognizer$a
                            (not (eq equiv$a 'equal)))
                 :append `((local
                             (defthm ,(symbolicate "ATOMIC-STOBJS" recognizer$a "-CONSTRAINTS-" i)
                               (and (booleanp (,recognizer$a ,field))
                                    (,recognizer$a ,initial-element))
                               :rule-classes
                               ((:rewrite :corollary
                                          (booleanp (,recognizer$a ,field)))
                                ,@(and (not (equal initial-element initial-element-name))
                                       `((:rewrite :corollary
                                                   (,recognizer$a ,initial-element)))))))

                           (local
                             (defthm ,(symbolicate "ATOMIC-STOBJS" fixer$a "-CONSTRAINTS-" i)
                               (equal (,fixer$a ,field)
                                      (if (,recognizer$a ,field)
                                          ,field
                                          ,initial-element))))

                           (local
                             (defthm ,(symbolicate "ATOMIC-STOBJS" equiv$a "-CONSTRAINTS-" i)
                               (equal (,equiv$a ,%field ,field)
                                      (equal (,fixer$a ,%field)
                                             (,fixer$a ,field)))))))

         (local
           (deflabel prologue-end))

         (local
           (include-book "std/lists/nth" :dir :system))

         (local
           (table acl2::theory-invariant-table nil nil :clear))

         (local
           (in-theory
             (union-theories
              (union-theories (theory 'acl2::ground-zero)
                              (theory ',frame$a-theorems))
              (set-difference-theories (current-theory 'prologue-end)
                                       (current-theory 'prologue-begin)))))

         ,@(loop$ :for recognizer$a :in recognizers$a
                 :when recognizer$a
                 :collect `(local
                             (in-theory
                               (e/d ((:e ,recognizer$a))
                                    (,recognizer$a)))))

         ,@(loop$ :for absstobj-info :in absstobj-info-list
                 :when absstobj-info
                 :collect `(local
                             (in-theory
                               (enable ,@(strip-cars (cdr absstobj-info))))))

         (local
           (in-theory
             (enable ,@(strip-cars (cdr (getpropc frame 'acl2::absstobj-info))))))

         ;; `EXPORTP'
         (defun ,exportp (export)
           (declare (xargs :guard t))
           (and (consp export)
                (equal (car export) ',frame)
                (true-listp export)
                (= (len export) ,(1+ (* 2 (len fields))))
                ,@(loop$ :for field :in fields
                        :as recognizer$a :in recognizers$a
                        :as export :in export-list
                        :as i :from 1 :to (len fields)
                        :append `((eq ,(intern (symbol-name field) "KEYWORD")
                                      (nth ,(1- (* 2 i)) export))
                                  (,(or (first export) recognizer$a)
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
                         :as updater :in updaters
                         :as export :in export-list
                         :as stobj :in stobjs
                         :append `(,(intern (symbol-name field) "KEYWORD")
                                    ,(if stobj
                                         `(stobj-let ((,stobj (,accessor ,frame) ,updater))
                                                     (export)
                                                     (,(second export) ,stobj)
                                            export)
                                         `(,accessor ,frame))))))

         (defthm ,export-tp
           (and (consp (,export ,frame))
                (true-listp (,export ,frame)))
           :rule-classes :type-prescription)

         (defthm ,exportp-of-export
           (,exportp (,export ,frame)))

         ;; `IMPORT'
         (defun ,import (export ,frame)
           (declare (xargs :stobjs ,frame
                           :guard (,exportp export)))
           (if (mbt (,exportp export))
               ,(loop$ :with body := `(,the-frame ,frame)
                      :with fields := (reverse fields)
                      :with stobjs := (reverse stobjs)
                      :with export-list := (reverse export-list)
                      :with accessors := (reverse accessors)
                      :with updaters := (reverse updaters)
                      :with i := (* 2 (len fields))
                      :do
                      (progn
                        (cond
                          ((endp stobjs)
                           (return body))
                          ((car stobjs)
                           (setq body (let ((stobj (car stobjs))
                                            (import (third (car export-list)))
                                            (accessor (car accessors))
                                            (updater (car updaters)))
                                        `(stobj-let ((,stobj (,accessor ,frame) ,updater))
                                                    (,stobj)
                                                    (,import (nth ,i export) ,stobj)
                                           ,body))))
                          (t
                           (setq body `(let* ((,(car fields) (nth ,i export))
                                              (,frame (,(car updaters) ,(car fields) ,frame)))
                                         ,body))))
                        (setq fields (cdr fields))
                        (setq stobjs (cdr stobjs))
                        (setq export-list (cdr export-list))
                        (setq accessors (cdr accessors))
                        (setq updaters (cdr updaters))
                        (setq i (- i 2))))
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

         ,@(and coupledp
                `((defthm ,coupledp-of-import
                    (,coupledp (,import export ,frame)))))

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
                 :as creator$a :in creators$a
                 :as i :from 1 :to (len fields)
                 :as initial-element-name :in initial-element-names
                 :as accessor$a :in accessors$a
                 :as export :in export-list
                 :as stobj :in stobjs
                 :collect `(defthm ,(symbolicate package-witness accessor$a "-OF-" import)
                             (equal (,accessor$a (,import export ,frame))
                                    ,(if stobj
                                         `(if (,exportp export)
                                              (,(third export)
                                                (nth ,(* 2 i) export)
                                                (,creator$a))
                                              (,creator$a))
                                         `(if (,exportp export)
                                              (nth ,(* 2 i) export)
                                              ,initial-element-name)))
                             :rule-classes
                             ((:rewrite :corollary
                                        (equal (,accessor$a (,import export ,frame))
                                               ,(if stobj
                                                    `(if (,exportp export)
                                                         (,(third export)
                                                           (nth ,(* 2 i) (double-rewrite export))
                                                           (,creator$a))
                                                         (,creator$a))
                                                    `(if (,exportp export)
                                                         (nth ,(* 2 i) (double-rewrite export))
                                                         ,initial-element-name)))))))

         ;; Composition Theorems
         (defthm ,export-of-import
           (implies (,exportp export)
                    (equal (,export (,import export ,frame))
                           export))
           :hints
           ((acl2::equal-by-nths-hint)))

         (defthm ,import-of-export
           ;; TODO: Remove hypothesis and rewrite to copy of `%FRAME'
           ,(if coupledp
                `(implies (,coupledp ,%frame)
                          (equal (,import (,export ,%frame) ,frame)
                                 (,fixer$a ,%frame)))
                `(equal (,import (,export ,%frame) ,frame)
                        (,fixer$a ,%frame)))
           :hints
           (("Goal"
             :use ((:instance ,frame$a-equal
                              (,%frame$a (,import (,export ,%frame) ,frame))
                              (,frame$a (,fixer$a ,%frame))))))))

       (deflabel ,export-end)

       (table export ',frame ',(list exportp
                                     export
                                     import))

       (deftheory-static ,export-theory
         (set-difference-theories
          (set-difference-theories (current-theory ',export-end)
                                   (current-theory ',export-begin))
          '(,exportp
            ,export
            ,import)))

       (in-theory
         (union-theories (current-theory ',export-begin)
                         (theory ',export-theory))))))


;;;; `DEFINE-EXPORT'
(defmacro define-export (stobj &key
                                 (debug 'nil)
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
           ((and (= (len stobj$a-property) 3)
                 (= (len (third stobj$a-property)) 5))
            (make-hash-table-export-events stobj package-witness state))
           ((and (= (len stobj$a-property) 3)
                 (= (len (third stobj$a-property)) 9))
            (make-frame-export-events stobj package-witness state)))))))
