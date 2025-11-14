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

(include-book "std/osets/top" :dir :system)

(include-book "../utilities/top")
(include-book "congruent")

(deftheory set::theorems
  (append
   #!acl2'((:definition fast-alphorder)
           (:executable-counterpart fast-alphorder)
           (:type-prescription fast-alphorder)
           (:executable-counterpart fast-lexorder)
           (:type-prescription fast-lexorder)
           (:rewrite fast-lexorder-is-lexorder)
           (:executable-counterpart fast-<<)
           (:type-prescription fast-<<)
           (:executable-counterpart <<)
           (:type-prescription <<)
           (:rewrite <<-irreflexive)
           (:rewrite <<-transitive)
           (:rewrite <<-asymmetric)
           (:rewrite <<-trichotomy)
           (:rewrite <<-implies-lexorder)
           (:rewrite fast-<<-is-<<))

   #!set'((:executable-counterpart setp)
          (:type-prescription setp)
          (:type-prescription setp-type)
          (:executable-counterpart emptyp)
          (:type-prescription emptyp)
          (:type-prescription emptyp-type)
          (:executable-counterpart sfix)
          (:type-prescription sfix)
          (:executable-counterpart head)
          (:type-prescription head)
          (:executable-counterpart tail)
          (:type-prescription tail)
          (:executable-counterpart insert)
          (:type-prescription insert)
          (:executable-counterpart in)
          (:type-prescription in)
          (:type-prescription in-type)
          (:executable-counterpart fast-subset)
          (:type-prescription fast-subset)
          (:executable-counterpart subset)
          (:type-prescription subset)
          (:type-prescription subset-type)
          (:executable-counterpart fast-measure)
          (:type-prescription fast-measure)
          (:definition fast-union)
          (:executable-counterpart fast-union)
          (:type-prescription fast-union)
          (:induction fast-union)
          (:definition fast-intersect)
          (:executable-counterpart fast-intersect)
          (:type-prescription fast-intersect)
          (:induction fast-intersect)
          (:definition fast-intersectp)
          (:executable-counterpart fast-intersectp)
          (:type-prescription fast-intersectp)
          (:induction fast-intersectp)
          (:definition fast-difference)
          (:executable-counterpart fast-difference)
          (:type-prescription fast-difference)
          (:induction fast-difference)
          (:executable-counterpart delete)
          (:type-prescription delete)
          (:executable-counterpart union)
          (:type-prescription union)
          (:executable-counterpart intersect)
          (:type-prescription intersect)
          (:definition intersectp)
          (:executable-counterpart intersectp)
          (:type-prescription intersectp)
          (:executable-counterpart difference)
          (:type-prescription difference)
          (:executable-counterpart cardinality)
          (:type-prescription cardinality)
          (:executable-counterpart halve-list-aux)
          (:type-prescription halve-list-aux)
          (:executable-counterpart halve-list)
          (:type-prescription halve-list)
          (:definition mergesort-exec)
          (:executable-counterpart mergesort-exec)
          (:type-prescription mergesort-exec)
          (:induction mergesort-exec)
          (:executable-counterpart mergesort)
          (:type-prescription mergesort)
          (:definition all)
          (:executable-counterpart all)
          (:type-prescription all)
          (:induction all)
          (:executable-counterpart subset-trigger)
          (:type-prescription subset-trigger)
          (:rewrite pick-a-point-subset-constraint-helper)
          (:compound-recognizer sets-are-true-lists-compound-recognizer)
          (:rewrite sets-are-true-lists-cheap)
          (:rewrite tail-count)
          (:linear tail-count)
          (:rewrite head-count)
          (:linear head-count)
          (:built-in-clause tail-count-built-in)
          (:built-in-clause head-count-built-in)
          (:rewrite insert-insert)
          (:rewrite sfix-produces-set)
          (:rewrite tail-produces-set)
          (:rewrite insert-produces-set)
          (:rewrite insert-never-empty)
          (:rewrite nonempty-means-set)
          (:rewrite sfix-set-identity)
          (:rewrite emptyp-sfix-cancel)
          (:rewrite head-sfix-cancel)
          (:rewrite tail-sfix-cancel)
          (:rewrite insert-head)
          (:rewrite insert-head-tail)
          (:rewrite repeated-insert)
          (:rewrite insert-sfix-cancel)
          (:rewrite head-when-emptyp)
          (:rewrite tail-when-emptyp)
          (:rewrite insert-when-emptyp)
          (:rewrite head-of-insert-a-nil)
          (:rewrite tail-of-insert-a-nil)
          (:rewrite sfix-when-emptyp)
          (:rewrite not-in-self)
          (:rewrite in-sfix-cancel)
          (:rewrite never-in-empty)
          (:rewrite in-set)
          (:rewrite in-tail)
          (:rewrite in-tail-or-head)
          (:rewrite in-head)
          (:rewrite head-unique)
          (:rewrite insert-identity)
          (:rewrite in-insert)
          (:rewrite subset-insert-x)
          (:rewrite subset-sfix-cancel-x)
          (:rewrite subset-sfix-cancel-y)
          (:rewrite emptyp-subset)
          (:rewrite emptyp-subset-2)
          (:rewrite subset-reflexive)
          (:rewrite subset-insert)
          (:rewrite subset-tail)
          (:forward-chaining subset-tail)
          (:rewrite weak-insert-induction-helper-1)
          (:rewrite weak-insert-induction-helper-2)
          (:rewrite weak-insert-induction-helper-3)
          (:definition weak-insert-induction)
          (:executable-counterpart weak-insert-induction)
          (:type-prescription weak-insert-induction)
          (:induction weak-insert-induction)
          (:induction use-weak-insert-induction)
          (:rewrite delete-delete)
          (:rewrite delete-set)
          (:rewrite delete-preserves-emptyp)
          (:rewrite delete-in)
          (:rewrite delete-sfix-cancel)
          (:rewrite delete-nonmember-cancel)
          (:rewrite repeated-delete)
          (:rewrite delete-insert-cancel)
          (:rewrite insert-delete-cancel)
          (:rewrite subset-delete)
          (:rewrite union-insert-x)
          (:rewrite union-insert-y)
          (:rewrite union-set)
          (:rewrite union-sfix-cancel-x)
          (:rewrite union-sfix-cancel-y)
          (:rewrite union-emptyp-x)
          (:rewrite union-emptyp-y)
          (:rewrite union-emptyp)
          (:rewrite union-in)
          (:rewrite union-subset-x)
          (:rewrite union-subset-y)
          (:rewrite union-self)
          (:rewrite union-associative)
          (:rewrite union-outer-cancel)
          (:rewrite intersect-delete-x)
          (:rewrite intersect-delete-y)
          (:rewrite intersect-set)
          (:rewrite intersect-sfix-cancel-x)
          (:rewrite intersect-sfix-cancel-y)
          (:rewrite intersect-emptyp-x)
          (:rewrite intersect-emptyp-y)
          (:rewrite intersect-in)
          (:rewrite intersect-subset-x)
          (:rewrite intersect-subset-y)
          (:rewrite intersect-self)
          (:rewrite intersect-associative)
          (:rewrite intersect-outer-cancel)
          (:rewrite difference-set)
          (:rewrite difference-sfix-x)
          (:rewrite difference-sfix-y)
          (:rewrite difference-emptyp-x)
          (:rewrite difference-emptyp-y)
          (:rewrite difference-in)
          (:rewrite difference-subset-x)
          (:rewrite subset-difference)
          (:rewrite difference-insert-y)
          (:rewrite difference-delete-x)
          (:rewrite difference-preserves-subset)
          (:type-prescription cardinality-type)
          (:rewrite cardinality-zero-emptyp)
          (:rewrite cardinality-sfix-cancel)
          (:rewrite subset-cardinality)
          (:linear subset-cardinality)
          (:rewrite proper-subset-cardinality)
          (:linear proper-subset-cardinality)
          (:rewrite intersect-cardinality-x)
          (:linear intersect-cardinality-x)
          (:rewrite intersect-cardinality-y)
          (:linear intersect-cardinality-y)
          (:rewrite expand-cardinality-of-union)
          (:rewrite expand-cardinality-of-difference)
          (:rewrite intersect-cardinality-non-subset)
          (:linear intersect-cardinality-non-subset)
          (:rewrite intersect-cardinality-subset-2)
          (:rewrite intersect-cardinality-non-subset-2)
          (:rewrite mergesort-set)
          (:rewrite in-mergesort-under-iff)
          (:rewrite mergesort-set-identity)
          (:rewrite insert-under-set-equiv)
          (:rewrite delete-under-set-equiv)
          (:rewrite union-under-set-equiv)
          (:rewrite intersect-under-set-equiv)
          (:rewrite difference-under-set-equiv)
          (:rewrite mergesort-under-set-equiv)
          (:congruence set-equiv-implies-equal-mergesort-1))))


;;;; `MAKE-VECTOR-COPY-EVENTS'
(defun make-vector-copy-events (vector state)
  (declare (xargs :stobjs state
                  :guard (symbolp vector)
                  :verify-guards nil))
  (let* ((%vector (symbolicate vector "%" vector))
         (copy (symbolicate vector vector "-COPY"))
         (copy-rec (symbolicate vector copy "-REC"))
         (copy{rewrite} (symbolicate vector copy "{REWRITE}"))

         (index (symbolicate vector "I"))
         (%index (symbolicate index "%" index))

         (coupledp (symbolicate vector vector "-COUPLED-P"))
         (coupledp-witness (symbolicate vector coupledp "-WITNESS"))

         ;; `VECTOR'
         (stobj-property (getpropc vector 'acl2::stobj))
         (recognizer (caadr stobj-property))
         (fixer (first (third stobj-property)))
         (length (second (third stobj-property)))
         (resizer (third (third stobj-property)))
         (accessor (fourth (third stobj-property)))
         (updater (fifth (third stobj-property)))

         ;; `VECTOR$A'
         (vector$a (symbolicate vector vector "$A"))
         (%vector$a (symbolicate vector "%" vector$a))
         (vector$a-theorems (symbolicate vector vector$a "-THEOREMS"))
         (vector$a-aggressive (symbolicate vector vector$a "-AGGRESSIVE"))
         (world (w state))
         (stobj$a-property (cdr (assoc vector (table-alist 'stobj$a-property world))))
         (recognizer$a (first (second stobj$a-property)))
         (creator$a (second (second stobj$a-property)))
         (fixer$a (third (second stobj$a-property)))
         (length$a (first (third (third stobj$a-property))))
         (resizer$a (second (third (third stobj$a-property))))
         (accessor$a (third (third (third stobj$a-property))))
         (updater$a (fourth (third (third stobj$a-property))))
         (vector$a-equal (cdr (assoc vector$a (table-alist 'equality world))))

         (element (first (first (third stobj$a-property))))
         (element-stobj-property (getpropc element 'acl2::stobj))
         (element-stobj$a-property (cdr (assoc element (table-alist 'stobj$a-property world))))
         (element-recognizer (second (first (third stobj$a-property))))
         (element-creator (second (second element-stobj$a-property)))
         (initial-element (if element-stobj-property
                              `(,element-creator)
                              (third (first (third stobj$a-property)))))
         (element-fixer (fourth (first (third stobj$a-property))))

         (fixer (if element-stobj-property
                    (third (third stobj-property))
                    fixer))
         (length (if element-stobj-property
                     (fourth (third stobj-property))
                     length))
         (resizer (if element-stobj-property
                      (fifth (third stobj-property))
                      resizer))
         (accessor (if element-stobj-property
                       (first (third stobj-property))
                       accessor))
         (%accessor (symbolicate vector "%" accessor))
         (updater (if element-stobj-property
                      (second (third stobj-property))
                      updater))
         (%updater (symbolicate vector "%" updater))

         (element-copy (cdr (assoc element (table-alist 'copy world))))
         (%element (car (getpropc element-copy 'acl2::formals)))
         (element-coupled-p (cdr (assoc element (table-alist 'coupledp world))))
         (element-coupled-p-theory (symbolicate element element "-COUPLED-P-THEORY"))

         (coupledp-begin (symbolicate vector coupledp "-BEGIN"))
         (coupledp-end (symbolicate vector coupledp "-END"))
         (coupledp-theory (symbolicate vector coupledp "-THEORY"))

         ;; Theorem Names
         (booleanp-of-element-recognizer (symbolicate "ATOMIC-STOBJS" "BOOLEANP-OF-" element-recognizer))
         (element-recognizer-of-default-element (symbolicate "ATOMIC-STOBJS" element-recognizer "-OF-DEFAULT-ELEMENT"))
         (element-fixer{rewrite} (symbolicate "ATOMIC-STOBJS" element-fixer "{REWRITE}"))

         (coupledp-when-not-recognizer$a (symbolicate vector coupledp "-WHEN-NOT-" recognizer$a))
         (coupledp-of-creator$a (symbolicate vector coupledp "-OF-" creator$a))
         (coupledp-of-fixer$a (symbolicate vector coupledp "-OF-" fixer$a))
         (coupledp-of-resizer$a (symbolicate vector coupledp "-OF-" resizer$a))
         (element-coupled-p-of-accessor$a (symbolicate vector element-coupled-p "-OF-" accessor$a))
         (coupledp-of-updater$a (symbolicate vector coupledp "-OF-" updater$a))

         (recognizer$a-of-copy (symbolicate vector recognizer$a "-OF-" copy))
         (length$a-of-copy (symbolicate vector length$a "-OF-" copy))
         (accessor$a-of-copy (symbolicate vector accessor$a "-OF-" copy))
         (recognizer$a-of-copy-rec (symbolicate vector recognizer$a "-OF-" copy-rec))
         (length$a-of-copy-rec (symbolicate vector length$a "-OF-" copy-rec))
         (accessor$a-of-copy-rec (symbolicate vector accessor$a "-OF-" copy-rec)))

    `(progn
       (deflabel ,coupledp-begin)

       (encapsulate ()

         (local
           (deflabel prologue-begin))

         ,@(and element-recognizer
                element-fixer
                `((local
                    (defthm ,booleanp-of-element-recognizer
                      (booleanp (,element-recognizer ,element))
                      :rule-classes
                      (:rewrite
                       :type-prescription)))

                  (local
                    (defthm ,element-recognizer-of-default-element
                      (,element-recognizer ,initial-element)
                      :rule-classes nil))

                  (local
                    (defthm ,element-fixer{rewrite}
                      (equal (,element-fixer ,element)
                             (if (,element-recognizer ,element)
                                 ,element
                                 ,initial-element))))))

         (local
           (deflabel prologue-end))

         (local
           (in-theory
             (union-theories
              (union-theories
               (theory 'acl2::ground-zero)
               (union-theories (theory ',vector$a-theorems)
                               (theory ',vector$a-aggressive)))
              (set-difference-theories (current-theory 'prologue-end)
                                       (current-theory 'prologue-begin)))))

         ,@(and element-recognizer
                element-fixer
                `((local
                    (in-theory
                      (disable ,element-recognizer
                               ,element-fixer)))))

         ,@(and element-stobj$a-property
                `((local
                    (in-theory
                      (disable ,element-creator)))))

         ,@(and element-stobj-property
                `((local
                    (in-theory
                      (enable ,element-coupled-p-theory)))))

         ,@(and element-stobj-property
                `((local
                    (in-theory
                      (enable ,@(strip-cars (cdr (getpropc element 'acl2::absstobj-info))))))))

         (local
           (in-theory
             (enable ,@(strip-cars (cdr (getpropc vector 'acl2::absstobj-info))))))

         (define-congruent ,vector)

         (local
           (in-theory
             (enable ,@(strip-cars (cdr (getpropc %vector 'acl2::absstobj-info))))))

         ;; `COUPLEDP'
         ,@(and element-coupled-p
                `((defun-sk ,coupledp (,vector)
                    (declare (xargs :guard (,recognizer ,vector)
                                    :verify-guards nil))
                    (forall ,index
                      (,element-coupled-p (,accessor$a ,index ,vector)))
                    :rewrite :direct)

                  (table coupledp ',vector ',coupledp)

                  (defthm ,coupledp-when-not-recognizer$a
                    (implies (not (,recognizer$a ,vector))
                             (,coupledp ,vector)))

                  (defthm ,coupledp-of-creator$a
                    (,coupledp (,creator$a)))

                  (defthm ,coupledp-of-fixer$a
                    (equal (,coupledp (,fixer$a ,vector))
                           (,coupledp ,vector)))

                  (defthm ,coupledp-of-resizer$a
                    (implies (,coupledp ,vector)
                             (,coupledp (,resizer$a length ,vector))))

                  (defthm ,element-coupled-p-of-accessor$a
                    (implies (,coupledp ,vector)
                             (,element-coupled-p (,accessor$a ,index ,vector))))

                  (defthm ,coupledp-of-updater$a
                    (implies (and (,coupledp ,vector)
                                  (,element-coupled-p ,element))
                             (,coupledp (,updater$a ,index ,element ,vector)))
                    :hints
                    (("Goal"
                      :cases ((< (nfix (,coupledp-witness (,updater ,index ,element ,vector)))
                                 (,length$a ,vector)))
                      :in-theory (disable ,coupledp
                                          nfix)
                      :expand (,coupledp (,updater$a ,index ,element ,vector)))))

                  (in-theory
                    (disable ,coupledp))))

         (defun ,copy-rec (,index ,%vector ,vector)
           (declare (xargs :stobjs (,%vector ,vector)
                           :guard (and (= (,length ,%vector) (,length ,vector))
                                       (natp ,index)
                                       (<= ,index (,length ,vector)))))
           (if (zp ,index)
               (,fixer ,%vector)
               ,(if element-copy
                    `(let ((,index (1- ,index)))
                       (stobj-let ((,element (,accessor ,index ,vector) ,updater))
                                  (,%vector)
;;; TODO: `CONCRETE-ACCESSOR' gives error:
;;; ```
;;; HARD ACL2 ERROR in ASSERT$:  Assertion failed:
;;; (ASSERT$ ACCESSOR$C (CONCRETE-ACCESSOR ACCESSOR$C (CDR TUPLES-LST)))
;;; '''
;;; when ACCESSOR is used instead of %ACCESSOR here (respectively UPDATER vs %UPDATER).
;;; Is this a bug?
                                  (stobj-let ((,%element (,%accessor ,index ,%vector) ,%updater))
                                             (,%element)
                                             (,element-copy ,%element ,element)
                                    ,%vector)
                         (,copy-rec ,index ,%vector ,vector)))
                    `(let* ((,index (1- ,index))
                            (,element (,accessor ,index ,vector))
                            (,%vector (,updater ,index ,element ,%vector)))
                       (,copy-rec ,index ,%vector ,vector)))))

         (local
           (defthm ,recognizer$a-of-copy-rec
             (,recognizer$a (,copy-rec ,index ,%vector ,vector))))

         (local
           (defthm ,length$a-of-copy-rec
             (equal (,length$a (,copy-rec ,index ,%vector ,vector))
                    (,length$a ,%vector))))

         (local
           (defthm ,accessor$a-of-copy-rec
             (implies ,(if element-coupled-p
                           `(and (,coupledp ,vector)
                                 (< (nfix i) (,length$a ,%vector)))
                           `(< (nfix ,%index) (,length$a ,%vector)))
                      (equal (,accessor$a ,%index (,copy-rec ,index ,%vector ,vector))
                             (if (< (nfix ,%index) (nfix ,index))
                                 (,accessor$a ,%index ,vector)
                                 (,accessor$a ,%index ,%vector))))))

         (in-theory
           (disable ,copy-rec))

         (defun ,copy (,%vector ,vector)
           (declare (xargs :stobjs (,%vector ,vector)))
           (let* ((length (,length ,vector))
                  (,%vector (if (= (,length ,%vector) length)
                                ,%vector
                                (,resizer length ,%vector))))
             (,copy-rec length ,%vector ,vector)))

         (table copy ',vector ',copy)

         (defthm ,recognizer$a-of-copy
           (,recognizer$a (,copy ,%vector ,vector)))

         (defthm ,length$a-of-copy
           (equal (,length$a (,copy ,%vector ,vector))
                  (,length$a ,vector)))

         (local
           (defthm ,accessor$a-of-copy
             (implies ,(if element-coupled-p
                           `(and (,coupledp ,vector)
                                 (< (nfix ,index) (,length$a ,vector)))
                           `(< (nfix ,index) (,length$a ,vector)))
                      (equal (,accessor$a ,index (,copy ,%vector ,vector))
                             (,accessor$a ,index ,vector)))))

         (in-theory
           (disable ,copy))

         (defthm ,copy{rewrite}
           ,(if element-coupled-p
                `(implies (case-split (,coupledp ,vector))
                          (equal (,copy ,%vector ,vector)
                                 (,fixer ,vector)))
                `(equal (,copy ,%vector ,vector)
                        (,fixer$a ,vector)))
           :hints
           (("Goal"
             :use ((:instance ,vector$a-equal
                              (,%vector$a (,copy ,%vector ,vector))
                              (,vector$a (,fixer$a ,vector))))))))

       (deflabel ,coupledp-end)

       (deftheory-static ,coupledp-theory
         (set-difference-theories (current-theory ',coupledp-end)
                                  (current-theory ',coupledp-begin))))))

(defun make-hash-table-copy-events (hash-table state)
  (declare (xargs :stobjs state
                  :guard (symbolp hash-table)
                  :verify-guards nil))
  (let* ((%hash-table (symbolicate hash-table "%" hash-table))
         (copy (symbolicate hash-table hash-table "-COPY"))
         (copy-rec (symbolicate hash-table copy "-REC"))
         (copy{rewrite} (symbolicate hash-table copy "{REWRITE}"))

         (coupledp (symbolicate hash-table hash-table "-COUPLED-P"))
         (coupled-keys-p (symbolicate hash-table hash-table "-COUPLED-KEYS-P"))
         (coupled-keys-p-witness (symbolicate hash-table coupled-keys-p "-WITNESS"))
         (coupled-keys-p-necc (symbolicate hash-table coupled-keys-p "-NECC"))
         (coupled-vals-p (symbolicate hash-table hash-table "-COUPLED-VALS-P"))
         (coupled-vals-p-witness (symbolicate hash-table coupled-vals-p "-WITNESS"))
         (coupled-vals-p-necc (symbolicate hash-table coupled-vals-p "-NECC"))

         ;; `HASH-TABLE'
         (stobj-property (getpropc hash-table 'acl2::stobj))
         (recognizer (caadr stobj-property))
         (fixer (first (third stobj-property)))
         (accessor (second (third stobj-property)))
         (updater (third (third stobj-property)))
         (count (seventh (third stobj-property)))
         (init (ninth (third stobj-property)))
         (keys (tenth (third stobj-property)))
         (keys-set (nth 10 (third stobj-property)))

         ;; `HASH-TABLE$A'
         (hash-table$a (symbolicate hash-table hash-table "$A"))
         (%hash-table$a (symbolicate hash-table "%" hash-table$a))
         (hash-table$a-theorems (symbolicate hash-table hash-table$a "-THEOREMS"))
         (hash-table$a-aggressive (symbolicate hash-table hash-table$a "-AGGRESSIVE"))
         (world (w state))
         (stobj$a-property (cdr (assoc hash-table (table-alist 'stobj$a-property world))))
         (recognizer$a (first (second stobj$a-property)))
         (creator$a (second (second stobj$a-property)))
         (fixer$a (third (second stobj$a-property)))
         (accessor$a (first (fourth (third stobj$a-property))))
         (updater$a (second (fourth (third stobj$a-property))))
         (boundp$a (third (fourth (third stobj$a-property))))
         (remover$a (fifth (fourth (third stobj$a-property))))
         (count$a (sixth (fourth (third stobj$a-property))))
         (keysp$a (nth 8 (fourth (third stobj$a-property))))
         (keys$a-fix (nth 9 (fourth (third stobj$a-property))))
         (keys$a (nth 10 (fourth (third stobj$a-property))))
         (keys-set$a (nth 11 (fourth (third stobj$a-property))))
         (hash-table$a-equal (cdr (assoc hash-table$a (table-alist 'equality world))))

         (key (first (first (third stobj$a-property))))
         (key-recognizer (second (first (third stobj$a-property))))
         (default-key (third (first (third stobj$a-property))))
         (key-fixer (fourth (first (third stobj$a-property))))

         (val (first (second (third stobj$a-property))))
         (val-stobj-property (getpropc val 'acl2::stobj))
         (val-stobj$a-property (cdr (assoc val (table-alist 'stobj$a-property world))))
         (val-recognizer (second (second (third stobj$a-property))))
         (val-creator (second (second val-stobj$a-property)))
         (default-val (if val-stobj-property
                          `(,val-creator)
                          (third (second (third stobj$a-property)))))
         (val-fixer (fourth (second (third stobj$a-property))))

         (fixer (if val-stobj-property
                    (third (third stobj-property))
                    fixer))
         (accessor (if val-stobj-property
                       (first (third stobj-property))
                       accessor))
         (%accessor (symbolicate hash-table "%" accessor))
         (updater (if val-stobj-property
                      (second (third stobj-property))
                      updater))
         (%updater (symbolicate hash-table "%" updater))

         (val-copy (cdr (assoc val (table-alist 'copy world))))
         (%val (car (getpropc val-copy 'acl2::formals)))
         (val-coupled-p (cdr (assoc val (table-alist 'coupledp world))))
         (val-coupled-p-theory (symbolicate val val "-COUPLED-P-THEORY"))

         (coupledp-begin (symbolicate hash-table coupledp "-BEGIN"))
         (coupledp-end (symbolicate hash-table coupledp "-END"))
         (coupledp-theory (symbolicate hash-table coupledp "-THEORY"))

         ;; Theorem Names
         (booleanp-of-key-recognizer (symbolicate "ATOMIC-STOBJS" "BOOLEANP-OF-" key-recognizer))
         (key-recognizer-of-default-key (symbolicate "ATOMIC-STOBJS" key-recognizer "-OF-DEFAULT-KEY"))
         (key-fixer{rewrite} (symbolicate "ATOMIC-STOBJS" key-fixer "{REWRITE}"))

         (booleanp-of-val-recognizer (symbolicate "ATOMIC-STOBJS" "BOOLEANP-OF-" val-recognizer))
         (val-recognizer-of-default-val (symbolicate "ATOMIC-STOBJS" val-recognizer "-OF-DEFAULT-VAL"))
         (val-fixer{rewrite} (symbolicate "ATOMIC-STOBJS" val-fixer "{REWRITE}"))

         (coupled-keys-p-when-not-recognizer$a (symbolicate hash-table coupled-keys-p "-WHEN-NOT-" recognizer$a))
         (coupled-keys-p-of-creator$a (symbolicate hash-table coupled-keys-p "-OF-" creator$a))
         (coupled-keys-p-of-fixer$a (symbolicate hash-table coupled-keys-p "-OF-" fixer$a))
         (coupled-keys-p-of-updater$a-when-boundp$a (symbolicate hash-table coupled-keys-p "-OF-" updater$a "-WHEN-" boundp$a))
         (coupled-keys-p-of-updater$a-when-not-boundp$a (symbolicate hash-table coupled-keys-p "-OF-" updater$a "-WHEN-NOT-" boundp$a))
         (coupled-keys-p-of-remover$a-when-boundp$a (symbolicate hash-table coupled-keys-p "-OF-" remover$a "-WHEN-" boundp$a))
         (coupled-keys-p-of-remover$a-when-not-boundp$a (symbolicate hash-table coupled-keys-p "-OF-" remover$a "-WHEN-NOT-" boundp$a))

         (coupled-vals-p-when-not-recognizer$a (symbolicate hash-table coupled-vals-p "-WHEN-NOT-" recognizer$a))
         (coupled-vals-p-of-creator$a (symbolicate hash-table coupled-vals-p "-OF-" creator$a))
         (coupled-vals-p-of-fixer$a (symbolicate hash-table coupled-vals-p "-OF-" fixer$a))
         (coupled-vals-p-of-updater$a (symbolicate hash-table coupled-vals-p "-OF-" updater$a))
         (coupled-vals-p-of-remover$a (symbolicate hash-table coupled-vals-p "-OF-" remover$a))
         (coupled-vals-p-of-keys-set$a (symbolicate hash-table coupled-vals-p "-OF-" keys-set$a))
         (coupled-vals-p-of-keys-set$a-lemma (symbolicate hash-table coupled-vals-p-of-keys-set$a "-LEMMA"))

         (coupledp-when-not-recognizer$a (symbolicate hash-table coupledp "-WHEN-NOT-" recognizer$a))
         (coupledp-of-creator$a (symbolicate hash-table coupledp "-OF-" creator$a))
         (coupledp-of-fixer$a (symbolicate hash-table coupledp "-OF-" fixer$a))
         (coupledp-of-updater$a-when-boundp$a (symbolicate hash-table coupledp "-OF-" updater$a "-WHEN-" boundp$a))
         (coupledp-of-updater$a-when-not-boundp$a (symbolicate hash-table coupledp "-OF-" updater$a "-WHEN-NOT-" boundp$a))
         (coupledp-of-remover$a-when-boundp$a (symbolicate hash-table coupledp "-OF-" remover$a "-WHEN-" boundp$a))
         (coupledp-of-remover$a-when-not-boundp$a (symbolicate hash-table coupledp "-OF-" remover$a "-WHEN-NOT-" boundp$a))
         (cardinality-of-keys$a (symbolicate hash-table "CARDINALITY-OF-" keys$a))
         (in-of-keys$a (symbolicate hash-table "IN-OF-" keys$a))
         (val-coupled-p-of-accessor$a (symbolicate hash-table val-coupled-p "-OF-" accessor$a))
         (emptyp-of-keys$a (symbolicate hash-table "EMPTYP-OF-" keys$a))

         (recognizer$a-of-copy (symbolicate hash-table recognizer$a "-OF-" copy))
         (coupledp-of-copy (symbolicate hash-table coupledp "-OF-" copy))
         (coupledp-of-copy/lemma-0 (symbolicate hash-table coupledp-of-copy "/LEMMA-0"))
         (coupledp-of-copy/lemma-1 (symbolicate hash-table coupledp-of-copy "/LEMMA-1"))
         (keys$a-of-copy (symbolicate hash-table keys$a "-OF-" copy))
         (boundp$a-of-copy (symbolicate hash-table boundp$a "-OF-" copy))
         (accessor$a-of-copy (symbolicate hash-table accessor$a "-OF-" copy))
         (count$a-of-copy (symbolicate hash-table count$a "-OF-" copy))

         (recognizer$a-of-copy-rec (symbolicate hash-table recognizer$a "-OF-" copy-rec))
         (keys$a-of-copy-rec (symbolicate hash-table keys$a "-OF-" copy-rec))
         (copy-rec-of-updater$a (symbolicate hash-table copy-rec "-OF-" updater$a))
         (boundp$a-of-copy-rec (symbolicate hash-table boundp$a "-OF-" copy-rec))
         (accessor$a-of-copy-rec (symbolicate hash-table accessor$a "-OF-" copy-rec))
         (count$a-of-copy-rec (symbolicate hash-table count$a "-OF-" copy-rec)))

    `(progn
       (deflabel ,coupledp-begin)

       (encapsulate ()

         (local
           (deflabel prologue-begin))

         (local
           (defthm head-not-in-tail
             (implies (and (not (set::emptyp set))
                           (equal head (set::head set))
                           (equal tail (set::tail set)))
                      (not (set::in head tail)))))

         (local
           (defthm head-in-set
             (implies (and (not (set::emptyp set))
                           (equal head (set::head set)))
                      (set::in head set))))

         (local
           (defthm in-tail-iff
             (implies (and (not (set::emptyp set))
                           (not (equal element (set::head set))))
                      (equal (set::in element (set::tail set))
                             (set::in element set)))
             :hints
             (("Goal"
               :expand (set::in element set)))))

         (local
           (defthm head-of-tail-neq-head
             (implies (and (not (set::emptyp set))
                           (not (set::emptyp (set::tail set))))
                      (not (equal (set::head (set::tail set))
                                  (set::head set))))
             :hints
             (("Goal"
               :in-theory (enable set::setp
                                  set::emptyp
                                  set::head
                                  set::tail)))))

         ,@(and key-recognizer
                key-fixer
                `((local
                    (defthm ,booleanp-of-key-recognizer
                      (booleanp (,key-recognizer ,key))
                      :rule-classes
                      (:rewrite
                       :type-prescription)))

                  (local
                    (defthm ,key-recognizer-of-default-key
                      (,key-recognizer ,default-key)
                      :rule-classes nil))

                  (local
                    (defthm ,key-fixer{rewrite}
                      (equal (,key-fixer ,key)
                             (if (,key-recognizer ,key)
                                 ,key
                                 ,default-key))))))

         ,@(and val-recognizer
                val-fixer
                `((local
                    (defthm ,booleanp-of-val-recognizer
                      (booleanp (,val-recognizer ,val))
                      :rule-classes
                      (:rewrite
                       :type-prescription)))

                  (local
                    (defthm ,val-recognizer-of-default-val
                      (,val-recognizer ,default-val)
                      :rule-classes nil))

                  (local
                    (defthm ,val-fixer{rewrite}
                      (equal (,val-fixer ,val)
                             (if (,val-recognizer ,val)
                                 ,val
                                 ,default-val))))))

         (local
           (deflabel prologue-end))

         (local
           (in-theory
             (union-theories
              (union-theories
               (union-theories (theory 'acl2::ground-zero)
                               (theory 'set::theorems))
               (union-theories (theory ',hash-table$a-theorems)
                               (theory ',hash-table$a-aggressive)))
              (set-difference-theories (current-theory 'prologue-end)
                                       (current-theory 'prologue-begin)))))

         ,@(and key-recognizer
                key-fixer
                `((local
                    (in-theory
                      (disable ,key-recognizer
                               ,key-fixer)))))

         ,@(and val-recognizer
                val-fixer
                `((local
                    (in-theory
                      (disable ,val-recognizer
                               ,val-fixer)))))

         ,@(and val-stobj$a-property
                `((local
                    (in-theory
                      (disable ,val-creator)))))

         ,@(and val-stobj-property
                `((local
                    (in-theory
                      (enable ,val-coupled-p-theory)))))

         ,@(and val-stobj-property
                `((local
                    (in-theory
                      (enable ,@(strip-cars (cdr (getpropc val 'acl2::absstobj-info))))))))

         (local
           (in-theory
             (acl2::enable* set::expensive-rules)))

         (local
           (in-theory
             (enable ,@(strip-cars (cdr (getpropc hash-table 'acl2::absstobj-info))))))

         (define-congruent ,hash-table)

         (local
           (in-theory
             (enable ,@(strip-cars (cdr (getpropc %hash-table 'acl2::absstobj-info))))))

         ;; `COUPLED-KEYS-P'
         (defun-sk ,coupled-keys-p (,hash-table)
           (declare (xargs :guard (,recognizer ,hash-table)
                           :verify-guards nil))
           (forall ,key
             (equal (set::in ,key (,keys$a ,hash-table))
                    ,(if key-recognizer
                         `(and (,key-recognizer ,key)
                               (,boundp$a ,key ,hash-table))
                         `(,boundp$a ,key ,hash-table))))
           :rewrite :direct)

         (defthm ,coupled-keys-p-when-not-recognizer$a
           (implies (not (,recognizer$a ,hash-table))
                    (,coupled-keys-p ,hash-table)))

         (defthm ,coupled-keys-p-of-creator$a
           (,coupled-keys-p (,creator$a)))

         (defthm ,coupled-keys-p-of-fixer$a
           (equal (,coupled-keys-p (,fixer$a ,hash-table))
                  (,coupled-keys-p ,hash-table)))

         (defthm ,coupled-keys-p-of-updater$a-when-boundp$a
           (implies (and (,boundp$a ,key ,hash-table)
                         (,coupled-keys-p ,hash-table))
                    (,coupled-keys-p (,updater$a ,key ,val ,hash-table))))

         (defthm ,coupled-keys-p-of-updater$a-when-not-boundp$a
           (implies (let* ((,keys$a (,keys$a ,hash-table))
                           (trimmed (set::delete ,(if key-fixer
                                                      `(,key-fixer ,key)
                                                      key)
                                                 ,keys$a)))
                      (and (not (,boundp$a ,key ,hash-table))
                           (set::in ,(if key-fixer
                                         `(,key-fixer ,key)
                                         key)
                                    ,keys$a)
                           (,coupled-keys-p (,keys-set$a trimmed ,hash-table))))
                    (,coupled-keys-p (,updater$a ,key ,val ,hash-table)))
           :hints
           (("Goal"
             :do-not-induct t
             :in-theory (disable ,coupled-keys-p
                                 ,coupled-keys-p-necc)
             :use ((:instance ,coupled-keys-p-necc
                              (,key (,coupled-keys-p-witness (,updater$a ,default-key ,val ,hash-table)))
                              (,hash-table (,keys-set$a (set::delete ,default-key (,keys$a ,hash-table))
                                                        ,hash-table)))
                   (:instance ,coupled-keys-p-necc
                              (,key (,coupled-keys-p-witness (,updater$a ,key ,val ,hash-table)))
                              (,hash-table (,keys-set$a (set::delete k (,keys$a ,hash-table))
                                                        ,hash-table))))
             :expand (:free (,key) (,coupled-keys-p (,updater$a ,key ,val ,hash-table))))))

         (defthm ,coupled-keys-p-of-remover$a-when-boundp$a
           (implies (let* ((,keys$a (,keys$a ,hash-table))
                           (inserted (set::insert ,(if key-fixer
                                                       `(,key-fixer ,key)
                                                       key)
                                                  ,keys$a)))
                      (and (,boundp$a ,key ,hash-table)
                           (not (set::in ,(if key-fixer
                                              `(,key-fixer ,key)
                                              key)
                                         ,keys$a))
                           (,coupled-keys-p (,keys-set$a inserted ,hash-table))))
                    (,coupled-keys-p (,remover$a ,key ,hash-table)))
           :hints
           (("Goal"
             :do-not-induct t
             :in-theory (disable ,coupled-keys-p
                                 ,coupled-keys-p-necc)
             :use ((:instance ,coupled-keys-p-necc
                              (,key (,coupled-keys-p-witness (,remover$a ,default-key ,hash-table)))
                              (,hash-table (,keys-set$a (set::insert ,default-key (,keys$a ,hash-table))
                                                        ,hash-table)))
                   (:instance ,coupled-keys-p-necc
                              (,key (,coupled-keys-p-witness (,remover$a ,key ,hash-table)))
                              (,hash-table (,keys-set$a (set::insert ,key (,keys$a ,hash-table))
                                                        ,hash-table))))
             :expand (:free (,key) (,coupled-keys-p (,remover$a ,key ,hash-table))))))

         (defthm ,coupled-keys-p-of-remover$a-when-not-boundp$a
           (implies (and (not (,boundp$a ,key ,hash-table))
                         (,coupled-keys-p ,hash-table))
                    (,coupled-keys-p (,remover$a ,key ,hash-table))))

         (in-theory
           (disable ,coupled-keys-p))

         ,@(and val-coupled-p
                `((defun-sk ,coupled-vals-p (,hash-table)
                    (declare (xargs :guard (,recognizer ,hash-table)
                                    :verify-guards nil))
                    (forall ,key
                      (,val-coupled-p (,accessor$a ,key ,hash-table)))
                    :rewrite :direct)

                  (defthm ,coupled-vals-p-when-not-recognizer$a
                    (implies (not (,recognizer$a ,hash-table))
                             (,coupled-vals-p ,hash-table)))

                  (defthm ,coupled-vals-p-of-creator$a
                    (,coupled-vals-p (,creator$a)))

                  (defthm ,coupled-vals-p-of-fixer$a
                    (equal (,coupled-vals-p (,fixer$a ,hash-table))
                           (,coupled-vals-p ,hash-table)))

                  (defthm ,coupled-vals-p-of-updater$a
                    (implies (,coupled-vals-p ,hash-table)
                             (equal (,coupled-vals-p (,updater$a ,key ,val ,hash-table))
                                    (,val-coupled-p ,val)))
                    :hints
                    (("Goal"
                      :in-theory (disable ,coupled-vals-p
                                          ,coupled-vals-p-necc)
                      :use ((:instance ,coupled-vals-p-necc
                                       (,hash-table (,updater$a ,key ,val ,hash-table))))
                      :expand (:free (,key ,val)
                                     (,coupled-vals-p (,updater$a ,key ,val ,hash-table))))))

                  (defthm ,coupled-vals-p-of-remover$a
                    (implies (,coupled-vals-p ,hash-table)
                             (,coupled-vals-p (,remover$a ,key ,hash-table))))

                  (local
                    (defthmd ,coupled-vals-p-of-keys-set$a-lemma
                      (iff (,coupled-vals-p (,keys-set$a ,keys$a ,hash-table))
                           (,coupled-vals-p ,hash-table))
                      :hints
                      (("Goal"
                        :in-theory (disable ,coupled-vals-p
                                            ,coupled-vals-p-necc))
                       ("Subgoal 2"
                        :expand (:free (,keys$a)
                                       (,coupled-vals-p (,keys-set$a ,keys$a ,hash-table))))
                       ("Subgoal 1"
                        :use ((:instance ,coupled-vals-p-necc
                                         (,key (,coupled-vals-p-witness ,hash-table))
                                         (,hash-table (,keys-set$a ,keys$a ,hash-table))))
                        :expand (,coupled-vals-p ,hash-table)))))

                  (defthm ,coupled-vals-p-of-keys-set$a
                    (equal (,coupled-vals-p (,keys-set$a ,keys$a ,hash-table))
                           (,coupled-vals-p ,hash-table))
                    :hints
                    (("Goal"
                      :use ,coupled-vals-p-of-keys-set$a-lemma)))

                  (in-theory
                    (disable ,coupled-vals-p))))

         (defun-nx ,coupledp (,hash-table)
           (declare (xargs :guard (,recognizer ,hash-table)
                           :verify-guards nil))
           (and (= (set::cardinality (,keys$a ,hash-table))
                   (,count$a ,hash-table))
                (,coupled-keys-p ,hash-table)
                ,@(and val-coupled-p
                       `((,coupled-vals-p ,hash-table)))))

         (table coupledp ',hash-table ',coupledp)

         (defthm ,coupledp-when-not-recognizer$a
           (implies (not (,recognizer$a ,hash-table))
                    (,coupledp ,hash-table)))

         (defthm ,coupledp-of-creator$a
           (,coupledp (,creator$a)))

         (defthm ,coupledp-of-fixer$a
           (equal (,coupledp (,fixer$a ,hash-table))
                  (,coupledp ,hash-table)))

         (defthm ,coupledp-of-updater$a-when-boundp$a
           (implies (and (,boundp$a ,key ,hash-table)
                         (,coupledp ,hash-table))
                    ,(if val-coupled-p
                         `(equal (,coupledp (,updater$a ,key ,val ,hash-table))
                                 (,val-coupled-p ,val))
                         `(,coupledp (,updater$a ,key ,val ,hash-table)))))

         (defthm ,coupledp-of-updater$a-when-not-boundp$a
           (implies (let* ((,keys$a (,keys$a ,hash-table))
                           (trimmed (set::delete ,(if key-fixer
                                                      `(,key-fixer ,key)
                                                      key)
                                                 ,keys$a)))
                      (and (not (,boundp$a ,key ,hash-table))
                           (set::in ,(if key-fixer
                                         `(,key-fixer ,key)
                                         key)
                                    ,keys$a)
                           (,coupledp (,keys-set$a trimmed ,hash-table))))
                    ,(if val-coupled-p
                         `(equal (,coupledp (,updater$a ,key ,val ,hash-table))
                                 (,val-coupled-p ,val))
                         `(,coupledp (,updater$a ,key ,val ,hash-table)))))

         (defthm ,coupledp-of-remover$a-when-boundp$a
           (implies (let* ((,keys$a (,keys$a ,hash-table))
                           (inserted (set::insert ,(if key-fixer
                                                       `(,key-fixer ,key)
                                                       key)
                                                  ,keys$a)))
                      (and (,boundp$a ,key ,hash-table)
                           (not (set::in ,(if key-fixer
                                              `(,key-fixer ,key)
                                              key)
                                         ,keys$a))
                           (,coupledp (,keys-set$a inserted ,hash-table))))
                    (,coupledp (,remover$a ,key ,hash-table))))

         (defthm ,coupledp-of-remover$a-when-not-boundp$a
           (implies (and (not (,boundp$a ,key ,hash-table))
                         (,coupledp ,hash-table))
                    (,coupledp (,remover$a ,key ,hash-table))))

         (defthm ,cardinality-of-keys$a
           (implies (,coupledp ,hash-table)
                    (equal (set::cardinality (,keys$a ,hash-table))
                           (,count$a ,hash-table))))

         (defthm ,in-of-keys$a
           (implies (,coupledp ,hash-table)
                    (equal (set::in ,key (,keys$a ,hash-table))
                           ,(if key-recognizer
                                `(and (,key-recognizer ,key)
                                      (,boundp$a ,key ,hash-table))
                                `(,boundp$a ,key ,hash-table)))))

         ,@(and val-coupled-p
                `((defthm ,val-coupled-p-of-accessor$a
                    (implies (,coupledp ,hash-table)
                             (,val-coupled-p (,accessor$a ,key ,hash-table))))))

         (defthm ,emptyp-of-keys$a
           (implies (,coupledp ,hash-table)
                    (equal (set::emptyp (,keys$a ,hash-table))
                           (= (,count$a ,hash-table) 0))))

         (in-theory
           (disable ,coupledp))

         (defun ,copy-rec (set ,%hash-table ,hash-table)
           (declare (xargs :stobjs (,%hash-table ,hash-table)
                           :guard (and (,keysp$a set)
                                       (set::subset set (,keys ,hash-table)))))
           ,(let ((body
                   `(if (set::emptyp set)
                        ;; TODO: replace above condition with (set::emptyp
                        ;; (,keys$a-fix set)) for performance and remove let
                        ;; wrapper.
                        (,fixer ,%hash-table)
                        ,(if val-copy
                             `(let ((,key ,(if key-fixer
                                               `(,key-fixer (set::head set))
                                               '(set::head set))))
                                (stobj-let ((,val (,accessor ,key ,hash-table) ,updater))
                                           (,%hash-table)
                                           (stobj-let ((,%val (,%accessor ,key ,%hash-table) ,%updater))
                                                      (,%val)
                                                      (,val-copy ,%val ,val)
                                             ,%hash-table)
                                  (,copy-rec (set::tail set) ,%hash-table ,hash-table)))
                             `(let* ((,key (set::head set))
                                     (,val (,accessor ,key ,hash-table))
                                     (,%hash-table (,updater ,key ,val ,%hash-table)))
                                (,copy-rec (set::tail set) ,%hash-table ,hash-table))))))
              (if key-recognizer
                  `(let ((set (,keys$a-fix set)))
                     ,body)
                  body)))

         (local
           (defthm ,recognizer$a-of-copy-rec
             (,recognizer$a (,copy-rec set ,%hash-table ,hash-table))))

         (local
           (defthm ,keys$a-of-copy-rec
             (equal (,keys$a (,copy-rec set ,%hash-table ,hash-table))
                    (,keys$a ,%hash-table))))

         (local
           (defthm ,copy-rec-of-updater$a
             (implies (and (,coupledp ,hash-table)
                           (set::subset set (,keys$a ,hash-table)))
                      (equal (,copy-rec set (,updater$a ,key ,val ,%hash-table) ,hash-table)
                             (if (set::in ,(if key-fixer
                                               `(,key-fixer ,key)
                                               key)
                                          set)
                                 (,copy-rec set ,%hash-table ,hash-table)
                                 (,updater$a ,key ,val (,copy-rec set ,%hash-table ,hash-table)))))
             :hints
             (("Goal"
               :induct (,copy-rec set ,%hash-table ,hash-table)
               :in-theory (enable set::in)
               :expand (:free (,key)
                              (,copy-rec set (,updater$a ,key ,val ,%hash-table) ,hash-table)))
              ("Subgoal *1/1"
               :cases ((set::emptyp set))))))

         (local
           (defthm ,boundp$a-of-copy-rec
             (implies (and (,coupledp ,hash-table)
                           (set::subset set (,keys$a ,hash-table)))
                      (equal (,boundp$a ,key (,copy-rec set ,%hash-table ,hash-table))
                             (or (,boundp$a ,key ,%hash-table)
                                 (set::in ,(if key-fixer
                                               `(,key-fixer ,key)
                                               key)
                                          set))))
             :hints
             (("Goal"
               :induct (,copy-rec set ,%hash-table ,hash-table)
               :in-theory (enable set::in))
              ("Subgoal *1/1"
               :cases ((set::emptyp set))))))

         (local
           (defthm ,accessor$a-of-copy-rec
             (implies (and (,coupledp ,hash-table)
                           (set::subset set (,keys$a ,hash-table)))
                      (equal (,accessor$a ,key (,copy-rec set ,%hash-table ,hash-table))
                             (if (set::in ,(if key-fixer
                                               `(,key-fixer ,key)
                                               key)
                                          set)
                                 (,accessor$a ,key ,hash-table)
                                 (,accessor$a ,key ,%hash-table))))
             :hints
             (("Goal"
               :induct (,copy-rec set ,%hash-table ,hash-table)
               :in-theory (enable set::in)))))

         (local
           (defthm ,count$a-of-copy-rec
             (implies (and (,coupledp ,hash-table)
                           (set::subset set (,keys$a ,hash-table)))
                      (equal (,count$a (,copy-rec set ,%hash-table ,hash-table))
                             (cond
                               (,(if key-recognizer
                                     `(or (set::emptyp set)
                                          (not (,keysp$a set)))
                                     `(set::emptyp set))
                                (,count$a ,%hash-table))
                               ((,boundp$a (set::head set) ,%hash-table)
                                (,count$a (,copy-rec (set::tail set) ,%hash-table ,hash-table)))
                               (t
                                (1+ (,count$a (,copy-rec (set::tail set) ,%hash-table ,hash-table)))))))))

         (in-theory
           (disable ,copy-rec))

         (defun ,copy (,%hash-table ,hash-table)
           (declare (xargs :stobjs (,%hash-table ,hash-table)))
           (let* ((keys (,keys ,hash-table))
                  (count (,count ,hash-table))
                  (,%hash-table (,init count nil nil ,%hash-table))
                  (,%hash-table (,keys-set keys ,%hash-table)))
             (,copy-rec keys ,%hash-table ,hash-table)))

         (table copy ',hash-table ',copy)

         (defthm ,recognizer$a-of-copy
           (,recognizer$a (,copy ,%hash-table ,hash-table)))

         (local
           (defthm ,coupledp-of-copy/lemma-0
             (implies (and (,(if key-recognizer
                                 keysp$a
                                 'set::setp)
                             %set)
                           (,coupledp ,hash-table)
                           (set::subset set (,keys$a ,hash-table)))
                      (equal (,count$a (,copy-rec set (,keys-set$a %set (,creator$a)) ,hash-table))
                             (,count$a (,copy-rec set (,creator$a) ,hash-table))))
             :hints
             (("Goal"
               :induct (set::cardinality set)
               :in-theory (enable (:i set::cardinality))))))

         (local
           (defthm ,coupledp-of-copy/lemma-1
             (implies (and (,coupledp ,hash-table)
                           (set::subset set (,keys$a ,hash-table)))
                      (equal (,count$a (,copy-rec set (,creator$a) ,hash-table))
                             (set::cardinality set)))
             :hints
             (("Goal"
               :induct (set::cardinality set)
               :in-theory (enable set::cardinality)))))

         (local
           (defthm ,coupledp-of-copy
             (implies (,coupledp ,hash-table)
                      (,coupledp (,copy ,%hash-table ,hash-table)))
             :hints
             (("Goal"
               :in-theory (enable ,coupled-keys-p
                                  ,@(and val-coupled-p
                                         (list coupled-vals-p)))
               :expand (:free (set ,%hash-table ,hash-table)
                              (,coupledp (,copy-rec set ,%hash-table ,hash-table))))
              ("Subgoal 1"
               :expand (,coupledp ,hash-table)))))

         (defthm ,keys$a-of-copy
           (equal (,keys$a (,copy ,%hash-table ,hash-table))
                  (,keys$a ,hash-table)))

         (local
           (defthm ,boundp$a-of-copy
             (implies (,coupledp ,hash-table)
                      (equal (,boundp$a ,key (,copy ,%hash-table ,hash-table))
                             (,boundp$a ,key ,hash-table)))))

         (local
           (defthm ,accessor$a-of-copy
             (implies (,coupledp ,hash-table)
                      (equal (,accessor$a ,key (,copy ,%hash-table ,hash-table))
                             (,accessor$a ,key ,hash-table)))))

         (local
           (defthm ,count$a-of-copy
             (implies (,coupledp ,hash-table)
                      (equal (,count$a (,copy ,%hash-table ,hash-table))
                             (,count$a ,hash-table)))))

         (in-theory
           (disable ,copy))

         (defthm ,copy{rewrite}
           (implies (case-split (,coupledp ,hash-table))
                    (equal (,copy ,%hash-table ,hash-table)
                           (,fixer$a ,hash-table)))
           :hints
           (("goal"
             :do-not-induct t
             :use ((:instance ,hash-table$a-equal
                              (,%hash-table$a (,copy ,%hash-table ,hash-table))
                              (,hash-table$a (,fixer$a ,hash-table))))))))

       (deflabel ,coupledp-end)

       (deftheory-static ,coupledp-theory
         (set-difference-theories (current-theory ',coupledp-end)
                                  (current-theory ',coupledp-begin))))))

(defun make-frame-copy-events (stobj$a %stobj stobj state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp stobj$a)
                              (symbolp %stobj)
                              (symbolp stobj))
                  :verify-guards nil))
  (let* ((world (w state))
         (copier (symbolicate stobj stobj "-COPY"))
         (copier{rewrite} (symbolicate stobj copier "{REWRITE}"))

         (coupled (symbolicate stobj stobj "-COUPLED"))

         (recognizer (stobj-recognizer stobj))
         (exports (stobj$abs-exports stobj))
         (fixer (caar exports))
         (exports (cdr exports))
         (2n (len exports))
         (n (floor 2n 2))
         (accessors (loop$ :for i :from 0 :to (1- n)
                          :as export :in exports
                          :collect (car export)))
         (updaters (loop$ :for i :from 0 :to (1- n)
                         :as export :in (nthcdr n exports)
                         :collect (car export)))
         (fields (stobj$a-frame-fields stobj$a))
         (stobjs (stobj$a-frame-stobjs stobj$a))
         (field-recognizers (stobj$a-frame-recognizers stobj$a))
         (field-fixers (stobj$a-frame-fixers stobj$a))
         (stobj-copier-alist (stobj-copier-alist world))
         (field-copiers (loop$ :for stobj :in stobjs
                              :collect (and stobj
                                            (getprop stobj
                                                     'copier
                                                     nil
                                                     'acl2::current-acl2-world
                                                     stobj-copier-alist))))
         (copier-body
          (loop$ :with body := %stobj
                :with fields := (reverse fields)
                :with stobjs := (reverse stobjs)
                :with accessors := (reverse accessors)
                :with updaters := (reverse updaters)
                :with field-copiers := (reverse field-copiers)
                :do
                (progn
                  (cond
                    ((atom stobjs)
                     (return body))
                    ((car stobjs)
                     (setq body (let* ((element (car stobjs))
                                       (%element (symbolicate stobj "%" element))
                                       (accessor (car accessors))
                                       (updater (car updaters))
                                       (%accessor (symbolicate stobj "%" accessor))
                                       (%updater (symbolicate stobj "%" updater))
                                       (field-copier (car field-copiers)))
                                  `(stobj-let ((,element (,accessor ,stobj) ,updater))
                                              (,%stobj)
                                              (stobj-let ((,%element (,%accessor ,%stobj) ,%updater))
                                                         (,%element)
                                                         (,field-copier ,%element ,element)
                                                ,%stobj)
                                     ,body))))
                    (t
                     (setq body `(let* ((,(car fields) (,(car accessors) ,stobj))
                                        (,%stobj (,(car updaters) ,(car fields) ,%stobj)))
                                   ,body))))
                  (setq fields (cdr fields))
                  (setq stobjs (cdr stobjs))
                  (setq accessors (cdr accessors))
                  (setq updaters (cdr updaters))
                  (setq field-copiers (cdr field-copiers)))))
         (stobj-coupledp-alist (stobj-coupledp-alist world))
         (field-couplings (loop$ :for stobj :in stobjs
                                :collect (and stobj
                                              (getprop stobj
                                                       'coupled
                                                       nil
                                                       'acl2::current-acl2-world
                                                       stobj-coupledp-alist))))

         (stobj$a-lookup-alist (stobj$a-lookup-alist world))
         (stobjs$a (loop$ :for stobj :in stobjs
                         :collect (getprop stobj 'stobj$a
                                           nil 'acl2::current-acl2-world
                                           stobj$a-lookup-alist)))
         (stobj$a-property-alist (stobj$a-property-alist world))
         (stobj$a-properties (loop$ :for stobj$a :in stobjs$a
                                   :collect (getprop stobj$a 'stobj$a
                                                     nil 'acl2::current-acl2-world
                                                     stobj$a-property-alist)))
         (field-recognizers$a (loop$ :for stobj$a :in stobjs$a
                                    :as recognizer :in field-recognizers
                                    :as property$a :in stobj$a-properties
                                    :collect (if stobj$a
                                                 (first (second property$a))
                                                 recognizer)))
         (field-fixers$a (loop$ :for stobj$a :in stobjs$a
                               :as fixer :in field-fixers
                               :as property$a :in stobj$a-properties
                               :collect (if stobj$a
                                            (third (second property$a))
                                            fixer)))
         (stobj$a-aggressive (symbolicate stobj stobj$a "-AGGRESSIVE"))
         (%stobj$a (symbolicate stobj "%" stobj$a))
         (recognizer$a (stobj$a-recognizer stobj$a))
         (creator$a (stobj$a-creator stobj$a))
         (fixer$a (stobj$a-fixer stobj$a))
         (view$a (stobj$a-frame-view stobj$a))
         (accessors$a (stobj$a-frame-accessors stobj$a))
         (stobj$a-equal (symbolicate stobj stobj$a "-EQUAL"))

         (coupledp-when-not-recognizer$a (symbolicate stobj coupled "-WHEN-NOT-" recognizer$a))
         (coupledp-of-creator$a (symbolicate stobj coupled "-OF-" creator$a))
         (coupledp-of-fixer$a (symbolicate stobj coupled "-OF-" fixer$a))
         (coupledp-of-view$a (symbolicate stobj coupled "-OF-" view$a))

         (recognizer$a-of-copier (symbolicate stobj recognizer$a "-OF-" copier)))

    `(encapsulate ()
       ,@(let ((field-recognizers$a (remove nil field-recognizers$a))
               (field-fixers$a (remove nil field-fixers$a))
               (field-copiers (remove nil field-copiers))
               (field-couplings (remove nil field-couplings)))
           (and (or field-recognizers$a
                    field-fixers$a
                    field-copiers
                    field-couplings)
                `((local
                    (in-theory
                      (disable ,@field-recognizers$a
                               ,@field-fixers$a
                               ,@field-copiers
                               ,@field-couplings))))))

       ,@(and (remove nil field-couplings)
              `((defun-nx ,coupled (,stobj)
                  (declare (xargs :guard (,recognizer ,stobj)
                                  :verify-guards nil))
                  ,(let ((body (loop$ :for coupling :in field-couplings
                                     :as accessor$a :in accessors$a
                                     :when coupling
                                     :collect `(,coupling (,accessor$a ,stobj)))))
                     (if (consp (cdr body))
                         (cons 'and body)
                         (car body))))

                (table coupled ',stobj ',coupled)

                (defthm ,coupledp-when-not-recognizer$a
                  (implies (not (,recognizer$a ,stobj))
                           (,coupled ,stobj))
                  :hints
                  (("Goal"
                    :in-theory (enable ,stobj$a-aggressive))))

                (defthm ,coupledp-of-creator$a
                  (,coupled (,creator$a)))

                (defthm ,coupledp-of-fixer$a
                  (equal (,coupled (,fixer$a ,stobj))
                         (or (not (,recognizer$a ,stobj))
                             (,coupled ,stobj)))
                  :hints
                  (("Goal"
                    :cases ((,recognizer$a ,stobj))
                    :in-theory (disable ,coupled))))

                (defthm ,coupledp-of-view$a
                  (equal (,coupled (,view$a ,@fields ,stobj))
                         ,(let ((constraints (loop$ :for coupling :in field-couplings
                                                   :as field :in fields
                                                   :when coupling
                                                   :collect `(,coupling ,field))))
                            (if (consp (cdr constraints))
                                (cons 'and constraints)
                                (car constraints)))))

                ,@(loop$ :for accessor$a :in accessors$a
                        :as coupling :in field-couplings
                        :when coupling
                        :collect `(defthm ,(symbolicate stobj coupling "-OF-" accessor$a)
                                    (implies (coupled ,stobj)
                                             (,coupling (,accessor$a ,stobj)))))

                (in-theory
                  (disable ,coupled))))

       (defun ,copier (,%stobj ,stobj)
         (declare (xargs :stobjs (,%stobj ,stobj)))
         ,copier-body)

       (table copy ',stobj ',copier)

       (defthm ,recognizer$a-of-copier
         (,recognizer$a (,copier ,%stobj ,stobj))
         ,@(and (remove nil field-couplings)
                `(:hints
                  (("Goal"
                    :in-theory (disable (:e force)))))))

       ,@(loop$ :for accessor$a :in accessors$a
               :collect `(local
                           (defthm ,(symbolicate stobj accessor$a "-OF-" copier)
                             ,(if (remove nil field-couplings)
                                  `(implies (coupled ,stobj)
                                            (equal (,accessor$a (,copier ,%stobj ,stobj))
                                                   (,accessor$a ,stobj)))
                                  `(equal (,accessor$a (,copier ,%stobj ,stobj))
                                          (,accessor$a ,stobj))))))

       (in-theory
         (disable ,copier))

       (defthm ,copier{rewrite}
         ,(if (remove nil field-couplings)
              `(implies (coupled ,stobj)
                        (equal (,copier ,%stobj ,stobj)
                               (,fixer ,stobj)))
              `(equal (,copier ,%stobj ,stobj)
                      (,fixer ,stobj)))
         :hints
         (("Goal"
           :do-not-induct t
           :use ((:instance ,stobj$a-equal
                            (,%stobj$a (,copier ,%stobj ,stobj))
                            (,stobj$a (,fixer ,stobj))))))))))



;;;; `DEFINE-COPY'
