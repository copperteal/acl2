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
(include-book "std/lists/top" :dir :system)
(include-book "../lemmas/vector-a")
(include-book "../lemmas/hash-table-a")
|#

(include-book "../utilities/top")
(include-book "congruent")


;;; `COUPLEDP'
(encapsulate ()
  (local
    (defthm guard-lemma
      (implies (character-listp x)
               (character-listp (remove-equal a x)))))

  (defun coupledp-fn (names acc)
    (declare (xargs :guard (and (symbol-listp names)
                                (acl2::symbol-list-listp acc))))
    (if (endp names)
        (revappend acc ())
        (coupledp-fn (cdr names)
                     (cons (let ((name (car names)))
                             (list (symbolicate name (coerce (remove #\% (coerce (symbol-name name)
                                                                                 'list))
                                                             'string)
                                                "-COUPLED-P")
                                   name))
                           acc)))))

(defmacro coupledp (&rest names)
  (declare (xargs :guard (symbol-listp names)))
  (let ((expressions (coupledp-fn names ())))
    (list 'force (if (endp (cdr expressions))
                     (car expressions)
                     (cons 'and expressions)))))


;;;; `MAKE-VECTOR-COPY-EVENTS'
(defun make-vector-copy-events (vector package-witness debug state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp vector)
                              (package-witness-p package-witness)
                              (booleanp debug))
                  :verify-guards nil))
  (let* ((%vector (symbolicate package-witness "%" vector))
         (copy (symbolicate package-witness vector "-COPY"))
         (copy-rec (symbolicate package-witness copy "-REC"))
         (index (symbolicate package-witness "I"))

         (coupledp (symbolicate package-witness vector "-COUPLED-P"))
         (coupledp-witness (symbolicate package-witness coupledp "-WITNESS"))
         (coupledp-necc (symbolicate package-witness coupledp "-NECC"))

         ;; `VECTOR'
         (stobj-property (getpropc vector 'acl2::stobj))
         (recognizer (caadr stobj-property))
         (the-vector (symbolicate vector "THE-" vector))
         (length (second (third stobj-property)))
         (resizer (third (third stobj-property)))
         (accessor (fourth (third stobj-property)))
         (updater (fifth (third stobj-property)))

         ;; `VECTOR$A'
         (world (w state))
         (stobj$a-property (cdr (assoc vector (table-alist 'stobj$a-property world))))
         (vector$a (first stobj$a-property))
         (recognizer$a-aux (symbolicate vector$a vector$a "-AUX-P"))
         (vector$a-theorems (symbolicate vector$a vector$a "-THEOREMS"))
         (vector$a-aggressive (symbolicate vector$a vector$a "-AGGRESSIVE"))
         (vector$a-constraints (symbolicate vector$a vector$a "-CONSTRAINTS"))
         (recognizer$a (first (second stobj$a-property)))
         (creator$a (second (second stobj$a-property)))
         (fixer$a (third (second stobj$a-property)))
         (equiv$a (fourth (second stobj$a-property)))
         (resizable (first (second (third stobj$a-property))))
         (default-length-name (second (second (third stobj$a-property))))
         (length$a (first (third (third stobj$a-property))))
         (resizer$a (second (third (third stobj$a-property))))
         (accessor$a (third (third (third stobj$a-property))))
         (updater$a (fourth (third (third stobj$a-property))))

         (element (first (first (third stobj$a-property))))
         (%element (symbolicate element "%" element))
         (element-stobj-property (getpropc element 'acl2::stobj))
         (element-stobj$a-property (cdr (assoc element (table-alist 'stobj$a-property world))))
         (element-recognizer (second (first (third stobj$a-property))))
         (initial-element-name (third (first (third stobj$a-property))))
         (element-creator (second (second element-stobj$a-property)))
         (initial-element (if element-stobj-property
                              `(,element-creator)
                              initial-element-name))
         (element-fixer (fourth (first (third stobj$a-property))))
         (element-equiv (fifth (first (third stobj$a-property))))

         ;; Adjust for nested stobj interface shuffle
         (length (if element-stobj-property
                     (fourth (third stobj-property))
                     length))
         (resizer (if element-stobj-property
                      (fifth (third stobj-property))
                      resizer))
         (accessor (if element-stobj-property
                       (first (third stobj-property))
                       accessor))
         (%accessor (symbolicate package-witness "%" accessor))
         (updater (if element-stobj-property
                      (second (third stobj-property))
                      updater))
         (%updater (symbolicate package-witness "%" updater))

         (element-copy (cdr (assoc element (table-alist 'copy world))))
         (element-copy-theory (symbolicate element-copy element-copy "-THEORY"))
         (element-coupled-p (cdr (assoc element (table-alist 'coupledp world))))

         (copy-begin (symbolicate package-witness copy "-BEGIN"))
         (copy-end (symbolicate package-witness copy "-END"))
         (copy-theory (symbolicate package-witness copy "-THEORY"))

         ;; Theorem Names
         (element-recognizer-constraints (symbolicate "ATOMIC-STOBJS" element-recognizer "-CONSTRAINTS"))
         (element-fixer-constraints (symbolicate "ATOMIC-STOBJS" element-fixer "-CONSTRAINTS"))
         (element-equiv-constraints (symbolicate "ATOMIC-STOBJS" element-equiv "-CONSTRAINTS"))

         (coupledp-constraints (symbolicate package-witness coupledp "-CONSTRAINTS"))
         (coupledp-tp (symbolicate package-witness coupledp "-TP"))
         (coupledp-when-not-recognizer$a (symbolicate package-witness coupledp "-WHEN-NOT-" recognizer$a))
         (coupledp-of-creator$a (symbolicate package-witness coupledp "-OF-" creator$a))
         (coupledp-of-resizer$a (symbolicate package-witness coupledp "-OF-" resizer$a))
         (element-coupled-p-of-accessor$a (symbolicate package-witness element-coupled-p "-OF-" accessor$a))
         (coupledp-of-updater$a (symbolicate package-witness coupledp "-OF-" updater$a))

         (copy-rec-of-fixer$a-2 (symbolicate "ATOMIC-STOBJS" copy-rec "-OF-" fixer$a "-2"))
         (copy-rec-of-fixer$a-3 (symbolicate "ATOMIC-STOBJS" copy-rec "-OF-" fixer$a "-3"))

         (vector-copy-constraints (symbolicate package-witness copy "-CONSTRAINTS"))
         (recognizer$a-of-copy (symbolicate package-witness recognizer$a "-OF-" copy))
         (copy-ignores-1 (symbolicate package-witness copy "-IGNORES-1"))
         (coupledp-of-copy (symbolicate package-witness coupledp "-OF-" copy))
         (length$a-of-copy (symbolicate package-witness length$a "-OF-" copy))
         (copy-of-resizer$a (symbolicate package-witness copy "-OF-" resizer$a))
         (accessor$a-of-copy (symbolicate package-witness accessor$a "-OF-" copy))
         (accessor$a-of-copy-lemma (symbolicate "ATOMIC-STOBJS" accessor$a-of-copy "-LEMMA"))
         (copy-of-updater$a (symbolicate package-witness copy "-OF-" updater$a))
         (copy-of-updater$a-lemma (symbolicate "ATOMIC-STOBJS" copy-of-updater$a "-LEMMA"))
         (copy-rw (symbolicate package-witness copy "-RW"))

         (fi-bindings
          (append
           (and element-coupled-p
                (list (if resizable
                          `(lem-vector$a::coupledp/resizable-witness ,coupledp-witness)
                          `(lem-vector$a::coupledp/fixed-witness ,coupledp-witness))))

           (list `(lem-vector$a::element-coupled-p ,(or element-coupled-p
                                                        '(lambda (element)
                                                          t)))
                 (if resizable
                     `(lem-vector$a::coupledp/resizable ,(if element-coupled-p
                                                             coupledp
                                                             '(lambda (element)
                                                               t)))
                     `(lem-vector$a::coupledp/fixed ,(if element-coupled-p
                                                         coupledp
                                                         '(lambda (element)
                                                           t))))

                 `(lem-vector$a::default-length (lambda ()
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
                 `(lem-vector$a::element-equiv ,(or element-equiv
                                                    'equal))

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
                     `(lem-vector$a::equiv/resizable ,equiv$a)
                     `(lem-vector$a::equiv/fixed ,equiv$a))
                 (if resizable
                     `(lem-vector$a::length/resizable ,length$a)
                     `(lem-vector$a::length/fixed ,length$a))
                 (if resizable
                     `(lem-vector$a::resizer/resizable ,resizer$a)
                     `(lem-vector$a::resizer/fixed ,resizer$a))
                 (if resizable
                     `(lem-vector$a::accessor/resizable ,accessor$a)
                     `(lem-vector$a::accessor/fixed ,accessor$a))
                 (if resizable
                     `(lem-vector$a::updater/resizable ,updater$a)
                     `(lem-vector$a::updater/fixed ,updater$a)))))

         (fi-bindings-with-copy
          (list* `(lem-vector$a::element-copy ,(cond
                                                 (element-copy)
                                                 (element-fixer
                                                  `(lambda (%element element)
                                                     (,element-fixer element)))
                                                 (t
                                                  `(lambda (%element element)
                                                     element))))
                 (if resizable
                     `(lem-vector$a::copy/resizable-rec ,copy-rec)
                     `(lem-vector$a::copy/fixed-rec ,copy-rec))
                 (if resizable
                     `(lem-vector$a::copy/resizable ,copy)
                     `(lem-vector$a::copy/fixed ,copy))
                 fi-bindings)))

    `(progn
       (deflabel ,copy-begin)

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
             (union-theories
              (theory 'acl2::ground-zero)
              (set-difference-theories (current-theory 'prologue-end)
                                       (current-theory 'prologue-begin)))))

         ,@(and element-copy
                `((local
                    (in-theory
                      (enable ,element-copy-theory)))))

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

         (define-congruent ,vector
           :package-witness ,package-witness
           :debug ,debug)

         ;; `COUPLEDP'
         ,@(and element-coupled-p
                `((defun-sk ,coupledp (,vector)
                    (declare (xargs :guard (,recognizer ,vector)
                                    :verify-guards nil))
                    (forall ,index
                      (,element-coupled-p (,accessor$a ,index ,vector)))
                    :rewrite :direct)

                  (table coupledp ',vector ',coupledp)

                  (defthm ,coupledp-constraints
                    (and (equal (,coupledp ,vector)
                                ((lambda (,index ,vector)
                                   (,element-coupled-p (,accessor$a ,index ,vector)))
                                 (,coupledp-witness ,vector)
                                 ,vector))
                         (implies (,coupledp ,vector)
                                  (,element-coupled-p (,accessor$a ,index ,vector))))
                    :rule-classes
                    ((:definition :corollary
                         (equal (,coupledp ,vector)
                                ((lambda (,index ,vector)
                                   (,element-coupled-p (,accessor$a ,index ,vector)))
                                 (,coupledp-witness ,vector)
                                 ,vector)))
                     (:rewrite :corollary
                               (implies (,coupledp ,vector)
                                        (,element-coupled-p (,accessor$a ,index ,vector)))))
                    :hints
                    (("Goal"
                      :in-theory (disable ,coupledp-necc)
                      :use ((:instance ,coupledp-necc)))))

                  (local
                    (in-theory
                      (disable ,coupledp
                               (:definition ,coupledp-constraints))))

                  (defthm ,coupledp-tp
                    (booleanp (,coupledp ,vector))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :in-theory (enable ,vector$a-theorems)
                      :by (:functional-instance
                           ,(if resizable
                                'lem-vector$a::coupledp/resizable-tp
                                'lem-vector$a::coupledp/fixed-tp)
                           ,@fi-bindings))
                     ("Subgoal 7"
                      :use ((:instance (:definition ,coupledp-constraints)
                                       (,vector lem-vector$a::vector))))
                     ,@(if resizable
                           `(("Subgoal 6"
                              :in-theory (enable ,vector$a-constraints))
                             ("Subgoal 4"
                              :in-theory (enable ,vector$a-constraints))
                             ("Subgoal 3"
                              :in-theory (enable ,vector$a-constraints))
                             ("Subgoal 1"
                              :in-theory (enable ,vector$a-constraints)))
                           `(("Subgoal 6"
                              :in-theory (enable ,vector$a-constraints))
                             ("Subgoal 4"
                              :in-theory (enable ,vector$a-constraints))
                             ("Subgoal 3"
                              :in-theory (enable ,vector$a-constraints))
                             ("Subgoal 2"
                              :in-theory (enable ,vector$a-constraints))))))

                  (defthm ,coupledp-when-not-recognizer$a
                    (implies (not (,recognizer$a ,vector))
                             (,coupledp ,vector))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if resizable
                                'lem-vector$a::coupledp/resizable-when-not-recognizer/resizable
                                'lem-vector$a::coupledp/fixed-when-not-recognizer/fixed)
                           ,@fi-bindings))))

                  (defthm ,coupledp-of-creator$a
                    (,coupledp (,creator$a))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if resizable
                                'lem-vector$a::coupledp/resizable-of-creator
                                'lem-vector$a::coupledp/fixed-of-creator)
                           ,@fi-bindings))))

                  (defcong ,equiv$a equal (,coupledp ,vector) 1
                    :hints
                    (("Goal"
                      :in-theory (enable ,equiv$a)
                      :by (:functional-instance
                           ,(if resizable
                                'lem-vector$a::equiv/resizable-implies-equal-coupledp/resizable-1
                                'lem-vector$a::equiv/fixed-implies-equal-coupledp/fixed-1)
                           ,@fi-bindings))))

                  ,@(and resizable
                         `((defthm ,coupledp-of-resizer$a
                             (implies (,coupledp ,vector)
                                      (,coupledp (,resizer$a length ,vector)))
                             :hints
                             (("Goal"
                               :in-theory (enable ,vector$a-constraints)
                               :by (:functional-instance
                                    lem-vector$a::coupledp/resizable-of-resizer/resizable
                                    ,@fi-bindings))))))

                  (defthm ,element-coupled-p-of-accessor$a
                    (implies (,coupledp ,vector)
                             (,element-coupled-p (,accessor$a ,index ,vector)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if resizable
                                'lem-vector$a::element-coupled-p-of-accessor/resizable
                                'lem-vector$a::element-coupled-p-of-accessor/fixed)
                           ,@fi-bindings))))

                  (defthm ,coupledp-of-updater$a
                    (implies (,coupledp ,vector)
                             (equal (,coupledp (,updater$a ,index ,element ,vector))
                                    (if (< (nfix ,index)
                                           ,(if resizable
                                                `(,length$a ,vector)
                                                default-length-name))
                                        (,element-coupled-p ,element)
                                        t)))
                    :hints
                    (("Goal"
                      :in-theory (enable ,vector$a-constraints)
                      :by (:functional-instance
                           ,(if resizable
                                'lem-vector$a::coupledp/resizable-of-updater/resizable
                                'lem-vector$a::coupledp/fixed-of-updater/fixed)
                           ,@fi-bindings))))))

         ;; `COPY-REC'
         (defun ,copy-rec (,index ,%vector ,vector)
           (declare (xargs :stobjs (,%vector ,vector)
                           :guard (and (= (,length ,%vector) (,length ,vector))
                                       (natp ,index)
                                       (<= ,index (,length ,vector)))
                           :guard-hints
                           (("Goal"
                             :in-theory (enable ,vector$a-theorems
                                                ,vector$a-aggressive)))))
           (if (zp ,index)
               (,the-vector ,%vector)
               ,(if element-copy
                    `(let ((,index (1- ,index)))
                       (stobj-let ((,element (,accessor ,index ,vector) ,updater))
                                  (,%vector)
                                  (stobj-let ((,%element (,%accessor ,index ,%vector) ,%updater))
                                             (,%element)
                                             (,element-copy ,%element ,element)
                                    ,%vector)
                         (,copy-rec ,index ,%vector ,vector)))
                    `(let* ((,index (1- ,index))
                            (,element (,accessor ,index ,vector))
                            (,%vector (,updater ,index ,element ,%vector)))
                       (,copy-rec ,index ,%vector ,vector)))))

         ;; `COPY'
         (defun ,copy (,%vector ,vector)
           (declare (xargs :stobjs (,%vector ,vector)
                           :guard-hints
                           (("Goal"
                             :in-theory (enable ,vector$a-theorems
                                                ,vector$a-aggressive)))))
           ,(if resizable
                `(let* ((length (,length ,vector))
                        (,%vector (if (= (,length ,%vector) length)
                                      (,the-vector ,%vector)
                                      (,resizer length ,%vector))))
                   (,copy-rec length ,%vector ,vector))
                `(,copy-rec ,default-length-name ,%vector ,vector)))

         (table copy ',vector ',copy)

         (local
           (defthmd ,copy-rec-of-fixer$a-2
             (equal (,copy-rec ,index (,fixer$a ,%vector) ,vector)
                    (,copy-rec ,index ,%vector ,vector))
             :hints
             (("Goal"
               :induct (,copy-rec ,index ,%vector ,vector)
               :in-theory (enable ,vector$a-theorems)))))

         (local
           (defthmd ,copy-rec-of-fixer$a-3
             (equal (,copy-rec ,index ,%vector (,fixer$a ,vector))
                    (,copy-rec ,index ,%vector ,vector))
             :hints
             (("Goal"
               :induct (,copy-rec ,index ,%vector ,vector)
               :in-theory (enable ,vector$a-theorems)
               :expand (,copy-rec ,index ,%vector (,fixer$a ,vector))))))

         (defthm ,vector-copy-constraints
           (and (equal (,copy-rec ,index ,%vector ,vector)
                       (if (zp ,index)
                           (,fixer$a ,%vector)
                           ((lambda (,index ,%vector ,vector)
                              ((lambda (,element ,vector ,%vector ,index)
                                 ((lambda (,%element ,index ,%vector ,vector ,element)
                                    (declare (ignorable ,%element))
                                    ((lambda (,%element ,element ,vector ,%vector ,index)
                                       ((lambda (,%vector ,vector ,element ,index)
                                          ((lambda (,vector ,%vector ,index)
                                             (,copy-rec ,index ,%vector ,vector))
                                           (,updater$a ,index ,element ,vector)
                                           ,%vector ,index))
                                        (,updater$a ,index ,%element ,%vector)
                                        ,vector ,element ,index))
                                     ,(cond
                                        (element-copy
                                         `(,element-copy ,%element ,element))
                                        (element-fixer
                                         `(,element-fixer ,element))
                                        (t
                                         element))
                                     ,element ,vector ,%vector ,index))
                                  (,accessor$a ,index ,%vector)
                                  ,index ,%vector ,vector ,element))
                               (,accessor$a ,index ,vector)
                               ,vector ,%vector ,index))
                            (binary-+ '-1 ,index)
                            ,%vector ,vector)))
                (equal (,copy ,%vector ,vector)
                       ((lambda (length ,vector ,%vector)
                          ((lambda (,%vector ,vector length)
                             (,copy-rec length ,%vector ,vector))
                           ,(if resizable
                                `(if (equal (,length$a ,%vector)
                                            length)
                                     ,%vector
                                     (,resizer$a length ,%vector))
                                %vector)
                           ,vector length))
                        (,length$a ,vector)
                        ,vector ,%vector)))
           :rule-classes
           ((:definition :corollary
                (equal (,copy-rec ,index ,%vector ,vector)
                       (if (zp ,index)
                           (,fixer$a ,%vector)
                           ((lambda (,index ,%vector ,vector)
                              ((lambda (,element ,vector ,%vector ,index)
                                 ((lambda (,%element ,index ,%vector ,vector ,element)
                                    (declare (ignorable ,%element))
                                    ((lambda (,%element ,element ,vector ,%vector ,index)
                                       ((lambda (,%vector ,vector ,element ,index)
                                          ((lambda (,vector ,%vector ,index)
                                             (,copy-rec ,index ,%vector ,vector))
                                           (,updater$a ,index ,element ,vector)
                                           ,%vector ,index))
                                        (,updater$a ,index ,%element ,%vector)
                                        ,vector ,element ,index))
                                     ,(cond
                                        (element-copy
                                         `(,element-copy ,%element ,element))
                                        (element-fixer
                                         `(,element-fixer ,element))
                                        (t
                                         element))
                                     ,element ,vector ,%vector ,index))
                                  (,accessor$a ,index ,%vector)
                                  ,index ,%vector ,vector ,element))
                               (,accessor$a ,index ,vector)
                               ,vector ,%vector ,index))
                            (binary-+ '-1 ,index)
                            ,%vector ,vector))))
            (:definition :corollary
                (equal (,copy ,%vector ,vector)
                       ((lambda (length ,vector ,%vector)
                          ((lambda (,%vector ,vector length)
                             (,copy-rec length ,%vector ,vector))
                           ,(if resizable
                                `(if (equal (,length$a ,%vector)
                                            length)
                                     ,%vector
                                     (,resizer$a length ,%vector))
                                %vector)
                           ,vector length))
                        (,length$a ,vector)
                        ,vector ,%vector))))
           :hints
           (("Goal"
             :do-not-induct t
             :in-theory (enable ,vector$a-theorems
                                ,vector$a-aggressive
                                ,copy-rec-of-fixer$a-3
                                ,copy-rec-of-fixer$a-2))))

         (local
           (in-theory
             (disable ,copy-rec
                      ,copy)))

         (defthm ,recognizer$a-of-copy
           (,recognizer$a (,copy ,%vector ,vector))
           :hints
           (("Goal"
             :do-not-induct t
             :in-theory (enable ,vector$a-constraints)
             :by (:functional-instance
                  ,(if resizable
                       'lem-vector$a::recognizer/resizable-of-copy/resizable
                       'lem-vector$a::recognizer/fixed-of-copy/fixed)
                  ,@fi-bindings-with-copy))))

         (defthm ,copy-ignores-1
           (equal (,copy ,%vector ,vector)
                  (,copy (,creator$a) ,vector))
           :rule-classes
           ((:rewrite :corollary
                      (implies (syntaxp (not (and (consp ,%vector)
                                                  (eq (car ,%vector) ',creator$a))))
                               (equal (,copy ,%vector ,vector)
                                      (,copy (,creator$a) ,vector)))))
           :hints
           (("Goal"
             :by (:functional-instance
                  ,(if resizable
                       'lem-vector$a::copy/resizable-ignores-1
                       'lem-vector$a::copy/fixed-ignores-1)
                  ,@fi-bindings-with-copy))))

         (defcong ,equiv$a equal (,copy ,%vector ,vector) 2
           :hints
           (("Goal"
             :in-theory (enable ,vector$a-constraints)
             :by (:functional-instance
                  ,(if resizable
                       'lem-vector$a::equiv/resizable-implies-equal-copy/resizable-2
                       'lem-vector$a::equiv/fixed-implies-equal-copy/fixed-2)
                  ,@fi-bindings-with-copy))))

         ,@(and element-coupled-p
                `((defthm ,coupledp-of-copy
                    (,coupledp (,copy ,%vector ,vector))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if resizable
                                'lem-vector$a::coupledp/resizable-of-copy/resizable
                                'lem-vector$a::coupledp/fixed-of-copy/fixed)
                           ,@fi-bindings-with-copy))))))

         ,@(and resizable
                `((defthm ,length$a-of-copy
                    (equal (,length$a (,copy ,%vector ,vector))
                           (,length$a ,vector))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-vector$a::length/resizable-of-copy/resizable
                           ,@fi-bindings-with-copy))))

                  (defthm ,copy-of-resizer$a
                    (equal (,copy ,%vector (,resizer$a length ,vector))
                           (,resizer$a length (,copy ,%vector ,vector)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-vector$a::copy/resizable-of-resizer/resizable
                           ,@fi-bindings-with-copy))))))

         (local
           (defthmd ,accessor$a-of-copy-lemma
             (equal (,accessor$a ,index (,copy ,%vector ,vector))
                    ,(cond
                       (element-copy
                        `(,element-copy ,initial-element (,accessor$a ,index ,vector)))
                       (element-fixer
                        `(,element-fixer (,accessor$a ,index ,vector)))
                       (t
                        `((lambda (x) x) (,accessor$a ,index ,vector)))))
             :hints
             (("Goal"
               :by (:functional-instance
                    ,(if resizable
                         'lem-vector$a::accessor/resizable-of-copy/resizable
                         'lem-vector$a::accessor/fixed-of-copy/fixed)
                    ,@fi-bindings-with-copy)))))

         (defthm ,accessor$a-of-copy
           (equal (,accessor$a ,index (,copy ,%vector ,vector))
                  ,(if element-copy
                       `(,element-copy ,initial-element (,accessor$a ,index ,vector))
                       `(,accessor$a ,index ,vector)))
           :hints
           (("Goal"
             :use ,accessor$a-of-copy-lemma)))

         (local
           (defthmd ,copy-of-updater$a-lemma
             (equal (,copy ,%vector (,updater$a ,index ,element ,vector))
                    (if (< (nfix ,index) ,(if resizable
                                              `(,length$a ,vector)
                                              default-length-name))
                        (,updater$a ,index
                                    ,(cond
                                       (element-copy
                                        `(,element-copy ,initial-element ,element))
                                       (element-fixer
                                        `(,element-fixer ,element))
                                       (t
                                        `((lambda (x) x) ,element)))
                                    (,copy ,%vector ,vector))
                        (,copy ,%vector ,vector)))
             :hints
             (("Goal"
               :by (:functional-instance
                    ,(if resizable
                         'lem-vector$a::copy/resizable-of-updater/resizable
                         'lem-vector$a::copy/fixed-of-updater/fixed)
                    ,@fi-bindings-with-copy)))))

         (defthm ,copy-of-updater$a
           (equal (,copy ,%vector (,updater$a ,index ,element ,vector))
                  (if (< (nfix ,index) ,(if resizable
                                            `(,length$a ,vector)
                                            default-length-name))
                      (,updater$a ,index
                                  ,(if element-copy
                                       `(,element-copy ,initial-element ,element)
                                       element)
                                  (,copy ,%vector ,vector))
                      (,copy ,%vector ,vector)))
           :hints
           (("Goal"
             :in-theory (enable ,vector$a-aggressive)
             :use ,copy-of-updater$a-lemma)))

         (defthm ,copy-rw
           ,(if element-coupled-p
                `(implies (,coupledp ,vector)
                          (equal (,copy ,%vector ,vector)
                                 (,fixer$a ,vector)))
                `(equal (,copy ,%vector ,vector)
                        (,fixer$a ,vector)))
           :hints
           (("Goal"
             :by (:functional-instance
                  ,(if resizable
                       'lem-vector$a::copy/resizable-rw
                       'lem-vector$a::copy/fixed-rw)
                  ,@fi-bindings-with-copy)))))

       (deflabel ,copy-end)

       (deftheory-static ,copy-theory
         (set-difference-theories
          (set-difference-theories (current-theory ',copy-end)
                                   (current-theory ',copy-begin))
          '(,@(and element-coupled-p
                   `(,coupledp
                     ,coupledp-constraints))
            ,copy-rec
            ,copy
            ,vector-copy-constraints)))

       (in-theory
         (union-theories (current-theory ',copy-begin)
                         (theory ',copy-theory))))))


;;;; `MAKE-HASH-TABLE-COPY-EVENTS'
(defun make-hash-table-copy-events (hash-table package-witness debug state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp hash-table)
                              (package-witness-p package-witness)
                              (booleanp debug))
                  :verify-guards nil))
  (let* ((%hash-table (symbolicate package-witness "%" hash-table))
         (copy (symbolicate package-witness hash-table "-COPY"))
         (copy-rec (symbolicate package-witness copy "-REC"))

         (coupledp (symbolicate package-witness hash-table "-COUPLED-P"))
         (coupled-keys-p (symbolicate package-witness hash-table "-COUPLED-KEYS-P"))
         (coupled-keys-p-witness (symbolicate package-witness coupled-keys-p "-WITNESS"))
         (coupled-keys-p-necc (symbolicate package-witness coupled-keys-p "-NECC"))
         (coupled-vals-p (symbolicate package-witness hash-table "-COUPLED-VALS-P"))
         (coupled-vals-p-witness (symbolicate package-witness coupled-vals-p "-WITNESS"))
         (coupled-vals-p-necc (symbolicate package-witness coupled-vals-p "-NECC"))

         ;; `HASH-TABLE'
         (stobj-property (getpropc hash-table 'acl2::stobj))
         (recognizer (caadr stobj-property))
         (the-hash-table (symbolicate hash-table "THE-" hash-table))
         (accessor (second (third stobj-property)))
         (updater (third (third stobj-property)))
         (count (seventh (third stobj-property)))
         (init (ninth (third stobj-property)))
         (keys (tenth (third stobj-property)))
         (keys-set (nth 10 (third stobj-property)))

         ;; `HASH-TABLE$A'
         (world (w state))
         (stobj$a-property (cdr (assoc hash-table (table-alist 'stobj$a-property world))))
         (hash-table$a (first stobj$a-property))
         (hash-table$a-theorems (symbolicate hash-table$a hash-table$a "-THEOREMS"))
         (hash-table$a-aggressive (symbolicate hash-table$a hash-table$a "-AGGRESSIVE"))
         (hash-table$a-constraints (symbolicate hash-table$a hash-table$a "-CONSTRAINTS"))
         (recognizer$a (first (second stobj$a-property)))
         (creator$a (second (second stobj$a-property)))
         (fixer$a (third (second stobj$a-property)))
         (equiv$a (fourth (second stobj$a-property)))
         (accessor$a (first (fourth (third stobj$a-property))))
         (updater$a (second (fourth (third stobj$a-property))))
         (boundp$a (third (fourth (third stobj$a-property))))
         (getp$a (fourth (fourth (third stobj$a-property))))
         (remover$a (fifth (fourth (third stobj$a-property))))
         (count$a (sixth (fourth (third stobj$a-property))))
         (clear$a (seventh (fourth (third stobj$a-property))))
         (init$a (eighth (fourth (third stobj$a-property))))
         (keys$a (first (fifth (third stobj$a-property))))
         (keys$a-set (second (fifth (third stobj$a-property))))
         (keys$ap (third (fifth (third stobj$a-property))))
         (keys$a-fix (fourth (fifth (third stobj$a-property))))

         (contents$a (symbolicate hash-table$a hash-table$a "-CONTENTS"))
         (contents-recognizer$a (symbolicate hash-table$a contents$a "-P"))
         (contents-creator$a (symbolicate hash-table$a "CREATE-" contents$a))
         (contents-fixer$a (symbolicate hash-table$a contents$a "-FIX"))
         (contents-accessor$a (symbolicate hash-table$a contents$a "-GET"))
         (contents-updater$a (symbolicate hash-table$a contents$a "-PUT"))
         (contents-boundp$a (symbolicate hash-table$a contents$a "-BNDP"))
         (contents-getp$a (symbolicate hash-table$a contents$a "-GETP"))
         (contents-remover$a (symbolicate hash-table$a contents$a "-REM"))
         (contents-count$a (symbolicate hash-table$a contents$a "-CNT"))
         (contents-clear$a (symbolicate hash-table$a contents$a "-CLR"))
         (contents-init$a (symbolicate hash-table$a contents$a "-INIT"))

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

         ;; Adjust for nested stobj interface shuffle
         (accessor (if val-stobj-property
                       (first (third stobj-property))
                       accessor))
         (%accessor (symbolicate package-witness "%" accessor))
         (updater (if val-stobj-property
                      (second (third stobj-property))
                      updater))
         (%updater (symbolicate package-witness "%" updater))

         (val-copy (cdr (assoc val (table-alist 'copy world))))
         (val-copy-theory (symbolicate val-copy val-copy "-THEORY"))
         (val-coupled-p (cdr (assoc val (table-alist 'coupledp world))))

         (copy-begin (symbolicate package-witness copy "-BEGIN"))
         (copy-end (symbolicate package-witness copy "-END"))
         (copy-theory (symbolicate package-witness copy "-THEORY"))

         ;; Theorem Names
         (key-recognizer-constraints (symbolicate "ATOMIC-STOBJS" key-recognizer "-CONSTRAINTS"))
         (key-fixer-constraints (symbolicate "ATOMIC-STOBJS" key-fixer "-CONSTRAINTS"))
         (key-equiv-constraints (symbolicate "ATOMIC-STOBJS" key-equiv "-CONSTRAINTS"))

         (val-recognizer-constraints (symbolicate "ATOMIC-STOBJS" val-recognizer "-CONSTRAINTS"))
         (val-fixer-constraints (symbolicate "ATOMIC-STOBJS" val-fixer "-CONSTRAINTS"))
         (val-equiv-constraints (symbolicate "ATOMIC-STOBJS" val-equiv "-CONSTRAINTS"))

         (coupledp-constraints (symbolicate package-witness coupledp "-CONSTRAINTS"))
         (coupledp-tp (symbolicate package-witness coupledp "-TP"))
         (coupledp-when-not-recognizer$a (symbolicate package-witness coupledp "-WHEN-NOT-" recognizer$a))
         (coupledp-of-creator$a (symbolicate package-witness coupledp "-OF-" creator$a))
         (val-coupled-p-of-accessor$a (symbolicate package-witness val-coupled-p "-OF-" accessor$a))
         (coupledp-of-updater$a-when-boundp$a (symbolicate package-witness coupledp "-OF-" updater$a "-WHEN-" boundp$a))
         (coupledp-of-updater$a-when-not-boundp$a (symbolicate package-witness coupledp "-OF-" updater$a "-WHEN-NOT-" boundp$a))
         (in-of-keys$a-when-coupledp (symbolicate package-witness "IN-OF-" keys$a "-WHEN-" coupledp))
         (coupledp-of-remover$a-when-boundp$a (symbolicate package-witness coupledp "-OF-" remover$a "-WHEN-" boundp$a))
         (coupledp-of-remover$a-when-not-boundp$a (symbolicate package-witness coupledp "-OF-" remover$a "-WHEN-NOT-" boundp$a))
         (cardinality-of-keys$a-when-coupledp (symbolicate package-witness "CARDINALITY-OF-" keys$a "-WHEN-" coupledp))
         (emptyp-of-keys$a-when-coupledp (symbolicate package-witness "EMPTYP-OF-" keys$a "-WHEN-" coupledp))

         (copy-rec-of-updater$a-2 (symbolicate "ATOMIC-STOBJS" copy-rec "-OF-" updater$a "-2"))
         (copy-rec-of-updater$a-3 (symbolicate "ATOMIC-STOBJS" copy-rec "-OF-" updater$a "-3"))
         (copy-rec-of-fixer$a-3 (symbolicate "ATOMIC-STOBJS" copy-rec "-OF-" fixer$a "-3"))

         (hash-table-copy-constraints (symbolicate package-witness copy "-CONSTRAINTS"))
         (recognizer$a-of-copy (symbolicate package-witness recognizer$a "-OF-" copy))
         (copy-ignores-1 (symbolicate package-witness copy "-IGNORES-1"))
         (coupledp-of-copy (symbolicate package-witness coupledp "-OF-" copy))
         (accessor$a-of-copy (symbolicate package-witness accessor$a "-OF-" copy))
         (accessor$a-of-copy-lemma (symbolicate "ATOMIC-STOBJS" accessor$a-of-copy "-LEMMA"))
         (copy-of-updater$a (symbolicate package-witness copy "-OF-" updater$a))
         (copy-of-updater$a-lemma (symbolicate "ATOMIC-STOBJS" copy-of-updater$a "-LEMMA"))
         (boundp$a-of-copy (symbolicate package-witness boundp$a "-OF-" copy))
         (copy-of-remover$a (symbolicate package-witness copy "-OF-" remover$a))
         (count$a-of-copy (symbolicate package-witness count$a "-OF-" copy))
         (keys$a-of-copy (symbolicate package-witness keys$a "-OF-" copy))
         (copy-rw (symbolicate package-witness copy "-RW"))

         (fi-bindings
          (append
           (and val-coupled-p
                (list `(lem-hash-table$a::coupled-vals-p-witness ,coupled-vals-p-witness)))
           (list `(lem-hash-table$a::val-coupled-p ,(or val-coupled-p
                                                        '(lambda (val)
                                                          t)))
                 `(lem-hash-table$a::coupled-keys-p ,coupled-keys-p)
                 `(lem-hash-table$a::coupled-keys-p-witness ,coupled-keys-p-witness)
                 `(lem-hash-table$a::coupled-vals-p ,(if val-coupled-p
                                                         coupled-vals-p
                                                         '(lambda (hash-table)
                                                           t)))
                 `(lem-hash-table$a::coupledp ,coupledp)

                 `(lem-hash-table$a::key-recognizer ,(or key-recognizer
                                                         '(lambda (key)
                                                           t)))
                 `(lem-hash-table$a::default-key (lambda ()
                                                   ,default-key-name))
                 `(lem-hash-table$a::key-fixer ,(or key-fixer
                                                    '(lambda (key)
                                                      key)))
                 `(lem-hash-table$a::key-equiv ,(or key-equiv
                                                    'equal))

                 `(lem-hash-table$a::val-recognizer ,(or val-recognizer
                                                         '(lambda (val)
                                                           t)))
                 `(lem-hash-table$a::default-val ,(or val-creator
                                                      `(lambda ()
                                                         ,default-val-name)))
                 `(lem-hash-table$a::val-fixer ,(or val-fixer
                                                    '(lambda (val)
                                                      val)))
                 `(lem-hash-table$a::val-equiv ,(or val-equiv
                                                    'equal))

                 `(lem-hash-table$a::keysp ,keys$ap)
                 `(lem-hash-table$a::keys-fix ,keys$a-fix)
                 `(lem-hash-table$a::recognizer/unique ,contents-recognizer$a)
                 `(lem-hash-table$a::creator/unique ,contents-creator$a)
                 `(lem-hash-table$a::fixer/unique ,contents-fixer$a)
                 `(lem-hash-table$a::accessor/unique ,contents-accessor$a)
                 `(lem-hash-table$a::updater/unique ,contents-updater$a)
                 `(lem-hash-table$a::boundp/unique ,contents-boundp$a)
                 `(lem-hash-table$a::getp/unique ,contents-getp$a)
                 `(lem-hash-table$a::remover/unique ,contents-remover$a)
                 `(lem-hash-table$a::count/unique ,contents-count$a)
                 `(lem-hash-table$a::clear/unique ,contents-clear$a)
                 `(lem-hash-table$a::init/unique ,contents-init$a)

                 `(lem-hash-table$a::recognizer/copyable ,recognizer$a)
                 `(lem-hash-table$a::creator/copyable ,creator$a)
                 `(lem-hash-table$a::fixer/copyable ,fixer$a)
                 `(lem-hash-table$a::equiv/copyable ,equiv$a)
                 `(lem-hash-table$a::accessor/copyable ,accessor$a)
                 `(lem-hash-table$a::updater/copyable ,updater$a)
                 `(lem-hash-table$a::boundp/copyable ,boundp$a)
                 `(lem-hash-table$a::getp/copyable ,getp$a)
                 `(lem-hash-table$a::remover/copyable ,remover$a)
                 `(lem-hash-table$a::count/copyable ,count$a)
                 `(lem-hash-table$a::clear/copyable ,clear$a)
                 `(lem-hash-table$a::init/copyable ,init$a)
                 `(lem-hash-table$a::keys ,keys$a)
                 `(lem-hash-table$a::keys-set ,keys$a-set))))

         (fi-bindings-with-copy
          (list* `(lem-hash-table$a::val-copy ,(cond
                                                 (val-copy)
                                                 (val-fixer
                                                  `(lambda (%val val)
                                                     (,val-fixer val)))
                                                 (t
                                                  `(lambda (%val val)
                                                     val))))
                 `(lem-hash-table$a::copy-rec ,copy-rec)
                 `(lem-hash-table$a::copy ,copy)
                 fi-bindings)))

    `(progn
       (deflabel ,copy-begin)

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
             (union-theories
              (theory 'acl2::ground-zero)
              (set-difference-theories (current-theory 'prologue-end)
                                       (current-theory 'prologue-begin)))))

         ,@(and val-copy
                `((local
                    (in-theory
                      (enable ,val-copy-theory)))))

         (local
           (in-theory
             (enable (:e set::emptyp)
                     set::setp-type
                     set::sets-are-true-lists-compound-recognizer
                     set::tail-produces-set
                     set::never-in-empty
                     set::subset-reflexive
                     set::head-unique)))

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

         (define-congruent ,hash-table
           :package-witness ,package-witness
           :debug ,debug)

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

         ;; `COUPLED-VALS-P'
         ,@(and val-coupled-p
                `((defun-sk ,coupled-vals-p (,hash-table)
                    (declare (xargs :guard (,recognizer ,hash-table)
                                    :verify-guards nil))
                    (forall ,key
                      (,val-coupled-p (,accessor$a ,key ,hash-table)))
                    :rewrite :direct)))

         ;; `COUPLEDP'
         (defun-nx ,coupledp (,hash-table)
           (declare (xargs :guard (,recognizer ,hash-table)
                           :verify-guards nil))
           (and (= (set::cardinality (,keys$a ,hash-table))
                   (,count$a ,hash-table))
                (,coupled-keys-p ,hash-table)
                ,@(and val-coupled-p
                       `((,coupled-vals-p ,hash-table)))))

         (table coupledp ',hash-table ',coupledp)

         (defthm ,coupledp-constraints
           (and (equal (,coupled-keys-p ,hash-table)
                       ((lambda (,key ,hash-table)
                          (equal (set::in ,key (,keys$a ,hash-table))
                                 ,(if key-recognizer
                                      `(if (,key-recognizer ,key)
                                           (,boundp$a ,key ,hash-table)
                                           'nil)
                                      `(,boundp$a ,key ,hash-table))))
                        (,coupled-keys-p-witness ,hash-table)
                        ,hash-table))
                (implies (,coupled-keys-p ,hash-table)
                         (equal (set::in ,key (,keys$a ,hash-table))
                                ,(if key-recognizer
                                     `(if (,key-recognizer ,key)
                                          (,boundp$a ,key ,hash-table)
                                          'nil)
                                     `(,boundp$a ,key ,hash-table))))
                ,@(and val-coupled-p
                       `((equal (,coupled-vals-p ,hash-table)
                                ((lambda (,key ,hash-table)
                                   (,val-coupled-p (,accessor$a ,key ,hash-table)))
                                 (,coupled-vals-p-witness ,hash-table)
                                 ,hash-table))
                         (implies (,coupled-vals-p ,hash-table)
                                  (,val-coupled-p (,accessor$a ,key ,hash-table)))))
                (equal (,coupledp ,hash-table)
                       (if (equal (set::cardinality (,keys$a ,hash-table))
                                  (,count$a ,hash-table))
                           ,(if val-coupled-p
                                `(if (,coupled-keys-p ,hash-table)
                                     (,coupled-vals-p ,hash-table)
                                     'nil)
                                `(,coupled-keys-p ,hash-table))
                           'nil)))
           :rule-classes
           ((:definition :corollary
                (equal (,coupled-keys-p ,hash-table)
                       ((lambda (,key ,hash-table)
                          (equal (set::in ,key (,keys$a ,hash-table))
                                 ,(if key-recognizer
                                      `(if (,key-recognizer ,key)
                                           (,boundp$a ,key ,hash-table)
                                           'nil)
                                      `(,boundp$a ,key ,hash-table))))
                        (,coupled-keys-p-witness ,hash-table)
                        ,hash-table)))
            (:rewrite :corollary
                      (implies (,coupled-keys-p ,hash-table)
                               (equal (set::in ,key (,keys$a ,hash-table))
                                      ,(if key-recognizer
                                           `(if (,key-recognizer ,key)
                                                (,boundp$a ,key ,hash-table)
                                                'nil)
                                           `(,boundp$a ,key ,hash-table)))))
            ,@(and val-coupled-p
                   `((:definition :corollary
                         (equal (,coupled-vals-p ,hash-table)
                                ((lambda (,key ,hash-table)
                                   (,val-coupled-p (,accessor$a ,key ,hash-table)))
                                 (,coupled-vals-p-witness ,hash-table)
                                 ,hash-table)))
                     (:rewrite :corollary
                               (implies (,coupled-vals-p ,hash-table)
                                        (,val-coupled-p (,accessor$a ,key ,hash-table))))))
            (:definition :corollary
                (equal (,coupledp ,hash-table)
                       (if (equal (set::cardinality (,keys$a ,hash-table))
                                  (,count$a ,hash-table))
                           ,(if val-coupled-p
                                `(if (,coupled-keys-p ,hash-table)
                                     (,coupled-vals-p ,hash-table)
                                     'nil)
                                `(,coupled-keys-p ,hash-table))
                           'nil))))
           :hints
           (("Goal"
             :in-theory (disable ,coupled-keys-p-necc
                                 ,@(and val-coupled-p
                                        `(,coupled-vals-p-necc)))
             :use ((:instance ,coupled-keys-p-necc)
                   ,@(and val-coupled-p
                          `((:instance ,coupled-vals-p-necc)))))))

         (local
           (in-theory
             (disable ,coupledp
                      ,coupled-keys-p
                      (:definition ,coupledp-constraints . 1)
                      ,@(and val-coupled-p
                             `(,coupled-vals-p
                               (:definition ,coupledp-constraints . 2))))))

         (defthm ,coupledp-tp
           (booleanp (,coupledp ,hash-table))
           :rule-classes :type-prescription
           :hints
           (("Goal"
             :in-theory (enable ,hash-table$a-constraints)
             :by (:functional-instance
                  lem-hash-table$a::coupledp-tp
                  ,@fi-bindings))
            ,@(and val-coupled-p
                   key-recognizer
                   `(("Subgoal 14"
                      :in-theory (e/d (,hash-table$a-constraints)
                                      (,coupled-vals-p-necc))
                      :use ((:instance ,coupled-vals-p-necc
                                       (,hash-table lem-hash-table$a::hash-table)
                                       (,key lem-hash-table$a::key))))
                     ("Subgoal 13"
                      :use ((:instance (:definition ,coupledp-constraints . 2)
                                       (,hash-table lem-hash-table$a::hash-table))))))
            ,@(and val-coupled-p
                   (not key-recognizer)
                   `(("Subgoal 13"
                      :in-theory (e/d (,hash-table$a-constraints)
                                      (,coupled-vals-p-necc))
                      :use ((:instance ,coupled-vals-p-necc
                                       (,hash-table lem-hash-table$a::hash-table)
                                       (,key lem-hash-table$a::key))))
                     ("Subgoal 12"
                      :use ((:instance (:definition ,coupledp-constraints . 2)
                                       (,hash-table lem-hash-table$a::hash-table))))))
            ("Subgoal 4"
             :in-theory (e/d (,hash-table$a-constraints)
                             (,coupled-keys-p-necc))
             :use ((:instance ,coupled-keys-p-necc
                              (,hash-table lem-hash-table$a::hash-table)
                              (,key lem-hash-table$a::key))))
            ("Subgoal 3"
             :use ((:instance (:definition ,coupledp-constraints . 1)
                              (,hash-table lem-hash-table$a::hash-table))))))

         (defthm ,coupledp-when-not-recognizer$a
           (implies (not (,recognizer$a ,hash-table))
                    (,coupledp ,hash-table))
           :hints
           (("Goal"
             :do-not-induct t
             :by (:functional-instance
                  lem-hash-table$a::coupledp-when-not-recognizer/copyable
                  ,@fi-bindings))))

         (defthm ,coupledp-of-creator$a
           (,coupledp (,creator$a))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::coupledp-of-creator/copyable
                  ,@fi-bindings))))

         (defcong ,equiv$a equal (,coupledp ,hash-table) 1
           :hints
           (("Goal"
             :in-theory (enable ,equiv$a)
             :by (:functional-instance
                  lem-hash-table$a::equiv/copyable-implies-equal-coupledp-1
                  ,@fi-bindings))))

         ,@(and val-coupled-p
                `((defthm ,val-coupled-p-of-accessor$a
                    (implies (,coupledp ,hash-table)
                             (,val-coupled-p (,accessor$a ,key ,hash-table)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-hash-table$a::val-coupled-p-of-accessor/copyable
                           ,@fi-bindings))))))

         (defthm ,coupledp-of-updater$a-when-boundp$a
           (implies (and (,boundp$a ,key ,hash-table)
                         (,coupledp ,hash-table))
                    (equal (,coupledp (,updater$a ,key ,val ,hash-table))
                           ,(if val-coupled-p
                                `(,val-coupled-p ,val)
                                't)))
           :hints
           (("Goal"
             :do-not-induct t
             :in-theory (enable ,hash-table$a-constraints)
             :by (:functional-instance
                  lem-hash-table$a::coupledp-of-updater/copyable-when-boundp/copyable
                  ,@fi-bindings))))

         (defthm ,coupledp-of-updater$a-when-not-boundp$a
           (implies (let* ((,keys$a (,keys$a ,hash-table))
                           (trimmed (set::delete ,(if key-fixer `(,key-fixer ,key) key) ,keys$a)))
                      (and (not (,boundp$a ,key ,hash-table))
                           (set::in ,(if key-fixer `(,key-fixer ,key) key) ,keys$a)
                           (,coupledp (,keys$a-set trimmed ,hash-table))))
                    (equal (,coupledp (,updater$a ,key ,val ,hash-table))
                           ,(if val-coupled-p
                                `(,val-coupled-p ,val)
                                't)))
           :hints
           (("Goal"
             :do-not-induct t
             :in-theory (enable ,hash-table$a-constraints)
             :by (:functional-instance
                  lem-hash-table$a::coupledp-of-updater/copyable-when-not-boundp/copyable
                  ,@fi-bindings))))

         (defthm ,in-of-keys$a-when-coupledp
           (implies (,coupledp ,hash-table)
                    (equal (set::in ,key (,keys$a ,hash-table))
                           ,(if key-recognizer
                                `(and (,key-recognizer ,key)
                                      (,boundp$a ,key ,hash-table))
                                `(,boundp$a ,key ,hash-table))))
           :rule-classes
           ((:rewrite :corollary
                      (implies (,coupledp ,hash-table)
                               (equal (set::in ,key (,keys$a ,hash-table))
                                      ,(if key-recognizer
                                           `(and (,key-recognizer ,key)
                                                 (,boundp$a (double-rewrite ,key) ,hash-table))
                                           `(,boundp$a (double-rewrite ,key) ,hash-table))))))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::in-of-keys-when-coupledp
                  ,@fi-bindings))))

         (defthm ,coupledp-of-remover$a-when-boundp$a
           (implies (let* ((,keys$a (,keys$a ,hash-table))
                           (inserted (set::insert ,(if key-fixer `(,key-fixer ,key) key) ,keys$a)))
                      (and (,boundp$a ,key ,hash-table)
                           (not (set::in ,(if key-fixer `(,key-fixer ,key) key) ,keys$a))
                           (,coupledp (,keys$a-set inserted ,hash-table))))
                    (,coupledp (,remover$a ,key ,hash-table)))
           :hints
           (("Goal"
             :do-not-induct t
             :in-theory (enable ,hash-table$a-constraints)
             :by (:functional-instance
                  lem-hash-table$a::coupledp-of-remover/copyable-when-boundp/copyable
                  ,@fi-bindings))))

         (defthm ,coupledp-of-remover$a-when-not-boundp$a
           (implies (and (not (,boundp$a ,key ,hash-table))
                         (,coupledp ,hash-table))
                    (,coupledp (,remover$a ,key ,hash-table)))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::coupledp-of-remover/copyable-when-not-boundp/copyable
                  ,@fi-bindings))))

         (defthm ,cardinality-of-keys$a-when-coupledp
           (implies (,coupledp ,hash-table)
                    (equal (set::cardinality (,keys$a ,hash-table))
                           (,count$a ,hash-table)))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::cardinality-of-keys-when-coupledp
                  ,@fi-bindings))))

         (defthm ,emptyp-of-keys$a-when-coupledp
           (implies (,coupledp ,hash-table)
                    (equal (set::emptyp (,keys$a ,hash-table))
                           (,equiv$a ,hash-table (,creator$a))))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::emptyp-of-keys-when-coupledp
                  ,@fi-bindings))))

         ;; `COPY-REC'
         (defun ,copy-rec (set ,%hash-table ,hash-table)
           (declare (xargs :stobjs (,%hash-table ,hash-table)
                           :guard (and (,keys$ap set)
                                       (set::subset set (,keys ,hash-table)))
                           :guard-hints
                           (("Goal"
                             :in-theory (enable ,hash-table$a-theorems
                                                ,hash-table$a-aggressive
                                                set::subset
                                                set::emptyp
                                                set::in)))
                           :measure (set::cardinality set)
                           :hints
                           (("Goal"
                             :in-theory (enable set::cardinality)))))
           (if (mbe :logic (or (set::emptyp set)
                               (not (,keys$ap set)))
                    :exec (endp set))
               (,the-hash-table ,%hash-table)
               ,(if val-copy
                    `(let ((,key (set::head set)))
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
                       (,copy-rec (set::tail set) ,%hash-table ,hash-table)))))

         ;; `COPY'
         (defun ,copy (,%hash-table ,hash-table)
           (declare (xargs :stobjs (,%hash-table ,hash-table)
                           :guard-hints
                           (("Goal"
                             :in-theory (enable ,hash-table$a-theorems
                                                ,hash-table$a-aggressive)))))
           (let* ((,keys (,keys ,hash-table))
                  (,count (,count ,hash-table))
                  (,%hash-table (,init ,count nil nil ,%hash-table))
                  (,%hash-table (,keys-set ,keys ,%hash-table)))
             (,copy-rec ,keys ,%hash-table ,hash-table)))

         (table copy ',hash-table ',copy)

         (local
           (defthmd ,copy-rec-of-updater$a-2
             (implies (,keys$ap set)
                      (equal (,copy-rec set (,updater$a ,key ,val ,%hash-table) ,hash-table)
                             (if (set::in ,(if key-fixer `(,key-fixer ,key) key) set)
                                 (,copy-rec set ,%hash-table ,hash-table)
                                 (,updater$a ,key ,val (,copy-rec set ,%hash-table ,hash-table)))))
             :hints
             (("Goal"
               :induct (,copy-rec set ,%hash-table ,hash-table)
               :in-theory (enable set::subset
                                  set::in
                                  ,hash-table$a-theorems
                                  ,hash-table$a-aggressive)
               :expand (:free (,key ,val)
                              (,copy-rec set (,updater$a ,key ,val ,%hash-table) ,hash-table))))))

         (local
           (defthmd ,copy-rec-of-updater$a-3
             (implies (and (,keys$ap set)
                           (not (set::in ,(if key-fixer `(,key-fixer ,key) key) set)))
                      (equal (,copy-rec set ,%hash-table (,updater$a ,key ,val ,hash-table))
                             (,copy-rec set ,%hash-table ,hash-table)))
             :hints
             (("Goal"
               :induct (,copy-rec set ,%hash-table ,hash-table)
               :in-theory (enable set::subset
                                  set::in
                                  ,hash-table$a-theorems
                                  ,hash-table$a-aggressive
                                  ,copy-rec-of-updater$a-2)
               :expand (:free (,key ,val)
                              (,copy-rec set ,%hash-table (,updater$a ,key ,val ,hash-table)))))))

         (local
           (defthmd ,copy-rec-of-fixer$a-3
             (equal (,copy-rec set ,%hash-table (,fixer$a ,hash-table))
                    (,copy-rec set ,%hash-table ,hash-table))
             :hints
             (("Goal"
               :induct (,copy-rec set ,%hash-table ,hash-table)
               :in-theory (enable ,hash-table$a-theorems
                                  ,hash-table$a-aggressive)
               :expand (,copy-rec set ,%hash-table (,fixer$a ,hash-table))))))

         (defthm ,hash-table-copy-constraints
           (and (equal (,copy-rec set ,%hash-table ,hash-table)
                       (if (if (set::emptyp set)
                               (set::emptyp set)
                               (not (,keys$ap set)))
                           (,fixer$a ,%hash-table)
                           ((lambda (,key ,%hash-table set ,hash-table)
                              ((lambda (,val ,hash-table set ,%hash-table ,key)
                                 ((lambda (,%val ,key ,%hash-table set ,hash-table ,val)
                                    (declare (ignorable ,%val))
                                    ((lambda (,%val ,val ,hash-table set ,%hash-table ,key)
                                       ((lambda (,%hash-table set ,hash-table ,val ,key)
                                          ((lambda (,hash-table ,%hash-table set)
                                             (,copy-rec (set::tail set) ,%hash-table ,hash-table))
                                           (,updater$a ,key ,val ,hash-table)
                                           ,%hash-table set))
                                        (,updater$a ,key ,%val ,%hash-table)
                                        set ,hash-table ,val ,key))
                                     ,(cond
                                        (val-copy
                                         `(,val-copy ,%val ,val))
                                        (val-fixer
                                         `(,val-fixer ,val))
                                        (t
                                         val))
                                     ,val ,hash-table set ,%hash-table ,key))
                                  (,accessor$a ,key ,%hash-table)
                                  ,key ,%hash-table set ,hash-table ,val))
                               (,accessor$a ,key ,hash-table)
                               ,hash-table set ,%hash-table ,key))
                            (set::head set)
                            ,%hash-table set ,hash-table)))
                (equal (,copy ,%hash-table ,hash-table)
                       ((lambda (,keys$a ,%hash-table ,hash-table)
                          ((lambda (count ,keys$a ,hash-table ,%hash-table)
                             ((lambda (,%hash-table ,hash-table ,keys$a)
                                ((lambda (,%hash-table ,hash-table ,keys$a)
                                   (,copy-rec ,keys$a ,%hash-table ,hash-table))
                                 (,keys$a-set ,keys$a ,%hash-table)
                                 ,hash-table ,keys$a))
                              (,init$a count 'nil 'nil ,%hash-table)
                              ,hash-table ,keys$a))
                           (,count$a ,hash-table)
                           ,keys$a
                           ,hash-table ,%hash-table))
                        (,keys$a ,hash-table)
                        ,%hash-table ,hash-table)))
           :rule-classes
           ((:definition :corollary
                (equal (,copy-rec set ,%hash-table ,hash-table)
                       (if (if (set::emptyp set)
                               (set::emptyp set)
                               (not (,keys$ap set)))
                           (,fixer$a ,%hash-table)
                           ((lambda (,key ,%hash-table set ,hash-table)
                              ((lambda (,val ,hash-table set ,%hash-table ,key)
                                 ((lambda (,%val ,key ,%hash-table set ,hash-table ,val)
                                    (declare (ignorable ,%val))
                                    ((lambda (,%val ,val ,hash-table set ,%hash-table ,key)
                                       ((lambda (,%hash-table set ,hash-table ,val ,key)
                                          ((lambda (,hash-table ,%hash-table set)
                                             (,copy-rec (set::tail set) ,%hash-table ,hash-table))
                                           (,updater$a ,key ,val ,hash-table)
                                           ,%hash-table set))
                                        (,updater$a ,key ,%val ,%hash-table)
                                        set ,hash-table ,val ,key))
                                     ,(cond
                                        (val-copy
                                         `(,val-copy ,%val ,val))
                                        (val-fixer
                                         `(,val-fixer ,val))
                                        (t
                                         val))
                                     ,val ,hash-table set ,%hash-table ,key))
                                  (,accessor$a ,key ,%hash-table)
                                  ,key ,%hash-table set ,hash-table ,val))
                               (,accessor$a ,key ,hash-table)
                               ,hash-table set ,%hash-table ,key))
                            (set::head set)
                            ,%hash-table set ,hash-table)))
              )
            (:definition :corollary
                (equal (,copy ,%hash-table ,hash-table)
                       ((lambda (,keys$a ,%hash-table ,hash-table)
                          ((lambda (count ,keys$a ,hash-table ,%hash-table)
                             ((lambda (,%hash-table ,hash-table ,keys$a)
                                ((lambda (,%hash-table ,hash-table ,keys$a)
                                   (,copy-rec ,keys$a ,%hash-table ,hash-table))
                                 (,keys$a-set ,keys$a ,%hash-table)
                                 ,hash-table ,keys$a))
                              (,init$a count 'nil 'nil ,%hash-table)
                              ,hash-table ,keys$a))
                           (,count$a ,hash-table)
                           ,keys$a
                           ,hash-table ,%hash-table))
                        (,keys$a ,hash-table)
                        ,%hash-table ,hash-table))))
           :hints
           (("Goal"
             :do-not-induct t
             :in-theory (enable ,hash-table$a-theorems
                                ,hash-table$a-aggressive
                                ,copy-rec-of-fixer$a-3
                                ,copy-rec-of-updater$a-3
                                ,copy-rec-of-updater$a-2)
             :expand (,copy-rec set ,%hash-table ,hash-table))))

         (local
           (in-theory
             (disable ,copy-rec
                      ,copy)))

         (defthm ,recognizer$a-of-copy
           (,recognizer$a (,copy ,%hash-table ,hash-table))
           :hints
           (("Goal"
             :do-not-induct t
             :in-theory (enable ,hash-table$a-theorems)
             :by (:functional-instance
                  lem-hash-table$a::recognizer/copyable-of-copy
                  ,@fi-bindings-with-copy)
             :expand ((,copy-rec lem-hash-table$a::set
                                 lem-hash-table$a::%hash-table
                                 lem-hash-table$a::hash-table)))))

         (defthm ,copy-ignores-1
           (equal (,copy ,%hash-table ,hash-table)
                  (,copy (,creator$a) ,hash-table))
           :rule-classes
           ((:rewrite :corollary
                      (implies (syntaxp (not (and (consp ,%hash-table)
                                                  (eq (car ,%hash-table) ',creator$a))))
                               (equal (,copy ,%hash-table ,hash-table)
                                      (,copy (,creator$a) ,hash-table)))))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::copy-ignores-1
                  ,@fi-bindings-with-copy))))

         (defcong ,equiv$a equal (,copy ,%hash-table ,hash-table) 2
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::equiv/copyable-implies-equal-copy-2
                  ,@fi-bindings-with-copy))))

         (defthm ,coupledp-of-copy
           (,coupledp (,copy ,%hash-table ,hash-table))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::coupledp-of-copy
                  ,@fi-bindings-with-copy))))

         (local
           (defthmd ,accessor$a-of-copy-lemma
             (equal (,accessor$a ,key (,copy ,%hash-table ,hash-table))
                    (if (set::in ,(if key-fixer `(,key-fixer ,key) key) (,keys$a ,hash-table))
                        ,(cond
                           (val-copy
                            `(,val-copy ,default-val (,accessor$a ,key ,hash-table)))
                           (val-fixer
                            `(,val-fixer (,accessor$a ,key ,hash-table)))
                           (t
                            `(,accessor$a ,key ,hash-table)))
                        ,default-val))
             :hints
             (("Goal"
               :by (:functional-instance
                    lem-hash-table$a::accessor/copyable-of-copy
                    ,@fi-bindings-with-copy)))))

         (defthm ,accessor$a-of-copy
           (equal (,accessor$a ,key (,copy ,%hash-table ,hash-table))
                  (if (set::in ,(if key-fixer `(,key-fixer ,key) key) (,keys$a ,hash-table))
                      ,(if val-copy
                           `(,val-copy ,default-val (,accessor$a ,key ,hash-table))
                           `(,accessor$a ,key ,hash-table))
                      ,default-val))
           :hints
           (("Goal"
             :use ,accessor$a-of-copy-lemma)))

         (local
           (defthmd ,copy-of-updater$a-lemma
             (equal (,copy ,%hash-table (,updater$a ,key ,val ,hash-table))
                    (if (set::in ,(if key-fixer `(,key-fixer ,key) key) (,keys$a ,hash-table))
                        (,updater$a ,key
                                    ,(cond
                                       (val-copy
                                        `(,val-copy ,default-val ,val))
                                       (val-fixer
                                        `(,val-fixer ,val))
                                       (t
                                        val))
                                    (,copy ,%hash-table ,hash-table))
                        (,copy ,%hash-table ,hash-table)))
             :hints
             (("Goal"
               :by (:functional-instance
                    lem-hash-table$a::copy-of-updater/copyable
                    ,@fi-bindings-with-copy)))))

         (defthm ,copy-of-updater$a
           (equal (,copy ,%hash-table (,updater$a ,key ,val ,hash-table))
                  (if (set::in ,(if key-fixer `(,key-fixer ,key) key) (,keys$a ,hash-table))
                      (,updater$a ,key
                                  ,(if val-copy
                                       `(,val-copy ,default-val ,val)
                                       val)
                                  (,copy ,%hash-table ,hash-table))
                      (,copy ,%hash-table ,hash-table)))
           :hints
           (("Goal"
             :in-theory (enable ,hash-table$a-aggressive)
             :use ,copy-of-updater$a-lemma)))

         (defthm ,boundp$a-of-copy
           (equal (,boundp$a ,key (,copy ,%hash-table ,hash-table))
                  (set::in ,(if key-fixer `(,key-fixer ,key) key) (,keys$a ,hash-table)))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::boundp/copyable-of-copy
                  ,@fi-bindings-with-copy))))

         (defthm ,copy-of-remover$a
           (equal (,copy ,%hash-table (,remover$a ,key ,hash-table))
                  (if (set::in ,(if key-fixer `(,key-fixer ,key) key) (,keys$a ,hash-table))
                      (,updater$a ,key
                                  ,default-val
                                  (,copy ,%hash-table ,hash-table))
                      (,copy ,%hash-table ,hash-table)))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::copy-of-remover/copyable
                  ,@fi-bindings-with-copy))))

         (defthm ,count$a-of-copy
           (equal (,count$a (,copy ,%hash-table ,hash-table))
                  (set::cardinality (,keys$a ,hash-table)))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::count/copyable-of-copy
                  ,@fi-bindings-with-copy))))

         (defthm ,keys$a-of-copy
           (equal (,keys$a (,copy ,%hash-table ,hash-table))
                  (,keys$a ,hash-table))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::keys-of-copy
                  ,@fi-bindings-with-copy))))

         (defthm ,copy-rw
           (implies (,coupledp ,hash-table)
                    (equal (,copy ,%hash-table ,hash-table)
                           (,fixer$a ,hash-table)))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::copy-rw
                  ,@fi-bindings-with-copy)))))

       (deflabel ,copy-end)

       (deftheory-static ,copy-theory
         (set-difference-theories
          (set-difference-theories (current-theory ',copy-end)
                                   (current-theory ',copy-begin))
          '(,@(and val-coupled-p
                   `(,coupled-vals-p))
            ,coupled-keys-p
            ,coupledp
            ,coupledp-constraints
            ,copy-rec
            ,copy
            ,hash-table-copy-constraints)))

       (in-theory
         (union-theories (current-theory ',copy-begin)
                         (theory ',copy-theory))))))


;;;; `MAKE-FRAME-COPY-EVENTS'
(defun make-frame-copy-events (frame package-witness debug state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp frame)
                              (package-witness-p package-witness)
                              (booleanp debug))
                  :verify-guards nil))
  (let* ((%frame (symbolicate package-witness "%" frame))
         (copy (symbolicate package-witness frame "-COPY"))

         (coupledp (symbolicate package-witness frame "-COUPLED-P"))

         ;; `FRAME'
         (stobj-property (getpropc frame 'acl2::stobj))
         (recognizer (caadr stobj-property))
         (the-frame (symbolicate frame "THE-" frame))

         ;; `FRAME$A'
         (world (w state))
         (stobj$a-property (cdr (assoc frame (table-alist 'stobj$a-property world))))
         (frame$a (first stobj$a-property))
         (frame$a-equal (cdr (assoc frame$a (table-alist 'equality world))))
         (%frame$a (car (getpropc frame$a-equal 'acl2::formals)))
         (frame$a-theorems (symbolicate frame$a frame$a "-THEOREMS"))
         (frame$a-aggressive (symbolicate frame$a frame$a "-AGGRESSIVE"))
         (recognizer$a (first (second stobj$a-property)))
         (creator$a (second (second stobj$a-property)))
         (fixer$a (third (second stobj$a-property)))
         (equiv$a (fourth (second stobj$a-property)))

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
         (view$a (first (ninth (third stobj$a-property))))

         ;; Adjust for nested stobj interface shuffle
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
                                 (setq non-stobj-accessors-and-updaters (cddr non-stobj-accessors-and-updaters)))))
                            (setq stobjs (cdr stobjs)))))
         (updaters (loop$ :with stobj-accessors-and-updaters := (cdr stobj-accessors-and-updaters)
                         :with non-stobj-accessors-and-updaters := (cdr non-stobj-accessors-and-updaters)
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
                                (setq non-stobj-accessors-and-updaters (cddr non-stobj-accessors-and-updaters)))))
                           (setq stobjs (cdr stobjs)))))
         (%accessors (loop$ :for accessor :in accessors
                           :collect (symbolicate package-witness "%" accessor)))
         (%updaters (loop$ :for updater :in updaters
                          :collect (symbolicate package-witness "%" updater)))

         (stobj-copy-alist (table-alist 'copy world))
         (stobj-copy-list (loop$ :for stobj :in stobjs
                                :collect (and stobj
                                              (cdr (assoc stobj stobj-copy-alist)))))
         (stobj-copy-theory-list (loop$ :for stobj-copy :in stobj-copy-list
                                       :collect (and stobj-copy
                                                     (symbolicate stobj-copy stobj-copy "-THEORY"))))
         (%stobjs (loop$ :for stobj-copy :in stobj-copy-list
                        :collect (and stobj-copy
                                      (car (getprop stobj-copy
                                                    'acl2::formals
                                                    nil
                                                    'acl2::current-acl2-world
                                                    world)))))
         (stobj-coupled-p-alist (table-alist 'coupledp world))
         (stobj-coupled-p-list (loop$ :for stobj :in stobjs
                                     :collect (and stobj
                                                   (cdr (assoc stobj stobj-coupled-p-alist)))))

         (copy-begin (symbolicate package-witness copy "-BEGIN"))
         (copy-end (symbolicate package-witness copy "-END"))
         (copy-theory (symbolicate package-witness copy "-THEORY"))

         ;; Theorem Names
         (coupledp-tp (symbolicate package-witness coupledp "-TP"))
         (coupledp-when-not-recognizer$a (symbolicate package-witness coupledp "-WHEN-NOT-" recognizer$a))
         (coupledp-of-creator$a (symbolicate package-witness coupledp "-OF-" creator$a))
         (coupledp-of-view$a (symbolicate package-witness coupledp "-OF-" view$a))

         (recognizer$a-of-copy (symbolicate package-witness recognizer$a "-OF-" copy))
         (copy-ignores-1 (symbolicate package-witness copy "-IGNORES-1"))
         (coupledp-of-copy (symbolicate package-witness coupledp "-OF-" copy))
         (copy-of-view$a (symbolicate package-witness copy "-OF-" view$a))
         (copy-rw (symbolicate package-witness copy "-RW")))

    `(progn
       (deflabel ,copy-begin)

       (encapsulate ()

         (local
           (deflabel prologue-begin))

         ,@(loop$ :for recognizer$a :in recognizers$a
                 :as initial-element :in initial-elements
                 :as initial-element-name :in initial-element-names
                 :as fixer$a :in fixers$a
                 :as equiv$a :in equivs$a
                 :as field :in fields
                 :as %field :in %fields
                 :as i :from 1 :to (len fields)
                 :when (and recognizer$a
                            fixer$a)
                 :append (list
                          `(local
                             (defthm ,(symbolicate "ATOMIC-STOBJS" recognizer$a "-CONSTRAINT-" i)
                               (and (booleanp (,recognizer$a ,field))
                                    (,recognizer$a ,initial-element))
                               :rule-classes
                               ((:rewrite :corollary
                                          (booleanp (,recognizer$a ,field)))
                                ,@(and (not (equal initial-element initial-element-name))
                                       `((:rewrite :corollary
                                                   (,recognizer$a ,initial-element)))))))

                          `(local
                             (defthm ,(symbolicate "ATOMIC-STOBJS" fixer$a "-CONSTRAINT-" i)
                               (equal (,fixer$a ,field)
                                      (if (,recognizer$a ,field)
                                          ,field
                                          ,initial-element))))

                          `(local
                             (defthm ,(symbolicate "ATOMIC-STOBJS" equiv$a "-CONSTRAINT-" i)
                               (equal (,equiv$a ,%field ,field)
                                      (equal (,fixer$a ,%field)
                                             (,fixer$a ,field)))))))

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

         ,@(loop$ :for stobj-copy-theory :in stobj-copy-theory-list
                 :when stobj-copy-theory
                 :collect `(local
                             (in-theory
                               (enable ,stobj-copy-theory))))

         ,@(loop$ :for recognizer$a :in recognizers$a
                 :when recognizer$a
                 :collect `(local
                             (in-theory
                               (enable (:e ,recognizer$a)))))

         ,@(loop$ :for absstobj-info :in absstobj-info-list
                 :when absstobj-info
                 :collect `(local
                             (in-theory
                               (enable ,@(strip-cars (cdr absstobj-info))))))

         (local
           (in-theory
             (enable ,@(strip-cars (cdr (getpropc frame 'acl2::absstobj-info))))))

         (define-congruent ,frame
           :package-witness ,package-witness
           :debug ,debug)

         ;; `COUPLEDP'
         ,@(and (remove nil stobj-coupled-p-list)
                `((defun-nx ,coupledp (,frame)
                    (declare (xargs :guard (,recognizer ,frame)
                                    :verify-guards nil))
                    ,(let ((body (loop$ :for stobj-coupled-p :in stobj-coupled-p-list
                                       :as accessor$a :in accessors$a
                                       :when stobj-coupled-p
                                       :collect `(,stobj-coupled-p (,accessor$a ,frame)))))
                       (if (consp (cdr body))
                           (cons 'and body)
                           (car body))))

                  (table coupledp ',frame ',coupledp)

                  (defthm ,coupledp-tp
                    (booleanp (,coupledp ,frame))
                    :rule-classes :type-prescription)

                  (defthm ,coupledp-when-not-recognizer$a
                    (implies (not (,recognizer$a ,frame))
                             (,coupledp ,frame))
                    :hints
                    (("Goal"
                      :in-theory (enable ,frame$a-aggressive))))

                  (defthm ,coupledp-of-creator$a
                    (,coupledp (,creator$a)))

                  (defcong ,equiv$a equal (,coupledp ,frame) 1)

                  (defthm ,coupledp-of-view$a
                    (equal (,coupledp (,view$a ,@fields))
                           ,(let ((constraints (loop$ :for stobj-coupled-p :in stobj-coupled-p-list
                                                     :as field :in fields
                                                     :when stobj-coupled-p
                                                     :collect `(,stobj-coupled-p ,field))))
                              (if (consp (cdr constraints))
                                  (cons 'and constraints)
                                  (car constraints)))))

                  ,@(loop$ :for accessor$a :in accessors$a
                          :as stobj-coupled-p :in stobj-coupled-p-list
                          :when stobj-coupled-p
                          :collect `(defthm ,(symbolicate package-witness stobj-coupled-p "-OF-" accessor$a)
                                      (implies (,coupledp ,frame)
                                               (,stobj-coupled-p (,accessor$a ,frame)))))

                  (local
                    (in-theory
                      (disable ,coupledp)))))

         ;; `COPY'
         (defun ,copy (,%frame ,frame)
           (declare (xargs :stobjs (,%frame ,frame)))
           ,(loop$ :with body := `(,the-frame ,%frame)
                  :with fields := (reverse fields)
                  :with stobjs := (reverse stobjs)
                  :with %stobjs := (reverse %stobjs)
                  :with accessors := (reverse accessors)
                  :with %accessors := (reverse %accessors)
                  :with updaters := (reverse updaters)
                  :with %updaters := (reverse %updaters)
                  :with stobj-copy-list := (reverse stobj-copy-list)
                  :do
                  (progn
                    (cond
                      ((endp stobjs)
                       (return body))
                      ((car stobjs)
                       (setq body (let ((stobj (car stobjs))
                                        (%stobj (car %stobjs))
                                        (accessor (car accessors))
                                        (%accessor (car %accessors))
                                        (updater (car updaters))
                                        (%updater (car %updaters))
                                        (stobj-copy (car stobj-copy-list)))
                                    `(stobj-let ((,stobj (,accessor ,frame) ,updater))
                                                (,%frame)
                                                (stobj-let ((,%stobj (,%accessor ,%frame) ,%updater))
                                                           (,%stobj)
                                                           (,stobj-copy ,%stobj ,stobj)
                                                  ,%frame)
                                       ,body))))
                      (t
                       (setq body `(let* ((,(car fields) (,(car accessors) ,frame))
                                          (,%frame (,(car updaters) ,(car fields) ,%frame)))
                                     ,body))))
                    (setq fields (cdr fields))
                    (setq stobjs (cdr stobjs))
                    (setq %stobjs (cdr %stobjs))
                    (setq accessors (cdr accessors))
                    (setq %accessors (cdr %accessors))
                    (setq updaters (cdr updaters))
                    (setq %updaters (cdr %updaters))
                    (setq stobj-copy-list (cdr stobj-copy-list)))))

         (table copy ',frame ',copy)

         (defthm ,recognizer$a-of-copy
           (,recognizer$a (,copy ,%frame ,frame)))

         (defthm ,copy-ignores-1
           (implies (syntaxp (not (and (consp ,%frame)
                                       (eq (car ,%frame) ',creator$a))))
                    (equal (,copy ,%frame ,frame)
                           (,copy (,creator$a) ,frame))))

         (defcong ,equiv$a equal (,copy ,%frame ,frame) 2)

         ,@(and (remove nil stobj-coupled-p-list)
                `((defthm ,coupledp-of-copy
                    (,coupledp (,copy ,%frame ,frame)))))

         ,@(loop$ :for accessor$a :in accessors$a
                 :as stobj-copy :in stobj-copy-list
                 :as initial-element :in initial-elements
                 :collect `(local
                             (defthm ,(symbolicate package-witness accessor$a "-OF-" copy)
                               (equal (,accessor$a (,copy ,%frame ,frame))
                                      ,(if stobj-copy
                                           `(,stobj-copy ,initial-element (,accessor$a ,frame))
                                           `(,accessor$a ,frame))))))

         (defthm ,copy-of-view$a
           (equal (,copy ,frame (,view$a ,@fields))
                  (,view$a ,@(loop$ :for field :in fields
                                   :as stobj-copy :in stobj-copy-list
                                   :as initial-element :in initial-elements
                                   :collect (if stobj-copy
                                                `(,stobj-copy ,initial-element ,field)
                                                field))))
           :hints
           (("Goal"
             :use ((:instance ,frame$a-equal
                              (,%frame$a (,copy ,frame (,view$a ,@fields)))
                              (,frame$a (,view$a ,@(loop$ :for field :in fields
                                                         :as stobj-copy :in stobj-copy-list
                                                         :as initial-element :in initial-elements
                                                         :collect (if stobj-copy
                                                                      `(,stobj-copy ,initial-element ,field)
                                                                      field)))))))))

         (local
           (in-theory
             (disable ,copy)))

         (defthm ,copy-rw
           ,(if (remove nil stobj-coupled-p-list)
                `(implies (,coupledp ,frame)
                          (equal (,copy ,%frame ,frame)
                                 (,fixer$a ,frame)))
                `(equal (,copy ,%frame ,frame)
                        (,fixer$a ,frame)))
           :hints
           (("Goal"
             :do-not-induct t
             :use ((:instance ,frame$a-equal
                              (,%frame$a (,copy ,%frame ,frame))
                              (,frame$a (,fixer$a ,frame))))))))

       (deflabel ,copy-end)

       (deftheory-static ,copy-theory
         (set-difference-theories
          (set-difference-theories (current-theory ',copy-end)
                                   (current-theory ',copy-begin))
          '(,@(and (remove nil stobj-coupled-p-list)
                   `(,coupledp))
            ,copy)))

       (in-theory
         (union-theories (current-theory ',copy-begin)
                         (theory ',copy-theory))))))


;;;; `DEFINE-COPY'
(defmacro define-copy (stobj &key
                               (package-witness 'nil package-witness-supplied-p)
                               (debug 'nil))
  (declare (xargs :guard (and (symbolp stobj)
                              (package-witness-p package-witness)
                              (booleanp debug))))
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
              (debug ',debug)
              (stobj$a-property (cdr (assoc stobj (table-alist 'stobj$a-property world)))))
         (cond
           ((and (= (len stobj$a-property) 3)
                 (= (len (third stobj$a-property)) 3))
            (make-vector-copy-events stobj package-witness debug state))
           ((and (= (len stobj$a-property) 3)
                 (= (len (third stobj$a-property)) 5))
            (make-hash-table-copy-events stobj package-witness debug state))
           ((and (= (len stobj$a-property) 3)
                 (= (len (third stobj$a-property)) 9))
            (make-frame-copy-events stobj package-witness debug state)))))))
