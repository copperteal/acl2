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
    (list 'case-split (if (endp (cdr expressions))
                          (car expressions)
                          (cons 'and expressions)))))


;;;; `MAKE-VECTOR-COPY-EVENTS'
(defun make-vector-copy-events (vector package-witness state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp vector)
                              (or (symbolp package-witness)
                                  (and (stringp package-witness)
                                       (not (equal package-witness "")))))
                  :verify-guards nil))
  (let* ((%vector (symbolicate package-witness "%" vector))
         (copy (symbolicate package-witness vector "-COPY"))
         (copy-rec (symbolicate package-witness copy "-REC"))
         (copy{rewrite} (symbolicate package-witness copy "{REWRITE}"))
         (index (symbolicate package-witness "I"))

         (coupledp (symbolicate package-witness vector "-COUPLED-P"))
         (coupledp-witness (symbolicate package-witness coupledp "-WITNESS"))

         ;; `VECTOR'
         (stobj-property (getpropc vector 'acl2::stobj))
         (recognizer (caadr stobj-property))
         (fixer (first (third stobj-property)))
         (length (second (third stobj-property)))
         (resizer (third (third stobj-property)))
         (accessor (fourth (third stobj-property)))
         (updater (fifth (third stobj-property)))

         ;; `VECTOR$A'
         (world (w state))
         (stobj$a-property (cdr (assoc vector (table-alist 'stobj$a-property world))))
         (vector$a (first stobj$a-property))
         (recognizer$a-aux (symbolicate vector$a vector$a "-AUX-P"))
         (vector$a-definitions (symbolicate vector$a vector$a "-DEFINITIONS"))
         (vector$a-theorems (symbolicate vector$a vector$a "-THEOREMS"))
         (vector$a-aggressive (symbolicate vector$a vector$a "-AGGRESSIVE"))
         (recognizer$a (first (second stobj$a-property)))
         (creator$a (second (second stobj$a-property)))
         (fixer$a (third (second stobj$a-property)))
         (resizable (first (second (third stobj$a-property))))
         (default-length-name (second (second (third stobj$a-property))))
         (length$a (first (third (third stobj$a-property))))
         (resizer$a (second (third (third stobj$a-property))))
         (accessor$a (third (third (third stobj$a-property))))
         (updater$a (fourth (third (third stobj$a-property))))

         (element (first (first (third stobj$a-property))))
         (element-stobj-property (getpropc element 'acl2::stobj))
         (element-stobj$a-property (cdr (assoc element (table-alist 'stobj$a-property world))))
         (element-recognizer (second (first (third stobj$a-property))))
         (initial-element-name (third (first (third stobj$a-property))))
         (element-creator (second (second element-stobj$a-property)))
         (initial-element (if element-stobj-property
                              `(,element-creator)
                              initial-element-name))
         (element-fixer (fourth (first (third stobj$a-property))))

         ;; Adjust for nested stobj interface shuffle
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
         (%accessor (symbolicate package-witness "%" accessor))
         (updater (if element-stobj-property
                      (second (third stobj-property))
                      updater))
         (%updater (symbolicate package-witness "%" updater))

         (element-copy (cdr (assoc element (table-alist 'copy world))))
         (element-copy-theory (symbolicate element-copy element-copy "-THEORY"))
         (%element (car (getpropc element-copy 'acl2::formals)))
         (element-coupled-p (cdr (assoc element (table-alist 'coupledp world))))

         (copy-begin (symbolicate package-witness copy "-BEGIN"))
         (copy-end (symbolicate package-witness copy "-END"))
         (copy-theory (symbolicate package-witness copy "-THEORY"))

         ;; Theorem Names
         (booleanp-of-element-recognizer (symbolicate "ATOMIC-STOBJS" "BOOLEANP-OF-" element-recognizer))
         (element-recognizer-of-initial-element (symbolicate "ATOMIC-STOBJS" element-recognizer "-OF-INITIAL-ELEMENT"))
         (element-fixer{rewrite} (symbolicate "ATOMIC-STOBJS" element-fixer "{REWRITE}"))

         (coupledp-constraint-1 (symbolicate "ATOMIC-STOBJS" coupledp "-CONSTRAINT-1"))
         (coupledp-constraint-2 (symbolicate "ATOMIC-STOBJS" coupledp "-CONSTRAINT-2"))
         (coupledp-constraint-1/expanded (symbolicate "ATOMIC-STOBJS" coupledp-constraint-1 "/EXPANDED"))
         (coupledp-constraint-2/expanded (symbolicate "ATOMIC-STOBJS" coupledp-constraint-2 "/EXPANDED"))

         (copy-rec-of-fixer$a-3 (symbolicate "ATOMIC-STOBJS" copy-rec "-OF-" fixer$a "-3"))
         (copy-rec-constraint (symbolicate "ATOMIC-STOBJS" copy-rec "-CONSTRAINT"))

         (coupledp-when-not-recognizer$a (symbolicate package-witness coupledp "-WHEN-NOT-" recognizer$a))
         (coupledp-of-creator$a (symbolicate package-witness coupledp "-OF-" creator$a))
         (coupledp-of-fixer$a (symbolicate package-witness coupledp "-OF-" fixer$a))
         (coupledp-of-resizer$a (symbolicate package-witness coupledp "-OF-" resizer$a))
         (element-coupled-p-of-accessor$a (symbolicate package-witness element-coupled-p "-OF-" accessor$a))
         (coupledp-of-updater$a (symbolicate package-witness coupledp "-OF-" updater$a))

         (recognizer$a-of-copy (symbolicate package-witness recognizer$a "-OF-" copy))
         (copy-ignores-1 (symbolicate package-witness copy "-IGNORES-1"))
         (copy-of-fixer$a-2 (symbolicate package-witness copy "-OF-" fixer$a "-2"))
         (length$a-of-copy (symbolicate package-witness length$a "-OF-" copy))

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
                 `(lem-vector$a::contents-recognizer ,(if element-recognizer
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

         ,@(and element-recognizer
                element-fixer
                `((local
                    (defthm ,booleanp-of-element-recognizer
                      (booleanp (,element-recognizer ,element))
                      :rule-classes
                      (:rewrite
                       :type-prescription)))

                  (local
                    (defthm ,element-recognizer-of-initial-element
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
           (include-book "projects/atomic-stobjs/lemmas/vector$a" :dir :system))

         (local
           (table acl2::theory-invariant-table nil nil :clear))

         (local
           (in-theory
             (union-theories
              (union-theories (theory 'acl2::ground-zero)
                              (theory ',vector$a-definitions))
              (set-difference-theories (current-theory 'prologue-end)
                                       (current-theory 'prologue-begin)))))

         (local
           (in-theory
             (disable make-list-ac
                      (:e make-list-ac))))

         ,@(and element-recognizer
                element-fixer
                `((local
                    (in-theory
                      (e/d ((:e ,element-recognizer)
                            (:e ,element-fixer))
                           (,element-recognizer
                            ,element-fixer))))))

         ,@(and element-stobj$a-property
                `((local
                    (in-theory
                      (disable ,element-creator)))))

         ,@(and element-stobj-property
                `((local
                    (in-theory
                      (enable ,element-copy-theory)))))

         ,@(and element-stobj-property
                `((local
                    (in-theory
                      (enable ,@(strip-cars (cdr (getpropc element 'acl2::absstobj-info))))))))

         (local
           (in-theory
             (enable ,@(strip-cars (cdr (getpropc vector 'acl2::absstobj-info))))))

         (define-congruent ,vector
           :package-witness ,package-witness)

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

                  (local
                    (defthmd ,coupledp-constraint-1
                      (implies (,coupledp ,vector)
                               (,element-coupled-p (,accessor$a ,index ,vector)))
                      :hints
                      (("Goal"
                        :in-theory (disable ,coupledp
                                            ,vector$a-definitions)))))

                  (local
                    (defthmd ,coupledp-constraint-2
                      (equal (,coupledp ,vector)
                             ((lambda (,index ,vector)
                                (,element-coupled-p (,accessor$a ,index ,vector)))
                              (,coupledp-witness ,vector) ,vector))))

                  (in-theory
                    (disable ,coupledp))

                  (local
                    (defthmd ,coupledp-constraint-1/expanded
                      (implies (,coupledp ,vector)
                               (,element-coupled-p (let ((,index (nfix ,index))
                                                         (,vector (,fixer$a ,vector)))
                                                     (if (< ,index ,(if resizable
                                                                        `(len (,fixer$a ,vector))
                                                                        default-length-name))
                                                         (,element-fixer (nth ,index ,vector))
                                                         (,element-creator)))))
                      :hints
                      (("Goal"
                        :in-theory (e/d (,vector$a-theorems)
                                        (,vector$a-definitions
                                         nfix))
                        :use ,coupledp-constraint-1
                        :expand ((:free (,index ,vector)
                                        (,accessor$a ,index ,vector))
                                 (:free (,vector)
                                        (,length$a ,vector)))))))

                  (local
                    (defthmd ,coupledp-constraint-2/expanded
                      (equal (,coupledp ,vector)
                             (,element-coupled-p (let ((,index (nfix (,coupledp-witness ,vector)))
                                                       (,vector (,fixer$a ,vector)))
                                                   (if (< ,index ,(if resizable
                                                                      `(len (,fixer$a ,vector))
                                                                      default-length-name))
                                                       (,element-fixer (nth ,index ,vector))
                                                       (,element-creator)))))
                      :hints
                      (("Goal"
                        :in-theory (e/d (,vector$a-theorems)
                                        (,vector$a-definitions
                                         nfix))
                        :use ,coupledp-constraint-2
                        :expand ((:free (,index ,vector)
                                        (,accessor$a ,index ,vector))
                                 (:free (,vector)
                                        (,length$a ,vector)))))))

                  (defthm ,coupledp-when-not-recognizer$a
                    (implies (not (,recognizer$a ,vector))
                             (,coupledp ,vector))
                    :hints
                    (("Goal"
                      :do-not-induct t
                      :by (:functional-instance
                           ,(if resizable
                                'lem-vector$a::coupledp/resizable-when-not-recognizer/resizable
                                'lem-vector$a::coupledp/fixed-when-not-recognizer/fixed)
                           ,@fi-bindings))
                     ,@(and element-coupled-p
                            (if resizable
                                `(("Subgoal 6"
                                   :in-theory (theory 'acl2::minimal-theory)
                                   :use (:instance ,coupledp-constraint-1/expanded
                                                   (,index lem-vector$a::index)
                                                   (,vector common-lisp::vector)))
                                  ("Subgoal 5"
                                   :in-theory (theory 'acl2::minimal-theory)
                                   :use (:instance ,coupledp-constraint-2/expanded
                                                   (,vector common-lisp::vector))))
                                `(("Subgoal 7"
                                   :in-theory (theory 'acl2::minimal-theory)
                                   :use (:instance ,coupledp-constraint-1/expanded
                                                   (,index lem-vector$a::index)
                                                   (,vector common-lisp::vector)))
                                  ("Subgoal 6"
                                   :in-theory (theory 'acl2::minimal-theory)
                                   :use (:instance ,coupledp-constraint-2/expanded
                                                   (,vector common-lisp::vector))))))))

                  (defthm ,coupledp-of-creator$a
                    (,coupledp (,creator$a))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if resizable
                                'lem-vector$a::coupledp/resizable-of-creator
                                'lem-vector$a::coupledp/fixed-of-creator)
                           ,@fi-bindings))))

                  (defthm ,coupledp-of-fixer$a
                    (equal (,coupledp (,fixer$a ,vector))
                           (,coupledp ,vector))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if resizable
                                'lem-vector$a::coupledp/resizable-of-fixer/resizable
                                'lem-vector$a::coupledp/fixed-of-fixer/fixed)
                           ,@fi-bindings))))

                  ,@(and resizable
                         `((defthm ,coupledp-of-resizer$a
                             (implies (,coupledp ,vector)
                                      (,coupledp (,resizer$a length ,vector)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-vector$a::coupledp/resizable-of-resizer/resizable
                                    ,@fi-bindings))))))

                  (defthm ,element-coupled-p-of-accessor$a
                    (implies (,coupledp ,vector)
                             (,element-coupled-p (,accessor$a ,index ,vector)))
                    :rule-classes
                    ((:rewrite :corollary
                               (implies (coupledp ,vector)
                                        (,element-coupled-p (,accessor$a ,index ,vector)))))
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
                                    (if (<= ,(if resizable
                                                 `(,length$a ,vector)
                                                 default-length-name)
                                            (nfix ,index))
                                        t
                                        (,element-coupled-p ,element))))
                    :hints
                    (("Goal"
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
                             :in-theory (e/d (,vector$a-theorems
                                              ,vector$a-aggressive)
                                             (,vector$a-definitions))))))
           (if (zp ,index)
               (,fixer ,%vector)
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

         (local
           (defthm ,copy-rec-of-fixer$a-3
             (equal (,copy-rec ,index ,%vector (,fixer$a ,vector))
                    (,copy-rec ,index ,%vector ,vector))
             :hints
             (("Goal"
               :in-theory (e/d (,vector$a-theorems
                                ,vector$a-aggressive)
                               (,vector$a-definitions))))))

         (local
           (defthm ,copy-rec-constraint
             (equal (,copy-rec ,index ,%vector ,vector)
                    (if (zp ,index)
                        (,fixer$a ,%vector)
                        (let* ((,index (1- ,index))
                               (element (,accessor$a ,index ,vector))
                               (%element (,accessor$a ,index ,%vector)))
                          (declare (ignorable %element))
                          (let* ((%element ,(cond
                                              (element-copy
                                               `(,element-copy %element element))
                                              (element-fixer
                                               `(,element-fixer element))
                                              (t
                                               'element)))
                                 (,%vector (,updater$a ,index %element ,%vector))
                                 (,vector (,updater$a ,index element ,vector)))
                            (,copy-rec ,index ,%vector ,vector)))))
             :hints
             (("Goal"
               :do-not-induct t
               :in-theory (e/d (,vector$a-theorems
                                ,vector$a-aggressive)
                               (,vector$a-definitions))))))

         (in-theory
           (disable ,copy-rec))

         ;; `COPY'
         (defun ,copy (,%vector ,vector)
           (declare (xargs :stobjs (,%vector ,vector)
                           :guard-hints
                           (("Goal"
                             :in-theory (e/d (,vector$a-theorems
                                              ,vector$a-aggressive)
                                             (,vector$a-definitions))))))
           ,(if resizable
                `(let* ((length (,length ,vector))
                        (,%vector (if (= (,length ,%vector) length)
                                      ,%vector
                                      (,resizer length ,%vector))))
                   (,copy-rec length ,%vector ,vector))
                `(,copy-rec ,default-length-name ,%vector ,vector)))

         (table copy ',vector ',copy)

         (defthm ,recognizer$a-of-copy
           (,recognizer$a (,copy ,%vector ,vector))
           :hints
           (("Goal"
             :do-not-induct t
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

         (defthm ,copy-of-fixer$a-2
           (equal (,copy ,%vector (,fixer$a ,vector))
                  (,copy ,%vector ,vector))
           :hints
           (("Goal"
             :by (:functional-instance
                  ,(if resizable
                       'lem-vector$a::copy/resizable-of-fixer/resizable-2
                       'lem-vector$a::copy/fixed-of-fixer/fixed-2)
                  ,@fi-bindings-with-copy))))

         ,@(and resizable
                `((defthm ,length$a-of-copy
                    (equal (,length$a (,copy ,%vector ,vector))
                           (,length$a ,vector))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-vector$a::length/resizable-of-copy/resizable
                           ,@fi-bindings-with-copy))))))

         (in-theory
           (disable ,copy))

         (defthm ,copy{rewrite}
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
                       'lem-vector$a::copy/resizable{rewrite}
                       'lem-vector$a::copy/fixed{rewrite})
                  ,@fi-bindings-with-copy)))))

       (deflabel ,copy-end)

       (deftheory-static ,copy-theory
         (set-difference-theories (current-theory ',copy-end)
                                  (current-theory ',copy-begin))))))


;;;; `MAKE-HASH-TABLE-COPY-EVENTS'
(defun make-hash-table-copy-events (hash-table package-witness state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp hash-table)
                              (or (symbolp package-witness)
                                  (and (stringp package-witness)
                                       (not (equal package-witness "")))))
                  :verify-guards nil))
  (let* ((%hash-table (symbolicate package-witness "%" hash-table))
         (copy (symbolicate package-witness hash-table "-COPY"))
         (copy-rec (symbolicate package-witness copy "-REC"))
         (copy{rewrite} (symbolicate package-witness copy "{REWRITE}"))

         (coupledp (symbolicate package-witness hash-table "-COUPLED-P"))
         (coupled-keys-p (symbolicate package-witness hash-table "-COUPLED-KEYS-P"))
         (coupled-keys-p-witness (symbolicate package-witness coupled-keys-p "-WITNESS"))
         (coupled-vals-p (symbolicate package-witness hash-table "-COUPLED-VALS-P"))
         (coupled-vals-p-witness (symbolicate package-witness coupled-vals-p "-WITNESS"))

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
         (world (w state))
         (stobj$a-property (cdr (assoc hash-table (table-alist 'stobj$a-property world))))
         (hash-table$a (first stobj$a-property))
         (hash-table$a-definitions (symbolicate hash-table$a hash-table$a "-DEFINITIONS"))
         (hash-table$a-theorems (symbolicate hash-table$a hash-table$a "-THEOREMS"))
         (hash-table$a-aggressive (symbolicate hash-table$a hash-table$a "-AGGRESSIVE"))
         (recognizer$a (first (second stobj$a-property)))
         (creator$a (second (second stobj$a-property)))
         (fixer$a (third (second stobj$a-property)))
         (accessor$a (first (fourth (third stobj$a-property))))
         (updater$a (second (fourth (third stobj$a-property))))
         (boundp$a (third (fourth (third stobj$a-property))))
         (getp$a (fourth (fourth (third stobj$a-property))))
         (remover$a (fifth (fourth (third stobj$a-property))))
         (count$a (sixth (fourth (third stobj$a-property))))
         (clear$a (seventh (fourth (third stobj$a-property))))
         (init$a (eighth (fourth (third stobj$a-property))))
         (keysp$a (nth 8 (fourth (third stobj$a-property))))
         (keys$a-fix (nth 9 (fourth (third stobj$a-property))))
         (keys$a (nth 10 (fourth (third stobj$a-property))))
         (keys-set$a (nth 11 (fourth (third stobj$a-property))))

         (contents$a (symbolicate hash-table$a hash-table$a "-CONTENTS"))
         (contents-recognizer$a (symbolicate hash-table$a contents$a "-P"))
         (contents-creator$a (symbolicate hash-table$a "CREATE-" contents$a))
         (contents-fixer$a (symbolicate hash-table$a contents$a "-FIX"))
         (contents-accessor$a (symbolicate hash-table$a contents$a "-GET"))
         (contents-updater$a (symbolicate hash-table$a contents$a "-PUT"))
         (contents-boundp$a (symbolicate hash-table$a contents$a "-BOUNDP"))
         (contents-getp$a (symbolicate hash-table$a contents$a "-GETP"))
         (contents-remover$a (symbolicate hash-table$a contents$a "-REM"))
         (contents-count$a (symbolicate hash-table$a contents$a "-COUNT"))
         (contents-clear$a (symbolicate hash-table$a contents$a "-CLEAR"))
         (contents-init$a (symbolicate hash-table$a contents$a "-INIT"))

         (key (first (first (third stobj$a-property))))
         (key-recognizer (second (first (third stobj$a-property))))
         (default-key-name (third (first (third stobj$a-property))))
         (key-fixer (fourth (first (third stobj$a-property))))

         (val (first (second (third stobj$a-property))))
         (val-stobj-property (getpropc val 'acl2::stobj))
         (val-stobj$a-property (cdr (assoc val (table-alist 'stobj$a-property world))))
         (val-recognizer (second (second (third stobj$a-property))))
         (default-val-name (third (second (third stobj$a-property))))
         (val-creator (second (second val-stobj$a-property)))
         (default-val (if val-stobj-property
                          `(,val-creator)
                          default-val-name))
         (val-fixer (fourth (second (third stobj$a-property))))

         ;; Adjust for nested stobj interface shuffle
         (fixer (if val-stobj-property
                    (third (third stobj-property))
                    fixer))
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
         (%val (car (getpropc val-copy 'acl2::formals)))
         (val-coupled-p (cdr (assoc val (table-alist 'coupledp world))))

         (copy-begin (symbolicate package-witness copy "-BEGIN"))
         (copy-end (symbolicate package-witness copy "-END"))
         (copy-theory (symbolicate package-witness copy "-THEORY"))

         ;; Theorem Names
         (booleanp-of-key-recognizer (symbolicate "ATOMIC-STOBJS" "BOOLEANP-OF-" key-recognizer))
         (key-recognizer-of-default-key (symbolicate "ATOMIC-STOBJS" key-recognizer "-OF-DEFAULT-KEY"))
         (key-fixer{rewrite} (symbolicate "ATOMIC-STOBJS" key-fixer "{REWRITE}"))

         (booleanp-of-val-recognizer (symbolicate "ATOMIC-STOBJS" "BOOLEANP-OF-" val-recognizer))
         (val-recognizer-of-default-val (symbolicate "ATOMIC-STOBJS" val-recognizer "-OF-DEFAULT-VAL"))
         (val-fixer{rewrite} (symbolicate "ATOMIC-STOBJS" val-fixer "{REWRITE}"))

         (coupled-keys-p-constraint-1 (symbolicate "ATOMIC-STOBJS" coupled-keys-p "-CONSTRAINT-1"))
         (coupled-keys-p-constraint-2 (symbolicate "ATOMIC-STOBJS" coupled-keys-p "-CONSTRAINT-2"))
         (coupled-vals-p-constraint-1 (symbolicate "ATOMIC-STOBJS" coupled-vals-p "-CONSTRAINT-1"))
         (coupled-vals-p-constraint-2 (symbolicate "ATOMIC-STOBJS" coupled-vals-p "-CONSTRAINT-2"))
         (coupled-keys-p-constraint-1/expanded (symbolicate "ATOMIC-STOBJS" coupled-keys-p-constraint-1 "/EXPANDED"))
         (coupled-keys-p-constraint-2/expanded (symbolicate "ATOMIC-STOBJS" coupled-keys-p-constraint-2 "/EXPANDED"))
         (coupled-vals-p-constraint-1/expanded (symbolicate "ATOMIC-STOBJS" coupled-vals-p-constraint-1 "/EXPANDED"))
         (coupled-vals-p-constraint-2/expanded (symbolicate "ATOMIC-STOBJS" coupled-vals-p-constraint-2 "/EXPANDED"))
         (coupledp/expanded (symbolicate "ATOMIC-STOBJS" coupledp "/EXPANDED"))
         (copy-rec-of-fixer$a-3 (symbolicate "ATOMIC-STOBJS" copy-rec "-OF-" fixer$a "-3"))
         (copy-rec-constraint (symbolicate "ATOMIC-STOBJS" copy-rec "-CONSTRAINT"))

         (coupledp-when-not-recognizer$a (symbolicate package-witness coupledp "-WHEN-NOT-" recognizer$a))
         (coupledp-of-creator$a (symbolicate package-witness coupledp "-OF-" creator$a))
         (coupledp-of-fixer$a (symbolicate package-witness coupledp "-OF-" fixer$a))
         (coupledp-of-updater$a-when-boundp$a (symbolicate package-witness coupledp "-OF-" updater$a "-WHEN-" boundp$a))
         (coupledp-of-updater$a-when-boundp$a-lemma (symbolicate package-witness coupledp-of-updater$a-when-boundp$a "-LEMMA"))
         (coupledp-of-updater$a-when-not-boundp$a (symbolicate package-witness coupledp "-OF-" updater$a "-WHEN-NOT-" boundp$a))
         (coupledp-of-updater$a-when-not-boundp$a-lemma (symbolicate package-witness coupledp-of-updater$a-when-not-boundp$a "-LEMMA"))
         (coupledp-of-remover$a-when-boundp$a (symbolicate package-witness coupledp "-OF-" remover$a "-WHEN-" boundp$a))
         (coupledp-of-remover$a-when-not-boundp$a (symbolicate package-witness coupledp "-OF-" remover$a "-WHEN-NOT-" boundp$a))
         (cardinality-of-keys$a-when-coupledp (symbolicate package-witness "CARDINALITY-OF-" keys$a "-WHEN-" coupledp))
         (in-of-keys$a-when-coupledp (symbolicate package-witness "IN-OF-" keys$a "-WHEN-" coupledp))
         (val-coupled-p-of-accessor$a (symbolicate package-witness val-coupled-p "-OF-" accessor$a))
         (emptyp-of-keys$a-when-coupledp (symbolicate package-witness "EMPTYP-OF-" keys$a "-WHEN-" coupledp))

         (recognizer$a-of-copy (symbolicate package-witness recognizer$a "-OF-" copy))
         (copy-ignores-1 (symbolicate package-witness copy "-IGNORES-1"))
         (copy-of-fixer$a-2 (symbolicate package-witness copy "-OF-" fixer$a "-2"))
         (keys$a-of-copy (symbolicate package-witness keys$a "-OF-" copy))

         (fi-bindings
          (list `(lem-hash-table$a::val-coupled-p ,(or val-coupled-p
                                                       '(lambda (val)
                                                         t)))
                `(lem-hash-table$a::coupled-keys-p ,coupled-keys-p)
                `(lem-hash-table$a::coupled-keys-p-witness ,coupled-keys-p-witness)
                `(lem-hash-table$a::coupled-vals-p ,(if val-coupled-p
                                                        coupled-vals-p
                                                        '(lambda (hash-table)
                                                          t)))
                `(lem-hash-table$a::coupled-vals-p-witness ,(if val-coupled-p
                                                                coupled-vals-p-witness
                                                                `(lambda (hash-table)
                                                                   ,default-key-name)))
                `(lem-hash-table$a::coupledp ,coupledp)

                `(lem-hash-table$a::keysp ,(if key-recognizer
                                               keysp$a
                                               'set::setp))
                `(lem-hash-table$a::keys-fix ,(if key-recognizer
                                                  keys$a-fix
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
                `(lem-hash-table$a::accessor/copyable ,accessor$a)
                `(lem-hash-table$a::updater/copyable ,updater$a)
                `(lem-hash-table$a::boundp/copyable ,boundp$a)
                `(lem-hash-table$a::getp/copyable ,getp$a)
                `(lem-hash-table$a::remover/copyable ,remover$a)
                `(lem-hash-table$a::count/copyable ,count$a)
                `(lem-hash-table$a::clear/copyable ,clear$a)
                `(lem-hash-table$a::init/copyable ,init$a)
                `(lem-hash-table$a::keys ,keys$a)
                `(lem-hash-table$a::keys-set ,keys-set$a)))

         (fi-bindings-with-copy
          (list* `(lem-hash-table$a::val-copy ,(or val-copy
                                                   `(lambda (%val val)
                                                      (,val-fixer val))))
                 `(lem-hash-table$a::copy-rec ,copy-rec)
                 `(lem-hash-table$a::copy ,copy)
                 fi-bindings)))

    `(progn
       (deflabel ,copy-begin)

       (encapsulate ()

         (local
           (deflabel prologue-begin))

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
                      (,key-recognizer ,default-key-name)
                      :rule-classes nil))

                  (local
                    (defthm ,key-fixer{rewrite}
                      (equal (,key-fixer ,key)
                             (if (,key-recognizer ,key)
                                 ,key
                                 ,default-key-name))))))

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
           (include-book "projects/atomic-stobjs/lemmas/hash-table$a" :dir :system))

         (local
           (table acl2::theory-invariant-table nil nil :clear))

         (local
           (in-theory
             (union-theories
              (union-theories (theory 'acl2::ground-zero)
                              (theory ',hash-table$a-definitions))
              (set-difference-theories (current-theory 'prologue-end)
                                       (current-theory 'prologue-begin)))))

         ,@(and key-recognizer
                key-fixer
                `((local
                    (in-theory
                      (e/d ((:e ,key-recognizer)
                            (:e ,key-fixer))
                           (,key-recognizer
                            ,key-fixer))))))

         ,@(and val-recognizer
                val-fixer
                `((local
                    (in-theory
                      (e/d ((:e ,val-recognizer)
                            (:e ,val-fixer))
                           (,val-recognizer
                            ,val-fixer))))))

         ,@(and val-stobj$a-property
                `((local
                    (in-theory
                      (disable ,val-creator)))))

         ,@(and val-stobj-property
                `((local
                    (in-theory
                      (enable ,val-copy-theory)))))

         ,@(and val-stobj-property
                `((local
                    (in-theory
                      (enable ,@(strip-cars (cdr (getpropc val 'acl2::absstobj-info))))))))

         (local
           (in-theory
             (enable ,@(strip-cars (cdr (getpropc hash-table 'acl2::absstobj-info))))))

         (define-congruent ,hash-table
           :package-witness ,package-witness)

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

         (local
           (defthmd ,coupled-keys-p-constraint-1
             (implies (,coupled-keys-p ,hash-table)
                      (equal (set::in ,key (,keys$a ,hash-table))
                             ,(if key-recognizer
                                  `(if (,key-recognizer ,key)
                                       (,boundp$a ,key ,hash-table)
                                       nil)
                                  `(,boundp$a ,key ,hash-table))))
             :hints
             (("Goal"
               :in-theory (disable ,coupled-keys-p
                                   ,hash-table$a-definitions)))))

         (local
           (defthmd ,coupled-keys-p-constraint-2
             (equal (,coupled-keys-p ,hash-table)
                    ((lambda (,key ,hash-table)
                       (equal (set::in ,key (,keys$a ,hash-table))
                              ,(if key-recognizer
                                   `(if (,key-recognizer ,key)
                                        (,boundp$a ,key ,hash-table)
                                        nil)
                                   `(,boundp$a ,key ,hash-table))))
                     (,coupled-keys-p-witness ,hash-table) ,hash-table))))

         (in-theory
           (disable ,coupled-keys-p))

         ;; `COUPLED-VALS-P'
         ,@(and val-coupled-p
                `((defun-sk ,coupled-vals-p (,hash-table)
                    (declare (xargs :guard (,recognizer ,hash-table)
                                    :verify-guards nil))
                    (forall ,key
                      (,val-coupled-p (,accessor$a ,key ,hash-table)))
                    :rewrite :direct)

                  (local
                    (defthmd ,coupled-vals-p-constraint-1
                      (implies (,coupled-vals-p ,hash-table)
                               (,val-coupled-p (,accessor$a ,key ,hash-table)))
                      :hints
                      (("Goal"
                        :in-theory (disable ,coupled-vals-p
                                            ,hash-table$a-definitions)))))

                  (local
                    (defthmd ,coupled-vals-p-constraint-2
                      (equal (,coupled-vals-p ,hash-table)
                             ((lambda (,key ,hash-table)
                                (,val-coupled-p (,accessor$a ,key ,hash-table)))
                              (,coupled-vals-p-witness ,hash-table) ,hash-table))))

                  (in-theory
                    (disable ,coupled-vals-p))))

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

         (local
           (defthmd ,coupled-keys-p-constraint-1/expanded
             (implies (,coupled-keys-p ,hash-table)
                      (equal (set::in ,key (car (,fixer$a ,hash-table)))
                             ,(if key-recognizer
                                  `(and (,key-recognizer ,key)
                                        (,contents-boundp$a (,key-fixer ,key) (cdr (,fixer$a ,hash-table))))
                                  `(,contents-boundp$a ,key (cdr (,fixer$a ,hash-table))))))
             :hints
             (("Goal"
               :in-theory (disable ,hash-table$a-definitions)
               :use ,coupled-keys-p-constraint-1
               :expand ((:free (,key ,hash-table)
                               (,boundp$a ,key ,hash-table))
                        (:free (,hash-table)
                               (,keys$a ,hash-table)))))))

         (local
           (defthmd ,coupled-keys-p-constraint-2/expanded
             (equal (,coupled-keys-p ,hash-table)
                    (let ((,key (,coupled-keys-p-witness ,hash-table)))
                      (equal (set::in ,key (car (,fixer$a ,hash-table)))
                             ,(if key-recognizer
                                  `(and (,key-recognizer ,key)
                                        (,contents-boundp$a (,key-fixer ,key) (cdr (,fixer$a ,hash-table))))
                                  `(,contents-boundp$a ,key (cdr (,fixer$a ,hash-table)))))))
             :hints
             (("Goal"
               :in-theory (disable ,hash-table$a-definitions)
               :use ,coupled-keys-p-constraint-2
               :expand ((:free (,key ,hash-table)
                               (,boundp$a ,key ,hash-table))
                        (:free (,hash-table)
                               (,keys$a ,hash-table)))))))

         ,@(and val-coupled-p
                `((local
                    (defthmd ,coupled-vals-p-constraint-1/expanded
                      (implies (,coupled-vals-p ,hash-table)
                               (,val-coupled-p (,contents-accessor$a ,(if key-fixer
                                                                          `(,key-fixer ,key)
                                                                          key)
                                                                     (cdr (,fixer$a ,hash-table)))))
                      :hints
                      (("Goal"
                        :in-theory (disable ,hash-table$a-definitions)
                        :use ,coupled-vals-p-constraint-1
                        :expand ((:free (,key ,hash-table)
                                        (,accessor$a ,key ,hash-table)))))))

                  (local
                    (defthmd ,coupled-vals-p-constraint-2/expanded
                      (equal (,coupled-vals-p ,hash-table)
                             (,val-coupled-p (,contents-accessor$a ,(if key-fixer
                                                                        `(,key-fixer (,coupled-vals-p-witness ,hash-table))
                                                                        `(,coupled-vals-p-witness ,hash-table))
                                                                   (cdr (,fixer$a ,hash-table)))))
                      :hints
                      (("Goal"
                        :in-theory (disable ,hash-table$a-definitions)
                        :use ,coupled-vals-p-constraint-2
                        :expand ((:free (,key ,hash-table)
                                        (,accessor$a ,key ,hash-table)))))))))

         (local
           (defthmd ,coupledp/expanded
             (equal (,coupledp ,hash-table)
                    (and (equal (set::cardinality (car (,fixer$a ,hash-table)))
                                (,contents-count$a (cdr (,fixer$a ,hash-table))))
                         (,coupled-keys-p ,hash-table)
                         ,@(and val-coupled-p
                                `((,coupled-vals-p ,hash-table)))))
             :hints
             (("Goal"
               :in-theory (disable ,hash-table$a-definitions)
               :expand ((:free (,hash-table)
                               (,keys$a ,hash-table))
                        (:free (,hash-table)
                               (,count$a ,hash-table)))))))

         (defthm ,coupledp-when-not-recognizer$a
           (implies (not (,recognizer$a ,hash-table))
                    (,coupledp ,hash-table))
           :hints
           (("Goal"
             :do-not-induct t
             :in-theory (enable set::in
                                set::emptyp
                                set::setp)
             :by (:functional-instance
                  lem-hash-table$a::coupledp-when-not-recognizer/copyable
                  ,@fi-bindings))
            ,@(and val-coupled-p
                   `(,@(if key-recognizer
                           `(("Subgoal 14"
                              :in-theory (theory 'acl2::minimal-theory)
                              :use (:instance ,coupled-vals-p-constraint-1/expanded
                                              (,key lem-hash-table$a::key)
                                              (,hash-table acl2::hash-table)))
                             ("Subgoal 13"
                              :in-theory (theory 'acl2::minimal-theory)
                              :use (:instance ,coupled-vals-p-constraint-2/expanded
                                              (,hash-table acl2::hash-table))))
                           `(("Subgoal 14"
                              :in-theory (theory 'acl2::minimal-theory)
                              :use (:instance ,coupledp/expanded
                                              (,hash-table acl2::hash-table)))
                             ("Subgoal 13"
                              :in-theory (theory 'acl2::minimal-theory)
                              :use (:instance ,coupled-vals-p-constraint-1/expanded
                                              (,key lem-hash-table$a::key)
                                              (,hash-table acl2::hash-table)))
                             ("Subgoal 12"
                              :in-theory (theory 'acl2::minimal-theory)
                              :use (:instance ,coupled-vals-p-constraint-2/expanded
                                              (,hash-table acl2::hash-table)))))))
            ,@(and (not key-recognizer)
                   `(("Subgoal 7"
                      :in-theory (enable set::setp
                                         acl2::fast-<<-is-<<))))
            ("Subgoal 4"
             :in-theory (theory 'acl2::minimal-theory)
             :use (:instance ,coupled-keys-p-constraint-1/expanded
                             (,key lem-hash-table$a::key)
                             (,hash-table acl2::hash-table)))
            ("Subgoal 3"
             :in-theory (theory 'acl2::minimal-theory)
             :use (:instance ,coupled-keys-p-constraint-2/expanded
                             (,hash-table acl2::hash-table)))))

         (defthm ,coupledp-of-creator$a
           (,coupledp (,creator$a))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::coupledp-of-creator/copyable
                  ,@fi-bindings))))

         (defthm ,coupledp-of-fixer$a
           (equal (,coupledp (,fixer$a ,hash-table))
                  (,coupledp ,hash-table))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::coupledp-of-fixer/copyable
                  ,@fi-bindings))))

         ,@(and val-coupled-p
                `((defthm ,val-coupled-p-of-accessor$a
                    (implies (,coupledp ,hash-table)
                             (,val-coupled-p (,accessor$a ,key ,hash-table)))
                    :rule-classes
                    ((:rewrite :corollary
                               (implies (coupledp ,hash-table)
                                        (,val-coupled-p (,accessor$a ,key ,hash-table)))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-hash-table$a::val-coupled-p-of-accessor/copyable
                           ,@fi-bindings))))))

         ,@(and (not val-coupled-p)
                `((local
                    (defthm ,coupledp-of-updater$a-when-boundp$a-lemma
                      (implies (and (,boundp$a ,key ,hash-table)
                                    (,coupledp ,hash-table))
                               (equal (,coupledp (,updater$a ,key ,val ,hash-table))
                                      t))
                      :hints
                      (("Goal"
                        :do-not-induct t
                        :by (:functional-instance
                             lem-hash-table$a::coupledp-of-updater/copyable-when-boundp/copyable
                             ,@fi-bindings)))))))

         (defthm ,coupledp-of-updater$a-when-boundp$a
           (implies (and (,boundp$a ,key ,hash-table)
                         (,coupledp ,hash-table))
                    ,(if val-coupled-p
                         `(equal (,coupledp (,updater$a ,key ,val ,hash-table))
                                 (,val-coupled-p ,val))
                         `(,coupledp (,updater$a ,key ,val ,hash-table))))
           :hints
           (("Goal"
             :do-not-induct t
             ,@(if val-coupled-p
                   `(:by (:functional-instance
                          lem-hash-table$a::coupledp-of-updater/copyable-when-boundp/copyable
                          ,@fi-bindings))
                   `(:use ,coupledp-of-updater$a-when-boundp$a-lemma)))))

         ,@(and (not val-coupled-p)
                `((defthm ,coupledp-of-updater$a-when-not-boundp$a-lemma
                    (implies (let* ((,keys$a (,keys$a ,hash-table))
                                    (trimmed (set::delete ,(if key-fixer `(,key-fixer ,key) key) ,keys$a)))
                               (and (not (,boundp$a ,key ,hash-table))
                                    (set::in ,(if key-fixer `(,key-fixer ,key) key) ,keys$a)
                                    (,coupledp (,keys-set$a trimmed ,hash-table))))
                             (equal (,coupledp (,updater$a ,key ,val ,hash-table))
                                    t))
                    :hints
                    (("Goal"
                      :do-not-induct t
                      :in-theory (enable set::sfix-set-identity)
                      :by (:functional-instance
                           lem-hash-table$a::coupledp-of-updater/copyable-when-not-boundp/copyable
                           ,@fi-bindings))))))

         (defthm ,coupledp-of-updater$a-when-not-boundp$a
           (implies (let* ((,keys$a (,keys$a ,hash-table))
                           (trimmed (set::delete ,(if key-fixer `(,key-fixer ,key) key) ,keys$a)))
                      (and (not (,boundp$a ,key ,hash-table))
                           (set::in ,(if key-fixer `(,key-fixer ,key) key) ,keys$a)
                           (,coupledp (,keys-set$a trimmed ,hash-table))))
                    ,(if val-coupled-p
                         `(equal (,coupledp (,updater$a ,key ,val ,hash-table))
                                 (,val-coupled-p ,val))
                         `(,coupledp (,updater$a ,key ,val ,hash-table))))
           :hints
           (("Goal"
             :do-not-induct t
             :in-theory (enable set::sfix-set-identity)
             ,@(if val-coupled-p
                   `(:by (:functional-instance
                          lem-hash-table$a::coupledp-of-updater/copyable-when-not-boundp/copyable
                          ,@fi-bindings))
                   `(:use ,coupledp-of-updater$a-when-not-boundp$a-lemma)))))

         (defthm ,in-of-keys$a-when-coupledp
           (implies (,coupledp ,hash-table)
                    (equal (set::in ,key (,keys$a ,hash-table))
                           ,(if key-recognizer
                                `(and (,key-recognizer ,key)
                                      (,boundp$a ,key ,hash-table))
                                `(,boundp$a ,key ,hash-table))))
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
                           (,coupledp (,keys-set$a inserted ,hash-table))))
                    (,coupledp (,remover$a ,key ,hash-table)))
           :hints
           (("Goal"
             :do-not-induct t
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
                           (or (not (,recognizer$a ,hash-table))
                               (equal ,hash-table (,creator$a)))))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::emptyp-of-keys-when-coupledp
                  ,@fi-bindings))))

         (in-theory
           (disable ,coupledp))

         ;; `COPY-REC'
         (defun ,copy-rec (set ,%hash-table ,hash-table)
           (declare (xargs :stobjs (,%hash-table ,hash-table)
                           :guard (and (,keysp$a set)
                                       (set::subset set (,keys ,hash-table)))
                           :guard-hints
                           (("Goal"
                             :in-theory (e/d (set::subset
                                              set::emptyp
                                              set::setp
                                              ,hash-table$a-theorems
                                              ,hash-table$a-aggressive)
                                             (,hash-table$a-definitions))))
                           :measure (set::cardinality set)
                           :hints
                           (("Goal"
                             :in-theory (enable set::cardinality)))))
           (if (mbe :logic (or (set::emptyp set)
                               (not (,keysp$a set)))
                    :exec (endp set))
               (,fixer ,%hash-table)
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

         (local
           (defthm ,copy-rec-of-fixer$a-3
             (equal (,copy-rec set ,%hash-table (,fixer$a ,hash-table))
                    (,copy-rec set ,%hash-table ,hash-table))
             :hints
             (("Goal"
               :in-theory (e/d (,hash-table$a-theorems
                                ,hash-table$a-aggressive)
                               (,hash-table$a-definitions))))))

         (local
           (defthm copy-rec-of-updater$a-when-not-in
             (implies (and (,keysp$a set)
                           (not (set::in ,(if key-fixer
                                              `(,key-fixer ,key)
                                              key)
                                         set)))
                      (equal (,copy-rec set ,%hash-table (,updater$a ,key ,val ,hash-table))
                             (,copy-rec set ,%hash-table ,hash-table)))
             :hints
             (("Goal"
               :in-theory (e/d (,hash-table$a-theorems
                                ,hash-table$a-aggressive
                                set::in)
                               (,hash-table$a-definitions))))))

         (local
           (defthm ,copy-rec-constraint
             (equal (,copy-rec set ,%hash-table ,hash-table)
                    (if (or (set::emptyp set)
                            (not (,keysp$a set)))
                        (,fixer$a ,%hash-table)
                        (let* ((,key (set::head set))
                               (val (,accessor$a ,key ,hash-table))
                               (%val (,accessor$a ,key ,%hash-table)))
                          (declare (ignorable %val))
                          (let* ((%val ,(if val-copy
                                            `(,val-copy %val val)
                                            `(,val-fixer val)))
                                 (,%hash-table (,updater$a ,key %val ,%hash-table))
                                 (,hash-table (,updater$a ,key val ,hash-table)))
                            (,copy-rec (set::tail set) ,%hash-table ,hash-table)))))
             :hints
             (("Goal"
               :do-not-induct t
               :in-theory (e/d (,hash-table$a-theorems
                                ,hash-table$a-aggressive
                                set::head-unique
                                set::tail-produces-set)
                               (,hash-table$a-definitions))))))

         (in-theory
           (disable ,copy-rec))

         ;; `COPY'
         (defun ,copy (,%hash-table ,hash-table)
           (declare (xargs :stobjs (,%hash-table ,hash-table)
                           :guard-hints
                           (("Goal"
                             :in-theory (e/d (set::subset-reflexive
                                              ,hash-table$a-theorems
                                              ,hash-table$a-aggressive)
                                             (,hash-table$a-definitions))))))
           (let* ((,keys (,keys ,hash-table))
                  (,count (,count ,hash-table))
                  (,%hash-table (,init ,count nil nil ,%hash-table))
                  (,%hash-table (,keys-set ,keys ,%hash-table)))
             (,copy-rec ,keys ,%hash-table ,hash-table)))

         (table copy ',hash-table ',copy)

         (defthm ,recognizer$a-of-copy
           (,recognizer$a (,copy ,%hash-table ,hash-table))
           :hints
           (("Goal"
             :do-not-induct t
             :by (:functional-instance
                  lem-hash-table$a::recognizer/copyable-of-copy
                  ,@fi-bindings-with-copy))))

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

         (defthm ,copy-of-fixer$a-2
           (equal (,copy ,%hash-table (,fixer$a ,hash-table))
                  (,copy ,%hash-table ,hash-table))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::copy-of-fixer/copyable-2
                  ,@fi-bindings-with-copy))))

         (defthm ,keys$a-of-copy
           (equal (,keys$a (,copy ,%hash-table ,hash-table))
                  (,keys$a ,hash-table))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::keys-of-copy
                  ,@fi-bindings-with-copy))))

         (in-theory
           (disable ,copy))

         (defthm ,copy{rewrite}
           (implies (,coupledp ,hash-table)
                    (equal (,copy ,%hash-table ,hash-table)
                           (,fixer$a ,hash-table)))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::copy{rewrite}
                  ,@fi-bindings-with-copy)))))

       (deflabel ,copy-end)

       (deftheory-static ,copy-theory
         (set-difference-theories (current-theory ',copy-end)
                                  (current-theory ',copy-begin))))))


;;;; `MAKE-FRAME-COPY-EVENTS'
(defun make-frame-copy-events (frame package-witness state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp frame)
                              (or (symbolp package-witness)
                                  (and (stringp package-witness)
                                       (not (equal package-witness "")))))
                  :verify-guards nil))
  (let* ((%frame (symbolicate package-witness "%" frame))
         (copy (symbolicate package-witness frame "-COPY"))
         (copy{rewrite} (symbolicate package-witness copy "{REWRITE}"))

         (coupledp (symbolicate package-witness frame "-COUPLED-P"))

         ;; `FRAME'
         (stobj-property (getpropc frame 'acl2::stobj))
         (recognizer (caadr stobj-property))

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

         (fields (first (third stobj$a-property)))
         (stobjs (fifth (third stobj$a-property)))
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
         (accessors$a (sixth (third stobj$a-property)))
         (view$a (first (eighth (third stobj$a-property))))

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
         (coupledp-when-not-recognizer$a (symbolicate package-witness coupledp "-WHEN-NOT-" recognizer$a))
         (coupledp-of-creator$a (symbolicate package-witness coupledp "-OF-" creator$a))
         (coupledp-of-fixer$a (symbolicate package-witness coupledp "-OF-" fixer$a))
         (coupledp-of-view$a (symbolicate package-witness coupledp "-OF-" view$a))

         (recognizer$a-of-copy (symbolicate package-witness recognizer$a "-OF-" copy))
         (copy-ignores-1 (symbolicate package-witness copy "-IGNORES-1")))

    `(progn
       (deflabel ,copy-begin)

       (encapsulate ()

         (local
           (deflabel prologue-begin))

         ,@(loop$ :for recognizer$a :in recognizers$a
                 :as initial-element :in initial-elements
                 :as fixer$a :in fixers$a
                 :as field :in fields
                 :as i :from 0 :to (1- (len fields))
                 :when (and recognizer$a
                            fixer$a)
                 :append (list
                          `(local
                             (defthm ,(symbolicate "ATOMIC-STOBJS" "BOOLEANP-OF-" recognizer$a "-" i)
                               (booleanp (,recognizer$a ,field))
                               :rule-classes
                               (:rewrite
                                :type-prescription)))

                          `(local
                             (defthm ,(symbolicate "ATOMIC-STOBJS" recognizer$a "-OF-INITIAL-ELEMENT-" i)
                               (,recognizer$a ,initial-element)
                               :rule-classes nil))

                          `(local
                             (defthm ,(symbolicate "ATOMIC-STOBJS" fixer$a "{REWRITE}-" i)
                               (equal (,fixer$a ,field)
                                      (if (,recognizer$a ,field)
                                          ,field
                                          ,initial-element))))))

         (local
           (deflabel prologue-end))

         (local
           (in-theory
             (union-theories
              (union-theories (theory 'acl2::ground-zero)
                              (theory ',frame$a-theorems))
              (set-difference-theories (current-theory 'prologue-end)
                                       (current-theory 'prologue-begin)))))

         ,@(loop$ :for recognizer$a :in recognizers$a
                 :as fixer$a :in fixers$a
                 :when (and recognizer$a
                            fixer$a)
                 :collect `(local
                             (in-theory
                               (e/d ((:e ,recognizer$a)
                                     (:e ,fixer$a))
                                    (,recognizer$a
                                     ,fixer$a)))))

         ,@(loop$ :for stobj$a-property :in stobj$a-property-list
                 :as creator$a :in creators$a
                 :when stobj$a-property
                 :collect `(local
                             (in-theory
                               (disable ,creator$a))))

         ,@(loop$ :for stobj-property :in stobj-property-list
                 :as stobj-copy-theory :in stobj-copy-theory-list
                 :when stobj-property
                 :collect `(local
                             (in-theory
                               (enable ,stobj-copy-theory))))

         ,@(loop$ :for stobj-property :in stobj-property-list
                 :as absstobj-info :in absstobj-info-list
                 :when stobj-property
                 :collect `(local
                             (in-theory
                               (enable ,@(strip-cars (cdr absstobj-info))))))

         (local
           (in-theory
             (enable ,@(strip-cars (cdr (getpropc frame 'acl2::absstobj-info))))))

         (define-congruent ,frame
           :package-witness ,package-witness)

         (local
           (in-theory
             (enable ,@(strip-cars (cdr (getpropc %frame 'acl2::absstobj-info))))))

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

                  (defthm ,coupledp-when-not-recognizer$a
                    (implies (not (,recognizer$a ,frame))
                             (,coupledp ,frame))
                    :hints
                    (("Goal"
                      :in-theory (enable ,frame$a-aggressive))))

                  (defthm ,coupledp-of-creator$a
                    (,coupledp (,creator$a)))

                  (defthm ,coupledp-of-fixer$a
                    (equal (,coupledp (,fixer$a ,frame))
                           (,coupledp ,frame)))

                  (defthm ,coupledp-of-view$a
                    (equal (,coupledp (,view$a ,@fields ,frame))
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
                                      (implies (coupledp ,frame)
                                               (,stobj-coupled-p (,accessor$a ,frame)))))

                  (in-theory
                    (disable ,coupledp))))

         ;; `COPY'
         (defun ,copy (,%frame ,frame)
           (declare (xargs :stobjs (,%frame ,frame)))
           ,(loop$ :with body := %frame
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

         ,@(loop$ :for accessor$a :in accessors$a
                 :collect `(local
                             (defthm ,(symbolicate package-witness accessor$a "-OF-" copy)
                               ,(if (remove nil stobj-coupled-p-list)
                                    `(implies (,coupledp ,frame)
                                              (equal (,accessor$a (,copy ,%frame ,frame))
                                                     (,accessor$a ,frame)))
                                    `(equal (,accessor$a (,copy ,%frame ,frame))
                                            (,accessor$a ,frame))))))

         (in-theory
           (disable ,copy))

         (defthm ,copy{rewrite}
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
         (set-difference-theories (current-theory ',copy-end)
                                  (current-theory ',copy-begin))))))


;;;; `DEFINE-COPY'
(defmacro define-copy (stobj &key (debug 'nil) (package-witness 'nil package-witness-supplied-p))
  (declare (xargs :guard (and (symbolp stobj)
                              (booleanp debug)
                              (or (symbolp package-witness)
                                  (and (stringp package-witness)
                                       (not (equal package-witness "")))))))
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
            (make-vector-copy-events stobj package-witness state))
           ((and (= (len stobj$a-property) 3)
                 (= (len (third stobj$a-property)) 4))
            (make-hash-table-copy-events stobj package-witness state))
           ((and (= (len stobj$a-property) 3)
                 (= (len (third stobj$a-property)) 8))
            (make-frame-copy-events stobj package-witness state)))))))
