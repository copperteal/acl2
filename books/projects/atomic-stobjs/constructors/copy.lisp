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
    (if (atom names)
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
    (list 'case-split (if (null (cdr expressions))
                          (car expressions)
                          (cons 'and expressions)))))


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
         (coupledp (symbolicate vector vector "-COUPLED-P"))

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
         (recognizer$a-aux (symbolicate vector vector$a "-AUX-P"))
         (vector$a-theorems (symbolicate vector vector$a "-THEOREMS"))
         (vector$a-aggressive (symbolicate vector vector$a "-AGGRESSIVE"))
         (world (w state))
         (stobj$a-property (cdr (assoc vector (table-alist 'stobj$a-property world))))
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

         (copy-rec-of-fixer$a-2 (symbolicate vector copy-rec "-OF-" fixer$a "-2"))
         (recognizer$a-of-copy (symbolicate vector recognizer$a "-OF-" copy))
         (copy-of-fixer$a-1 (symbolicate vector copy "-OF-" fixer$a "-1"))
         (copy-of-fixer$a-2 (symbolicate vector copy "-OF-" fixer$a "-2"))
         (length$a-of-copy (symbolicate vector length$a "-OF-" copy))

         (fi-bindings
          (list `(lem-vector$a::element-coupled-p ,(or element-coupled-p
                                                       '(lambda (value)
                                                         t)))
                (if resizable
                    `(lem-vector$a::coupledp/resizable ,(if element-coupled-p
                                                            coupledp
                                                            '(lambda (value)
                                                              t)))
                    `(lem-vector$a::coupledp/fixed ,(if element-coupled-p
                                                        coupledp
                                                        '(lambda (value)
                                                          t))))

                `(lem-vector$a::default-length (lambda ()
                                                 ,default-length-name))
                `(lem-vector$a::element-recognizer ,(or element-recognizer
                                                        '(lambda (value)
                                                          t)))
                `(lem-vector$a::initial-element ,(or element-creator
                                                     `(lambda ()
                                                        ,initial-element-name)))
                `(lem-vector$a::element-fixer ,(or element-fixer
                                                   '(lambda (value)
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
                    `(lem-vector$a::updater/fixed ,updater$a))))
         (fi-bindings-with-copy
          (list* `(lem-vector$a::element-copy ,(or element-copy
                                                   `(lambda (%value value)
                                                      (,element-fixer value))))
                 (if resizable
                     `(lem-vector$a::copy/resizable-rec ,copy-rec)
                     `(lem-vector$a::copy/fixed-rec ,copy-rec))
                 (if resizable
                     `(lem-vector$a::copy/resizable ,copy)
                     `(lem-vector$a::copy/fixed ,copy))
                 fi-bindings)))

    `(progn
       (deflabel ,coupledp-begin)

       (with-books (("../lemmas/vector$a"))

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
              (union-theories (theory 'acl2::ground-zero)
                              (union-theories (theory ',vector$a-theorems)
                                              (theory ',vector$a-aggressive)))
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
                                            (nfix index))
                                        t
                                        (element-coupled-p value))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           ,(if resizable
                                'lem-vector$a::coupledp/resizable-of-updater/resizable
                                'lem-vector$a::coupledp/fixed-of-updater/fixed)
                           ,@fi-bindings))))

                  (in-theory
                    (disable ,coupledp))))

         ;; `COPY-REC'
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
           (declare (xargs :stobjs (,%vector ,vector)))
           (let* ((length (,length ,vector))
                  (,%vector (if (= (,length ,%vector) length)
                                ,%vector
                                (,resizer length ,%vector))))
             (,copy-rec length ,%vector ,vector)))

         (table copy ',vector ',copy)

         (local
           (defthm ,copy-rec-of-fixer$a-2
             (equal (,copy-rec ,index ,%vector (,fixer$a ,vector))
                    (,copy-rec ,index ,%vector ,vector))))

         (local
           (in-theory
             (disable ,fixer$a
                      nfix)))

         (defthm ,recognizer$a-of-copy
           (,recognizer$a (,copy ,%vector ,vector))
           :hints
           (("Goal"
             :do-not-induct t
             :by (:functional-instance
                  ,(if resizable
                       'lem-vector$a::recognizer/resizable-of-copy/resizable
                       'lem-vector$a::recognizer/fixed-of-copy/fixed)
                  ,@fi-bindings-with-copy))
            ("Subgoal 9"
             :in-theory (enable (:d ,resizer$a)))
            ("Subgoal 7"
             :in-theory (enable (:d ,accessor$a)
                                (:d ,creator$a)))
            ("Subgoal 6"
             :in-theory (enable (:d ,accessor$a)))
            ("Subgoal 5"
             :in-theory (enable (:d ,creator$a)
                                (:d ,recognizer$a)))
            ("Subgoal 4"
             :in-theory (enable (:d ,recognizer$a)
                                ,@(and (not resizable)
                                       `((:d ,recognizer$a-aux)))
                                (:d ,creator$a)
                                (:d ,length$a)))
            ("Subgoal 3"
             :in-theory (enable (:d ,recognizer$a)
                                ,@(and (not resizable)
                                       `((:d ,recognizer$a-aux)))))
            ("Subgoal 2"
             :in-theory (enable (:d ,accessor$a)))
            ("Subgoal 1"
             :in-theory (enable (:d ,updater$a)))))

         (defthm ,copy-of-fixer$a-1
           (equal (,copy (,fixer$a ,%vector) ,vector)
                  (,copy ,%vector ,vector))
           :hints
           (("Goal"
             :by (:functional-instance
                  ,(if resizable
                       'lem-vector$a::copy/resizable-of-fixer/resizable-1
                       'lem-vector$a::copy/fixed-of-fixer/fixed-1)
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
           (disable ,copy-rec
                    ,copy))

         (defthm ,copy{rewrite}
           ,(if element-coupled-p
                `(implies (,coupledp ,vector)
                          (equal (,copy ,%vector ,vector)
                                 (,fixer ,vector)))
                `(equal (,copy ,%vector ,vector)
                        (,fixer$a ,vector)))
           :hints
           (("Goal"
             :by (:functional-instance
                  ,(if resizable
                       'lem-vector$a::copy/resizable{rewrite}
                       'lem-vector$a::copy/fixed{rewrite})
                  ,@fi-bindings-with-copy)))))

       (deflabel ,coupledp-end)

       (deftheory-static ,coupledp-theory
         (set-difference-theories (current-theory ',coupledp-end)
                                  (current-theory ',coupledp-begin))))))


;;;; `MAKE-HASH-TABLE-COPY-EVENTS'
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
         (coupled-vals-p (symbolicate hash-table hash-table "-COUPLED-VALS-P"))

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

         (coupledp-when-not-recognizer$a (symbolicate hash-table coupledp "-WHEN-NOT-" recognizer$a))
         (coupledp-of-creator$a (symbolicate hash-table coupledp "-OF-" creator$a))
         (coupledp-of-fixer$a (symbolicate hash-table coupledp "-OF-" fixer$a))
         (coupledp-of-updater$a-when-boundp$a (symbolicate hash-table coupledp "-OF-" updater$a "-WHEN-" boundp$a))
         (coupledp-of-updater$a-when-not-boundp$a (symbolicate hash-table coupledp "-OF-" updater$a "-WHEN-NOT-" boundp$a))
         (coupledp-of-remover$a-when-boundp$a (symbolicate hash-table coupledp "-OF-" remover$a "-WHEN-" boundp$a))
         (coupledp-of-remover$a-when-not-boundp$a (symbolicate hash-table coupledp "-OF-" remover$a "-WHEN-NOT-" boundp$a))
         (cardinality-of-keys$a-when-coupledp (symbolicate hash-table "CARDINALITY-OF-" keys$a "-WHEN-" coupledp))
         (in-of-keys$a-when-coupledp (symbolicate hash-table "IN-OF-" keys$a "-WHEN-" coupledp))
         (val-coupled-p-of-accessor$a (symbolicate hash-table val-coupled-p "-OF-" accessor$a))
         (emptyp-of-keys$a-when-coupledp (symbolicate "EMPTYP-OF-" keys$a "-WHEN-" coupledp))

         (recognizer$a-of-copy (symbolicate hash-table recognizer$a "-OF-" copy))
         (copy-of-fixer$a-1 (symbolicate hash-table copy "-OF-" fixer$a "-1"))
         (copy-of-fixer$a-2 (symbolicate hash-table copy "-OF-" fixer$a "-2"))
         (count$a-of-copy (symbolicate hash-table count$a "-OF-" copy))
         (accessor$a-of-copy (symbolicate hash-table accessor$a "-OF-" copy))
         (boundp$a-of-copy (symbolicate hash-table boundp$a "-OF-" copy))
         (keys$a-of-copy (symbolicate hash-table keys$a "-OF-" copy))


    `(progn
       (deflabel ,coupledp-begin)

       (with-books (("../lemmas/hash-table$a"))

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
              (union-theories (theory 'acl2::ground-zero)
                              (union-theories (theory ',hash-table$a-theorems)
                                              (theory ',hash-table$a-aggressive)))
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
                      (enable ,val-coupled-p-theory)))))

         ,@(and val-stobj-property
                `((local
                    (in-theory
                      (enable ,@(strip-cars (cdr (getpropc val 'acl2::absstobj-info))))))))

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

         (defthm ,coupledp-when-not-recognizer$a
           (implies (not (,recognizer$a ,hash-table))
                    (,coupledp ,hash-table))
           :hints
           (("Goal"
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

         (defthm ,coupledp-of-updater$a-when-boundp$a
           (implies (and (,boundp$a ,key ,hash-table)
                         (,coupledp ,hash-table))
                    ,(if val-coupled-p
                         `(equal (,coupledp (,updater$a ,key ,val ,hash-table))
                                 (,val-coupled-p ,val))
                         `(,coupledp (,updater$a ,key ,val ,hash-table))))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::coupledp-of-updater/copyable-when-boundp/copyable
                  ,@fi-bindings))))

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
                                       (set::subset set (,keys ,hash-table)))))
           (if (set::emptyp set)
               (,fixer ,%hash-table)
               ,(if val-copy
                    `(let ((,key ,(if key-fixer `(,key-fixer (set::head set)) '(set::head set))))
                       (stobj-let ((,val (,accessor ,key ,hash-table) ,updater))
                                  (,%hash-table)
                                  (stobj-let ((,%val (,%accessor ,key ,%hash-table) ,%updater))
                                             (,%val)
                                             (,val-copy ,%val ,val)
                                    ,%hash-table)
                         (,copy-rec (set::tail set) ,%hash-table ,hash-table)))
                    `(let* ((,key ,(if key-fixer `(,key-fixer (set::head set)) '(set::head set)))
                            (,val (,accessor ,key ,hash-table))
                            (,%hash-table (,updater ,key ,val ,%hash-table)))
                       (,copy-rec (set::tail set) ,%hash-table ,hash-table)))))

         ;; `COPY'
         (defun ,copy (,%hash-table ,hash-table)
           (declare (xargs :stobjs (,%hash-table ,hash-table)))
           (let* ((,keys (,keys ,hash-table))
                  (,count (,count ,hash-table))
                  (,%hash-table (,init ,count nil nil ,%hash-table))
                  (,%hash-table (,keys-set ,keys ,%hash-table)))
             (,copy-rec keys ,%hash-table ,hash-table)))

         (table copy ',hash-table ',copy)

         (local
           (in-theory
             (disable ,fixer$a)))

         (defthm ,recognizer$a-of-copy ; HERE
           (,recognizer$a (,copy ,%hash-table ,hash-table))
           :otf-flg t ; TODO: delete
           :hints
           (("Goal"
             :do-not-induct t
             :by (:functional-instance
                  lem-hash-table$a::recognizer/copyable-of-copy
                  ,@fi-bindings-with-copy))))

         (defthm ,copy-of-fixer$a-1
           (equal (,copy (,fixer$a ,%hash-table) ,hash-table)
                  (,copy ,%hash-table ,hash-table))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::copy-of-fixer/copyable-1
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
           (disable ,copy-rec
                    ,copy))

         (defthm ,copy{rewrite}
           (implies (,coupledp ,hash-table)
                    (equal (,copy ,%hash-table ,hash-table)
                           (,fixer$a ,hash-table)))
           :hints
           (("Goal"
             :by (:functional-instance
                  lem-hash-table$a::copy{rewrite}
                  ,@fi-bindings-with-copy)))))

       (deflabel ,coupledp-end)

       (deftheory-static ,coupledp-theory
         (set-difference-theories (current-theory ',coupledp-end)
                                  (current-theory ',coupledp-begin))))))


;;;; `MAKE-FRAME-COPY-EVENTS'
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
