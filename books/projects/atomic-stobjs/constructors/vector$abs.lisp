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


;;;; `DEFINE-VECTOR$CORR'
(defmacro define-vector$corr (vector
                              &key
                                (logic 'nil)
                                (exec 'nil)

                                (debug 'nil))

  (declare (xargs :guard (and (symbolp vector)
                              (symbolp logic)
                              (symbolp exec)
                              (booleanp debug))))

  `(with-output
     ,@(and (not debug)
            '#!acl2(:off (warning! observation prove event history proof-tree)
                         :summary-off (rules)
                         :gag-mode t))

     (make-event
       (let* ((vector ',vector)
              (logic ',logic)
              (exec ',exec)

              (vector$corr (symbolicate vector vector "$CORR"))
              (vector$corr-contents (symbolicate vector vector$corr "-CONTENTS"))

              (vector$a (or logic
                            (symbolicate vector vector "$A")))
              (vector$c (or exec
                            (symbolicate vector vector "$C")))

              (stobj-property (getpropc vector$c 'stobj))
              (recognizer$c (caadr stobj-property))
              (length$c (second (third stobj-property)))
              (accessor$c (fourth (third stobj-property)))

              (stobj$a-property (cdr (assoc vector$a (table-alist 'stobj$a-property (w state)))))
              (recognizer$a (first (second stobj$a-property)))
              (length$a (first (third (third stobj$a-property))))
              (accessor$a (third (third (third stobj$a-property)))))

         `(progn
            (defun-sk ,vector$corr-contents (,vector$c ,vector$a)
              (declare (xargs :stobjs ,vector$c
                              :guard t
                              :verify-guards nil))
              (forall index
                (implies (and (natp index)
                              (< index (,length$c ,vector$c)))
                         (equal (,accessor$c index ,vector$c)
                                (,accessor$a index ,vector$a))))
              :rewrite :direct)

            (defun-nx ,vector$corr (,vector$c ,vector$a)
              (declare (xargs :stobjs ,vector$c
                              :guard (,recognizer$a ,vector$a)
                              :verify-guards nil))
              (and (,recognizer$c ,vector$c)
                   (,recognizer$a ,vector$a)
                   (= (,length$c ,vector$c)
                      (,length$a ,vector$a))
                   (,vector$corr-contents ,vector$c
                                          ,vector$a)))

            (table corr ',vector ',(list vector$corr-contents
                                         vector$corr)))))))


;;;; `DEFINE-VECTOR$ABS'
(defmacro define-vector$abs
    (vector
     &key
       (logic 'nil)
       (exec 'nil)

       (recognizer 'nil)
       (creator 'nil)
       (fixer 'nil)
       (length 'nil)
       (resizer 'nil)
       (accessor 'nil)
       (updater 'nil)

       (executable 'nil)

       (debug 'nil))

  (declare (xargs :guard (and (symbolp vector)
                              (symbolp logic)
                              (symbolp exec)
                              (symbol-listp (list recognizer
                                                  creator
                                                  fixer
                                                  length
                                                  resizer
                                                  accessor
                                                  updater))
                              (booleanp executable)
                              (booleanp debug))))

  `(with-output
     ,@(and (not debug)
            '#!acl2(:off (warning! observation prove event history proof-tree)
                         :summary-off (rules)
                         :gag-mode t))

     (make-event
       (let* ((vector ',vector)
              (logic ',logic)
              (exec ',exec)
              (recognizer ',recognizer)
              (creator ',creator)
              (fixer ',fixer)
              (length ',length)
              (resizer ',resizer)
              (accessor ',accessor)
              (updater ',updater)
              (executable ',executable)

              ;; Interface Symbols
              (vector$a (or logic
                            (symbolicate vector vector "$A")))
              (vector$c (or exec
                            (symbolicate vector vector "$C")))
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
                           (symbolicate vector vector "-SET")))

              (world (w state))
              (vector$corr-list (cdr (assoc vector (table-alist 'corr world))))
              (vector$corr-contents (first vector$corr-list))
              (vector$corr (second vector$corr-list))

              ;; `VECTOR$C'
              (stobj-property (getpropc vector$c 'stobj))
              (recognizer$c (caadr stobj-property))
              (creator$c (cdadr stobj-property))
              (fixer$c (cdr (assoc vector$c (table-alist 'fixer world))))
              (fixer$c$inline (or (cdr (assoc fixer$c (table-alist 'acl2::macro-aliases-table world)))
                                  fixer$c))
              (length$c (second (third stobj-property)))
              (resizer$c (third (third stobj-property)))
              (accessor$c (fourth (third stobj-property)))
              (updater$c (fifth (third stobj-property)))

              ;; `VECTOR$A'
              (stobj$a-property (cdr (assoc vector$a (table-alist 'stobj$a-property world))))
              (recognizer$a (first (second stobj$a-property)))
              (creator$a (second (second stobj$a-property)))
              (fixer$a (third (second stobj$a-property)))
              (length$a (first (third (third stobj$a-property))))
              (resizer$a (second (third (third stobj$a-property))))
              (accessor$a (third (third (third stobj$a-property))))
              (updater$a (fourth (third (third stobj$a-property))))
              (element (first (first (third stobj$a-property))))
              (element-recognizer (second (first (third stobj$a-property))))
              (resizable (first (second (third stobj$a-property))))
              (default-length-name (second (second (third stobj$a-property))))

              (element-stobj-property (getpropc element 'stobj))

              ;; Theorem Names
              (creator{correspondence} (symbolicate vector creator "{CORRESPONDENCE}"))
              (creator{preserved} (symbolicate vector creator "{PRESERVED}"))
              (fixer{correspondence} (symbolicate vector fixer "{CORRESPONDENCE}"))
              (fixer{preserved} (symbolicate vector fixer "{PRESERVED}"))
              (length{correspondence} (symbolicate vector length "{CORRESPONDENCE}"))
              (resizer{correspondence} (symbolicate vector resizer "{CORRESPONDENCE}"))
              (resizer{preserved} (symbolicate vector resizer "{PRESERVED}"))
              (accessor{correspondence} (symbolicate vector accessor "{CORRESPONDENCE}"))
              (accessor{guard-thm} (symbolicate vector accessor "{GUARD-THM}"))
              (updater{correspondence} (symbolicate vector updater "{CORRESPONDENCE}"))
              (updater{guard-thm} (symbolicate vector updater "{GUARD-THM}"))
              (updater{preserved} (symbolicate vector updater "{PRESERVED}"))

              ;; Exports
              (exports `((,fixer :logic ,fixer$a
                                 :exec ,fixer$c$inline)
                         (,length :logic ,length$a
                                  :exec ,length$c)
                         (,resizer :logic ,resizer$a
                                   :exec ,resizer$c)
                         (,accessor :logic ,accessor$a
                                    :exec ,accessor$c
                                    ,@(and element-stobj-property
                                           `(:updater ,updater)))
                         (,updater :logic ,updater$a
                                   :exec ,updater$c)))

              ;; Miscellaneous
              (updater$c-guard
               (cdr (untranslate (getpropc updater$c 'guard) nil world)))
              (updater$c-guard (if element-stobj-property
                                   (cddr updater$c-guard)
                                   (cdr updater$c-guard)))

              (aggressive$a (symbolicate vector$a vector$a "-AGGRESSIVE"))
              (accessor$c-of-resizer$c (symbolicate vector$c accessor$c "-OF-" resizer$c))

              (resizer$c-index (car (getpropc resizer$c 'formals)))
              (accessor$c-index (car (getpropc accessor$c 'formals)))
              (updater$c-index (car (getpropc updater$c 'formals)))
              (updater$c-value (cadr (getpropc updater$c 'formals))))

         `(encapsulate ()

            (local
              (progn
                (defthm ,creator{correspondence}
                  (,vector$corr (,creator$c) (,creator$a))
                  :rule-classes nil)

                (defthm ,creator{preserved}
                  (,recognizer$a (,creator$a))
                  :rule-classes nil)

                (defthm ,fixer{correspondence}
                  (implies (and (,vector$corr ,vector$c ,vector)
                                (,recognizer$a ,vector))
                           (,vector$corr (,fixer$c ,vector$c)
                                         (,fixer$a ,vector)))
                  :rule-classes nil)

                (defthm ,fixer{preserved}
                  (implies (,recognizer$a ,vector)
                           (,recognizer$a (,fixer$a ,vector)))
                  :rule-classes nil)

                (defthm ,length{correspondence}
                  (implies (and (,vector$corr ,vector$c ,vector)
                                (,recognizer$a ,vector))
                           (equal (,length$c ,vector$c)
                                  (,length$a ,vector)))
                  :rule-classes nil)

                (defthm ,resizer{correspondence}
                  (implies (and (,vector$corr ,vector$c ,vector)
                                (natp ,resizer$c-index)
                                (,recognizer$a ,vector))
                           (,vector$corr (,resizer$c ,resizer$c-index ,vector$c)
                                         (,resizer$a ,resizer$c-index ,vector)))
                  :rule-classes nil
                  :hints
                  (("Goal"
                    :in-theory (e/d (,aggressive$a
                                     ,@(and resizable
                                            `(,accessor$c-of-resizer$c)))
                                    (,vector$corr-contents))
                    :expand (,vector$corr-contents (,resizer$c ,resizer$c-index ,vector$c)
                                                   (,resizer$a ,resizer$c-index ,vector)))))

                (defthm ,resizer{preserved}
                  (implies (and (natp ,resizer$c-index)
                                (,recognizer$a ,vector))
                           (,recognizer$a (,resizer$a ,resizer$c-index ,vector)))
                  :rule-classes nil)

                (defthm ,accessor{correspondence}
                  (implies (and (,vector$corr ,vector$c ,vector)
                                (natp ,accessor$c-index)
                                (,recognizer$a ,vector)
                                (< ,accessor$c-index ,(if resizable
                                                          `(,length$a ,vector)
                                                          default-length-name)))
                           (equal (,accessor$c ,accessor$c-index ,vector$c)
                                  (,accessor$a ,accessor$c-index ,vector)))
                  :rule-classes nil
                  :hints
                  (("Goal"
                    :in-theory (e/d (,aggressive$a)
                                    (,vector$corr-contents)))))

                (defthm ,accessor{guard-thm}
                  (implies (and (,vector$corr ,vector$c ,vector)
                                (natp ,accessor$c-index)
                                (,recognizer$a ,vector)
                                (< ,accessor$c-index ,(if resizable
                                                          `(,length$a ,vector)
                                                          default-length-name)))
                           (and (integerp ,accessor$c-index)
                                (<= 0 ,accessor$c-index)
                                (< ,accessor$c-index (,length$c ,vector$c))))
                  :rule-classes nil)

                (defthm ,updater{correspondence}
                  (implies (and (,vector$corr ,vector$c ,vector)
                                (natp ,updater$c-index)
                                ,@(and element-recognizer
                                       `((,element-recognizer ,updater$c-value)))
                                (,recognizer$a ,vector)
                                (< ,updater$c-index ,(if resizable
                                                         `(,length$a ,vector)
                                                         default-length-name)))
                           (,vector$corr (,updater$c ,updater$c-index ,updater$c-value ,vector$c)
                                         (,updater$a ,updater$c-index ,updater$c-value ,vector)))
                  :rule-classes nil
                  :hints
                  (("Goal"
                    :in-theory (e/d (,aggressive$a)
                                    (,vector$corr-contents))
                    :expand (,vector$corr-contents (,updater$c ,updater$c-index ,updater$c-value ,vector$c)
                                                   (,updater$a ,updater$c-index ,updater$c-value ,vector)))))

                (defthm ,updater{guard-thm}
                  (implies (and (,vector$corr ,vector$c ,vector)
                                (natp ,updater$c-index)
                                ,@(and element-recognizer
                                       `((,element-recognizer ,updater$c-value)))
                                (,recognizer$a ,vector)
                                (< ,updater$c-index ,(if resizable
                                                         `(,length$a ,vector)
                                                         default-length-name)))
                           (and ,@updater$c-guard))
                  :rule-classes nil)

                (defthm ,updater{preserved}
                  (implies (and (natp ,updater$c-index)
                                ,@(and element-recognizer
                                       `((,element-recognizer ,updater$c-value)))
                                (,recognizer$a ,vector)
                                (< ,updater$c-index ,(if resizable
                                                         `(,length$a ,vector)
                                                         default-length-name)))
                           (,recognizer$a (,updater$a ,updater$c-index ,updater$c-value ,vector)))
                  :rule-classes nil)))

            (defabsstobj ,vector
              :foundation ,vector$c
              :recognizer (,recognizer :logic ,recognizer$a
                                       :exec ,recognizer$c)
              :creator (,creator :logic ,creator$a
                                 :exec ,creator$c)
              :corr-fn ,vector$corr
              :non-executable ,(not executable)
              :exports ,exports)

            (table stobj$a-property ',vector ',stobj$a-property))))))
