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

(include-book "std/basic/arith-equiv-defs" :dir :system)

(include-book "../utilities/top")


;;;; `DEFINE-VECTOR$CORR'
(defmacro define-vector$corr (vector
                              &key
                                (logic 'nil)
                                (exec 'nil)

                                (pkg-witness 'nil pkg-witness-supplied-p)
                                (pkg-witness$a 'nil pkg-witness$a-supplied-p)
                                (pkg-witness$c 'nil pkg-witness$c-supplied-p)
                                (debug 'nil))

  (declare (xargs :guard (and (symbolp vector)
                              (symbolp logic)
                              (symbolp exec)
                              ;; (pkg-witness-p pkg-witness)
                              ;; (pkg-witness-p pkg-witness$a)
                              ;; (pkg-witness-p pkg-witness$c)
                              (booleanp debug))))

  `(with-output
     ,@(and (not debug)
            *constructor-output*)

     (make-event
       (let* ((vector ',vector)
              (logic ',logic)
              (exec ',exec)
              (pkg-witness (pkg-witness-fix (if ',pkg-witness-supplied-p
                                                ',pkg-witness
                                                (current-package state))))
              (pkg-witness$a (pkg-witness-fix (if ',pkg-witness$a-supplied-p
                                                  ',pkg-witness$a
                                                  pkg-witness)))
              (pkg-witness$c (pkg-witness-fix (if ',pkg-witness$c-supplied-p
                                                  ',pkg-witness$c
                                                  pkg-witness)))

              (vector$corr (symbolicate$ pkg-witness vector "$CORR"))
              (vector$corr-contents (symbolicate$ pkg-witness vector$corr "-CONTENTS"))

              (vector$a (or logic
                            (symbolicate$ pkg-witness$a vector "$A")))
              (vector$c (or exec
                            (symbolicate$ pkg-witness$c vector "$C")))

              (stobj$c-property (stobj$c-property vector$c (w state)))
              (recognizer$c (access vector$c-property stobj$c-property :recognizer))
              (length$c (access vector$c-property stobj$c-property :length))
              (accessor$c (access vector$c-property stobj$c-property :accessor))

              (stobj$a-property (stobj$a-property vector$a (w state)))
              (recognizer$a (access vector$a-property stobj$a-property :recognizer))
              (length$a (access vector$a-property stobj$a-property :length))
              (accessor$a (access vector$a-property stobj$a-property :accessor)))

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

       (pkg-witness 'nil pkg-witness-supplied-p)
       (pkg-witness$a 'nil pkg-witness$a-supplied-p)
       (pkg-witness$c 'nil pkg-witness$c-supplied-p)
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
                              ;; (pkg-witness-p pkg-witness)
                              ;; (pkg-witness-p pkg-witness$a)
                              ;; (pkg-witness-p pkg-witness$c)
                              (booleanp debug))))

  `(with-output
     ,@(and (not debug)
            *constructor-output*)

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
              (pkg-witness (pkg-witness-fix (if ',pkg-witness-supplied-p
                                                ',pkg-witness
                                                (current-package state))))
              (pkg-witness$a (pkg-witness-fix (if ',pkg-witness$a-supplied-p
                                                  ',pkg-witness$a
                                                  pkg-witness)))
              (pkg-witness$c (pkg-witness-fix (if ',pkg-witness$c-supplied-p
                                                  ',pkg-witness$c
                                                  pkg-witness)))

              ;; Interface Symbols
              (vector$a (or logic
                            (symbolicate$ pkg-witness$a vector "$A")))
              (vector$c (or exec
                            (symbolicate$ pkg-witness$c vector "$C")))
              (recognizer (or recognizer
                              (symbolicate$ pkg-witness vector (make-predicate-suffix vector))))
              (creator (or creator
                           (symbolicate$ pkg-witness "CREATE-" vector)))
              (fixer (or fixer
                         (symbolicate$ pkg-witness vector "-FIX")))
              (length (or length
                          (symbolicate$ pkg-witness vector "-LEN")))
              (resizer (or resizer
                           (symbolicate$ pkg-witness vector "-RSZ")))
              (accessor (or accessor
                            (symbolicate$ pkg-witness vector "-REF")))
              (updater (or updater
                           (symbolicate$ pkg-witness vector "-SET")))

              (world (w state))
              (vector$corr-list (cdr (assoc vector (table-alist 'corr world))))
              (vector$corr-contents (first vector$corr-list))
              (vector$corr-contents-witness (symbolicate$ vector$corr-contents vector$corr-contents "-WITNESS"))
              (vector$corr (second vector$corr-list))

              ;; `VECTOR$A'
              (stobj$a-property (stobj$a-property vector$a world))
              (recognizer$a (access vector$a-property stobj$a-property :recognizer))
              (creator$a (access vector$a-property stobj$a-property :creator))
              (fixer$a (access vector$a-property stobj$a-property :fixer))
              (length$a (access vector$a-property stobj$a-property :length))
              (resizer$a (access vector$a-property stobj$a-property :resizer))
              (accessor$a (access vector$a-property stobj$a-property :accessor))
              (updater$a (access vector$a-property stobj$a-property :updater))

              (element (access vector$a-property stobj$a-property :element))
              (element-stobj-property (getpropc element 'acl2::stobj))
              (element-recognizer (if element-stobj-property
                                      (caadr element-stobj-property)
                                      (access vector$a-property stobj$a-property :element-recognizer)))
              (resizable (access vector$a-property stobj$a-property :resizable))
              (default-length-name (access vector$a-property stobj$a-property :default-length))

              ;; `VECTOR$C'
              (stobj$c-property (stobj$c-property vector$c (w state)))
              (recognizer$c (access vector$c-property stobj$c-property :recognizer))
              (creator$c (access vector$c-property stobj$c-property :creator))
              (fixer$c (access vector$c-property stobj$c-property :fixer))
              (fixer$c$inline (or (cdr (assoc fixer$c (table-alist 'acl2::macro-aliases-table world)))
                                  fixer$c))
              (length$c (access vector$c-property stobj$c-property :length))
              (resizer$c (access vector$c-property stobj$c-property :resizer))
              (accessor$c (access vector$c-property stobj$c-property :accessor))
              (updater$c (access vector$c-property stobj$c-property :updater))

              ;; Theorem Names
              (creator{correspondence} (symbolicate$ pkg-witness creator "{CORRESPONDENCE}"))
              (creator{preserved} (symbolicate$ pkg-witness creator "{PRESERVED}"))
              (fixer{correspondence} (symbolicate$ pkg-witness fixer "{CORRESPONDENCE}"))
              (fixer{preserved} (symbolicate$ pkg-witness fixer "{PRESERVED}"))
              (length{correspondence} (symbolicate$ pkg-witness length "{CORRESPONDENCE}"))
              (resizer{correspondence} (symbolicate$ pkg-witness resizer "{CORRESPONDENCE}"))
              (resizer{preserved} (symbolicate$ pkg-witness resizer "{PRESERVED}"))
              (accessor{correspondence} (symbolicate$ pkg-witness accessor "{CORRESPONDENCE}"))
              (accessor{guard-thm} (symbolicate$ pkg-witness accessor "{GUARD-THM}"))
              (updater{correspondence} (symbolicate$ pkg-witness updater "{CORRESPONDENCE}"))
              (updater{guard-thm} (symbolicate$ pkg-witness updater "{GUARD-THM}"))
              (updater{preserved} (symbolicate$ pkg-witness updater "{PRESERVED}"))

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
               (cdr (untranslate (getpropc updater$c 'acl2::guard) nil world)))
              (updater$c-guard (if element-stobj-property
                                   (cddr updater$c-guard)
                                   (cdr updater$c-guard)))

              (aggressive$a (symbolicate$ pkg-witness$a vector$a "-AGGRESSIVE"))

              (resizer$c-index (car (getpropc resizer$c 'acl2::formals)))
              (accessor$c-index (car (getpropc accessor$c 'acl2::formals)))
              (updater$c-index (car (getpropc updater$c 'acl2::formals)))
              (updater$c-value (cadr (getpropc updater$c 'acl2::formals))))

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
                    :cases ((< (,vector$corr-contents-witness (,resizer$c ,resizer$c-index ,vector$c)
                                                              (,resizer$a ,resizer$c-index ,vector))
                               (,length$c ,vector$c)))
                    :in-theory (e/d (,aggressive$a)
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

            (table stobj$a ',vector ',stobj$a-property))))))
