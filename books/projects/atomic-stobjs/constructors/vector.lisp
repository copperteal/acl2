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


;;;; Prologue
(in-package "ATOMIC-STOBJS")

#||
(include-book "std/top" :dir :system) ; TODO: drop?
(include-book "../lemmas/vector$c")
(include-book "../lemmas/vector$a")
(include-book "../lemmas/vector$abs")
(include-book "../lemmas/vector")
||#

(include-book "../type-spec")
(include-book "../accessors/top")
(include-book "../utilities/top")

(deflabel define-vector-begin)


;;;; `VECTOR' Guard Predicates
(defun valid-vector-dimensions-p (dimensions)
  ;; TODO: refactor into separate file
  (declare (xargs :guard t))
  (or (and (consp dimensions)
           (natp (car dimensions))
           (null (cdr dimensions)))
      (natp dimensions)))

(defthm valid-vector-dimensions-p{compound-recognizer}
  ;; Q: Is this theorem useful?
  (implies (valid-vector-dimensions-p dimensions)
           (or (natp dimensions)
               (and (consp dimensions)
                    (true-listp dimensions))))
  :rule-classes :compound-recognizer)


;;;; `DEFINE-VECTOR$C'
(include-book "vector$c")


;;;; `DEFINE-VECTOR$A'
(include-book "vector$a")


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
  (let* ((vector$a (or logic
                      (symbolicate vector vector '$a)))
         (vector$c (or exec
                      (symbolicate vector vector '$c)))
         (vector$corr (symbolicate vector vector '$corr))
         (vector$corr-contents (symbolicate vector vector$corr '-contents)))

    `(with-output
       ,@(and (not debug)
              '#!acl2(:off (warning! observation prove event history proof-tree)
                           :summary-off (rules)
                           :gag-mode t))

       (make-event
         (let* ((recognizer$c (stobj-recognizer ',vector$c))
                (recognizer$a (stobj$a-recognizer ',vector$a))
                (length$c (stobj$c-vector-length ',vector$c))
                (length$a (stobj$a-vector-length ',vector$a))
                (accessor$c (stobj$c-vector-accessor ',vector$c))
                (accessor$a (stobj$a-vector-accessor ',vector$a)))

           `(progn
              (defun-sk ,',vector$corr-contents (,',vector$c ,',vector$a)
                (declare (xargs :stobjs ,',vector$c
                                :guard t
                                :verify-guards nil))
                (forall i
                  (implies (and (natp i)
                                (< i (,length$c ,',vector$c)))
                           (equal (,accessor$c i ,',vector$c)
                                  (,accessor$a i ,',vector$a))))
                :rewrite :direct)

              (defun-nx ,',vector$corr (,',vector$c ,',vector$a)
                (declare (xargs :stobjs ,',vector$c
                                :guard (,recognizer$a ,',vector$a)
                                :verify-guards nil))
                (and (,recognizer$c ,',vector$c)
                     (,recognizer$a ,',vector$a)
                     (= (,length$c ,',vector$c)
                        (,length$a ,',vector$a))
                     (,',vector$corr-contents ,',vector$c
                                             ,',vector$a)))))))))


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

  (let* ((vector$a (or logic
                      (symbolicate vector vector '$a)))
         (vector$c (or exec
                      (symbolicate vector vector '$c)))

         (recognizer (or recognizer
                         (symbolicate vector vector (make-predicate-suffix vector))))
         (creator (or creator
                      (symbolicate vector 'create- vector)))
         (fixer (or fixer
                    (symbolicate vector vector '-fix)))
         (length (or length
                     (symbolicate vector vector '-length)))
         (resizer (or resizer
                      (symbolicate vector vector '-resize)))
         (accessor (or accessor
                       (symbolicate vector vector '-ref)))
         (updater (or updater
                      (symbolicate vector vector '-set)))

         (vector$corr (symbolicate vector vector '$corr))
         (vector$corr-contents (symbolicate vector vector$corr '-contents))
         (vector$corr-contents-witness (symbolicate vector vector$corr-contents '-witness))
         (vector-element-guard (symbolicate vector vector '-element-guard))

         (creator{correspondence} (symbolicate vector creator '{correspondence}))
         (creator{preserved} (symbolicate vector creator '{preserved}))
         (fixer{correspondence} (symbolicate vector fixer '{correspondence}))
         (fixer{preserved} (symbolicate vector fixer '{preserved}))
         (length{correspondence} (symbolicate vector length '{correspondence}))
         (resizer{correspondence} (symbolicate vector resizer '{correspondence}))
         (resizer{preserved} (symbolicate vector resizer '{preserved}))
         (accessor{correspondence} (symbolicate vector accessor '{correspondence}))
         (accessor{guard-thm} (symbolicate vector accessor '{guard-thm}))
         (updater{correspondence} (symbolicate vector updater '{correspondence}))
         (updater{guard-thm} (symbolicate vector updater '{guard-thm}))
         (updater{preserved} (symbolicate vector updater '{preserved})))

    `(with-output
       ,@(and (not debug)
              '#!acl2(:off (warning! observation prove event history proof-tree)
                           :summary-off (rules)
                           :gag-mode t))

       (make-event
         (let* ((recognizer$c (stobj-recognizer ',vector$c))
                (recognizer$a (stobj$a-recognizer ',vector$a))
                (creator$c (stobj-creator ',vector$c))
                (creator$a (stobj$a-creator ',vector$a))
                (fixer$c (symbolicate ',vector$c ',vector$c '-fix))
                (fixer$c$inline (symbolicate ',vector$c fixer$c '$inline))
                (fixer$a (stobj$a-fixer ',vector$a))
                (length$c (stobj$c-vector-length ',vector$c))
                (length$a (stobj$a-vector-length ',vector$a))
                (resizer$c (stobj$c-vector-resizer ',vector$c))
                (resizer$a (stobj$a-vector-resizer ',vector$a))
                (accessor$c (stobj$c-vector-accessor ',vector$c))
                (accessor$a (stobj$a-vector-accessor ',vector$a))
                (updater$c (stobj$c-vector-updater ',vector$c))
                (updater$a (stobj$a-vector-updater ',vector$a))
                (element-recognizer (stobj$a-vector-element-recognizer ',vector$a))
                (element-fixer (stobj$a-vector-element-fixer ',vector$a))
                (element (stobj$a-vector-element ',vector$a))
                (element-type-is-stobj (stobj-p element))
                (element-stobj$a (stobj$a-lookup element))
                (element-recognizer$a (if element-stobj$a
                                          (stobj$a-recognizer element-stobj$a)
                                          element-recognizer))
                (element-fixer$a (if element-stobj$a
                                     (stobj$a-fixer element-stobj$a)
                                     element-fixer))

                (exports `((,',fixer :logic ,fixer$a
                                     :exec ,fixer$c$inline)
                           (,',length :logic ,length$a
                                      :exec ,length$c)
                           (,',resizer :logic ,resizer$a
                                       :exec ,resizer$c)
                           (,',accessor :logic ,accessor$a
                                        :exec ,accessor$c
                                        ,@(and element-type-is-stobj
                                               `(:updater ,',updater)))
                           (,',updater :logic ,updater$a
                                       :exec ,updater$c)))

                (updater$c-guard
                 (cdr (untranslate (getpropc updater$c 'guard)
                                   nil
                                   (w state))))
                (updater$c-guard (if element-type-is-stobj
                                     (cddr updater$c-guard)
                                     (cdr updater$c-guard)))

                (aggressive$a (symbolicate ',vector$a ',vector$a '-aggressive)))

           `(encapsulate ()
              ,@(and (or element-recognizer$a
                         element-fixer$a)
                     `((local
                         (in-theory
                           (disable ,element-recognizer$a
                                    ,element-fixer$a)))))

              (local
                (defthm ,',vector-element-guard
                  (equal (,length$c (,creator$c)) (,length$a (,creator$a)))
                  :rule-classes nil))

              ;; Proof Obligations
              (lprogn
                (defthm ,',creator{correspondence}
                  (,',vector$corr (,creator$c) (,creator$a))
                  :rule-classes nil)

                (defthm ,',creator{preserved}
                  (,recognizer$a (,creator$a))
                  :rule-classes nil)

                (defthm ,',fixer{correspondence}
                  (implies (and (,',vector$corr ,',vector$c ,',vector)
                                (,recognizer$a ,',vector))
                           (,',vector$corr (,fixer$c ,',vector$c)
                                          (,fixer$a ,',vector)))
                  :rule-classes nil)

                (defthm ,',fixer{preserved}
                  (implies (,recognizer$a ,',vector)
                           (,recognizer$a (,fixer$a ,',vector)))
                  :rule-classes nil)

                (defthm ,',length{correspondence}
                  (implies (and (,',vector$corr ,',vector$c ,',vector)
                                (,recognizer$a ,',vector))
                           (equal (,length$c ,',vector$c)
                                  (,length$a ,',vector)))
                  :rule-classes nil)

                (defthm ,',resizer{correspondence}
                  (implies (and (,',vector$corr ,',vector$c ,',vector)
                                (natp i)
                                (,recognizer$a ,',vector))
                           (,',vector$corr (,resizer$c i ,',vector$c)
                                          (,resizer$a i ,',vector)))
                  :rule-classes nil
                  :hints
                  (("Goal"
                    :cases ((< (,',vector$corr-contents-witness (,resizer$c i ,',vector$c)
                                                               (,resizer$a i ,',vector))
                               (,length$a ,',vector)))
                    :in-theory (e/d (,aggressive$a)
                                    (,',vector$corr-contents))
                    :expand (,',vector$corr-contents (,resizer$c i ,',vector$c)
                                                    (,resizer$a i ,',vector)))))

                (defthm ,',resizer{preserved}
                  (implies (and (natp i)
                                (,recognizer$a ,',vector))
                           (,recognizer$a (,resizer$a i ,',vector)))
                  :rule-classes nil)

                (defthm ,',accessor{correspondence}
                  (implies (and (,',vector$corr ,',vector$c ,',vector)
                                (natp i)
                                (,recognizer$a ,',vector)
                                (< i (,length$a ,',vector)))
                           (equal (,accessor$c i ,',vector$c)
                                  (,accessor$a i ,',vector)))
                  :rule-classes nil
                  :hints
                  (("Goal"
                    :in-theory (disable ,',vector$corr-contents))))

                (defthm ,',accessor{guard-thm}
                  (implies (and (,',vector$corr ,',vector$c ,',vector)
                                (natp i)
                                (,recognizer$a ,',vector)
                                (< i (,length$a ,',vector)))
                           (and (integerp i)
                                (<= 0 i)
                                (< i (,length$c ,',vector$c))))
                  :rule-classes nil)

                (defthm ,',updater{correspondence}
                  (implies (and (,',vector$corr ,',vector$c ,',vector)
                                (natp i)
                                ,@(and element-recognizer
                                       `((,element-recognizer v)))
                                (,recognizer$a ,',vector)
                                (< i (,length$a ,',vector)))
                           (,',vector$corr (,updater$c i v ,',vector$c)
                                          (,updater$a i v ,',vector)))
                  :rule-classes nil
                  :hints
                  (("Goal"
                    :cases ((equal i (,',vector$corr-contents-witness (,updater$c i v ,',vector$c)
                                                                     (,updater$a i v ,',vector))))
                    :in-theory (disable ,',vector$corr-contents)
                    :expand (,',vector$corr-contents (,updater$c i v ,',vector$c)
                                                    (,updater$a i v ,',vector)))))

                (defthm ,',updater{guard-thm}
                  (implies (and (,',vector$corr ,',vector$c ,',vector)
                                (natp i)
                                ,@(and element-recognizer
                                       `((,element-recognizer v)))
                                (,recognizer$a ,',vector)
                                (< i (,length$a ,',vector)))
                           (and ,@updater$c-guard))
                  :rule-classes nil)

                (defthm ,',updater{preserved}
                  (implies (and (natp i)
                                ,@(and element-recognizer
                                       `((,element-recognizer v)))
                                (,recognizer$a ,',vector)
                                (< i (,length$a ,',vector)))
                           (,recognizer$a (,updater$a i v ,',vector)))
                  :rule-classes nil))

              (defabsstobj ,',vector
                :foundation ,',vector$c
                :recognizer (,',recognizer :logic ,recognizer$a
                                           :exec ,recognizer$c)
                :creator (,',creator :logic ,creator$a
                                     :exec ,creator$c)
                :corr-fn ,',vector$corr
                :non-executable ,',(not executable)
                :exports ,exports)

              (table stobj$a
                     'stobj$a-lookup-alist
                     (putprop ',',vector
                              'stobj$a
                              ',',vector$a
                              (stobj$a-lookup-alist world)))))))))


;;;; `DEFINE-VECTOR'
(defmacro define-vector
    (vector dimensions
     &key
       (element-type 't)
       (specialize-element-type 'nil)
       (element-recognizer 'nil)
       (element-fixer 'nil)
       (element 'x)
       (initial-element 'nil)
       (resizable 'nil)

       (inline 'nil)
       (memoizable 'nil)
       (executable 'nil)

       (recognizer 'nil)
       (creator 'nil)
       (length 'nil)
       (resizer 'nil)
       (accessor 'nil)
       (updater 'nil)

       (logic 'nil)
       (exec 'nil)

       (debug 'nil))

  (declare (xargs :guard (and (symbolp vector)
                              (valid-vector-dimensions-p dimensions)
                              (if (acl2-type-spec-p element-type)
                                  (typep$ initial-element element-type)
                                  (symbolp element-type))
                              (booleanp specialize-element-type)
                              (symbolp element-recognizer)
                              (symbolp element-fixer)
                              (symbolp element)
                              (booleanp resizable)
                              (booleanp inline)
                              (booleanp memoizable)
                              (booleanp executable)
                              (symbol-listp (list recognizer
                                                  creator
                                                  length
                                                  resizer
                                                  accessor
                                                  updater))
                              (symbolp logic)
                              (symbolp exec)
                              (booleanp debug))))

  (let* ((vector$a (or logic
                      (symbolicate vector vector '$a)))
         (vector$c (or exec
                      (symbolicate vector vector '$c)))
         (recognizer (or recognizer
                         (symbolicate vector vector (make-predicate-suffix vector))))
         (creator (or creator
                      (symbolicate vector 'create- vector)))
         (length (or length
                     (symbolicate vector vector '-length)))
         (resizer (or resizer
                      (symbolicate vector vector '-resize)))
         (accessor (or accessor
                       (symbolicate vector vector '-ref)))
         (updater (or updater
                      (symbolicate vector vector '-set))))

    `(with-output
       ,@(and (not debug)
              '#!acl2(:off (warning! observation prove event history proof-tree)
                           :summary-off (rules)
                           :gag-mode t))

       (make-event
         `(progn
            (define-vector$c ,',vector$c ,',dimensions
              :element-type ,',element-type
              :specialize-element-type ,',specialize-element-type
              :initial-element ,',initial-element
              :resizable ,',resizable
              :inline ,',inline
              :memoizable ,',memoizable
              :executable ,',executable
              :debug ,',debug)

            (define-vector$a ,',vector$a ,',dimensions
              :element-recognizer ,',element-recognizer
              :element-fixer ,',element-fixer
              :element ,',element
              :initial-element ,',initial-element
              :resizable ,',resizable
              :debug ,',debug)

            (define-vector$corr ,',vector
              :logic ,',vector$a
              :exec ,',vector$c
              :debug ,',debug)

            (define-vector$abs ,',vector
              :logic ,',vector$a
              :exec ,',vector$c
              :recognizer ,',recognizer
              :creator ,',creator
              :length ,',length
              :resizer ,',resizer
              :accessor ,',accessor
              :updater ,',updater
              :executable ,',executable
              :debug ,',debug)

            (in-theory
              (disable ,',(symbolicate vector$c vector$c '-theorems))))))))


;;;; `DEFINE-VECTOR-THEOREMS'
(deflabel define-vector-end)

(deftheory-static define-vector-theorems
  (set-difference-theories
   (set-difference-theories
    (current-theory 'define-vector-end)
    (current-theory 'define-vector-begin))
   (function-theory 'define-vector-end)))


;;;; Epilogue
(in-theory
  (union-theories (current-theory 'define-vector-begin)
                  (theory 'define-vector-theorems)))
