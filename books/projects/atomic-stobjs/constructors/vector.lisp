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

(include-book "../type-spec")
(include-book "../utilities/top")
(include-book "vector$c")
(include-book "vector$a")
(include-book "vector$abs")

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
