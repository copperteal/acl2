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
(set-verify-guards-eagerness 2)

(include-book "../type-spec")
(include-book "../utilities/top")
(include-book "vector-c")
(include-book "vector-a")
(include-book "vector-abs")


;;;; `DEFINE-VECTOR'
(defmacro define-vector
    (vector dimensions
     &key
       (element-type 't element-type-supplied-p)
       (specialize-element-type 'nil specialize-element-type-supplied-p)
       (element-recognizer 'nil element-recognizer-supplied-p)
       (element-fixer 'nil element-fixer-supplied-p)
       (element-equiv 'nil element-equiv-supplied-p)
       (element 'nil element-supplied-p)
       (initial-element 'nil initial-element-supplied-p)
       (resizable 't resizable-supplied-p)

       (inline 't inline-supplied-p)
       (memoizable 'nil memoizable-supplied-p)
       (executable 'nil executable-supplied-p)

       (recognizer 'nil)
       (creator 'nil)
       (fixer 'nil)
       (length 'nil)
       (resizer 'nil)
       (accessor 'nil)
       (updater 'nil)

       (logic 'nil)
       (exec 'nil)

       (package-witness 'nil package-witness-supplied-p)
       (debug 'nil))

  (declare (xargs :guard (and (symbolp vector)
                              (or (and (consp dimensions)
                                       (natp (car dimensions))
                                       (null (cdr dimensions)))
                                  (natp dimensions))
                              (if (acl2-type-spec-p element-type)
                                  (typep$ initial-element element-type)
                                  (symbolp element-type))
                              (booleanp specialize-element-type)
                              (symbolp element-recognizer)
                              (symbolp element-fixer)
                              (symbolp element-equiv)
                              (symbolp element)
                              (booleanp resizable)
                              (booleanp inline)
                              (booleanp memoizable)
                              (booleanp executable)
                              (symbol-listp (list recognizer
                                                  creator
                                                  fixer
                                                  length
                                                  resizer
                                                  accessor
                                                  updater))
                              (symbolp logic)
                              (symbolp exec)
                              (package-witness-p package-witness)
                              (booleanp debug))))

  `(with-output
     ,@(and (not debug)
            *constructor-output*)

     (make-event
       (let* ((vector ',vector)
              (logic ',logic)
              (exec ',exec)
              (package-witness (if ',package-witness-supplied-p
                                   ',package-witness
                                   (current-package state)))
              (dimensions ',dimensions)
              (element-type ',element-type)
              (stobj-property (and (symbolp element-type)
                                   (getpropc element-type 'acl2::stobj)))
              (specialize-element-type ',specialize-element-type)
              (element-recognizer ',element-recognizer)
              (element-fixer ',element-fixer)
              (element-equiv ',element-equiv)
              (element ',element)
              (initial-element ',initial-element)
              (resizable ',resizable)

              (inline ',inline)
              (memoizable ',memoizable)
              (executable ',executable)

              (recognizer ',recognizer)
              (creator ',creator)
              (fixer ',fixer)
              (length ',length)
              (resizer ',resizer)
              (accessor ',accessor)
              (updater ',updater)

              (debug ',debug)

              (vector$a (or logic
                            (symbolicate package-witness vector "$A")))
              (vector$c (or exec
                            (symbolicate package-witness vector "$C")))
              (recognizer (or recognizer
                              (symbolicate package-witness vector (make-predicate-suffix vector))))
              (creator (or creator
                           (symbolicate package-witness "CREATE-" vector)))
              (fixer (or fixer
                         (symbolicate package-witness vector "-FIX")))
              (length (or length
                          (symbolicate package-witness vector "-LEN")))
              (resizer (or resizer
                           (symbolicate package-witness vector "-RSZ")))
              (accessor (or accessor
                            (symbolicate package-witness vector "-REF")))
              (updater (or updater
                           (symbolicate package-witness vector "-SET"))))

         `(progn
            (define-vector$c ,vector$c ,dimensions
              ,@(and ,element-type-supplied-p
                     `(:element-type ,element-type))
              ,@(and ,specialize-element-type-supplied-p
                     `(:specialize-element-type ,specialize-element-type))
              ,@(and ,initial-element-supplied-p
                     `(:initial-element ,initial-element))
              ,@(and ,resizable-supplied-p
                     `(:resizable ,resizable))
              ,@(and ,inline-supplied-p
                     `(:inline ,inline))
              ,@(and ,memoizable-supplied-p
                     `(:memoizable ,memoizable))
              ,@(and ,executable-supplied-p
                     `(:executable ,executable))
              ,@(and ,package-witness-supplied-p
                     `(:package-witness ,package-witness))
              :debug ,debug)

            (define-vector$a ,vector$a ,dimensions
              ,@(and ,element-recognizer-supplied-p
                     `(:element-recognizer ,element-recognizer))
              ,@(and ,element-fixer-supplied-p
                     `(:element-fixer ,element-fixer))
              ,@(and ,element-equiv-supplied-p
                     `(:element-equiv ,element-equiv))
              ,@(and (or ,element-supplied-p
                         stobj-property)
                     `(:element ,(if stobj-property
                                     element-type
                                     element)))
              ,@(and ,initial-element-supplied-p
                     `(:initial-element ,initial-element))
              ,@(and ,resizable-supplied-p
                     `(:resizable ,resizable))
              ,@(and ,package-witness-supplied-p
                     `(:package-witness ,package-witness))
              :debug ,debug)

            (define-vector$corr ,vector
              :logic ,vector$a
              :exec ,vector$c
              ,@(and ,package-witness-supplied-p
                     `(:package-witness ,package-witness))
              :debug ,debug)

            (define-vector$abs ,vector
              :logic ,vector$a
              :exec ,vector$c
              :recognizer ,recognizer
              :creator ,creator
              :fixer ,fixer
              :length ,length
              :resizer ,resizer
              :accessor ,accessor
              :updater ,updater
              ,@(and ,executable-supplied-p
                     `(:executable ,executable))
              ,@(and ,package-witness-supplied-p
                     `(:package-witness ,package-witness))
              :debug ,debug)

            (defmacro ,(symbolicate package-witness "THE-" vector) (,vector)
              (declare (xargs :guard (symbolp ,vector)))
              `(mbe :logic ,(list ',fixer ,vector)
                    :exec ,,vector))

            (in-theory
              (disable ,(symbolicate (if ,package-witness-supplied-p
                                         package-witness
                                         vector$c)
                                     vector$c
                                     "-THEOREMS"))))))))
