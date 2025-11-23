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

(include-book "../utilities/symbolicate")


;;;; `PROTECT-EXPORTS'
(defun protect-exports (foundation exports acc state)
  (declare (xargs :mode :program
                  :stobjs state
                  :guard (and (symbolp foundation)
                              (alistp exports)
                              (alistp acc))
                  :verify-guards nil))
  (cond
    ((endp exports)
     (reverse acc))
    ((acl2::unprotected-export-p foundation
                                 (cadr (assoc-keyword :exec
                                                      (cdar exports)))
                                 (w state))
     (protect-exports foundation
                      (cdr exports)
                      (cons (append (car exports)
                                    (list :protect t))
                            acc)
                      state))
    (t
     (protect-exports foundation
                      (cdr exports)
                      (cons (car exports) acc)
                      state))))


;;;; `DEFINE-CONGRUENT'
(defmacro define-congruent (stobj &key
                                    (executable 'nil)
                                    (debug 'nil)
                                    (package-witness 'nil package-witness-supplied-p))
  (declare (xargs :guard (and (symbolp stobj)
                              stobj
                              (booleanp executable)
                              (booleanp debug)
                              (or (symbolp package-witness)
                                  (and (stringp package-witness)
                                       (not (equal package-witness "")))))))

  `(with-output
     ,@(and (not debug)
            *constructor-output*)

     (make-event
       (let* ((stobj ',stobj)
              (executable ',executable)
              (package-witness (if ',package-witness-supplied-p
                                   ',package-witness
                                   (current-package state)))
              (%stobj (symbolicate package-witness "%" stobj))
              (stobj-property (getpropc stobj 'acl2::stobj))
              (absstobj-info (getpropc stobj 'acl2::absstobj-info))
              (recognizer-export (assoc (caadr stobj-property) (cdr absstobj-info)))
              (recognizer-export (list (symbolicate package-witness "%" (first recognizer-export))
                                       :logic (second recognizer-export)
                                       :exec (third recognizer-export)))
              (creator-export (assoc (cdadr stobj-property) (cdr absstobj-info)))
              (creator-export (list (symbolicate package-witness "%" (first creator-export))
                                    :logic (second creator-export)
                                    :exec (third creator-export)))
              (foundation (car absstobj-info))
              (exports (loop$ :for entry :in (cdddr absstobj-info)
                             :collect (append (list (symbolicate package-witness "%" (first entry))
                                                    :logic (second entry)
                                                    :exec (third entry))
                                              (let ((updater (cdr (last entry))))
                                                (and updater
                                                     (list :updater (symbolicate package-witness "%" updater)))))))
              (exports (protect-exports foundation exports () state)))

         `(defabsstobj ,%stobj
            :foundation ,foundation
            :congruent-to ,stobj
            :recognizer ,recognizer-export
            :creator ,creator-export
            :non-executable ,(not executable)
            :exports ,exports)))))
