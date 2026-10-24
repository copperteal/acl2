;;; Copyright 2026 J. David Taylor
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

(include-book "projects/apply/top" :dir :system)


(defrec vector$a-property
  (name
   ((recognizer . creator)
    (fixer . equiv))
   ((element
     element-recognizer
     initial-element-name
     element-fixer
     element-equiv)
    (resizable
     default-length-name)
    (length
     resizer
     accessor
     updater)))
  nil)

(defrec hash-table$a-property
  (name
   ((recognizer . creator)
    (fixer . equiv))
   ((key
     key-recognizer
     default-key-name
     key-fixer
     key-equiv)
    (val
     val-recognizer
     default-val-name
     val-fixer
     val-equiv)
    (test
     copyable)
    (accessor
     updater
     boundp
     getp
     remover
     count
     clear
     init)
    keys))
  nil)

(defrec frame$a-property
  (name
   ((recognizer . creator)
    (fixer . equiv))
   (fields
    recognizers
    initial-element-names
    fixers
    equivs
    stobjs
    accessors
    updaters
    (view)))
  nil)

(defrec stobj$a-property
  (type
   name
   ((recognizer . creator)
    (fixer . equiv))
   . extra)
  t)

(local
  (defthm stobj$a-property-generalizes
    (implies (or (weak-vector$a-property-p property)
                 (weak-hash-table$a-property-p property)
                 (weak-frame$a-property-p property))
             (weak-stobj$a-property-p property))))

;; TODO: strengthen table guard
(table stobj$a nil nil :guard (and (symbolp acl2::key)
                                   (or (weak-vector$a-property-p acl2::val)
                                       (weak-hash-table$a-property-p acl2::val)
                                       (weak-frame$a-property-p acl2::val))))

(table stobj$a nil nil :clear)

(defun stobj$a-property (name wrld)
  (declare (xargs :guard (and (symbolp name)
                              (plist-worldp wrld))))
  ;; TODO: How do I prove that table-alist always returns an alist?
  (cdr (assoc name (let ((alist (table-alist 'stobj$a wrld)))
                     (and (alistp alist)
                          alist)))))

(defwarrant stobj$a-property)
