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


(in-package "ACL2")
(set-verify-guards-eagerness 2)

(include-book "symbolicate")

(defun make-predicate-suffix (string-or-symbol)
  ;; TODO: Mention reference to CTL2 in XDOC
  (declare (xargs :guard (or (stringp string-or-symbol)
                             (symbolp string-or-symbol))))
  (if (position #\- (if (symbolp string-or-symbol)
                        (symbol-name string-or-symbol)
                        string-or-symbol))
      "-P"
      "P"))

(local
  (thm ; ensure `MAKE-PREDICATE-SUFFIX' is known to return a string
    (stringp (make-predicate-suffix sos))
    :hints
    (("Goal"
      :in-theory '((:t make-predicate-suffix))))))

;;; `COUPLED-FN'
(encapsulate ()
  (local
    (defthm guard-lemma
      (implies (character-listp x)
               (character-listp (remove-equal a x)))))

  (defun coupled-fn (names)
    (declare (xargs :guard (symbol-listp names)))
    (and (consp names)
         (cons (let ((name (car names)))
                 (list (symbolicate name (coerce (remove #\% (coerce (symbol-name name)
                                                                     'list))
                                                 'string)
                                    '-coupled)
                       name))
               (coupled-fn (cdr names))))))

(local
  (thm ; ensure `COUPLED-FN' is known to return a symbol-list
    (implies (symbol-listp names)
             (symbol-list-listp (coupled-fn names)))))

(defmacro coupled (&rest names)
  (declare (xargs :guard (symbol-listp names)))
  (let ((expressions (coupled-fn names)))
    (list 'force (if (null (cdr expressions))
                     (car expressions)
                     (cons 'and expressions)))))
