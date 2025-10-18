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

(include-book "xdoc/top" :dir :system)

(defconst *%with-books-keys*
  '(:load-compiled-file
    :uncertified-okp
    :defaxioms-okp
    :skip-proofs-okp
    :ttags
    :dir))

(defun %with-books-include-specs-p (include-specs)
  (declare (xargs :guard t))
  (if (consp include-specs)
      (let ((include-spec (car include-specs)))
        (and (consp include-spec)
             (stringp (car include-spec))
             (keyword-value-listp (cdr include-spec))
             (subsetp (evens (cdr include-spec)) *%with-books-keys*
                      :test 'eq)
             (%with-books-include-specs-p (cdr include-specs))))
      (null include-specs)))

(defun %with-books-includes (include-specs)
  (declare (xargs :guard (%with-books-include-specs-p include-specs)))
  (and (consp include-specs)
       (cons (list 'local (cons 'include-book (car include-specs)))
             (%with-books-includes (cdr include-specs)))))

(defmacro with-books (include-specs &body body)
  (declare (xargs :guard (%with-books-include-specs-p include-specs)))
  `(encapsulate ()
     ,@(%with-books-includes include-specs)
     ,@body))


(defxdoc with-books
  :parents (books-reference include-book)
  :short "Evaluate events with locally included books."
  :long "@({
Example:

(with-books ((\"std/lists/sets\" :dir :system))
  (defthm set-equiv-of-append
    (set-equiv (append x y) (append y x))))

expands to

(encapsulate ()
  (local
    (include-book \"std/lists/top\" :dir :system))
  (defthm set-equiv-of-append
    (set-equiv (append x y) (append y x))))

General Form:
(with-books include-specs
  body)
})

<p>where @('include-specs') must be a literal list of ``include
specifications.''  An include specification is the @('cdr') of an @(tsee
include-book) form.  @('Body') must be the valid body of a trivial @(tsee
encapsulate).</p>")
