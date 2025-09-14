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
;;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS”
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

(include-book "xdoc/top" :dir :system)
(include-book "projects/apply/top" :dir :system)

(defun package-witness-p (x)
  (declare (xargs :guard t))
  (if (stringp x)
      (not (equal x ""))
      (symbolp x)))

(defun %symbolicate-coerce (expr)
  (declare (xargs :guard t))
  (cond
    ((symbolp expr)
     (symbol-name expr))
    ((stringp expr)
     expr)
    (t
     "")))

(local
  (defthm stringp-of-%symbolicate-coerce
    (stringp (%symbolicate-coerce expr))
    :rule-classes nil))

(defwarrant %symbolicate-coerce)

(defun %symbolicate-expand (exprs)
  (declare (xargs :guard (true-listp exprs)))
  (if (atom exprs)
      ""
      (let ((expr (car exprs))
            (exprs (cdr exprs)))
        (if (consp exprs)
            (list 'string-append
                  (list '%symbolicate-coerce expr)
                  (%symbolicate-expand exprs))
            (list '%symbolicate-coerce expr)))))

(defmacro symbolicate (witness &rest exprs)
  (declare (xargs :guard t))
  `(let ((witness ,witness)
         (expansion ,(%symbolicate-expand exprs)))
     (cond
       ((stringp witness)
        (intern$ expansion witness))
       ((symbolp witness)
        (intern-in-package-of-symbol expansion witness))
       (t
        nil))))


(defxdoc symbolicate
  :parents (symbols)
  :short "Concatenate strings and symbols to construct a symbol."
  :long "<p>@(call symbolicate) evaluates each @('expr'), converts any symbol to a
string, converts any non-symbol, non-string to the empty string, and
concatenates these strings.  @('symbolicate') returns a symbol whose name is
that concatenation and whose package is determined by evaluating @('witness').
If @('witness') is a string, it is taken as the package name.  If @('witness')
is a symbol, its package name is used.  If @('witness') is not a symbol or a
string, @('symbolicate') expands to @('nil').</p>

<h3>Examples</h3>
<p>@({
(symbolicate \"ACL2\" 'hello \" world\") == ACL2::|HELLO world|
(defun foo () \"SOME-STRING\")
(symbolicate 'str::witness (foo) \"-suffix\") == STR::|SOME-STRING-suffix|
(defun bar () \"STR\")
(symbolicate (bar) (foo) 2 '-baz) == STR::SOME-STRING-BAZ
})</p>")
