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
(include-book "projects/apply/top" :dir :system)

(defun package-witness-p (x)
  (declare (xargs :guard t))
  (if (stringp x)
      (not (equal x ""))
      (symbolp x)))

(encapsulate ()
  (local
    (defthm character-listp-of-explode-nonnegative-integer
      (equal (character-listp (explode-nonnegative-integer n r ans))
             (character-listp ans))))

  (local
    (in-theory
      (disable explode-nonnegative-integer)))

  (defun %symbolicate-coerce (expr)
    (declare (xargs :guard t))
    (cond
      ((symbolp expr)
       (symbol-name expr))
      ((stringp expr)
       expr)
      ((natp expr)
       (coerce (explode-nonnegative-integer expr 10 nil) 'string))
      (t
       ""))))

(local
  (thm ; ensure `%SYMBOLICATE-COERCE' is known to return a string
    (stringp (%symbolicate-coerce expr))
    :hints
    (("Goal"
      :in-theory '((:t %symbolicate-coerce))))))

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
  :long "@({
Examples:

ACL2 !>(symbolicate \"ACL2\" 'hello \" world\")
|HELLO world|

ACL2 !>(defun foo () \"SOME-STRING\")
...

ACL2 !>(symbolicate 'str::witness (foo) \"-suffix\")
STR::|SOME-STRING-suffix|

ACL2 !>(defun bar () \"STR\")
...

ACL2 !>(symbolicate (bar) (foo) 2 '-baz)
STR::SOME-STRING-BAZ

General Form
(symbolicate witness expr1 ... exprn)
})

<p>@('Symbolicate') evaluates each of its arguments.  If @('witness') is a
string, it is taken as a <see topic=\"@(url packages)\">package</see> name.  If
@('witness') is a symbol, its package name is used.  Otherwise, the
@('symbolicate') form expands to @('nil').  For each @('expri'), if @('expri')
is a string, it is preserved; if @('expri') is a symbol, it is replaced by its
name; if @('expri') is a non-negative integer, it is converted to a base-10
string by @(see explode-nonnegative-integer); otherwise, @('expri') is replaced
with the empty string.  After this evaluation, @('symbolicate') concatenates the
strings resulting from @('expr1 ... exprn') and interns a symbol with that name
in the package derived from @('witness').  The @('symbolicate') form expands to
this symbol (assuming @('witness') evaluated to a string or symbol).</p>")
