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


(in-package "ACL2")
(set-verify-guards-eagerness 2)

(include-book "projects/apply/top" :dir :system)


;;;; `PKG-WITNESS-P'
(defun pkg-witness-p (x)
  (declare (xargs :guard t))
  (and (symbolp x)
       (not (equal (symbol-package-name x) *main-lisp-package-name*))
       (equal (symbol-name x) *pkg-witness-name*)))

(defthm pkg-witness-p-cr
  (implies (pkg-witness-p x)
           (symbolp x))
  :rule-classes :compound-recognizer)

(defthm pkg-witness-p-of-pkg-witness
  (equal (pkg-witness-p (pkg-witness x))
         (not (equal x *main-lisp-package-name*))))

(defthm symbol-package-name-when-pkg-witness-p
  (implies (pkg-witness-p x)
           (not (equal (symbol-package-name x) *main-lisp-package-name*))))

(defthm symbol-name-when-pkg-witness-p
  (implies (pkg-witness-p x)
           (equal (symbol-name x) *pkg-witness-name*)))

(defwarrant pkg-witness-p)

(in-theory
  (disable pkg-witness-p))


;;;; `PKG-WITNESS-FIX'
(defun pkg-witness-fix (x)
  (declare (xargs :guard t))
  (if (pkg-witness-p x)
      x
      (pkg-witness (fix-pkg (cond
                              ((symbolp x)
                               (symbol-package-name x))
                              ((and (stringp x)
                                    (not (equal x "")))
                               x)
                              (t
                               "ACL2"))))))

(defthm pkg-witness-p-of-pkg-witness-fix
  (pkg-witness-p (pkg-witness-fix x))
  :rule-classes
  (:rewrite
   (:type-prescription :typed-term (pkg-witness-fix x)
                       :corollary (symbolp (pkg-witness-fix x)))))

(defwarrant pkg-witness-fix)

(in-theory
  (disable pkg-witness-fix))
