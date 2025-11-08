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

(include-book "../constructors/frame$a")

(defun symbol-fix (x)
  (declare (xargs :guard t))
  (and (symbolp x)
       x))

(defthm symbol-fix-when-symbolp
  (implies (symbolp key)
           (equal (symbol-fix key) key)))

(defthm symbol-fix-when-not-symbolp
  (implies (not (symbolp key))
           (not (symbol-fix key))))

(defthm nfix-when-natp
  (implies (natp key)
           (equal (nfix key) key)))

(defthm nfix-when-not-natp
  (implies (not (natp key))
           (equal (nfix key) 0)))

(defun string-fix (x)
  (declare (xargs :guard t))
  (if (stringp x)
      x
      ""))

(defthm stringp-of-string-fix
  (stringp (string-fix x)))

(defthm string-fix-when-stringp
  (implies (stringp val)
           (equal (string-fix val) val)))

(defthm string-fix-when-not-stringp
  (implies (not (stringp val))
           (equal (string-fix val) "")))


;;;; Concrete Tests
(atomic-stobjs::define-frame$a fr$a/empty)

(atomic-stobjs::define-frame$a fr$a
  (f0 :recognizer natp
      :fixer nfix
      :initial-element 0)
  (f1 :recognizer symbolp
      :fixer symbol-fix
      :initial-element nil)
  (f2 :recognizer stringp
      :fixer string-fix
      :initial-element ""))

(atomic-stobjs::define-frame$a fr$a/big
  (f0) (f1) (f2) (f3)
  (f4) (f5) (f6) (f7)
  (f8) (f9) (f10) (f11)
  (f12) (f13) (f14) (f15)
  (f16) (f17) (f18) (f19)
  (f20) (f21) (f22) (f23)
  (f24) (f25) (f26) (f27)
  (f28) (f29) (f30) (f31))
