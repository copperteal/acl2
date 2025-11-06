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


;;;; Stobj Values
;; (defstobj st/0
;;   a/0
;;   :non-memoizable t
;;   :non-executable t)

;; (defthm st/0p-of-create-st/0
;;   (st/0p (create-st/0)))

;; (defun create-st/0$a ()
;;   (declare (xargs :guard t))
;;   '(nil))

;; (defthm create-st/0$a{rewrite}
;;   (equal (create-st/0$a)
;;          (create-st/0)))

;; (in-theory
;;   (disable (:d create-st/0$a)
;;            (:e create-st/0$a)))

;; (defun st/0-fix (x)
;;   (declare (xargs :guard t))
;;   (if (st/0p x)
;;       x
;;       (create-st/0$a)))

;; (defthm st/0-fix{rewrite}
;;   (equal (st/0-fix x)
;;          (if (st/0p x)
;;              x
;;              (create-st/0))))

;; (in-theory
;;   (disable (:d create-st/0)
;;            (:e create-st/0)))

;; (defstobj st/1
;;   a/1
;;   :non-memoizable t
;;   :non-executable t)

;; (defthm st/1p-of-create-st/1
;;   (st/1p (create-st/1)))

;; (defun create-st/1$a ()
;;   (declare (xargs :guard t))
;;   '(nil))

;; (defthm create-st/1$a{rewrite}
;;   (equal (create-st/1$a)
;;          (create-st/1)))

;; (in-theory
;;   (disable (:d create-st/1$a)
;;            (:e create-st/1$a)))

;; (defun st/1-fix (x)
;;   (declare (xargs :guard t))
;;   (if (st/1p x)
;;       x
;;       (create-st/1$a)))

;; (defthm st/1-fix{rewrite}
;;   (equal (st/1-fix x)
;;          (if (st/1p x)
;;              x
;;              (create-st/1))))

;; (in-theory
;;   (disable (:d create-st/1)
;;            (:e create-st/1)))

;; (defstobj st/2
;;   a/2
;;   :non-memoizable t
;;   :non-executable t)

;; (defthm st/2p-of-create-st/2
;;   (st/2p (create-st/2)))

;; (defun create-st/2$a ()
;;   (declare (xargs :guard t))
;;   '(nil))

;; (defthm create-st/2$a{rewrite}
;;   (equal (create-st/2$a)
;;          (create-st/2)))

;; (in-theory
;;   (disable (:d create-st/2$a)
;;            (:e create-st/2$a)))

;; (defun st/2-fix (x)
;;   (declare (xargs :guard t))
;;   (if (st/2p x)
;;       x
;;       (create-st/2$a)))

;; (defthm st/2-fix{rewrite}
;;   (equal (st/2-fix x)
;;          (if (st/2p x)
;;              x
;;              (create-st/2))))

;; (in-theory
;;   (disable (:d create-st/2)
;;            (:e create-st/2)))


;; (atomic-stobjs::define-frame$a frame/st
;;   (f0 :recognizer st/0p
;;       :fixer st/0-fix
;;       :stobj st/0
;;       :initial-element (create-st/0$a))
;;   (f1 :recognizer st/1p
;;       :fixer st/1-fix
;;       :stobj st/1
;;       :initial-element (create-st/1$a))
;;   (f2 :recognizer st/2p
;;       :fixer st/2-fix
;;       :stobj st/2
;;       :initial-element (create-st/2$a)))


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
