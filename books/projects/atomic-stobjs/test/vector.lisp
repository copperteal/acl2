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

(include-book "std/basic/nfix" :dir :system)
(include-book "std/basic/ifix" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)

(include-book "../constructors/vector")

(defun consify (x)
  (declare (xargs :guard t))
  (if (consp x)
      x
      (list 'a 'b)))

(defthm consify-when-consp
  (implies (consp x)
           (equal (consify x) x)))

(defthm consify-when-not-consp
  (implies (not (consp x))
           (equal (consify x) '(a b))))

(defthm ifix-not-integerp
  (implies (not (integerp x))
           (equal (ifix x) 0)))


;;;; Stobj Values
;; (defstobj foo$c
;;   a
;;   :inline t
;;   :non-memoizable t
;;   :non-executable t)

;; (defthm foo$cp-of-create-foo$c
;;   (foo$cp (create-foo$c)))

;; (defun create-foo$c$a ()
;;   (declare (xargs :guard t))
;;   '(nil))

;; (defthm create-foo$c$a{rewrite}
;;   (equal (create-foo$c$a)
;;          (create-foo$c)))

;; (in-theory
;;   (disable (:d create-foo$c$a)
;;            (:e create-foo$c$a)))

;; (defun foo$c-fix (x)
;;   (declare (xargs :guard t))
;;   (if (foo$cp x)
;;       x
;;       (create-foo$c$a)))

;; (defthm foo$c-fix{rewrite}
;;   (equal (foo$c-fix x)
;;          (if (foo$cp x)
;;              x
;;              (create-foo$c))))

;; (in-theory
;;   (disable (:d create-foo$c)
;;            (:e create-foo$c)))

;; (defstobj %foo$c
;;   %a
;;   :congruent-to foo$c
;;   :inline t
;;   :non-memoizable t
;;   :non-executable t)

;; (defun foo$c-copy (%foo$c foo$c)
;;   (declare (xargs :stobjs (%foo$c foo$c)))
;;   (update-a (a foo$c) %foo$c))

;; (defthm foo$c-copy{rewrite}
;;   (implies (and (foo$cp %foo$c)
;;                 (foo$cp foo$c))
;;            (equal (foo$c-copy %foo$c foo$c)
;;                   foo$c)))

;; ;; (table stobj-copier
;; ;;        'stobj-copier-alist
;; ;;        (putprop 'foo$c
;; ;;                 'copier
;; ;;                 'foo$c-copy
;; ;;                 (stobj-copier-alist world)))

;; (in-theory
;;   (disable foo$c-copy))


;; (atomic-stobjs::define-vector arr/0 21
;;   :element-type foo$c
;;   :element-recognizer foo$cp
;;   :element-fixer foo$c-fix
;;   :element foo$c
;;   :initial-element (create-foo$c$a))

;; (atomic-stobjs::define-vector arr/1 21
;;   :element-type foo$c
;;   :element-recognizer foo$cp
;;   :element-fixer foo$c-fix
;;   :element foo$c
;;   :initial-element (create-foo$c$a)
;;   :resizable t)

;; (atomic-stobjs::define-vector arr/2 0
;;   :element-type foo$c
;;   :element-recognizer foo$cp
;;   :element-fixer foo$c-fix
;;   :element foo$c
;;   :initial-element (create-foo$c$a))

;; (atomic-stobjs::define-vector arr/3 0
;;   :element-type foo$c
;;   :element-recognizer foo$cp
;;   :element-fixer foo$c-fix
;;   :element foo$c
;;   :initial-element (create-foo$c$a)
;;   :resizable t)


;;;; length zero, type t
;;; dimensions, element-type, resizable
(atomic-stobjs::define-vector arr/0-t-nil 0
  :element-type t
  :resizable nil)

(atomic-stobjs::define-vector arr/0-t-t 0
  :element-type t
  :resizable t)

(atomic-stobjs::define-vector arr/0-cons-\(A\ B\)-nil 0
  :element-type cons
  :element-recognizer consp
  :element-fixer consify
  :initial-element (a b)
  :resizable nil)

(atomic-stobjs::define-vector arr/0-cons-\(A\ B\)-t 0
  :element-type cons
  :element-recognizer consp
  :element-fixer consify
  :initial-element (a b)
  :resizable t)


;;;; length 1013, type t
;;; dimensions, element-type, resizable
(atomic-stobjs::define-vector arr/1013-t-nil 1013
  :element-type t
  :resizable nil)

(atomic-stobjs::define-vector arr/1013-t-t 1013
  :element-type t
  :resizable t)

(atomic-stobjs::define-vector arr/1013-cons-\(A\ B\)-nil 1013
  :element-type cons
  :element-recognizer consp
  :element-fixer consify
  :initial-element (a b)
  :resizable nil)

(atomic-stobjs::define-vector arr/1013-cons-\(A\ B\)-t 1013
  :element-type cons
  :element-recognizer consp
  :element-fixer consify
  :initial-element (a b)
  :resizable t)


;;;; length zero, type including nil
;;; dimensions, element-type, resizable
(atomic-stobjs::define-vector arr/0-\(MEMBER\ T\ NIL\)-nil 0
  :element-type (member t nil)
  :element-recognizer booleanp
  :element-fixer bool-fix
  :initial-element t
  :resizable nil)

(atomic-stobjs::define-vector arr/0-\(MEMBER\ T\ NIL\)-t 0
  :element-type (member t nil)
  :element-recognizer booleanp
  :element-fixer bool-fix
  :initial-element t
  :resizable t)


;;;; length 1234, type including nil
;;; dimensions, element-type, resizable
(atomic-stobjs::define-vector arr/1234-\(MEMBER\ T\ NIL\)-nil 1234
  :element-type (member t nil)
  :element-recognizer booleanp
  :element-fixer bool-fix
  :initial-element t
  :resizable nil)

(atomic-stobjs::define-vector arr/1234-\(MEMBER\ T\ NIL\)-t 1234
  :element-type (member t nil)
  :element-recognizer booleanp
  :element-fixer bool-fix
  :initial-element t
  :resizable t)


;;;; length zero, type not including nil
;;; dimensions, element-type, resizable
(atomic-stobjs::define-vector arr/0-signed-byte-nil 0
  :element-type signed-byte
  :element-recognizer integerp
  :element-fixer ifix
  :initial-element 0
  :resizable nil)

(atomic-stobjs::define-vector arr/0-signed-byte-t 0
  :element-type signed-byte
  :element-recognizer integerp
  :element-fixer ifix
  :initial-element 0
  :resizable t)


;;;; length #xbead, type not including nil
;;; dimensions, element-type, resizable
(atomic-stobjs::define-vector arr/bead-signed-byte-nil #xbead
  :element-type signed-byte
  :element-recognizer integerp
  :element-fixer ifix
  :initial-element 0
  :resizable nil)

(atomic-stobjs::define-vector arr/bead-signed-byte-t #xbead
  :element-type signed-byte
  :element-recognizer integerp
  :element-fixer ifix
  :initial-element 0
  :resizable t)
