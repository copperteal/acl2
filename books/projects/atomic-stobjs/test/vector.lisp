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

(defun cons-equiv (x y)
  (declare (xargs :guard t))
  (equal (consify x) (consify y)))

(defequiv cons-equiv)


;;;; length zero, type t
;;; dimensions, element-type, resizable
(atomic-stobjs::define-vector vec/0-t-nil 0
  :element-type t
  :resizable nil)

(atomic-stobjs::define-vector vec/0-t-t 0
  :element-type t
  :resizable t)

(atomic-stobjs::define-vector vec/0-cons-\(A\ B\)-nil 0
  :element-type cons
  :element-recognizer consp
  :element-fixer consify
  :element-equiv cons-equiv
  :initial-element (a b)
  :resizable nil)

(atomic-stobjs::define-vector vec/0-cons-\(A\ B\)-t 0
  :element-type cons
  :element-recognizer consp
  :element-fixer consify
  :element-equiv cons-equiv
  :initial-element (a b)
  :resizable t)


;;;; length 1013, type t
;;; dimensions, element-type, resizable
(atomic-stobjs::define-vector vec/1013-t-nil 1013
  :element-type t
  :resizable nil)

(atomic-stobjs::define-vector vec/1013-t-t 1013
  :element-type t
  :resizable t)

(atomic-stobjs::define-vector vec/1013-cons-\(A\ B\)-nil 1013
  :element-type cons
  :element-recognizer consp
  :element-fixer consify
  :element-equiv cons-equiv
  :initial-element (a b)
  :resizable nil)

(atomic-stobjs::define-vector vec/1013-cons-\(A\ B\)-t 1013
  :element-type cons
  :element-recognizer consp
  :element-fixer consify
  :element-equiv cons-equiv
  :initial-element (a b)
  :resizable t)


;;;; length zero, type including nil
;;; dimensions, element-type, resizable
(atomic-stobjs::define-vector vec/0-\(MEMBER\ T\ NIL\)-nil 0
  :element-type (member t nil)
  :element-recognizer booleanp
  :element-fixer bool-fix
  :element-equiv iff
  :initial-element t
  :resizable nil)

(atomic-stobjs::define-vector vec/0-\(MEMBER\ T\ NIL\)-t 0
  :element-type (member t nil)
  :element-recognizer booleanp
  :element-fixer bool-fix
  :element-equiv iff
  :initial-element t
  :resizable t)


;;;; length 1234, type including nil
;;; dimensions, element-type, resizable
(atomic-stobjs::define-vector vec/1234-\(MEMBER\ T\ NIL\)-nil 1234
  :element-type (member t nil)
  :element-recognizer booleanp
  :element-fixer bool-fix
  :element-equiv iff
  :initial-element t
  :resizable nil)

(atomic-stobjs::define-vector vec/1234-\(MEMBER\ T\ NIL\)-t 1234
  :element-type (member t nil)
  :element-recognizer booleanp
  :element-fixer bool-fix
  :element-equiv iff
  :initial-element t
  :resizable t)


;;;; length zero, type not including nil
;;; dimensions, element-type, resizable
(atomic-stobjs::define-vector vec/0-signed-byte-nil 0
  :element-type signed-byte
  :element-recognizer integerp
  :element-fixer ifix
  :element-equiv int-equiv
  :initial-element 0
  :resizable nil)

(atomic-stobjs::define-vector vec/0-signed-byte-t 0
  :element-type signed-byte
  :element-recognizer integerp
  :element-fixer ifix
  :element-equiv int-equiv
  :initial-element 0
  :resizable t)


;;;; length #xbead, type not including nil
;;; dimensions, element-type, resizable
(atomic-stobjs::define-vector vec/bead-signed-byte-nil #xbead
  :element-type signed-byte
  :element-recognizer integerp
  :element-fixer ifix
  :element-equiv int-equiv
  :initial-element 0
  :resizable nil)

(atomic-stobjs::define-vector vec/bead-signed-byte-t #xbead
  :element-type signed-byte
  :element-recognizer integerp
  :element-fixer ifix
  :element-equiv int-equiv
  :initial-element 0
  :resizable t)
