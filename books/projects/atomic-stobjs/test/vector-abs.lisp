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

(include-book "../constructors/vector-c")
(include-book "../constructors/vector-a")
(include-book "../constructors/vector-abs")

(defun not-null (x)
  (declare (xargs :guard t))
  (not (null x)))

(defthm not-null-when-booleanp
  (implies (booleanp x)
           (equal (not-null x) x)))

(defthm not-null-when-not-booleanp
  (implies (not (booleanp x))
           (equal (not-null x) t)))

(defthm nfix-when-not-natp
  (implies (not (natp x))
           (equal (nfix x) 0)))


(atomic-stobjs::define-vector$c vec/0$c #xbabe
  :resizable nil)

(atomic-stobjs::define-vector$a vec/0$a #xbabe
  :resizable nil)

(atomic-stobjs::define-vector$corr vec/0
  :logic vec/0$a
  :exec vec/0$c)

(atomic-stobjs::define-vector$abs vec/0
  :logic vec/0$a
  :exec vec/0$c)


(atomic-stobjs::define-vector$c vec/1$c #xbabe
  :resizable t)

(atomic-stobjs::define-vector$a vec/1$a #xbabe
  :resizable t)

(atomic-stobjs::define-vector$corr vec/1
  :logic vec/1$a
  :exec vec/1$c)

(atomic-stobjs::define-vector$abs vec/1
  :logic vec/1$a
  :exec vec/1$c)


(atomic-stobjs::define-vector$c vec/2$c #xdead
  :element-type (member t nil)
  :initial-element t
  :resizable t)

(atomic-stobjs::define-vector$a vec/2$a #xdead
  :element-recognizer booleanp
  :element-fixer not-null
  :element-equiv iff
  :initial-element t
  :resizable t)

(atomic-stobjs::define-vector$corr vec/2
  :logic vec/2$a
  :exec vec/2$c)

(atomic-stobjs::define-vector$abs vec/2
  :logic vec/2$a
  :exec vec/2$c)


(atomic-stobjs::define-vector$c vec/3$c 0
  :element-type (member t nil)
  :initial-element t
  :resizable nil)

(atomic-stobjs::define-vector$a vec/3$a 0
  :element-recognizer booleanp
  :element-fixer not-null
  :element-equiv iff
  :initial-element t
  :resizable nil)

(atomic-stobjs::define-vector$corr vec/3
  :logic vec/3$a
  :exec vec/3$c)

(atomic-stobjs::define-vector$abs vec/3
  :logic vec/3$a
  :exec vec/3$c)


(atomic-stobjs::define-vector$c vec/4$c #xbeef
  :element-type unsigned-byte
  :initial-element 0
  :resizable t)

(atomic-stobjs::define-vector$a vec/4$a #xbeef
  :element-recognizer natp
  :element-fixer nfix
  :element-equiv nat-equiv
  :initial-element 0
  :resizable t)

(atomic-stobjs::define-vector$corr vec/4
  :logic vec/4$a
  :exec vec/4$c)

(atomic-stobjs::define-vector$abs vec/4
  :logic vec/4$a
  :exec vec/4$c)
