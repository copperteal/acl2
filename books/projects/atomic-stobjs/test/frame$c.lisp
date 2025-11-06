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

(include-book "../constructors/frame$c")


;;;; Stobj Values
(defstobj st/0
  a/0
  :non-memoizable t
  :non-executable t)

(defstobj %st/0
  %a/0
  :congruent-to st/0
  :non-memoizable t
  :non-executable t)

(defun st/0-copy (%st/0 st/0)
  (declare (xargs :stobjs (%st/0 st/0)))
  (update-a/0 (a/0 st/0) %st/0))

(table atomic-stobjs::copier 'st/0 'st/0-copy)

(defun st/0-fix (st/0)
  (declare (xargs :stobjs st/0))
  (if (st/0p st/0)
      st/0
      (create-st/0)))

(table atomic-stobjs::fixer 'st/0 'st/0-fix)

(defstobj st/1
  a/1
  :non-memoizable t
  :non-executable t)

(defstobj %st/1
  %a/1
  :congruent-to st/1
  :non-memoizable t
  :non-executable t)

(defun st/1-copy (%st/1 st/1)
  (declare (xargs :stobjs (%st/1 st/1)))
  (update-a/1 (a/1 st/1) %st/1))

(table atomic-stobjs::copier 'st/1 'st/1-copy)

(defun st/1-fix (st/1)
  (declare (xargs :stobjs st/1))
  (if (st/1p st/1)
      st/1
      (create-st/1)))

(table atomic-stobjs::fixer 'st/1 'st/1-fix)

(defstobj st/2
  a/2
  :non-memoizable t
  :non-executable t)

(defstobj %st/2
  %a/2
  :congruent-to st/2
  :non-memoizable t
  :non-executable t)

(defun st/2-copy (%st/2 st/2)
  (declare (xargs :stobjs (%st/2 st/2)))
  (update-a/2 (a/2 st/2) %st/2))

(table atomic-stobjs::copier 'st/2 'st/2-copy)

(defun st/2-fix (st/2)
  (declare (xargs :stobjs st/2))
  (if (st/2p st/2)
      st/2
      (create-st/2)))

(table atomic-stobjs::fixer 'st/2 'st/2-fix)

(with-books (("std/lists/len" :dir :system))
  (defthm stobj-element-constraints
    (and (st/0p (create-st/0))
         (st/1p (create-st/1))
         (st/2p (create-st/2))
         (implies (and (st/0p %st/0)
                       (st/0p st/0))
                  (equal (st/0-copy %st/0 st/0)
                         st/0))
         (implies (and (st/1p %st/1)
                       (st/1p st/1))
                  (equal (st/1-copy %st/1 st/1)
                         st/1))
         (implies (and (st/2p %st/2)
                       (st/2p st/2))
                  (equal (st/2-copy %st/2 st/2)
                         st/2)))))


(atomic-stobjs::define-frame$c fr$c/st
  (f0 :element-type st/0)
  (f1 :element-type st/1)
  (f2 :element-type st/2))


(atomic-stobjs::define-frame$c fr$c/empty)

(atomic-stobjs::define-frame$c fr$c
  (f0 :element-type unsigned-byte
      :initial-element 0)
  (f1 :element-type symbol)
  (f2 :element-type string
      :initial-element ""))

(atomic-stobjs::define-frame$c fr$c/big
  (f0) (f1) (f2) (f3)
  (f4) (f5) (f6) (f7)
  (f8) (f9) (f10) (f11)
  (f12) (f13) (f14) (f15)
  (f16) (f17) (f18) (f19)
  (f20) (f21) (f22) (f23)
  (f24) (f25) (f26) (f27)
  (f28) (f29) (f30) (f31))
