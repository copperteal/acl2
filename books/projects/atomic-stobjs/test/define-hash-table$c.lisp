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


;;; test, element-type, default-element


(in-package "ACL2")

(include-book "../constructors/stobj-copy")
(include-book "../constructors/define-hash-table")


;;;; No Keyword Arguments
(atomic-stobjs::define-hash-table$c ht$c/nargs-eq eq)
(atomic-stobjs::define-hash-table$c ht$c/nargs-eq-nil eq
  :copyable nil)
(atomic-stobjs::define-hash-table$c ht$c/nargs-eql eql)
(atomic-stobjs::define-hash-table$c ht$c/nargs-eql-nil eql
  :copyable nil)
(atomic-stobjs::define-hash-table$c ht$c/nargs-hons-equal hons-equal)
(atomic-stobjs::define-hash-table$c ht$c/nargs-hons-equal-nil hons-equal
  :copyable nil)
(atomic-stobjs::define-hash-table$c ht$c/nargs-equal equal)
(atomic-stobjs::define-hash-table$c ht$c/nargs-equal-nil equal
  :copyable nil)


;;;; Stobj Values
(defstobj foo$c
  a
  :inline t
  :non-memoizable t
  :non-executable t)

(defstobj %foo$c
  %a
  :congruent-to foo$c
  :inline t
  :non-memoizable t
  :non-executable t)

(defun foo$c-fix (foo$c)
  (declare (xargs :stobjs foo$c))
  (mbe :logic (if (foo$cp foo$c)
                  foo$c
                  (create-foo$c))
       :exec foo$c))

(defthm foo$c-fix{rewrite}
  (equal (foo$c-fix foo$c)
         (if (foo$cp foo$c)
             foo$c
             (create-foo$c))))

(defun foo$c-copy (%foo$c foo$c)
  (declare (xargs :stobjs (%foo$c foo$c)))
  (let* ((%foo$c (foo$c-fix %foo$c))
         (%foo$c (update-%a (a foo$c) %foo$c)))
    %foo$c))

(defthm foo$c-copy{rewrite}
  (implies (foo$cp foo$c)
           (equal (foo$c-copy %foo$c foo$c)
                  foo$c)))

(table atomic-stobjs::stobj-copier
       'atomic-stobjs::stobj-copier-alist
       (putprop 'foo$c
                'atomic-stobjs::copier
                'foo$c-copy
                (atomic-stobjs::stobj-copier-alist world)))

(defthm foo$cp-of-create-foo$c
  (foo$cp (create-foo$c)))

(in-theory
  (disable (:d create-foo$c)
           (:e create-foo$c)
           (:d create-%foo$c)
           (:e create-%foo$c)
           foo$c-copy
           foo$cp
           foo$c-fix))

(atomic-stobjs::define-hash-table$c ht$c/eql-foo$c eql
  :element-type foo$c)

(atomic-stobjs::define-hash-table$c ht$c/eql-foo$c-nil eql
  :element-type foo$c
  :copyable nil)


;;;; type t
(atomic-stobjs::define-hash-table$c ht$c/he-t-t hons-equal
  :element-type t
  :default-value t)

(atomic-stobjs::define-hash-table$c ht$c/he-t-nil hons-equal
  :element-type t
  :default-value nil)

(atomic-stobjs::define-hash-table$c ht$c/he-t-t-nil hons-equal
  :element-type t
  :default-value t
  :copyable nil)

(atomic-stobjs::define-hash-table$c ht$c/he-t-nil-nil hons-equal
  :element-type t
  :default-value nil
  :copyable nil)


;;;; type including nil
(atomic-stobjs::define-hash-table$c ht$c/he-|(MEMBER T NIL)|-t hons-equal
  :element-type (member t nil)
  :default-value t)

(atomic-stobjs::define-hash-table$c ht$c/he-|(MEMBER T NIL)|-nil hons-equal
  :element-type (member t nil)
  :default-value nil)

(atomic-stobjs::define-hash-table$c ht$c/he-|(MEMBER T NIL)|-t-nil hons-equal
  :element-type (member t nil)
  :default-value t
  :copyable nil)

(atomic-stobjs::define-hash-table$c ht$c/he-|(MEMBER T NIL)|-nil-nil hons-equal
  :element-type (member t nil)
  :default-value nil
  :copyable nil)


;;;; type not including nil
(atomic-stobjs::define-hash-table$c ht$c/eq-unsigned-byte-0 eq
  :element-type unsigned-byte
  :default-value 0)

(atomic-stobjs::define-hash-table$c ht$c/eq-signed-byte--1 eq
  :element-type signed-byte
  :default-value -1)

(atomic-stobjs::define-hash-table$c ht$c/eq-unsigned-byte-0-nil eq
  :element-type unsigned-byte
  :default-value 0
  :copyable nil)

(atomic-stobjs::define-hash-table$c ht$c/eq-signed-byte--1-nil eq
  :element-type signed-byte
  :default-value -1
  :copyable nil)
