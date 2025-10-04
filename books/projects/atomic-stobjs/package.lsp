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

(defpkg "ATOMIC-STOBJS"
  (union-eq *common-lisp-symbols-from-main-lisp-package*
            *acl2-exports*
            *type-spec-exports*
            atomic-stobj-accessors::*exports*
            '(package-witness-p
              symbolicate
              with-books
              make-predicate-suffix
              lprogn
              coupled)
            '(hons-remove-assoc
              <<
              symbol-list-listp
              pairlis-x1
              pairlis-x2
              formals
              alist-fix)
            '(lst
              n
              default-value
              l
              key
              val
              i
              j
              rhs
              lhs
              k
              v
              %set
              keys
              ht-size
              rehash-size
              rehash-threshold
              a
              d
              n1
              n2
              v1
              v2
              x
              free
              ac)))

(defpkg "DEFINE-VECTOR"
  (set-difference-eq
   (union-eq *common-lisp-symbols-from-main-lisp-package*
             *acl2-exports*
             '(lst
               n
               default-value
               l
               key
               val
               i
               with-books))
   '(length
     set
     vectorp)))

(defpkg "DEFINE-HASH-TABLE"
  (set-difference-eq
   (union-eq *common-lisp-symbols-from-main-lisp-package*
             *acl2-exports*
             '(<<
               forall))
   '(boundp
     count
     hash-table)))

(defpkg "DEFINE-FRAME"
  (union-eq *common-lisp-symbols-from-main-lisp-package*
            *acl2-exports*))
