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

;;; dimensions, element-type, initial-element, resizable
(include-book "../constructors/vector$c")

; TODO: systematically test edge cases!


;;;; No Keyword Arguments
(atomic-stobjs::define-vector$c arr$c/nargs 31)


;;;; Stobj Values
(defstobj foo$c
  a
  :inline t
  :non-memoizable t
  :non-executable t)


;;;; length zero, type stobj
(atomic-stobjs::define-vector$c arr$c/0-foo$c-nil-nil 0
  :element-type foo$c
  :resizable nil)

(atomic-stobjs::define-vector$c arr$c/0-foo$c-nil-t 0
  :element-type foo$c
  :resizable t)


;;;; length 997, type stobj
(atomic-stobjs::define-vector$c arr$c/997-foo$c-nil-nil 997
  :element-type foo$c
  :resizable nil)

(atomic-stobjs::define-vector$c arr$c/997-foo$c-nil-t 997
  :element-type foo$c
  :resizable t)


;;;; length zero, type t
(atomic-stobjs::define-vector$c arr$c/0-t-nil-nil 0
  :element-type t
  :initial-element nil
  :resizable nil)

(atomic-stobjs::define-vector$c arr$c/0-t-nil-t 0
  :element-type t
  :initial-element nil
  :resizable t)

(atomic-stobjs::define-vector$c arr$c/0-t-|(A B)|-nil 0
  :element-type t
  :initial-element (a b)
  :resizable nil)

(atomic-stobjs::define-vector$c arr$c/0-t-c-t 0
  :element-type t
  :initial-element c
  :resizable t)


;;;; length 997, type t
(atomic-stobjs::define-vector$c arr$c/997-t-nil-nil 997
  :element-type t
  :initial-element nil
  :resizable nil)

(atomic-stobjs::define-vector$c arr$c/997-t-nil-t 997
  :element-type t
  :initial-element nil
  :resizable t)

(atomic-stobjs::define-vector$c arr$c/997-t-t-nil 997
  :element-type t
  :initial-element t
  :resizable nil)

(atomic-stobjs::define-vector$c arr$c/997-t-t-t 997
  :element-type t
  :initial-element t
  :resizable t)


;;;; length zero, type including nil
(atomic-stobjs::define-vector$c arr$c/0-|(MEMBER T NIL)|-nil-nil 0
  :element-type (member t nil)
  :initial-element nil
  :resizable nil)

(atomic-stobjs::define-vector$c arr$c/0-|(MEMBER T NIL)|-nil-t 0
  :element-type (member t nil)
  :initial-element nil
  :resizable t)

(atomic-stobjs::define-vector$c arr$c/0-|(MEMBER T NIL)|-t-nil 0
  :element-type (member t nil)
  :initial-element t
  :resizable nil)

(atomic-stobjs::define-vector$c arr$c/0-|(MEMBER T NIL)|-t-t 0
  :element-type (member t nil)
  :initial-element t
  :resizable t)


;;;; length 997, type including nil
(atomic-stobjs::define-vector$c arr$c/997-|(MEMBER T NIL)|-nil-nil 997
  :element-type (member t nil)
  :initial-element nil
  :resizable nil)

(atomic-stobjs::define-vector$c arr$c/997-|(MEMBER T NIL)|-nil-t 997
  :element-type (member t nil)
  :initial-element nil
  :resizable t)

(atomic-stobjs::define-vector$c arr$c/997-|(MEMBER T NIL)|-t-nil 997
  :element-type (member t nil)
  :initial-element t
  :resizable nil)

(atomic-stobjs::define-vector$c arr$c/997-|(MEMBER T NIL)|-t-t 997
  :element-type (member t nil)
  :initial-element t
  :resizable t)


;;;; length zero, type not including nil
(atomic-stobjs::define-vector$c arr$c/0-|(SIGNED-BYTE 1511)|-11-nil 0
  :element-type (signed-byte 1511)
  :initial-element 11
  :resizable nil)

(atomic-stobjs::define-vector$c arr$c/0-|(SIGNED-BYTE 1511)|-11-t 0
  :element-type (signed-byte 1511)
  :initial-element 11
  :resizable t)

(atomic-stobjs::define-vector$c arr$c/0-|(SIGNED-BYTE 1511)|--13-nil 0
  :element-type (signed-byte 1511)
  :initial-element -13
  :resizable nil)

(atomic-stobjs::define-vector$c arr$c/0-|(SIGNED-BYTE 1511)|--13-t 0
  :element-type (signed-byte 1511)
  :initial-element -13
  :resizable t)


;;;; length 997, type not including nil
(atomic-stobjs::define-vector$c arr$c/997-|(SIGNED-BYTE 1511)|-11-nil 997
  :element-type (signed-byte 1511)
  :initial-element 11
  :resizable nil)

(atomic-stobjs::define-vector$c arr$c/997-|(SIGNED-BYTE 1511)|-11-t 997
  :element-type (signed-byte 1511)
  :initial-element 11
  :resizable t)

(atomic-stobjs::define-vector$c arr$c/997-|(SIGNED-BYTE 1511)|--13-nil 997
  :element-type (signed-byte 1511)
  :initial-element -13
  :resizable nil)

(atomic-stobjs::define-vector$c arr$c/997-|(SIGNED-BYTE 1511)|--13-t 997
  :element-type (signed-byte 1511)
  :initial-element -13
  :resizable t)
