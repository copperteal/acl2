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

(include-book "../constructors/vector$c")

(atomic-stobjs::define-vector$c vec$c/nargs 31)


;;;; Stobj Values
(defstobj foo$c
  a
  :non-memoizable t
  :non-executable t)

(atomic-stobjs::define-vector$c vec$c/foo$c-0 0
  :element-type foo$c
  :resizable nil)

(atomic-stobjs::define-vector$c vec$c/foo$c-1 0
  :element-type foo$c
  :resizable t)

(atomic-stobjs::define-vector$c vec$c/foo$c-2 997
  :element-type foo$c
  :resizable nil)

(atomic-stobjs::define-vector$c vec$c/foo$c-3 997
  :element-type foo$c
  :resizable t)


;;;; type t
(atomic-stobjs::define-vector$c vec$c/t-0 0
  :element-type t
  :initial-element nil
  :resizable nil)

(atomic-stobjs::define-vector$c vec$c/t-1 0
  :element-type t
  :initial-element nil
  :resizable t)

(atomic-stobjs::define-vector$c vec$c/t-2 0
  :element-type t
  :initial-element (a b)
  :resizable nil)

(atomic-stobjs::define-vector$c vec$c/t-3 0
  :element-type t
  :initial-element c
  :resizable t)

(atomic-stobjs::define-vector$c vec$c/t-4 997
  :element-type t
  :initial-element nil
  :resizable nil)

(atomic-stobjs::define-vector$c vec$c/t-5 997
  :element-type t
  :initial-element nil
  :resizable t)

(atomic-stobjs::define-vector$c vec$c/t-6 997
  :element-type t
  :initial-element t
  :resizable nil)

(atomic-stobjs::define-vector$c vec$c/t-7 997
  :element-type t
  :initial-element t
  :resizable t)


;;;; type boolean
(atomic-stobjs::define-vector$c vec$c/bool-0 0
  :element-type (member t nil)
  :initial-element nil
  :resizable nil)

(atomic-stobjs::define-vector$c vec$c/bool-1 0
  :element-type (member t nil)
  :initial-element nil
  :resizable t)

(atomic-stobjs::define-vector$c vec$c/bool-2 0
  :element-type (member t nil)
  :initial-element t
  :resizable nil)

(atomic-stobjs::define-vector$c vec$c/bool-3 0
  :element-type (member t nil)
  :initial-element t
  :resizable t)

(atomic-stobjs::define-vector$c vec$c/bool-4 997
  :element-type (member t nil)
  :initial-element nil
  :resizable nil)

(atomic-stobjs::define-vector$c vec$c/bool-5 997
  :element-type (member t nil)
  :initial-element nil
  :resizable t)

(atomic-stobjs::define-vector$c vec$c/bool-6 997
  :element-type (member t nil)
  :initial-element t
  :resizable nil)

(atomic-stobjs::define-vector$c vec$c/bool-7 997
  :element-type (member t nil)
  :initial-element t
  :resizable t)


;;;; type signed-byte
(atomic-stobjs::define-vector$c vec$c/sb-0 0
  :element-type (signed-byte 1511)
  :initial-element 11
  :resizable nil)

(atomic-stobjs::define-vector$c vec$c/sb-1 0
  :element-type (signed-byte 1511)
  :initial-element 11
  :resizable t)

(atomic-stobjs::define-vector$c vec$c/sb-2 0
  :element-type (signed-byte 1511)
  :initial-element -13
  :resizable nil)

(atomic-stobjs::define-vector$c vec$c/sb-3 0
  :element-type (signed-byte 1511)
  :initial-element -13
  :resizable t)

(atomic-stobjs::define-vector$c vec$c/sb-4 997
  :element-type (signed-byte 1511)
  :initial-element 11
  :resizable nil)

(atomic-stobjs::define-vector$c vec$c/sb-5 997
  :element-type (signed-byte 1511)
  :initial-element 11
  :resizable t)

(atomic-stobjs::define-vector$c vec$c/sb-6 997
  :element-type (signed-byte 1511)
  :initial-element -13
  :resizable nil)

(atomic-stobjs::define-vector$c vec$c/sb-7 997
  :element-type (signed-byte 1511)
  :initial-element -13
  :resizable t)
