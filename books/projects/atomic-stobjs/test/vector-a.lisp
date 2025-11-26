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

(include-book "centaur/fty/basetypes" :dir :system)

(include-book "../constructors/vector-a")


;;;; Concrete Tests
(atomic-stobjs::define-vector$a arr/0 0)

(atomic-stobjs::define-vector$a arr/1 #xbabe)

(atomic-stobjs::define-vector$a arr/2 0
  :resizable t)

(atomic-stobjs::define-vector$a arr/3 #xbabe
  :resizable t)


;;;; `NATP' Elements
;;; dimensions, element-type, resizable
(atomic-stobjs::define-vector$a vec$a/10-nat-t 10
  :element-recognizer natp
  :element-fixer nfix
  :element nat
  :initial-element 0
  :resizable t)

(atomic-stobjs::define-vector$a vec$a/10-nat-nil 10
  :element-recognizer natp
  :element-fixer nfix
  :element nat
  :initial-element 0)

(atomic-stobjs::define-vector$a vec$a/0-nat-t 0
  :element-recognizer natp
  :element-fixer nfix
  :element nat
  :initial-element 0
  :resizable t)

(atomic-stobjs::define-vector$a vec$a/0-nat-nil 0
  :element-recognizer natp
  :element-fixer nfix
  :element nat
  :initial-element 0)


;;;; `BOOLEANP' Elements
;;; dimensions, element-type, resizable
(atomic-stobjs::define-vector$a vec$a/10-boolean-t 10
  :element-recognizer booleanp
  :element-fixer bool-fix
  :element b
  :initial-element t
  :resizable t)

(atomic-stobjs::define-vector$a vec$a/10-boolean-nil 10
  :element-recognizer booleanp
  :element-fixer bool-fix
  :element b
  :initial-element t)

(atomic-stobjs::define-vector$a vec$a/0-boolean-t 0
  :element-recognizer booleanp
  :element-fixer bool-fix
  :element b
  :initial-element t
  :resizable t)

(atomic-stobjs::define-vector$a vec$a/0-boolean-nil 0
  :element-recognizer booleanp
  :element-fixer bool-fix
  :element b
  :initial-element t)
