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

(include-book "std/basic/arith-equivs" :dir :system)

(include-book "../constructors/vector")
(include-book "../constructors/hash-table")
(include-book "../constructors/frame")
(include-book "../constructors/copy")
(include-book "../constructors/export")


(defun bytep (x)
  (declare (xargs :guard t))
  (unsigned-byte-p 8 x))

(defun byte-fix (x)
  (declare (xargs :guard (bytep x)))
  (if (bytep x)
      x
      0))

(defthm byte-lemmas
  (and (implies (bytep v)
                (equal (byte-fix v) v))
       (implies (not (bytep v))
                (equal (byte-fix v) 0))))

(defun byte-equiv (x y)
  (declare (xargs :guard (and (bytep x)
                              (bytep y))))
  (equal (byte-fix x)
         (byte-fix y)))

(defequiv byte-equiv)


(atomic-stobjs::define-vector vec0 1024
  :element-type (unsigned-byte 8)
  :element-recognizer bytep
  :element-fixer byte-fix
  :element-equiv byte-equiv
  :initial-element 0
  :resizable nil)

(atomic-stobjs::define-export vec0)

(atomic-stobjs::define-vector vec1 1024
  :element-type (unsigned-byte 8)
  :element-recognizer bytep
  :element-fixer byte-fix
  :element-equiv byte-equiv
  :initial-element 0
  :resizable t)

(atomic-stobjs::define-export vec1)


(defun keyword-fix (x)
  (declare (xargs :guard t))
  (if (keywordp x)
      x
      :||))

(defun keyword-equiv (x y)
  (declare (xargs :guard t))
  (equal (keyword-fix x)
         (keyword-fix y)))

(defequiv keyword-equiv)

(atomic-stobjs::define-hash-table ht0 eq
  :element-type unsigned-byte
  :key-recognizer keywordp
  :key-fixer keyword-fix
  :key-equiv keyword-equiv
  :default-key :||
  :val-recognizer natp
  :val-fixer nfix
  :val-equiv nat-equiv
  :default-val 0)

(atomic-stobjs::define-copy ht0)

(atomic-stobjs::define-export ht0)


(atomic-stobjs::define-frame fr0
  (f0 :element-type (unsigned-byte 8)
      :recognizer bytep
      :fixer byte-fix
      :equiv byte-equiv
      :initial-element 0)
  (f1 :element-type symbol
      :recognizer keywordp
      :fixer keyword-fix
      :equiv keyword-equiv
      :initial-element :||)
  (f2 :element-type unsigned-byte
      :recognizer natp
      :fixer nfix
      :equiv nat-equiv
      :initial-element 0))

(atomic-stobjs::define-export fr0)
