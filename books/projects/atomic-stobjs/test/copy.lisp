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

(atomic-stobjs::define-copy vec0)

(defun string-fix (x)
  (declare (xargs :guard (stringp x)))
  (if (stringp x)
      x
      ""))

(defun string-equiv (x y)
  (declare (xargs :guard (and (stringp x)
                              (stringp y))))
  (equal (string-fix x)
         (string-fix y)))

(defequiv string-equiv)

(atomic-stobjs::define-vector vec1 1024
  :element-type string
  :element-recognizer stringp
  :element-fixer string-fix
  :element-equiv string-equiv
  :initial-element ""
  :resizable nil)

(atomic-stobjs::define-copy vec1)

(atomic-stobjs::define-vector vec2 13
  :element-type vec0
  :resizable nil)

(atomic-stobjs::define-copy vec2)

(atomic-stobjs::define-vector vec3 13
  :element-type vec2
  :resizable nil)

(atomic-stobjs::define-copy vec3)

(atomic-stobjs::define-vector vec4 10000
  :element-type vec3
  :resizable t)

(atomic-stobjs::define-copy vec4)

(atomic-stobjs::define-vector vec5 20000
  :resizable nil)

(atomic-stobjs::define-copy vec5)


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

(defun character-fix (x)
  (declare (xargs :guard t))
  (if (characterp x)
      x
      #.acl2::*null-char*))

(defun character-equiv (x y)
  (declare (xargs :guard t))
  (equal (character-fix x)
         (character-fix y)))

(defequiv character-equiv)

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

(atomic-stobjs::define-hash-table ht1 eql
  :element-type ht0
  :key-recognizer characterp
  :key-fixer character-fix
  :key-equiv character-equiv
  :default-key #.acl2::*null-char*)

(atomic-stobjs::define-copy ht1)

(atomic-stobjs::define-hash-table ht2 equal
  :element-type ht1)

(atomic-stobjs::define-copy ht2)

(atomic-stobjs::define-hash-table ht3 equal
  :element-type ht2)

(atomic-stobjs::define-copy ht3)


(atomic-stobjs::define-hash-table ht-of-vec equal
  :element-type vec5)

(atomic-stobjs::define-copy ht-of-vec)

(atomic-stobjs::define-vector vec-of-ht 3000
  :element-type ht3
  :resizable nil)

(atomic-stobjs::define-copy vec-of-ht)

(atomic-stobjs::define-vector vec-of-ht/r 3000
  :element-type ht3
  :resizable t)

(atomic-stobjs::define-copy vec-of-ht/r)


(defun %symbol-fix (x)
  (declare (xargs :guard (symbolp x)))
  (if (symbolp x)
      x
      '||))

(defun %symbol-equiv (x y)
  (declare (xargs :guard (and (symbolp x)
                              (symbolp y))))
  (equal (%symbol-fix x)
         (%symbol-fix y)))

(defequiv %symbol-equiv)

(atomic-stobjs::define-hash-table ht eq
  :key-recognizer symbolp
  :key-fixer %symbol-fix
  :key-equiv %symbol-equiv
  :default-key ||
  :val-recognizer stringp
  :val-fixer string-fix
  :val-equiv string-equiv
  :default-val ""
  :element-type string)

(atomic-stobjs::define-copy ht)

(atomic-stobjs::define-vector vec 17
  :element-type ht
  :resizable t)

(atomic-stobjs::define-copy vec)

(atomic-stobjs::define-hash-table ht2$ eql
  :key-recognizer integerp
  :key-fixer ifix
  :key-equiv int-equiv
  :default-key 0
  :element-type vec)

(atomic-stobjs::define-copy ht2$)

(atomic-stobjs::define-frame fr
  (f0 :element-type ht)
  (f1 :element-type vec)
  (f2 :element-type ht2$)
  (f3 :element-type symbol
      :recognizer symbolp
      :fixer %symbol-fix
      :equiv %symbol-equiv
      :initial-element ||))

(atomic-stobjs::define-copy fr)

(atomic-stobjs::define-vector vec2$ 3
  :element-type fr
  :resizable nil)

(atomic-stobjs::define-copy vec2$)

(atomic-stobjs::define-hash-table ht3$ equal
  :element-type fr)

(atomic-stobjs::define-copy ht3$)

(atomic-stobjs::define-frame fr2
  (f0 :element-type fr)
  (f1 :element-type vec2$)
  (f2 :element-type ht2$))

(atomic-stobjs::define-copy fr2)
