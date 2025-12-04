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

(include-book "std/basic/defs" :dir :system)
(include-book "std/basic/arith-equivs" :dir :system)

(include-book "../constructors/hash-table-c")
(include-book "../constructors/hash-table-a")
(include-book "../constructors/hash-table-abs")

(defun keyword-fix (x)
  (declare (xargs :guard t))
  (if (keywordp x)
      x
      :||))

(defthm keyword-fix-when-keywordp
  (implies (keywordp key)
           (equal (keyword-fix key) key)))

(defthm keyword-fix-when-not-keywordp
  (implies (not (keywordp key))
           (equal (keyword-fix key) :||)))

(defthm keywordp-of-keyword-fix
  (keywordp (keyword-fix key)))

(defun keyword-equiv (x y)
  (declare (xargs :guard t))
  (equal (keyword-fix x)
         (keyword-fix y)))

(defequiv keyword-equiv)

(defun string-fix (x)
  (declare (xargs :guard t))
  (if (stringp x)
      x
      ""))

(defthm stringp-of-string-fix
  (stringp (string-fix x)))

(defthm string-fix-when-stringp
  (implies (stringp val)
           (equal (string-fix val) val)))

(defthm string-fix-when-not-stringp
  (implies (not (stringp val))
           (equal (string-fix val) "")))

(defun string-equiv (x y)
  (declare (xargs :guard t))
  (equal (string-fix x)
         (string-fix y)))

(defequiv string-equiv)

(defun if-bool-fix (x)
  (declare (xargs :guard t))
  (if (booleanp x)
      x
      t))

(defthm if-bool-fix-when-booleanp
  (implies (booleanp val)
           (equal (if-bool-fix val) val)))

(defthm if-bool-fix-when-not-booleanp
  (implies (not (booleanp val))
           (equal (if-bool-fix val) t)))

(defun char-equiv (x y)
  (declare (xargs :guard t))
  (equal (char-fix x)
         (char-fix y)))

(defequiv char-equiv)


(atomic-stobjs::define-hash-table$c ht/0$c equal)

(atomic-stobjs::define-hash-table$a ht/0$a equal)

(atomic-stobjs::define-hash-table$corr ht/0)

(atomic-stobjs::define-hash-table$abs ht/0)


(atomic-stobjs::define-hash-table$c htn/0$c equal
  :copyable nil)

(atomic-stobjs::define-hash-table$a htn/0$a equal
  :copyable nil)

(atomic-stobjs::define-hash-table$corr htn/0
  :copyable nil)

(atomic-stobjs::define-hash-table$abs htn/0
  :copyable nil)


(atomic-stobjs::define-hash-table$c ht/1$c hons-equal)

(atomic-stobjs::define-hash-table$a ht/1$a hons-equal)

(atomic-stobjs::define-hash-table$corr ht/1)

(atomic-stobjs::define-hash-table$abs ht/1)


(atomic-stobjs::define-hash-table$c htn/1$c hons-equal
  :copyable nil)

(atomic-stobjs::define-hash-table$a htn/1$a hons-equal
  :copyable nil)

(atomic-stobjs::define-hash-table$corr htn/1
  :copyable nil)

(atomic-stobjs::define-hash-table$abs htn/1
  :copyable nil)


(atomic-stobjs::define-hash-table$c ht/2$c eq)

(atomic-stobjs::define-hash-table$a ht/2$a eq
  :key-recognizer keywordp
  :key-fixer keyword-fix
  :key-equiv keyword-equiv
  :default-key :||)

(atomic-stobjs::define-hash-table$corr ht/2)

(atomic-stobjs::define-hash-table$abs ht/2)


(atomic-stobjs::define-hash-table$c htn/2$c eq
  :copyable nil)

(atomic-stobjs::define-hash-table$a htn/2$a eq
  :key-recognizer keywordp
  :key-fixer keyword-fix
  :key-equiv keyword-equiv
  :default-key :||
  :copyable nil)

(atomic-stobjs::define-hash-table$corr htn/2
  :copyable nil)

(atomic-stobjs::define-hash-table$abs htn/2
  :copyable nil)


(atomic-stobjs::define-hash-table$c ht/3$c eql)

(atomic-stobjs::define-hash-table$a ht/3$a eql
  :key-recognizer natp
  :key-fixer nfix
  :key-equiv nat-equiv
  :default-key 0)

(atomic-stobjs::define-hash-table$corr ht/3)

(atomic-stobjs::define-hash-table$abs ht/3)


(atomic-stobjs::define-hash-table$c htn/3$c eql
  :copyable nil)

(atomic-stobjs::define-hash-table$a htn/3$a eql
  :key-recognizer natp
  :key-fixer nfix
  :key-equiv nat-equiv
  :default-key 0
  :copyable nil)

(atomic-stobjs::define-hash-table$corr htn/3
  :copyable nil)

(atomic-stobjs::define-hash-table$abs htn/3
  :copyable nil)


(atomic-stobjs::define-hash-table$c ht/4$c eql)

(atomic-stobjs::define-hash-table$a ht/4$a eql
  :key-recognizer characterp
  :key-fixer char-fix
  :key-equiv char-equiv
  :default-key #.acl2::*null-char*)

(atomic-stobjs::define-hash-table$corr ht/4)

(atomic-stobjs::define-hash-table$abs ht/4)


(atomic-stobjs::define-hash-table$c htn/4$c eql
  :copyable nil)

(atomic-stobjs::define-hash-table$a htn/4$a eql
  :key-recognizer characterp
  :key-fixer char-fix
  :key-equiv char-equiv
  :default-key #.acl2::*null-char*
  :copyable nil)

(atomic-stobjs::define-hash-table$corr htn/4
  :copyable nil)

(atomic-stobjs::define-hash-table$abs htn/4
  :copyable nil)


;;;; `STRINGP' Values
(atomic-stobjs::define-hash-table$c ht-string/0$c eq
  :element-type string
  :default-value "")

(atomic-stobjs::define-hash-table$a ht-string/0$a eq
  :key-recognizer keywordp
  :key-fixer keyword-fix
  :key-equiv keyword-equiv
  :default-key :||
  :val-recognizer stringp
  :val-fixer string-fix
  :val-equiv string-equiv
  :default-val "")

(atomic-stobjs::define-hash-table$corr ht-string/0)

(atomic-stobjs::define-hash-table$abs ht-string/0)


;;;; `STRINGP' Values
(atomic-stobjs::define-hash-table$c htn-string/0$c eq
  :element-type string
  :default-value ""
  :copyable nil)

(atomic-stobjs::define-hash-table$a htn-string/0$a eq
  :key-recognizer keywordp
  :key-fixer keyword-fix
  :key-equiv keyword-equiv
  :default-key :||
  :val-recognizer stringp
  :val-fixer string-fix
  :val-equiv string-equiv
  :default-val ""
  :copyable nil)

(atomic-stobjs::define-hash-table$corr htn-string/0
  :copyable nil)

(atomic-stobjs::define-hash-table$abs htn-string/0
  :copyable nil)


(atomic-stobjs::define-hash-table$c ht-string/1$c eql
  :element-type string
  :default-value "")

(atomic-stobjs::define-hash-table$a ht-string/1$a eql
  :key-recognizer natp
  :key-fixer nfix
  :key-equiv nat-equiv
  :default-key 0
  :val-recognizer stringp
  :val-fixer string-fix
  :val-equiv string-equiv
  :default-val "")

(atomic-stobjs::define-hash-table$corr ht-string/1)

(atomic-stobjs::define-hash-table$abs ht-string/1)


(atomic-stobjs::define-hash-table$c htn-string/1$c eql
  :element-type string
  :default-value ""
  :copyable nil)

(atomic-stobjs::define-hash-table$a htn-string/1$a eql
  :key-recognizer natp
  :key-fixer nfix
  :key-equiv nat-equiv
  :default-key 0
  :val-recognizer stringp
  :val-fixer string-fix
  :val-equiv string-equiv
  :default-val ""
  :copyable nil)

(atomic-stobjs::define-hash-table$corr htn-string/1
  :copyable nil)

(atomic-stobjs::define-hash-table$abs htn-string/1
  :copyable nil)


(atomic-stobjs::define-hash-table$c ht-string/2$c eql
  :element-type string
  :default-value "")

(atomic-stobjs::define-hash-table$a ht-string/2$a eql
  :key-recognizer characterp
  :key-fixer char-fix
  :key-equiv char-equiv
  :default-key #.acl2::*null-char*
  :val-recognizer stringp
  :val-fixer string-fix
  :val-equiv string-equiv
  :default-val "")

(atomic-stobjs::define-hash-table$corr ht-string/2)

(atomic-stobjs::define-hash-table$abs ht-string/2)


(atomic-stobjs::define-hash-table$c htn-string/2$c eql
  :element-type string
  :default-value ""
  :copyable nil)

(atomic-stobjs::define-hash-table$a htn-string/2$a eql
  :key-recognizer characterp
  :key-fixer char-fix
  :key-equiv char-equiv
  :default-key #.acl2::*null-char*
  :val-recognizer stringp
  :val-fixer string-fix
  :val-equiv string-equiv
  :default-val ""
  :copyable nil)

(atomic-stobjs::define-hash-table$corr htn-string/2
  :copyable nil)

(atomic-stobjs::define-hash-table$abs htn-string/2
  :copyable nil)


(atomic-stobjs::define-hash-table$c ht-string/3$c hons-equal
  :element-type string
  :default-value "")

(atomic-stobjs::define-hash-table$a ht-string/3$a hons-equal
  :val-recognizer stringp
  :val-fixer string-fix
  :val-equiv string-equiv
  :default-val "")

(atomic-stobjs::define-hash-table$corr ht-string/3)

(atomic-stobjs::define-hash-table$abs ht-string/3)


(atomic-stobjs::define-hash-table$c htn-string/3$c hons-equal
  :element-type string
  :default-value ""
  :copyable nil)

(atomic-stobjs::define-hash-table$a htn-string/3$a hons-equal
  :val-recognizer stringp
  :val-fixer string-fix
  :val-equiv string-equiv
  :default-val ""
  :copyable nil)

(atomic-stobjs::define-hash-table$corr htn-string/3
  :copyable nil)

(atomic-stobjs::define-hash-table$abs htn-string/3
  :copyable nil)


(atomic-stobjs::define-hash-table$c ht-string/4$c equal
  :element-type string
  :default-value "")

(atomic-stobjs::define-hash-table$a ht-string/4$a equal
  :val-recognizer stringp
  :val-fixer string-fix
  :val-equiv string-equiv
  :default-val "")

(atomic-stobjs::define-hash-table$corr ht-string/4)

(atomic-stobjs::define-hash-table$abs ht-string/4)


(atomic-stobjs::define-hash-table$c htn-string/4$c equal
  :element-type string
  :default-value ""
  :copyable nil)

(atomic-stobjs::define-hash-table$a htn-string/4$a equal
  :val-recognizer stringp
  :val-fixer string-fix
  :val-equiv string-equiv
  :default-val ""
  :copyable nil)

(atomic-stobjs::define-hash-table$corr htn-string/4
  :copyable nil)

(atomic-stobjs::define-hash-table$abs htn-string/4
  :copyable nil)


;;;; `BOOLEANP' Values
(atomic-stobjs::define-hash-table$c ht-boolean/0$c eq
  :element-type (member nil t)
  :default-value t)

(atomic-stobjs::define-hash-table$a ht-boolean/0$a eq
  :key-recognizer keywordp
  :key-fixer keyword-fix
  :key-equiv keyword-equiv
  :default-key :||
  :val-recognizer booleanp
  :val-fixer if-bool-fix
  :val-equiv iff
  :default-val t)

(atomic-stobjs::define-hash-table$corr ht-boolean/0)

(atomic-stobjs::define-hash-table$abs ht-boolean/0)


;;;; `BOOLEANP' Values
(atomic-stobjs::define-hash-table$c htn-boolean/0$c eq
  :element-type (member nil t)
  :default-value t
  :copyable nil)

(atomic-stobjs::define-hash-table$a htn-boolean/0$a eq
  :key-recognizer keywordp
  :key-fixer keyword-fix
  :key-equiv keyword-equiv
  :default-key :||
  :val-recognizer booleanp
  :val-fixer if-bool-fix
  :val-equiv iff
  :default-val t
  :copyable nil)

(atomic-stobjs::define-hash-table$corr htn-boolean/0
  :copyable nil)

(atomic-stobjs::define-hash-table$abs htn-boolean/0
  :copyable nil)


(atomic-stobjs::define-hash-table$c ht-boolean/1$c eql
  :element-type (member nil t)
  :default-value t)

(atomic-stobjs::define-hash-table$a ht-boolean/1$a eql
  :key-recognizer natp
  :key-fixer nfix
  :key-equiv nat-equiv
  :default-key 0
  :val-recognizer booleanp
  :val-fixer if-bool-fix
  :val-equiv iff
  :default-val t)

(atomic-stobjs::define-hash-table$corr ht-boolean/1)

(atomic-stobjs::define-hash-table$abs ht-boolean/1)


(atomic-stobjs::define-hash-table$c htn-boolean/1$c eql
  :element-type (member nil t)
  :default-value t
  :copyable nil)

(atomic-stobjs::define-hash-table$a htn-boolean/1$a eql
  :key-recognizer natp
  :key-fixer nfix
  :key-equiv nat-equiv
  :default-key 0
  :val-recognizer booleanp
  :val-fixer if-bool-fix
  :val-equiv iff
  :default-val t
  :copyable nil)

(atomic-stobjs::define-hash-table$corr htn-boolean/1
  :copyable nil)

(atomic-stobjs::define-hash-table$abs htn-boolean/1
  :copyable nil)


(atomic-stobjs::define-hash-table$c ht-boolean/2$c eql
  :element-type (member nil t)
  :default-value t)

(atomic-stobjs::define-hash-table$a ht-boolean/2$a eql
  :key-recognizer characterp
  :key-fixer char-fix
  :key-equiv char-equiv
  :default-key #.acl2::*null-char*
  :val-recognizer booleanp
  :val-fixer if-bool-fix
  :val-equiv iff
  :default-val t)

(atomic-stobjs::define-hash-table$corr ht-boolean/2)

(atomic-stobjs::define-hash-table$abs ht-boolean/2)


(atomic-stobjs::define-hash-table$c htn-boolean/2$c eql
  :element-type (member nil t)
  :default-value t
  :copyable nil)

(atomic-stobjs::define-hash-table$a htn-boolean/2$a eql
  :key-recognizer characterp
  :key-fixer char-fix
  :key-equiv char-equiv
  :default-key #.acl2::*null-char*
  :val-recognizer booleanp
  :val-fixer if-bool-fix
  :val-equiv iff
  :default-val t
  :copyable nil)

(atomic-stobjs::define-hash-table$corr htn-boolean/2
  :copyable nil)

(atomic-stobjs::define-hash-table$abs htn-boolean/2
  :copyable nil)


(atomic-stobjs::define-hash-table$c ht-boolean/3$c hons-equal
  :element-type (member nil t)
  :default-value t)

(atomic-stobjs::define-hash-table$a ht-boolean/3$a hons-equal
  :val-recognizer booleanp
  :val-fixer if-bool-fix
  :val-equiv iff
  :default-val t)

(atomic-stobjs::define-hash-table$corr ht-boolean/3)

(atomic-stobjs::define-hash-table$abs ht-boolean/3)


(atomic-stobjs::define-hash-table$c htn-boolean/3$c hons-equal
  :element-type (member nil t)
  :default-value t
  :copyable nil)

(atomic-stobjs::define-hash-table$a htn-boolean/3$a hons-equal
  :val-recognizer booleanp
  :val-fixer if-bool-fix
  :val-equiv iff
  :default-val t
  :copyable nil)

(atomic-stobjs::define-hash-table$corr htn-boolean/3
  :copyable nil)

(atomic-stobjs::define-hash-table$abs htn-boolean/3
  :copyable nil)


(atomic-stobjs::define-hash-table$c ht-boolean/4$c equal
  :element-type (member nil t)
  :default-value t)

(atomic-stobjs::define-hash-table$a ht-boolean/4$a equal
  :val-recognizer booleanp
  :val-fixer if-bool-fix
  :val-equiv iff
  :default-val t)

(atomic-stobjs::define-hash-table$corr ht-boolean/4)

(atomic-stobjs::define-hash-table$abs ht-boolean/4)


(atomic-stobjs::define-hash-table$c htn-boolean/4$c equal
  :element-type (member nil t)
  :default-value t
  :copyable nil)

(atomic-stobjs::define-hash-table$a htn-boolean/4$a equal
  :val-recognizer booleanp
  :val-fixer if-bool-fix
  :val-equiv iff
  :default-val t
  :copyable nil)

(atomic-stobjs::define-hash-table$corr htn-boolean/4
  :copyable nil)

(atomic-stobjs::define-hash-table$abs htn-boolean/4
  :copyable nil)
