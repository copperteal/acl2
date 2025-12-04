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

(include-book "../constructors/hash-table")

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

(defun null-symbol-fix (x)
  (declare (xargs :guard t))
  (and (symbolp x)
       x))

(defthm null-symbol-fix-when-symbolp
  (implies (symbolp key)
           (equal (null-symbol-fix key) key)))

(defthm null-symbol-fix-when-not-symbolp
  (implies (not (symbolp key))
           (not (null-symbol-fix key))))

(defun null-symbol-equiv (x y)
  (declare (xargs :guard t))
  (equal (null-symbol-fix x)
         (null-symbol-fix y)))

(defequiv null-symbol-equiv)

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


;;;; Concrete Tests
(atomic-stobjs::define-hash-table ht/0 eq
  :key-recognizer symbolp
  :key-fixer null-symbol-fix
  :key-equiv null-symbol-equiv
  :default-key nil)

(atomic-stobjs::define-hash-table ht/0-nil eq
  :key-recognizer symbolp
  :key-fixer null-symbol-fix
  :key-equiv null-symbol-equiv
  :default-key nil
  :copyable nil)

(atomic-stobjs::define-hash-table ht/1 eql
  :key-recognizer natp
  :key-fixer nfix
  :key-equiv nat-equiv
  :default-key 0)

(atomic-stobjs::define-hash-table ht/1-nil eql
  :key-recognizer natp
  :key-fixer nfix
  :key-equiv nat-equiv
  :default-key 0
  :copyable nil)

(atomic-stobjs::define-hash-table ht/2 eql
  :key-recognizer characterp
  :key-fixer char-fix
  :key-equiv char-equiv
  :default-key #.acl2::*null-char*)

(atomic-stobjs::define-hash-table ht/2-nil eql
  :key-recognizer characterp
  :key-fixer char-fix
  :key-equiv char-equiv
  :default-key #.acl2::*null-char*
  :copyable nil)

(atomic-stobjs::define-hash-table ht/3 hons-equal)

(atomic-stobjs::define-hash-table ht/3-nil hons-equal
  :copyable nil)

(atomic-stobjs::define-hash-table ht/4 equal)

(atomic-stobjs::define-hash-table ht/4-nil equal
  :copyable nil)


;;;; `STRINGP' Values
(atomic-stobjs::define-hash-table ht/0-string eq
  :key-recognizer symbolp
  :key-fixer null-symbol-fix
  :key-equiv null-symbol-equiv
  :default-key nil
  :val-recognizer stringp
  :val-fixer string-fix
  :val-equiv string-equiv
  :default-val ""
  :element-type string)

(atomic-stobjs::define-hash-table ht/0-string-nil eq
  :key-recognizer symbolp
  :key-fixer null-symbol-fix
  :key-equiv null-symbol-equiv
  :default-key nil
  :val-recognizer stringp
  :val-fixer string-fix
  :val-equiv string-equiv
  :default-val ""
  :element-type string
  :copyable nil)

(atomic-stobjs::define-hash-table ht/1-string eql
  :key-recognizer natp
  :key-fixer nfix
  :key-equiv nat-equiv
  :default-key 0
  :val-recognizer stringp
  :val-fixer string-fix
  :val-equiv string-equiv
  :default-val ""
  :element-type string)

(atomic-stobjs::define-hash-table ht/1-string-nil eql
  :key-recognizer natp
  :key-fixer nfix
  :key-equiv nat-equiv
  :default-key 0
  :val-recognizer stringp
  :val-fixer string-fix
  :val-equiv string-equiv
  :default-val ""
  :element-type string
  :copyable nil)

(atomic-stobjs::define-hash-table ht/2-string eql
  :key-recognizer characterp
  :key-fixer char-fix
  :key-equiv char-equiv
  :default-key #.acl2::*null-char*
  :val-recognizer stringp
  :val-fixer string-fix
  :val-equiv string-equiv
  :default-val ""
  :element-type string)

(atomic-stobjs::define-hash-table ht/2-string-nil eql
  :key-recognizer characterp
  :key-fixer char-fix
  :key-equiv char-equiv
  :default-key #.acl2::*null-char*
  :val-recognizer stringp
  :val-fixer string-fix
  :val-equiv string-equiv
  :default-val ""
  :element-type string
  :copyable nil)

(atomic-stobjs::define-hash-table ht/3-string hons-equal
  :val-recognizer stringp
  :val-fixer string-fix
  :val-equiv string-equiv
  :default-val ""
  :element-type string)

(atomic-stobjs::define-hash-table ht/3-string-nil hons-equal
  :val-recognizer stringp
  :val-fixer string-fix
  :val-equiv string-equiv
  :default-val ""
  :element-type string
  :copyable nil)

(atomic-stobjs::define-hash-table ht/4-string equal
  :val-recognizer stringp
  :val-fixer string-fix
  :val-equiv string-equiv
  :default-val ""
  :element-type string)

(atomic-stobjs::define-hash-table ht/4-string-nil equal
  :val-recognizer stringp
  :val-fixer string-fix
  :val-equiv string-equiv
  :default-val ""
  :element-type string
  :copyable nil)


;;;; `BOOLEANP' Values
(atomic-stobjs::define-hash-table ht/0-boolean eq
  :key-recognizer symbolp
  :key-fixer null-symbol-fix
  :key-equiv null-symbol-equiv
  :default-key nil
  :val-recognizer booleanp
  :val-fixer if-bool-fix
  :val-equiv iff
  :default-val t
  :element-type (member nil t))

(atomic-stobjs::define-hash-table ht/0-boolean-nil eq
  :key-recognizer symbolp
  :key-fixer null-symbol-fix
  :key-equiv null-symbol-equiv
  :default-key nil
  :val-recognizer booleanp
  :val-fixer if-bool-fix
  :val-equiv iff
  :default-val t
  :element-type (member nil t)
  :copyable nil)

(atomic-stobjs::define-hash-table ht/1-boolean eql
  :key-recognizer natp
  :key-fixer nfix
  :key-equiv nat-equiv
  :default-key 0
  :val-recognizer booleanp
  :val-fixer if-bool-fix
  :val-equiv iff
  :default-val t
  :element-type (member nil t))

(atomic-stobjs::define-hash-table ht/1-boolean-nil eql
  :key-recognizer natp
  :key-fixer nfix
  :key-equiv nat-equiv
  :default-key 0
  :val-recognizer booleanp
  :val-fixer if-bool-fix
  :val-equiv iff
  :default-val t
  :element-type (member nil t)
  :copyable nil)

(atomic-stobjs::define-hash-table ht/2-boolean eql
  :key-recognizer characterp
  :key-fixer char-fix
  :key-equiv char-equiv
  :default-key #.acl2::*null-char*
  :val-recognizer booleanp
  :val-fixer if-bool-fix
  :val-equiv iff
  :default-val t
  :element-type (member nil t))

(atomic-stobjs::define-hash-table ht/2-boolean-nil eql
  :key-recognizer characterp
  :key-fixer char-fix
  :key-equiv char-equiv
  :default-key #.acl2::*null-char*
  :val-recognizer booleanp
  :val-fixer if-bool-fix
  :val-equiv iff
  :default-val t
  :element-type (member nil t)
  :copyable nil)

(atomic-stobjs::define-hash-table ht/3-boolean hons-equal
  :val-recognizer booleanp
  :val-fixer if-bool-fix
  :val-equiv iff
  :default-val t
  :element-type (member nil t))

(atomic-stobjs::define-hash-table ht/3-boolean-nil hons-equal
  :val-recognizer booleanp
  :val-fixer if-bool-fix
  :val-equiv iff
  :default-val t
  :element-type (member nil t)
  :copyable nil)

(atomic-stobjs::define-hash-table ht/4-boolean equal
  :val-recognizer booleanp
  :val-fixer if-bool-fix
  :val-equiv iff
  :default-val t
  :element-type (member nil t))

(atomic-stobjs::define-hash-table ht/4-boolean-nil equal
  :val-recognizer booleanp
  :val-fixer if-bool-fix
  :val-equiv iff
  :default-val t
  :element-type (member nil t)
  :copyable nil)
