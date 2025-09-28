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
;;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS”
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
(include-book "../constructors/stobj-copy")
(include-book "../constructors/define-array")
(include-book "../constructors/define-hash-table")
(include-book "../constructors/define-frame")

(defun string-fix (x)
  (declare (xargs :guard t))
  (if (stringp x) x ""))

(defthm symbol-fix-when-not-symbolp
  (implies (not (symbolp key))
           (equal (symbol-fix key) '||))
  :hints
  (("Goal"
    :in-theory (enable symbol-fix))))

(defthm string-fix-when-stringp
  (implies (stringp val)
           (equal (string-fix val) val)))

(defthm string-fix-when-not-stringp
  (implies (not (stringp val))
           (equal (string-fix val) "")))

(defthm ifix-when-integerp
  (implies (integerp key)
           (equal (ifix key) key)))

(defthm ifix-when-not-integerp
  (implies (not (integerp key))
           (equal (ifix key) 0)))


(atomic-stobjs::define-hash-table ht eq
  :key-recognizer symbolp
  :key-fixer symbol-fix
  :default-key ||
  :val-recognizer stringp
  :val-fixer string-fix
  :default-val ""
  :element-type string)

(atomic-stobjs::define-stobj-copier ht)

(atomic-stobjs::define-array arr 17
  :element-type ht
  :element-recognizer htp
  :element-fixer ht-fix
  :element ht
  :initial-element (create-ht$a)
  :resizable t)

(atomic-stobjs::define-stobj-copier arr)

(atomic-stobjs::define-hash-table ht2 eql
  :key-recognizer integerp
  :key-fixer ifix
  :default-key 0
  :val-recognizer arrp
  :val-fixer arr-fix
  :val arr
  :default-val (create-arr$a)
  :element-type arr)

(atomic-stobjs::define-stobj-copier ht2)

(atomic-stobjs::define-frame fr
  (f0 :element-type ht
      :stobj ht
      :recognizer htp
      :fixer ht-fix
      :initial-element (create-ht$a))
  (f1 :element-type arr
      :stobj arr
      :recognizer arrp
      :fixer arr-fix
      :initial-element (create-arr$a))
  (f2 :element-type ht2
      :stobj ht2
      :recognizer ht2p
      :fixer ht2-fix
      :initial-element (create-ht2$a))
  (f3 :element-type symbol
      :recognizer symbolp
      :fixer symbol-fix
      :initial-element ||))

(atomic-stobjs::define-stobj-copier fr)

(atomic-stobjs::define-array arr2 3
  :element-type fr
  :element-recognizer frp
  :element-fixer fr-fix
  :element fr
  :initial-element (create-fr$a))

(atomic-stobjs::define-stobj-copier arr2)

(atomic-stobjs::define-hash-table ht3 equal
  :val-recognizer frp
  :val-fixer fr-fix
  :val fr
  :default-val (create-fr$a)
  :element-type fr)

(atomic-stobjs::define-stobj-copier ht3)

(atomic-stobjs::define-frame fr2
  (f0 :element-type fr
      :stobj fr
      :recognizer frp
      :fixer fr-fix
      :initial-element (create-fr$a))
  (f1 :element-type arr2
      :stobj arr2
      :recognizer arr2p
      :fixer arr2-fix
      :initial-element (create-arr2$a))
  (f2 :element-type ht2
      :stobj ht2
      :recognizer ht2p
      :fixer ht2-fix
      :initial-element (create-ht2$a)))

(atomic-stobjs::define-stobj-copier fr2)
