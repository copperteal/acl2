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


;;;; `STOBJ$A'
(make-event
  `(progn
     (table atomic-stobj-accessors::stobj$a nil nil
            :guard (and (member key '(atomic-stobj-accessors::stobj$a-property-alist
                                      atomic-stobj-accessors::stobj$a-lookup-alist))
                        (plist-worldp val)))
     (table atomic-stobj-accessors::stobj$a 'atomic-stobj-accessors::stobj$a-property-alist '())
     (table atomic-stobj-accessors::stobj$a 'atomic-stobj-accessors::stobj$a-lookup-alist '())))

(defun atomic-stobj-accessors::stobj$a-property-alist (world)
  (declare (xargs :guard (plist-worldp world)
                  :verify-guards nil))
  (cdr (assoc-eq 'atomic-stobj-accessors::stobj$a-property-alist
                 (table-alist 'atomic-stobj-accessors::stobj$a world))))

(defmacro atomic-stobj-accessors::stobj$a-property (stobj$a)
  (declare (xargs :guard t))
  `(getprop ,stobj$a
            'atomic-stobj-accessors::stobj$a
            nil
            'current-acl2-world
            (atomic-stobj-accessors::stobj$a-property-alist (w state))))

(defmacro atomic-stobj-accessors::stobj$a-p (stobj$a)
  (declare (xargs :guard t))
  `(let ((stobj$a ,stobj$a))
     (and (symbolp stobj$a)
          (let* ((stobj$a-property (atomic-stobj-accessors::stobj$a-property stobj$a))
                 (indicator (first stobj$a-property))
                 (top (second stobj$a-property))
                 (interface (third stobj$a-property)))
            (and (true-listp stobj$a-property)
                 (= (len stobj$a-property) 3)
                 (eq indicator 'atomic-stobj-accessors::stobj$a-property)
                 (symbol-listp top)
                 (= (len top) 4)
                 (symbol-list-listp interface))))))

(defmacro atomic-stobj-accessors::stobj$a-recognizer (stobj$a)
  (declare (xargs :guard t))
  `(first (second (atomic-stobj-accessors::stobj$a-property ,stobj$a))))

(defmacro atomic-stobj-accessors::stobj$a-creator (stobj$a)
  (declare (xargs :guard t))
  `(second (second (atomic-stobj-accessors::stobj$a-property ,stobj$a))))

(defmacro atomic-stobj-accessors::stobj$a-fixer (stobj$a)
  (declare (xargs :guard t))
  `(third (second (atomic-stobj-accessors::stobj$a-property ,stobj$a))))

(defmacro atomic-stobj-accessors::stobj$a-equal (stobj$a)
  (declare (xargs :guard t))
  `(fourth (second (atomic-stobj-accessors::stobj$a-property ,stobj$a))))

(defmacro atomic-stobj-accessors::stobj$a-interface (stobj$a)
  (declare (xargs :guard t))
  `(third (atomic-stobj-accessors::stobj$a-property ,stobj$a)))

(defun atomic-stobj-accessors::stobj$a-lookup-alist (world)
  (declare (xargs :guard (plist-worldp world)
                  :verify-guards nil))
  (cdr (assoc-eq 'atomic-stobj-accessors::stobj$a-lookup-alist
                 (table-alist 'atomic-stobj-accessors::stobj$a world))))

(defmacro atomic-stobj-accessors::stobj$a-lookup (stobj$abs)
  (declare (xargs :guard t))
  `(getprop ,stobj$abs
            'atomic-stobj-accessors::stobj$a
            nil
            'current-acl2-world
            (atomic-stobj-accessors::stobj$a-lookup-alist (w state))))


;;;; `STOBJ$A-ARRAY'
(defmacro atomic-stobj-accessors::stobj$a-array-p (stobj$a)
  (declare (xargs :guard t))
  `(let ((stobj$a ,stobj$a))
     (and (atomic-stobj-accessors::stobj$a-p stobj$a)
          (let* ((stobj$a-interface (atomic-stobj-accessors::stobj$a-interface stobj$a))
                 (elements (first stobj$a-interface))
                 (params (second stobj$a-interface))
                 (defuns (third stobj$a-interface)))
            (and (symbol-listp elements)
                 (= (len elements) 4)
                 (or (null (fourth elements))
                     (getpropc (fourth elements) 'const))
                 (symbol-listp params)
                 (= (len params) 2)
                 (booleanp (first params))
                 (getpropc (second params) 'const)
                 (symbol-listp defuns)
                 (= (len defuns) 4))))))

(defmacro atomic-stobj-accessors::stobj$a-array-element-recognizer (stobj$a)
  (declare (xargs :guard t))
  `(first (first (atomic-stobj-accessors::stobj$a-interface ,stobj$a))))

(defmacro atomic-stobj-accessors::stobj$a-array-element-fixer (stobj$a)
  (declare (xargs :guard t))
  `(second (first (atomic-stobj-accessors::stobj$a-interface ,stobj$a))))

(defmacro atomic-stobj-accessors::stobj$a-array-element (stobj$a)
  (declare (xargs :guard t))
  `(third (first (atomic-stobj-accessors::stobj$a-interface ,stobj$a))))

(defmacro atomic-stobj-accessors::stobj$a-array-initial-element (stobj$a)
  (declare (xargs :guard t))
  `(fourth (first (atomic-stobj-accessors::stobj$a-interface ,stobj$a))))

(defmacro atomic-stobj-accessors::stobj$a-array-resizablep (stobj$a)
  (declare (xargs :guard t))
  `(first (second (atomic-stobj-accessors::stobj$a-interface ,stobj$a))))

(defmacro atomic-stobj-accessors::stobj$a-array-default-length (stobj$a)
  (declare (xargs :guard t))
  `(second (second (atomic-stobj-accessors::stobj$a-interface ,stobj$a))))

(defmacro atomic-stobj-accessors::stobj$a-array-length (stobj$a)
  (declare (xargs :guard t))
  `(first (third (atomic-stobj-accessors::stobj$a-interface ,stobj$a))))

(defmacro atomic-stobj-accessors::stobj$a-array-resizer (stobj$a)
  (declare (xargs :guard t))
  `(second (third (atomic-stobj-accessors::stobj$a-interface ,stobj$a))))

(defmacro atomic-stobj-accessors::stobj$a-array-accessor (stobj$a)
  (declare (xargs :guard t))
  `(third (third (atomic-stobj-accessors::stobj$a-interface ,stobj$a))))

(defmacro atomic-stobj-accessors::stobj$a-array-updater (stobj$a)
  (declare (xargs :guard t))
  `(fourth (third (atomic-stobj-accessors::stobj$a-interface ,stobj$a))))


;;;; `STOBJ$A-HASH-TABLE'
(defmacro atomic-stobj-accessors::stobj$a-hash-table-p (stobj$a)
  (declare (xargs :guard t))
  `(let ((stobj$a ,stobj$a))
     (and (atomic-stobj-accessors::stobj$a-p stobj$a)
          (let* ((stobj$a-interface (atomic-stobj-accessors::stobj$a-interface stobj$a))
                 (keys (first stobj$a-interface))
                 (vals (second stobj$a-interface))
                 (params (third stobj$a-interface))
                 (defuns (fourth stobj$a-interface)))
            (and (symbol-listp keys)
                 (= (len keys) 4)
                 (getpropc (fourth keys) 'const)
                 (symbol-listp vals)
                 (= (len vals) 4)
                 (or (null (fourth vals))
                     (getpropc (fourth vals) 'const))
                 (symbol-listp params)
                 (= (len params) 2)
                 (member (car params) '(eq eql hons-equal equal))
                 (symbol-listp defuns)
                 (= (len defuns) 10))))))

(defmacro atomic-stobj-accessors::stobj$a-hash-table-key-recognizer (stobj$a)
  (declare (xargs :guard t))
  `(first (first (atomic-stobj-accessors::stobj$a-interface ,stobj$a))))

(defmacro atomic-stobj-accessors::stobj$a-hash-table-key-fixer (stobj$a)
  (declare (xargs :guard t))
  `(second (first (atomic-stobj-accessors::stobj$a-interface ,stobj$a))))

(defmacro atomic-stobj-accessors::stobj$a-hash-table-key (stobj$a)
  (declare (xargs :guard t))
  `(third (first (atomic-stobj-accessors::stobj$a-interface ,stobj$a))))

(defmacro atomic-stobj-accessors::stobj$a-hash-table-default-key (stobj$a)
  (declare (xargs :guard t))
  `(fourth (first (atomic-stobj-accessors::stobj$a-interface ,stobj$a))))

(defmacro atomic-stobj-accessors::stobj$a-hash-table-val-recognizer (stobj$a)
  (declare (xargs :guard t))
  `(first (second (atomic-stobj-accessors::stobj$a-interface ,stobj$a))))

(defmacro atomic-stobj-accessors::stobj$a-hash-table-val-fixer (stobj$a)
  (declare (xargs :guard t))
  `(second (second (atomic-stobj-accessors::stobj$a-interface ,stobj$a))))

(defmacro atomic-stobj-accessors::stobj$a-hash-table-val (stobj$a)
  (declare (xargs :guard t))
  `(third (second (atomic-stobj-accessors::stobj$a-interface ,stobj$a))))

(defmacro atomic-stobj-accessors::stobj$a-hash-table-default-val (stobj$a)
  (declare (xargs :guard t))
  `(fourth (second (atomic-stobj-accessors::stobj$a-interface ,stobj$a))))

(defmacro atomic-stobj-accessors::stobj$a-hash-table-test (stobj$a)
  (declare (xargs :guard t))
  `(first (third (atomic-stobj-accessors::stobj$a-interface ,stobj$a))))

(defmacro atomic-stobj-accessors::stobj$a-hash-table-copyable (stobj$a)
  (declare (xargs :guard t))
  `(second (third (atomic-stobj-accessors::stobj$a-interface ,stobj$a))))

(defmacro atomic-stobj-accessors::stobj$a-hash-table-accessor (stobj$a)
  (declare (xargs :guard t))
  `(first (fourth (atomic-stobj-accessors::stobj$a-interface ,stobj$a))))

(defmacro atomic-stobj-accessors::stobj$a-hash-table-updater (stobj$a)
  (declare (xargs :guard t))
  `(second (fourth (atomic-stobj-accessors::stobj$a-interface ,stobj$a))))

(defmacro atomic-stobj-accessors::stobj$a-hash-table-boundp (stobj$a)
  (declare (xargs :guard t))
  `(third (fourth (atomic-stobj-accessors::stobj$a-interface ,stobj$a))))

(defmacro atomic-stobj-accessors::stobj$a-hash-table-getp (stobj$a)
  (declare (xargs :guard t))
  `(fourth (fourth (atomic-stobj-accessors::stobj$a-interface ,stobj$a))))

(defmacro atomic-stobj-accessors::stobj$a-hash-table-remover (stobj$a)
  (declare (xargs :guard t))
  `(fifth (fourth (atomic-stobj-accessors::stobj$a-interface ,stobj$a))))

(defmacro atomic-stobj-accessors::stobj$a-hash-table-count (stobj$a)
  (declare (xargs :guard t))
  `(sixth (fourth (atomic-stobj-accessors::stobj$a-interface ,stobj$a))))

(defmacro atomic-stobj-accessors::stobj$a-hash-table-clear (stobj$a)
  (declare (xargs :guard t))
  `(seventh (fourth (atomic-stobj-accessors::stobj$a-interface ,stobj$a))))

(defmacro atomic-stobj-accessors::stobj$a-hash-table-init (stobj$a)
  (declare (xargs :guard t))
  `(eighth (fourth (atomic-stobj-accessors::stobj$a-interface ,stobj$a))))

(defmacro atomic-stobj-accessors::stobj$a-hash-table-keys (stobj$a)
  (declare (xargs :guard t))
  `(ninth (fourth (atomic-stobj-accessors::stobj$a-interface ,stobj$a))))

(defmacro atomic-stobj-accessors::stobj$a-hash-table-keys-set (stobj$a)
  (declare (xargs :guard t))
  `(tenth (fourth (atomic-stobj-accessors::stobj$a-interface ,stobj$a))))


;;;; `STOBJ$A-FRAME'
(defmacro atomic-stobj-accessors::stobj$a-frame-p (stobj$a)
  (declare (xargs :guard t))
  `(let ((stobj$a ,stobj$a))
     (and (atomic-stobj-accessors::stobj$a-p stobj$a)
          (let* ((stobj$a-interface (atomic-stobj-accessors::stobj$a-interface stobj$a))
                 (recognizers (first stobj$a-interface))
                 (fixers (second stobj$a-interface))
                 (fields (third stobj$a-interface))
                 (initial-elements (fourth stobj$a-interface))
                 (stobjs (fifth stobj$a-interface))
                 (accessors (sixth stobj$a-interface))
                 (updaters (seventh stobj$a-interface))
                 (extra (eighth stobj$a-interface)))
            (and (symbol-listp recognizers)
                 (symbol-listp fixers)
                 (symbol-listp fields)
                 ;; TODO: Check each initial-element-name has the const prop
                 (symbol-listp initial-elements)
                 (symbol-listp stobjs)
                 (symbol-listp accessors)
                 (symbol-listp updaters)
                 (symbol-listp extra)
                 (= (len recognizers) (len fixers))
                 (= (len fixers) (len fields))
                 (= (len fields) (len initial-elements))
                 (= (len initial-elements) (len stobjs))
                 (= (len stobjs) (len accessors))
                 (= (len accessors) (len updaters))
                 (= (len extra) 1))))))

(defmacro atomic-stobj-accessors::stobj$a-frame-recognizers (stobj$a)
  (declare (xargs :guard t))
  `(first (atomic-stobj-accessors::stobj$a-interface ,stobj$a)))

(defmacro atomic-stobj-accessors::stobj$a-frame-fixers (stobj$a)
  (declare (xargs :guard t))
  `(second (atomic-stobj-accessors::stobj$a-interface ,stobj$a)))

(defmacro atomic-stobj-accessors::stobj$a-frame-fields (stobj$a)
  (declare (xargs :guard t))
  `(third (atomic-stobj-accessors::stobj$a-interface ,stobj$a)))

(defmacro atomic-stobj-accessors::stobj$a-frame-initial-elements (stobj$a)
  (declare (xargs :guard t))
  `(fourth (atomic-stobj-accessors::stobj$a-interface ,stobj$a)))

(defmacro atomic-stobj-accessors::stobj$a-frame-stobjs (stobj$a)
  (declare (xargs :guard t))
  `(fifth (atomic-stobj-accessors::stobj$a-interface ,stobj$a)))

(defmacro atomic-stobj-accessors::stobj$a-frame-accessors (stobj$a)
  (declare (xargs :guard t))
  `(sixth (atomic-stobj-accessors::stobj$a-interface ,stobj$a)))

(defmacro atomic-stobj-accessors::stobj$a-frame-updaters (stobj$a)
  (declare (xargs :guard t))
  `(seventh (atomic-stobj-accessors::stobj$a-interface ,stobj$a)))

(defmacro atomic-stobj-accessors::stobj$a-frame-view (stobj$a)
  (declare (xargs :guard t))
  `(first (eighth (atomic-stobj-accessors::stobj$a-interface ,stobj$a))))
