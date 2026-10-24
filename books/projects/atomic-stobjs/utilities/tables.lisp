;;; Copyright 2026 J. David Taylor
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


(in-package "ATOMIC-STOBJS")
(set-verify-guards-eagerness 2)

(include-book "projects/apply/top" :dir :system)


;;;; Records
(defrec stobj$a-property
  (type name
   ((recognizer . creator)
    (fixer . equiv))
   . extra)
  t)

(defun stobj$a-property-p (x)
  (declare (xargs :guard t))
  (and (weak-stobj$a-property-p x)
       (symbolp (access stobj$a-property x :type))
       (symbolp (access stobj$a-property x :name))
       (symbolp (access stobj$a-property x :recognizer))
       (symbolp (access stobj$a-property x :creator))
       (symbolp (access stobj$a-property x :fixer))
       (symbolp (access stobj$a-property x :equiv))))

(defrec vector$a-property
  (name
   ((recognizer . creator)
    (fixer . equiv))
   ((element
     element-recognizer
     initial-element-name
     element-fixer
     element-equiv)
    (resizable
     default-length-name)
    (length
     resizer
     accessor
     updater)))
  nil)

(defun vector$a-property-p (x)
  (declare (xargs :guard t))
  (and (weak-vector$a-property-p x)
       (stobj$a-property-p x)
       (symbolp (access vector$a-property x :element))
       (symbolp (access vector$a-property x :element-recognizer))
       (symbolp (access vector$a-property x :initial-element-name))
       (symbolp (access vector$a-property x :element-fixer))
       (symbolp (access vector$a-property x :element-equiv))
       (booleanp (access vector$a-property x :resizable))
       (symbolp (access vector$a-property x :default-length-name))
       (symbolp (access vector$a-property x :length))
       (symbolp (access vector$a-property x :resizer))
       (symbolp (access vector$a-property x :accessor))
       (symbolp (access vector$a-property x :updater))))

(defrec hash-table$a-property
  (name
   ((recognizer . creator)
    (fixer . equiv))
   ((key
     key-recognizer
     default-key-name
     key-fixer
     key-equiv)
    (val
     val-recognizer
     default-val-name
     val-fixer
     val-equiv)
    (test
     copyable)
    (accessor
     updater
     boundp
     getp
     remover
     count
     clear
     init)
    keys))
  nil)

(defun hash-table$a-property-p (x)
  (declare (xargs :guard t))
  (and (weak-hash-table$a-property-p x)
       (stobj$a-property-p x)
       (symbolp (access hash-table$a-property x :key))
       (symbolp (access hash-table$a-property x :key-recognizer))
       (symbolp (access hash-table$a-property x :default-key-name))
       (symbolp (access hash-table$a-property x :key-fixer))
       (symbolp (access hash-table$a-property x :key-equiv))
       (symbolp (access hash-table$a-property x :val))
       (symbolp (access hash-table$a-property x :val-recognizer))
       (symbolp (access hash-table$a-property x :default-val-name))
       (symbolp (access hash-table$a-property x :val-fixer))
       (symbolp (access hash-table$a-property x :val-equiv))
       (member (access hash-table$a-property x :test)
               '(eq eql equal hons-equal))
       (booleanp (access hash-table$a-property x :copyable))
       (symbolp (access hash-table$a-property x :accessor))
       (symbolp (access hash-table$a-property x :updater))
       (symbolp (access hash-table$a-property x :boundp))
       (symbolp (access hash-table$a-property x :getp))
       (symbolp (access hash-table$a-property x :remover))
       (symbolp (access hash-table$a-property x :count))
       (symbolp (access hash-table$a-property x :clear))
       (symbolp (access hash-table$a-property x :init))
       (symbol-listp (access hash-table$a-property x :keys))
       (int= (len (access hash-table$a-property x :keys))
             (if (access hash-table$a-property x :copyable)
                 5
                 0))))

(defrec frame$a-property
  (name
   ((recognizer . creator)
    (fixer . equiv))
   (fields
    recognizers
    initial-element-names
    fixers
    equivs
    stobjs
    accessors
    updaters
    view))
  nil)

(defun frame$a-property-p (x)
  (declare (xargs :guard t))
  (and (weak-frame$a-property-p x)
       (stobj$a-property-p x)
       (symbol-listp (access frame$a-property x :fields))
       (symbol-listp (access frame$a-property x :recognizers))
       (symbol-listp (access frame$a-property x :initial-element-names))
       (symbol-listp (access frame$a-property x :fixers))
       (symbol-listp (access frame$a-property x :equivs))
       (symbol-listp (access frame$a-property x :stobjs))
       (symbol-listp (access frame$a-property x :accessors))
       (symbol-listp (access frame$a-property x :updaters))
       (symbolp (access frame$a-property x :view))
       (let ((n (len (access frame$a-property x :fields))))
         (and (int= n (len (access frame$a-property x :recognizers)))
              (int= n (len (access frame$a-property x :initial-element-names)))
              (int= n (len (access frame$a-property x :fixers)))
              (int= n (len (access frame$a-property x :equivs)))
              (int= n (len (access frame$a-property x :stobjs)))
              (int= n (len (access frame$a-property x :accessors)))
              (int= n (len (access frame$a-property x :updaters)))))))

(local
  (defthm stobj$a-property-generalizes
    (implies (or (weak-vector$a-property-p property)
                 (weak-hash-table$a-property-p property)
                 (weak-frame$a-property-p property))
             (weak-stobj$a-property-p property))))

(table stobj$a nil nil :guard (and (symbolp acl2::key)
                                   (or (vector$a-property-p acl2::val)
                                       (hash-table$a-property-p acl2::val)
                                       (frame$a-property-p acl2::val))))

(table stobj$a nil nil :clear)

(defun stobj$a-property (name wrld)
  (declare (xargs :guard (and (symbolp name)
                              (plist-worldp wrld))))
  ;; TODO: How do I prove that table-alist always returns an alist?
  (cdr (assoc name (let ((alist (table-alist 'stobj$a wrld)))
                     (and (alistp alist)
                          alist)))))

(defwarrant stobj$a-property)
