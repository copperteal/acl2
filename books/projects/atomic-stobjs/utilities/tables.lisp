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

; We use property accessors in logic mode `LOOP$'s.
(include-book "projects/apply/top" :dir :system)

(include-book "pkg-witness")


;;;; `STOBJ$C' Table
; ACL2 system stobj-related properties are insufficient.
(defrec stobj$c-property
; Generic property for the `STOBJ$C' table.
  (type
   name
   (recognizer creator . fixer)
   . extra)
  t)

(defun stobj$c-property-p (x)
  (declare (xargs :guard t))
  (and (weak-stobj$c-property-p x)
       (symbolp (access stobj$c-property x :type))
       (symbolp (access stobj$c-property x :name))
       (symbolp (access stobj$c-property x :recognizer))
       (symbolp (access stobj$c-property x :creator))
       (symbolp (access stobj$c-property x :fixer))))

(defrec vector$c-property
  (name
   (recognizer creator . fixer)
   (length
    resizer
    accessor
    updater)
   (contents . contents-recognizer)
   ;; TODO: rename `ELEMENT-TYPE' to `ELEMENT-SPEC' because it is a stobj name
   ;; or type-spec, but never an ACL2 type.
   (element element-type initial-element . default-length)
   (resizable . memoizable)
   (theory fi-bindings . fi-theorem)
   pkg-witness)
  nil)

(defun vector$c-property-p (x)
  (declare (xargs :guard t))
  (and (weak-vector$c-property-p x)
       (stobj$c-property-p x)
       (symbolp (access vector$c-property x :length))
       (symbolp (access vector$c-property x :resizer))
       (symbolp (access vector$c-property x :accessor))
       (symbolp (access vector$c-property x :updater))
       (symbolp (access vector$c-property x :contents))
       (symbolp (access vector$c-property x :contents-recognizer))
       (symbolp (access vector$c-property x :element))
       ;; TODO: check it's a valid type-spec or a symbol
       (access vector$c-property x :element-type)
       (symbolp (access vector$c-property x :initial-element))
       (symbolp (access vector$c-property x :default-length))
       (booleanp (access vector$c-property x :resizable))
       (booleanp (access vector$c-property x :memoizable))
       (symbolp (access vector$c-property x :theory))
       (symbol-doublet-listp (access vector$c-property x :fi-bindings))
       (symbolp (access vector$c-property x :fi-theorem))
       (pkg-witness-p (access vector$c-property x :pkg-witness))))

(defrec hash-table$c-property
  (name
   (recognizer creator . fixer)
   (accessor
    updater
    boundp
    getp
    remover
    count
    clear
    init)
   ;; TODO: drop this pair, move keys to previous list
   (keys . keys-set)
   (contents . contents-recognizer)
   ;; TODO: drop copyable
   (value element-type default-value . copyable)
   (test . memoizable)
   (theory fi-bindings . fi-theorem)
   pkg-witness)
  nil)

(defun hash-table$c-property-p (x)
  (declare (xargs :guard t))
  (and (weak-hash-table$c-property-p x)
       (stobj$c-property-p x)
       (symbolp (access hash-table$c-property x :accessor))
       (symbolp (access hash-table$c-property x :updater))
       (symbolp (access hash-table$c-property x :boundp))
       (symbolp (access hash-table$c-property x :getp))
       (symbolp (access hash-table$c-property x :remover))
       (symbolp (access hash-table$c-property x :count))
       (symbolp (access hash-table$c-property x :clear))
       (symbolp (access hash-table$c-property x :init))
       (symbolp (access hash-table$c-property x :keys))
       (symbolp (access hash-table$c-property x :keys-set))
       (symbolp (access hash-table$c-property x :contents))
       (symbolp (access hash-table$c-property x :contents-recognizer))
       (symbolp (access hash-table$c-property x :value))
       ;; TODO: check it's a valid type-spec or a symbol
       (access hash-table$c-property x :element-type)
       (symbolp (access hash-table$c-property x :default-value))
       ;; TODO: drop copyable
       (booleanp (access hash-table$c-property x :copyable))
       (member (access hash-table$c-property x :test)
               ;; TODO: replace with a defined constant
               '(eq eql equal hons-equal))
       (booleanp (access hash-table$c-property x :memoizable))
       (symbolp (access hash-table$c-property x :theory))
       (symbol-doublet-listp (access hash-table$c-property x :fi-bindings))
       (symbolp (access hash-table$c-property x :fi-theorem))
       (pkg-witness-p (access hash-table$c-property x :pkg-witness))))

(defrec frame$c-property
  (name
   (recognizer creator . fixer)
   (recognizers
    accessors
    updaters)
   (fields element-types initial-elements)
   memoizable
   ;; TODO: drop bindings?
   (theory fi-bindings . fi-theorem)
   pkg-witness)
  nil)

(defun frame$c-property-p (x)
  (declare (xargs :guard t))
  (and (weak-frame$c-property-p x)
       (stobj$c-property-p x)
       (symbol-listp (access frame$c-property x :recognizers))
       (symbol-listp (access frame$c-property x :accessors))
       (symbol-listp (access frame$c-property x :updaters))
       (symbol-listp (access frame$c-property x :fields))
       (true-listp (access frame$c-property x :element-types))
       (symbol-listp (access frame$c-property x :initial-elements))
       (booleanp (access frame$c-property x :memoizable))
       (symbolp (access frame$c-property x :theory))
       (symbol-doublet-listp (access frame$c-property x :fi-bindings))
       (symbolp (access frame$c-property x :fi-theorem))
       (pkg-witness-p (access frame$c-property x :pkg-witness))
       (let ((n (len (access frame$c-property x :fields))))
         (and (int= n (len (access frame$c-property x :recognizers)))
              (int= n (len (access frame$c-property x :accessors)))
              (int= n (len (access frame$c-property x :updaters)))
              (int= n (len (access frame$c-property x :element-types)))
              (int= n (len (access frame$c-property x :initial-elements)))))))

(local
  (defthm stobj$c-property-generalizes
    (implies (or (weak-vector$c-property-p property)
                 (weak-hash-table$c-property-p property)
                 (weak-frame$c-property-p property))
             (weak-stobj$c-property-p property))))

(table stobj$c nil nil :guard (and (symbolp acl2::key)
                                   (or (vector$c-property-p acl2::val)
                                       (hash-table$c-property-p acl2::val)
                                       (frame$c-property-p acl2::val))))

(table stobj$c nil nil :clear)

(defun stobj$c-property (name wrld)
  (declare (xargs :guard (and (symbolp name)
                              (plist-worldp wrld))))
  ;; TODO: How do I prove that table-alist always returns an alist?
  (cdr (assoc name (let ((alist (table-alist 'stobj$c wrld)))
                     (and (alistp alist)
                          alist)))))

(defwarrant stobj$c-property)


;;;; `STOBJ$A' Table
(defrec stobj$a-property
  (type
   name
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
     initial-element
     element-fixer
     element-equiv)
    (resizable . default-length)
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
       (symbolp (access vector$a-property x :initial-element))
       (symbolp (access vector$a-property x :element-fixer))
       (symbolp (access vector$a-property x :element-equiv))
       (booleanp (access vector$a-property x :resizable))
       (symbolp (access vector$a-property x :default-length))
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
     default-key
     key-fixer
     key-equiv)
    (val
     val-recognizer
     default-val
     val-fixer
     val-equiv)
    ;; TODO: drop copyable
    (test . copyable)
    (accessor
     updater
     boundp
     getp
     remover
     count
     clear
     init)
    ;; TODO: drop `KEYS' field
    keys))
  nil)

(defun hash-table$a-property-p (x)
  (declare (xargs :guard t))
  (and (weak-hash-table$a-property-p x)
       (stobj$a-property-p x)
       (symbolp (access hash-table$a-property x :key))
       (symbolp (access hash-table$a-property x :key-recognizer))
       (symbolp (access hash-table$a-property x :default-key))
       (symbolp (access hash-table$a-property x :key-fixer))
       (symbolp (access hash-table$a-property x :key-equiv))
       (symbolp (access hash-table$a-property x :val))
       (symbolp (access hash-table$a-property x :val-recognizer))
       (symbolp (access hash-table$a-property x :default-val))
       (symbolp (access hash-table$a-property x :val-fixer))
       (symbolp (access hash-table$a-property x :val-equiv))
       (member (access hash-table$a-property x :test)
               ;; TODO: replace with a defined constant
               '(eq eql equal hons-equal))
       ;; TODO: drop copyable
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
    initial-elements
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
       (symbol-listp (access frame$a-property x :initial-elements))
       (symbol-listp (access frame$a-property x :fixers))
       (symbol-listp (access frame$a-property x :equivs))
       (symbol-listp (access frame$a-property x :stobjs))
       (symbol-listp (access frame$a-property x :accessors))
       (symbol-listp (access frame$a-property x :updaters))
       (symbolp (access frame$a-property x :view))
       (let ((n (len (access frame$a-property x :fields))))
         (and (int= n (len (access frame$a-property x :recognizers)))
              (int= n (len (access frame$a-property x :initial-elements)))
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
