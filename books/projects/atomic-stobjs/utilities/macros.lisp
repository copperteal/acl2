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
(set-verify-guards-eagerness 2)

(include-book "std/util/bstar" :dir :system)


;;;; `MV-ER'
(defmacro mv-er (n severity &rest rest)
  (declare (xargs :guard (and (integerp n)
                              (< 1 n)
                              (symbolp severity)
                              (member-symbol-name (symbol-name severity)
                                                  '(hard hard? hard! hard?!)))))
  (list 'prog2$ (list* 'er severity rest)
        (cons 'mv (make-list n))))


;;;; `DEFTHM-FI'
(defmacro defthm-fi (name statement &rest kvl)
  (declare (xargs :guard t))
  (let ((theorem (cadr (assoc-keyword :theorem kvl)))
        (bindings (cadr (assoc-keyword :bindings kvl)))
        (kvl (remove-keyword :bindings
                             (remove-keyword :theorem
                                             (remove-keyword :hints kvl)))))
    `(defthm ,name
       ,statement
       ,@kvl
       :hints
       (("Goal"
         :by (:functional-instance ,theorem
                                   ,@bindings))))))


;;;; `COLLECT-CONSTRAINT-INFO'
(defun collect-constraint-info-acc (list acc wrld)
  (declare (xargs :mode :program
                  :guard (and (symbol-listp list)
                              (true-listp acc)
                              (plist-worldp wrld))
                  :measure (acl2-count list)))
  (b*
      (((when (atom list))
        (reverse (remove-duplicates acc :test 'equal)))
       ((cons sym list) list)
       ((mv flg info &) (constraint-info+ sym wrld)))
    (collect-constraint-info-acc list
                                 (cond
                                   (flg
                                    (revappend info acc))
                                   ((and (quotep info)
                                         (equal (cadr info) ''t))
                                    acc)
                                   ((consp info)
                                    (cons info acc))
                                   (t
                                    acc))
                                 wrld)))

(defun-inline collect-constraint-info (list wrld)
  (declare (xargs :mode :program
                  :guard (and (symbol-listp list)
                              (plist-worldp wrld))))
  (collect-constraint-info-acc list nil wrld))
