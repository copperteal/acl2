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


(in-package "ATOMIC-STOBJS")
(set-verify-guards-eagerness 2)

#|
(include-book "../lemmas/vector-a")
(include-book "../lemmas/hash-table-a")
|#

(include-book "../utilities/top")
(include-book "copy")


;;;; `MAKE-VECTOR-EXPORT-EVENTS'
(defun make-vector-export-events (vector package-witness state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp vector)
                              (package-witness-p package-witness))
                  :verify-guards nil))
  (let* ()

    `(progn
       (deflabel ,export-begin)

       (encapsulate ()

         (local
           (deflabel prologue-begin))

         (local
           (deflabel prologue-end))

         (local
           (include-book "projects/atomic-stobjs/lemmas/vector-a" :dir :system))

         (local
           (table acl2::theory-invariant-table nil nil :clear))

         (local
           (in-theory
             (union-theories
              (union-theories (theory 'acl2::ground-zero)
                              (theory ',vector$a-definitions))
              (set-difference-theories (current-theory 'prologue-end)
                                       (current-theory 'prologue-begin)))))

         (local
           (in-theory
             (disable make-list-ac
                      (:e make-list-ac))))

         ;; `EXPORTP-REC'
         (defun ,exportp-rec (list)
           (declare (xargs :guard t))
           (if (atom list)
               (null list)
               ;; TODO: handle true-listp case
               (and (,(or element-export-p
                          element-recognizer)
                      (car list))
                    (,exportp-rec list))))

         (local
           (in-theory
             (disable ,exportp-rec)))

         ;; `EXPORTP'
         (defun ,exportp (export)
           (declare (xargs :guard t))
           (and (consp export)
                (equal (car export) ',vector)
                (,exportp-rec (cdr export))
                ,@(and (not resizable)
                       `((= (len (cdr export)) ,default-length-name)))))

         (defthm ,exportp-tp
           (booleanp (,exportp export))
           :rule-classes :type-prescription)

         (defthm ,exportp-cr
           (implies (,exportp export)
                    (and (consp export)
                         (true-listp export)))
           :rule-classes :compound-recognizer)

         ;; nth when exportp, satisfies element-recognizer

         ;; len when exportp (for non-resizable)

         (local
           (in-theory
             (disable ,exportp)))

         ;; `EXPORT-ACC'
         (defun ,export-acc (,index acc ,vector)
           (declare (xargs :stobjs ,vector
                           :guard (and (natp ,index)
                                       (,exportp-rec acc)
                                       (<= ,index ,(if resizable
                                                       `(,length ,vector)
                                                       default-length-name)))))
           (if (zp ,index)
               acc
               ,(if element-export
                    `(let ((,index (1- ,index)))
                       (stobj-let ((,element (,accessor ,index ,vector) ,updater))
                                  (export)
                                  (,element-export ,element)
                         (,export-acc ,index (cons export acc) ,vector)))
                    `(let* ((,index (1- ,index))
                            (,element (,accessor ,index ,vector)))
                       (,export-acc ,index (cons ,element acc) ,vector)))))

         (local
           (in-theory
             (disable ,export-acc)))

         ;; `EXPORT'
         (defun ,export (,vector)
           (declare (xargs :stobjs ,vector))
           (cons ',vector
                 (,export-acc ,(if resizable
                                   `(,length ,vector)
                                   default-length-name)
                              ()
                              ',vector)))

         (defthm ,export-tp
           (and (consp (,export ,vector))
                (true-listp (,export ,vector)))
           :rule-classes :type-prescription)

         (defthm ,exportp-of-export
           (,exportp (,export ,vector)))

         (defthm ,len-of-export
           (equal (len (,export ,vector))
                  (1+ ,(if resizable
                           `(,length$a ,vector)
                           default-length-name))))

         (defthm ,nth-of-export
           (equal (nth ,index (,export ,vector))
                  (cond
                    ((zp ,index)
                     ',vector)
                    ((<= ,index ,(if resizable
                                     `(,length$a ,vector)
                                     default-length-name))
                     ,(if element-export
                          `(,element-export (,accessor$a (1- ,index) ,vector))
                          `(,accessor$a (1- ,index) ,vector))))))

         (local
           (in-theory
             (disable ,export)))

         ;; `IMPORT-REC'
         (defun ,import-rec (list ,index ,vector)
           (declare (xargs :stobjs ,vector
                           :guard (and (,export-rec list)
                                       (natp ,index)
                                       (<= (+ (len list) ,index) ,(if resizable
                                                                      `(,length ,vector)
                                                                      default-length-name)))))
           (if (endp list)
               (,fixer ,vector)
               ,(if ,element-import
                    `(stobj-let ((,element (,accessor ,index ,vector) ,updater))
                                (,element)
                                (,element-import (car list) ,element)
                       (,import-rec (cdr list)
                                    (1+ (mbe :logic (nfix ,index)
                                             :exec ,index))
                                    ,vector))
                    `(let ((,vector (,updater ,index (car list) ,vector)))
                       (,import-rec (cdr list)
                                    (1+ (mbe :logic (nfix ,index)
                                             :exec ,index))
                                    ,vector)))))

         (local
           (in-theory
             (disable ,import-rec)))

         ;; `IMPORT'
         (defun ,import (export ,vector)
           (declare (xargs :stobjs ,vector
                           :guard (,exportp export)))
           (if (mbt (,exportp export))
               (let* ((list (cdr export))
                      ,@(and resizable
                             `((,vector (,resizer (len list) ,vector))))
                      (,vector (,import-rec list 0 ,vector)))
                 ,vector)
               (let ((,vector (,creator)))
                 ,vector)))

         (defthm ,import-tp
           ;; TODO: for fixed positive length vectors add consp
           (true-listp (,import export ,vector))
           :rule-classes :type-prescription)

         (defthm ,recognizer$a-of-import
           (,recognizer$a (,import export ,vector)))

         (defthm ,import-when-not-exportp
           (implies (not (,exportp export))
                    (equal (,import export ,vector)
                           (,creator$a))))

         (defthm ,import-ignores-vector
           (equal (,import export ,vector)
                  (,import export (,creator$a)))
           :rule-classes
           ((:rewrite :corollary
                      (implies (syntaxp (not (and (consp ,vector)
                                                  (eq (car ,vector) ',creator$a))))
                               (equal (,import export ,vector)
                                      (,import export (,creator$a)))))))

         (defthm ,length$a-of-import
           (equal (,length$a (,import export ,vector))
                  ,(if resizable
                       `(if (,exportp export)
                            (1- (len export))
                            ,default-length-name)
                       default-length-name)))

         (defthm ,accessor$a-of-import
           (equal (,accessor$a index (,import export ,vector))
                  (if (or (not (,exportp export))
                          ,(if resizable
                               `(<= (len export) (1+ (nfix ,index)))
                               `(<= ,default-length-name (nfix ,index))))
                      ,initial-element
                      ,(if element-import
                           `(,element-import (nth (1+ (nfix ,index)) export)
                                             ,initial-element)
                           `(nth (1+ (nfix ,index)) export)))))

         (local
           (in-theory
             (disable ,import)))

         ;; Composition Theorems
         (defthm ,export-of-import
           (implies (,exportp export)
                    (equal (,export (,import export ,vector))
                           export)))

         (defthm ,import-of-export
           ,(if coupledp
                `(implies (,coupledp ,%vector)
                          (equal (,import (,export ,%vector) ,vector)
                                 (,fixer$a ,%vector)))
                `(equal (,import (,export ,%vector) ,vector)
                        (,fixer$a ,%vector))))

         ;; TODO: table event
         )

       (deflabel ,export-end)

       (deftheory-static ,export-theory
         (set-different-theories (current-theory ',export-end)
                                 (current-theory ',export-begin))))))


;;;; `MAKE-HASH-TABLE-EXPORT-EVENTS'
(defun make-hash-table-export-events (hash-table package-witness state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp hash-table)
                              (package-witness-p package-witness))
                  :verify-guards nil))
  (let* ()

    `(progn
       (deflabel ,export-begin)

       (encapsulate ()

         (local
           (deflabel prologue-begin))

         (local
           (deflabel prologue-end))

         (local
           (include-book "projects/atomic-stobjs/lemmas/hash-table-a" :dir :system))

         (local
           (table acl2::theory-invariant-table nil nil :clear))

         (local
           (in-theory
             (union-theories
              (union-theories (theory 'acl2::ground-zero)
                              (theory ',hash-table$a-definitions))
              (set-difference-theories (current-theory 'prologue-end)
                                       (current-theory 'prologue-begin)))))

         ;; `EXPORTP-REC'
         (defun ,exportp-rec (omap)
           (declare (xargs :guard t))
           (if (atom omap)
               (null omap)
               (and (consp (car omap))
                    ,@(and key-recognizer
                           `((,key-recognizer (caar omap))))
                    ,@(cond
                        (val-export-p
                         `((,val-export-p (cdar omap))))
                        (val-recognizer
                         `((,val-recognizer (cdar omap)))))
                    (or (null (cdr omap))
                        (and (consp (cdr omap))
                             (consp (cadr omap))
                             (<< (caar omap) (caadr omap))
                             (exportp-rec (cdr omap)))))))

         (local
           (in-theory
             (disable ,exportp-rec)))

         ;; `EXPORTP'
         (defun ,exportp (export)
           (declare (xargs :guard t))
           (and (consp export)
                (equal (car export) ',hash-table)
                (,exportp-rec (cdr export))))

         (defthm ,exportp-tp
           (booleanp (,exportp export))
           :rule-classes :type-prescription)

         (defthm ,exportp-cr
           (implies (,exportp export)
                    (and (consp export)
                         (true-listp export)))
           :rule-classes :compound-recognizer)

         ;; TODO: mapp when export

         ;; TODO: assoc when export

         (local
           (in-theory
             (disable ,exportp)))

         ;; `EXPORT-ACC'
         (defun ,export-acc (set acc ,hash-table)
           (declare (xargs :stobjs ,hash-table
                           :guard (and (,keysp set)
                                       (,exportp-rec acc))))
           (if (mbe :logic (or (set::emptyp set)
                               (not (keysp set)))
                    :exec (endp set))
               (mbe :logic (omap::mfix acc)
                    :exec acc)
               ,(if val-export
                    `(let ((,key (set::head set)))
                       (stobj-let ((,val (,accessor ,key ,hash-table) ,updater))
                                  (export)
                                  (,val-export ,val)
                         (,export-acc (set::tail set) (omap::update ,key export acc) ,hash-table)))
                    `(let* ((,key (set::head set))
                            (,val (,accessor ,key ,hash-table)))
                       (,export-acc (set::tail set) (omap::update ,key ,val acc) ,hash-table)))))

         (local
           (in-theory
             (disable ,export-acc)))

         ;; `EXPORT'
         (defun ,export (,hash-table)
           (declare (xargs :stobjs ,hash-table))
           (cons ',hash-table
                 (,export-acc (,keys ,hash-table) () ',hash-table)))

         (defthm ,export-tp
           (and (consp (,export ,hash-table))
                (true-listp (,export ,hash-table)))
           :rule-classes :type-prescription)

         (defthm ,exportp-of-export
           (,exportp (,export ,hash-table)))

         (defthm ,keys-of-export
           (equal (omap::keys (cdr (,export ,hash-table)))
                  (,keys$a ,hash-table)))

         (defthm ,size-of-export
           (implies (,coupledp ,hash-table)
                    (equal (omap::size (cdr (,export ,hash-table)))
                           (,count$a ,hash-table))))

         (defthm ,assoc-of-export
           (implies ,(if key-recognizer
                         `(and (,key-recognizer ,key)
                               (,coupledp ,hash-table))
                         `(,coupledp ,hash-table))
                    (equal (omap::assoc ,key (cdr (,export ,hash-table)))
                           (and (,boundp$a ,key ,hash-table)
                                (cons ,key ,(if val-export
                                                `(,val-export (,accessor$a ,key ,hash-table))
                                                `(,accessor$a ,key ,hash-table)))))))

         (local
           (in-theory
             (disable ,export)))

         ;; `IMPORT-REC'
         (defun ,import-rec (omap ,index ,hash-table)
           (declare (xargs :stobjs ,hash-table
                           :guard (,exportp-rec omap)))
           (if (mbe :logic (or (omap::emptyp omap)
                               (not (exportp-rec omap)))
                    :exec (endp omap))
               (,fixer ,hash-table)
               (mv-let (,key ,val-export)
                       (omap::head omap)
                 ,(if val-import
                      `(stobj-let ((,val (,accessor ,key ,hash-table) ,updater))
                                  (,val)
                                  (,val-import ,val-export ,val)
                         (,import-rec (omap::tail omap) ,hash-table))
                      `(let ((,hash-table (,updater ,key ,val-export ,hash-table)))
                         (,import-rec (omap::tail omap) ,hash-table))))))

         (local
           (in-theory
             (disable ,import-rec)))

         ;; `IMPORT'
         (defun ,import (export ,hash-table)
           (declare (xargs :stobjs ,hash-table
                           :guard (,exportp export)))
           (if (mbt (,exportp export))
               (let* ((omap (cdr export))
                      (count (omap::size omap))
                      (,hash-table (,init count nil nil ,hash-table))
                      (,hash-table (,import-rec omap ,hash-table))
                      (,hash-table (,keys-set (omap::keys omap) ,hash-table)))
                 ,hash-table)
               (let ((,hash-table (,creator)))
                 ,hash-table)))

         (defthm ,import-tp
           (and (consp (,import export ,hash-table))
                (true-listp (,import export ,hash-table)))
           :rule-classes :type-prescription)

         (defthm ,recognizer$a-of-import
           (,recognizer$a (,import export ,hash-table)))

         (defthm ,import-when-not-exportp
           (implies (not (,exportp export))
                    (equal (,import export ,hash-table)
                           (,creator$a))))

         (defthm ,import-ignores-hash-table
           (equal (,import export ,hash-table)
                  (,import export (,creator$a)))
           :rule-classes
           ((:rewrite :corollary
                      (implies (syntaxp (not (and (consp ,hash-table)
                                                  (eq (car ,hash-table) ',creator$a))))
                               (equal (,import export ,hash-table)
                                      (,import export (,creator$a)))))))

         (defthm ,keys$a-of-import
           (equal (,keys$a (,import export ,hash-table))
                  (and (,exportp export)
                       (omap::,keys$a (cdr export)))))

         (defthm ,boundp$a-of-import
           (equal (,boundp$a ,key (,import export ,hash-table))
                  (and (omap::assoc ,(if key-fixer
                                         `(,key-fixer ,key)
                                         key)
                                    (cdr export))
                       (,exportp export))))

         (defthm ,accessor$a-of-import
           (equal (,accessor$a ,key (,import export ,hash-table))
                  (let ((pair (omap::assoc ,(if key-fixer
                                                `(,key-fixer ,key)
                                                key)
                                           (cdr export))))
                    (if (and (,exportp export)
                             pair)
                        (,val-import (cdr pair) ,default-val)
                        ,default-val))))

         (defthm ,count$a-of-import
           (equal (,count$a (,import export ,hash-table))
                  (if (,exportp export)
                      (omap::size (cdr export))
                      0)))

         (local
           (in-theory
             (disable ,import)))

         ;; Composition Theorems
         (defthm ,export-of-import
           (implies (,exportp export)
                    (equal (,export (,import export ,hash-table))
                           export)))

         (defthm ,import-of-export
           (implies (,coupledp ,%hash-table)
                    (equal (,import (,export ,%hash-table) ,hash-table)
                           (,fixer$a ,%hash-table))))

         ;; TODO: table event
         )

       (deflabel ,export-end)

       (deftheory-static ,export-theory
         (set-different-theories (current-theory ',export-end)
                                 (current-theory ',export-begin))))))


;;;; `MAKE-FRAME-EXPORT-EVENTS'
(defun make-frame-export-events (frame package-witness state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp hash-table)
                              (package-witness-p package-witness))
                  :verify-guards nil))
  (let* ()

    `(progn
       (deflabel ,export-begin)

       (encapsulate ()

         (local
           (deflabel prologue-begin))

         (local
           (deflabel prologue-end))

         (local ; TODO: ensure other frame books do this!
           (table acl2::theory-invariant-table nil nil :clear))

         (local
           (in-theory
             (union-theories
              (union-theories (theory 'acl2::ground-zero)
                              (theory ',frame$a-theorems))
              (set-difference-theories (current-theory 'prologue-end)
                                       (current-theory 'prologue-begin)))))

         ;; `EXPORTP'
         (defun ,exportp (export)
           (declare (xargs :guard t))
           (and (consp export)
                (equal (car export) ',frame)
                ,@(loop$ #|check that all fields
                        satisfy appropriate recognizers.  the format of an export is the
                        symbol naming the stobj consed onto a keyword-value list|#)))

         (defthm ,exportp-tp
           (booleanp (,exportp export))
           :rule-classes :type-prescription)

         (defthm ,exportp-cr
           (implies (,exportp export)
                    (and (consp export)
                         (true-listp export)))
           :rule-classes :compound-recognizer)

         ;; TODO: assoc-keyword when export

         (local
           (in-theory ; TODO: maybe move this later?
             (disable ,exportp)))

         ;; `EXPORT'
         (defun ,export (,frame)
           (declare (xargs :stobjs ,frame))
           (list ',frame
                 ,@(loop$ #|insert keyword value pairs in field order|#)))

         (defthm ,export-tp
           (and (consp (,export ,frame))
                (true-listp (,export ,frame)))
           :rule-classes :type-prescription)

         (defthm ,exportp-of-export
           (,exportp (,export ,frame)))

         ;; TODO: assoc-keyword of export: (equal (cadr (assoc-keyword :field
         ;; (,export ,frame))) (,accessor ,frame))

         (local
           (in-theory
             (disable ,export)))

         ;; `IMPORT'
         (defun ,import (export ,frame)
           (declare (xargs :stobj ,frame
                           :guard (,exportp export)))
           (if (mbt (,exportp export))
               ,(loop$ #|do-loop that sets every field in frame from the export|#)
               (let ((,frame (,creator)))
                 ,frame)))

         (defthm ,import-tp
           ;; TODO: if zero fields, only true-listp
           (and (consp (,import export ,frame))
                (true-listp (,import export ,frame)))
           :rule-classes :type-prescription)

         (defthm ,recognizer$a-of-import
           (,recognizer$a (,import export ,frame)))

         (defthm ,import-when-not-exportp
           (implies (not (,exportp export))
                    (equal (,import export ,frame)
                           (,creator$a))))

         (defthm ,import-ignores-frame
           (equal (,import export ,frame)
                  (,import export (,creator$a)))
           :rule-classes
           ((:rewrite :corollary
                      (implies (syntaxp (not (and (consp ,frame)
                                                  (eq (car ,frame) ',creator$a))))
                               (equal (,import export ,frame)
                                      (,import export (,creator$a)))))))

         ,@(loop$ #|accessors to import get export values via assoc-keyword|#)

         (local
           (in-theory
             (disable ,import)))

         ;; Composition Theorems
         (defthm ,export-of-import
           (implies (,exportp export)
                    (equal (,export (,import export ,frame))
                           export)))

         (defthm ,import-of-export
           ,(if coupledp
                `(implies (,coupledp ,%frame)
                          (equal (,import (,export ,%frame) ,frame)
                                 (,fixer$a ,%frame)))
                `(equal (,import (,export ,%frame) ,frame)
                        (,fixer$a ,%frame))))

         ;; TODO: table event
         )

       (deflabel ,export-end)

       (deftheory-static ,export-theory
         (set-different-theories (current-theory ',export-end)
                                 (current-theory ',export-begin))))))


;;;; `DEFINE-EXPORT'
(defmacro define-export (stobj &key (debug 'nil) (package-witness 'nil package-witness-supplied-p))
  (declare (xargs :guard (and (symbolp stobj)
                              (booleanp debug)
                              (package-witness-p package-witness))))
  `(with-output
     ,@(and (not debug)
            *constructor-output*)

     (make-event
       (let* ((stobj ',stobj)
              (world (w state))
              (package-witness-lookup (cdr (assoc stobj (table-alist 'package-witness world))))
              (package-witness (cond
                                 (',package-witness-supplied-p
                                  ',package-witness)
                                 (package-witness-lookup)
                                 (t
                                  (current-package state))))
              (stobj$a-property (cdr (assoc stobj (table-alist 'stobj$a-property world)))))
         (cond
           ((and (= (len stobj$a-property) 3)
                 (= (len (third stobj$a-property)) 3))
            (make-vector-export-events stobj package-witness state))
           ((and (= (len stobj$a-property) 3)
                 (= (len (third stobj$a-property)) 4))
            (make-hash-table-export-events stobj package-witness state))
           ((and (= (len stobj$a-property) 3)
                 (= (len (third stobj$a-property)) 8))
            (make-frame-export-events stobj package-witness state)))))))
