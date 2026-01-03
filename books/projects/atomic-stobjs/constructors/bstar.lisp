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

(include-book "std/util/bstar" :dir :system)

(include-book "../utilities/symbolicate")


;;;; `%GET-PREFIX'
(defun %get-prefix-acc (char-list %prefix)
  (declare (xargs :mode :program
                  :guard (and (character-listp char-list)
                              (character-listp %prefix))))
  (if (and (consp char-list)
           (eql (car char-list) #\%))
      (%get-prefix-acc (cdr char-list) (cons #\% %prefix))
      %prefix))

(defun %get-prefix (symbol)
  (declare (xargs :mode :program
                  :guard (symbolp symbol)))
  (%get-prefix-acc (coerce (symbol-name symbol) 'list) ()))


;;;; `MAKE-VECTOR-B*-EVENTS'
(defun make-vector-b*-events (vector package-witness state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp vector)
                              (package-witness-p package-witness))
                  :verify-guards nil))

  (let* ((binder-pair (symbolicate package-witness "*" vector "-B*-PAIR*"))
         (binder-parser (symbolicate package-witness vector "-B*-PARSER"))

         (stobj-property (getpropc vector 'acl2::stobj))
         (stobj$a-property (cdr (assoc vector (table-alist 'stobj$a-property (w state)))))
         (element (first (first (third stobj$a-property))))
         (element-stobj-property (getpropc element 'acl2::stobj))
         (accessor (if element-stobj-property
                       (first (third stobj-property))
                       (fourth (third stobj-property))))
         (updater (if element-stobj-property
                      (second (third stobj-property))
                      (fifth (third stobj-property)))))

    `(progn

       (defconst ,binder-pair ',(cons accessor (and element-stobj-property
                                                    updater)))

       (defun ,binder-parser (vector kvl %prefix bindings)
         (declare (xargs :mode :program
                         :guard (and (symbolp vector)
                                     (evenp (len kvl))
                                     (eqlable-listp (evens kvl))
                                     (no-duplicatesp (evens kvl) :test 'eql)
                                     (symbol-listp (odds kvl))
                                     (no-duplicatesp (odds kvl) :test 'eq)
                                     (character-listp %prefix)
                                     (alistp bindings))))
         (if (consp kvl)
             (let* ((index (first kvl))
                    (accessor (car ,binder-pair))
                    (updater (cdr ,binder-pair))
                    (accessor (symbolicate ',package-witness
                                           (coerce (append %prefix
                                                           (coerce (symbol-name accessor)
                                                                   'list))
                                                   'string)))
                    (updater (and updater
                                  (symbolicate ',package-witness
                                               (coerce (append %prefix
                                                               (coerce (symbol-name updater)
                                                                       'list))
                                                       'string)))))
               (,binder-parser vector
                               (cddr kvl)
                               (cons #\% %prefix)
                               (cons `(,(second kvl) (,accessor ,index ,vector) ,@(and updater
                                                                                       (list updater)))
                                     bindings)))
             (reverse bindings)))

       (def-b*-binder ,vector
         :decls
         ((declare (xargs :guard (and (oddp (len args))
                                      ;; This is a weak guard.  We need every
                                      ;; index to be a non-negative integer
                                      ;; literal or a symbol.
                                      (eqlable-listp (odds args))
                                      (no-duplicatesp (odds args) :test 'eql)
                                      (symbol-listp (evens args))
                                      (no-duplicatesp (evens args) :test 'eq)
                                      (consp (car forms))
                                      (symbol-listp (car forms))))))
         :body
         (b* ((vector (car args))
              (vector (if (equal (symbol-name vector) "-")
                          ',vector
                          vector))
              (%prefix (%get-prefix vector))
              (kvl (cdr args))
              (bindings (,binder-parser vector kvl %prefix ()))
              (values (car forms))
              (forms (cdr forms)))
           (cond
             (',element-stobj-property
              `(stobj-let ,bindings
                          ,values
                          ,@forms
                 ,rest-expr))
             ((consp (cdr values))
              `(mv-let ,values
                       (let ,bindings
                         ,@forms)
                 ,rest-expr))
             (t
              `(let ((,(car values) (let ,bindings
                                      ,@forms)))
                 ,rest-expr))))))))



;;;; `MAKE-HASH-TABLE-B*-EVENTS'
(defun make-hash-table-b*-events (hash-table package-witness state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp hash-table)
                              (package-witness-p package-witness))
                  :verify-guards nil))

  (let* ((binder-pair (symbolicate package-witness "*" hash-table "-B*-PAIR*"))
         (binder-parser (symbolicate package-witness hash-table "-B*-PARSER"))

         (stobj-property (getpropc hash-table 'acl2::stobj))
         (stobj$a-property (cdr (assoc hash-table (table-alist 'stobj$a-property (w state)))))
         (element (first (second (third stobj$a-property))))
         (element-stobj-property (getpropc element 'acl2::stobj))
         (accessor (if element-stobj-property
                       (first (third stobj-property))
                       (second (third stobj-property))))
         (updater (if element-stobj-property
                      (second (third stobj-property))
                      (third (third stobj-property)))))

    `(progn

       (defconst ,binder-pair ',(cons accessor (and element-stobj-property
                                                    updater)))

       (defun ,binder-parser (hash-table kvl %prefix bindings)
         (declare (xargs :mode :program
                         :guard (and (symbolp hash-table)
                                     (evenp (len kvl))
                                     (eqlable-listp (evens kvl))
                                     (no-duplicatesp (evens kvl) :test 'eql)
                                     (symbol-listp (odds kvl))
                                     (no-duplicatesp (odds kvl) :test 'eq)
                                     (character-listp %prefix)
                                     (alistp bindings))))
         (if (consp kvl)
             (let* ((index (first kvl))
                    (accessor (car ,binder-pair))
                    (updater (cdr ,binder-pair))
                    (accessor (symbolicate ',package-witness
                                           (coerce (append %prefix
                                                           (coerce (symbol-name accessor)
                                                                   'list))
                                                   'string)))
                    (updater (and updater
                                  (symbolicate ',package-witness
                                               (coerce (append %prefix
                                                               (coerce (symbol-name updater)
                                                                       'list))
                                                       'string)))))
               (,binder-parser hash-table
                               (cddr kvl)
                               (cons #\% %prefix)
                               (cons `(,(second kvl) (,accessor ,index ,hash-table) ,@(and updater
                                                                                           (list updater)))
                                     bindings)))
             (reverse bindings)))

       (def-b*-binder ,hash-table
         :decls
         ((declare (xargs :guard (and (oddp (len args))
                                      ;; This is a weak guard.  We need every
                                      ;; index to be a non-negative integer
                                      ;; literal or a symbol.
                                      (eqlable-listp (odds args))
                                      (no-duplicatesp (odds args) :test 'eql)
                                      (symbol-listp (evens args))
                                      (no-duplicatesp (evens args) :test 'eq)
                                      (consp (car forms))
                                      (symbol-listp (car forms))))))
         :body
         (b* ((hash-table (car args))
              (hash-table (if (equal (symbol-name hash-table) "-")
                              ',hash-table
                              hash-table))
              (%prefix (%get-prefix hash-table))
              (kvl (cdr args))
              (bindings (,binder-parser hash-table kvl %prefix ()))
              (values (car forms))
              (forms (cdr forms)))
           (cond
             (',element-stobj-property
              `(stobj-let ,bindings
                          ,values
                          ,@forms
                 ,rest-expr))
             ((consp (cdr values))
              `(mv-let ,values
                       (let ,bindings
                         ,@forms)
                 ,rest-expr))
             (t
              `(let ((,(car values) (let ,bindings
                                      ,@forms)))
                 ,rest-expr))))))))



;;;; `MAKE-FRAME-B*-EVENTS'
(defun make-frame-b*-events (frame package-witness state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp frame)
                              (package-witness-p package-witness))
                  :verify-guards nil))

  (let* ((binder-alist (symbolicate package-witness "*" frame "-B*-ALIST*"))
         (binder-parser (symbolicate package-witness frame "-B*-PARSER"))

         (world (w state))
         (stobj$a-property (cdr (assoc frame (table-alist 'stobj$a-property world))))
         (fields (first (third stobj$a-property)))
         (stobjs (sixth (third stobj$a-property)))

         (stobj-property (getpropc frame 'acl2::stobj))
         (stobj-count (len (remove nil stobjs)))
         (stobj-accessors-and-updaters (third stobj-property))
         (non-stobj-accessors-and-updaters (nthcdr (1+ (* 2 stobj-count)) stobj-accessors-and-updaters))
         (accessors (loop$ :with stobj-accessors-and-updaters := stobj-accessors-and-updaters
                          :with non-stobj-accessors-and-updaters := non-stobj-accessors-and-updaters
                          :with stobjs := stobjs
                          :with accessors := ()
                          :do
                          (progn
                            (cond
                              ((endp stobjs)
                               (return (reverse accessors)))
                              ((car stobjs)
                               (progn
                                 (setq accessors (cons (car stobj-accessors-and-updaters) accessors))
                                 (setq stobj-accessors-and-updaters (cddr stobj-accessors-and-updaters))))
                              (t
                               (progn
                                 (setq accessors (cons (car non-stobj-accessors-and-updaters) accessors))
                                 (setq non-stobj-accessors-and-updaters (cdr non-stobj-accessors-and-updaters)))))
                            (setq stobjs (cdr stobjs)))))
         (updaters (loop$ :with stobj-accessors-and-updaters := (cdr stobj-accessors-and-updaters)
                         :with non-stobj-accessors-and-updaters := (nthcdr (- (len fields) stobj-count)
                                                                           non-stobj-accessors-and-updaters)
                         :with stobjs := stobjs
                         :with updaters := ()
                         :do
                         (progn
                           (cond
                             ((endp stobjs)
                              (return (reverse updaters)))
                             ((car stobjs)
                              (progn
                                (setq updaters (cons (car stobj-accessors-and-updaters) updaters))
                                (setq stobj-accessors-and-updaters (cddr stobj-accessors-and-updaters))))
                             (t
                              (progn
                                (setq updaters (cons (car non-stobj-accessors-and-updaters) updaters))
                                (setq non-stobj-accessors-and-updaters (cdr non-stobj-accessors-and-updaters)))))
                           (setq stobjs (cdr stobjs))))))

    `(progn

       (defconst ,binder-alist
         ',(loop$ :for field :in fields
                 :as accessor :in accessors
                 :as updater :in updaters
                 :as stobj :in stobjs
                 :collect (list* (intern (symbol-name field) "KEYWORD") accessor (and stobj
                                                                                      updater))))

       (defun ,binder-parser (frame kvl stobj-bindings scalar-bindings)
         (declare (xargs :mode :program
                         :guard (and (symbolp frame)
                                     (keyword-value-listp kvl)
                                     (subsetp (evens kvl) (strip-cars ,binder-alist) :test 'eq)
                                     (no-duplicatesp (evens kvl) :test 'eq)
                                     (symbol-listp (odds kvl))
                                     (no-duplicatesp (odds kvl) :test 'eq)
                                     (alistp stobj-bindings)
                                     (alistp scalar-bindings))))
         (if (consp kvl)
             (let* ((list (cdr (assoc (first kvl) ,binder-alist)))
                    (accessor (car list))
                    (updater (cdr list)))
               (if updater
                   (,binder-parser frame
                                   (cddr kvl)
                                   (cons `(,(second kvl) (,accessor ,frame) ,updater)
                                         stobj-bindings)
                                   scalar-bindings)
                   (,binder-parser frame
                                   (cddr kvl)
                                   stobj-bindings
                                   (cons `(,(second kvl) (,accessor ,frame))
                                         scalar-bindings))))
             (mv (reverse stobj-bindings)
                 (reverse scalar-bindings))))

       (def-b*-binder ,frame
         :decls
         ((declare (xargs :guard (and (keyword-value-listp (cdr args))
                                      (subsetp (odds args) (strip-cars ,binder-alist) :test 'eq)
                                      (no-duplicatesp (odds args) :test 'eq)
                                      (symbol-listp (evens args))
                                      (no-duplicatesp (evens args) :test 'eq)
                                      (consp (car forms))
                                      (symbol-listp (car forms))))))
         :body
         (b* ((frame (car args))
              (frame (if (equal (symbol-name frame) "-")
                         ',frame
                         frame))
              (kvl (cdr args))
              ((mv stobj-bindings scalar-bindings)
               (,binder-parser frame kvl () ()))
              (values (car forms))
              (forms (cdr forms)))
           (cond
             (stobj-bindings
              `(let ,scalar-bindings
                 (stobj-let ,stobj-bindings
                            ,values
                            ,@forms
                   ,rest-expr)))
             ((consp (cdr values))
              `(mv-let ,values
                       (let ,scalar-bindings
                         ,@forms)
                 ,rest-expr))
             (t
              `(let ((,(car values) (let ,scalar-bindings
                                      ,@forms)))
                 ,rest-expr))))))))


;;;; `DEFINE-B*'
(defmacro define-b* (stobj &key
                             (package-witness 'nil package-witness-supplied-p)
                             (debug 'nil))
  (declare (xargs :guard (and (symbolp stobj)
                              (package-witness-p package-witness)
                              (booleanp debug))))
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
            (make-vector-b*-events stobj package-witness state))
           ((and (= (len stobj$a-property) 3)
                 (= (len (third stobj$a-property)) 5))
            (make-hash-table-b*-events stobj package-witness state))
           ((and (= (len stobj$a-property) 3)
                 (= (len (third stobj$a-property)) 9))
            (make-frame-b*-events stobj package-witness state)))))))
