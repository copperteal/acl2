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


;;;; Prologue
(in-package "ATOMIC-STOBJS")
(set-verify-guards-eagerness 2)

;;; cert.pl
#||
(include-book "std/top" :dir :system)
(include-book "../lemmas/top")
||#

(include-book "../type-spec")
(include-book "../utilities/top")
(include-book "frame$c")
(include-book "frame$a")
(include-book "frame$abs")

(defthm symbol-list-listp{compound-recognizer}
  ;; TODO: move this. where?
  (implies (symbol-list-listp x)
           (true-listp x))
  :rule-classes :compound-recognizer)

(deflabel define-frame-begin)

(defconst *field-keywords*
  '(:element-type :recognizer :fixer :stobj
    :initial-element :accessor :updater))

(defconst *body-keywords*
  '(:inline :memoizable :executable
    :recognizer :creator :fixer
    :logic :exec :debug))


(defun make-doublets (x y) ; TODO: move this, where?
  (declare (xargs :guard t))
  (and (consp x)
       (consp y)
       (cons (list (car x) (car y))
             (make-doublets (cdr x) (cdr y)))))

(defun make-doublets-x1 (x1 list) ; TODO: move this, where?
  (declare (xargs :guard t))
  (and (consp list)
       (cons (list x1 (car list))
             (make-doublets-x1 x1 (cdr list)))))

(defun make-doublets-x2 (list x2) ; TODO: move this, where?
  (declare (xargs :guard t))
  (and (consp list)
       (cons (list (car list) x2)
             (make-doublets-x2 (cdr list) x2))))


(defun make-rewrite-corollaries (clauses)
  ;; TODO: move this. where?
  (declare (xargs :guard (true-listp clauses)))
  (and (consp clauses)
       (cons (list :rewrite :corollary (car clauses))
             (make-rewrite-corollaries (cdr clauses)))))


;;;; `VALID-FRAME' Predicates
(defun valid-frame-descriptor-p (descriptor)
  (declare (xargs :guard t))
  (and (consp descriptor)
       (let ((name (car descriptor))
             (kvl (cdr descriptor)))
         (and (symbolp name)
              (keyword-value-listp kvl)
              (subsetp (evens kvl) *field-keywords*
                       :test 'eq)
              (let ((element-type (assoc-keyword :element-type kvl))
                    (recognizer (cadr (assoc-keyword :recognizer kvl)))
                    (fixer (cadr (assoc-keyword :fixer kvl)))
                    (stobj (cadr (assoc-keyword :stobj kvl)))
                    (initial-element (cadr (assoc-keyword :initial-element kvl)))
                    (accessor (cadr (assoc-keyword :accessor kvl)))
                    (updater (cadr (assoc-keyword :updater kvl))))
                (and (or (not element-type)
                         (let ((element-type (cadr element-type)))
                           (if (acl2-type-spec-p element-type)
                               (typep$ initial-element element-type)
                               (symbolp element-type))))
                     (symbolp recognizer)
                     (symbolp fixer)
                     (or (and (not recognizer)
                              (not fixer))
                         (and recognizer
                              fixer))
                     (symbolp stobj)
                     (symbolp accessor)
                     (symbolp updater)))))))

(defun valid-frame-body-p (body)
  (declare (xargs :guard t))
  (and (true-listp body)
       (if (consp (car body))
           (and (valid-frame-descriptor-p (car body))
                (valid-frame-body-p (cdr body)))
           (and (keyword-value-listp body)
                (subsetp (evens body) *body-keywords*
                         :test 'eq)
                (let ((inline (cadr (assoc-keyword :inline body)))
                      (memoizable (cadr (assoc-keyword :memoizable body)))
                      (executable (cadr (assoc-keyword :executable body)))
                      (recognizer (cadr (assoc-keyword :recognizer body)))
                      (creator (cadr (assoc-keyword :creator body)))
                      (fixer (cadr (assoc-keyword :fixer body)))
                      (logic (cadr (assoc-keyword :logic body)))
                      (exec (cadr (assoc-keyword :exec body)))
                      (debug (cadr (assoc-keyword :debug body))))
                  (and (booleanp inline)
                       (booleanp memoizable)
                       (booleanp executable)
                       (symbolp recognizer)
                       (symbolp creator)
                       (symbolp fixer)
                       (symbolp logic)
                       (symbolp exec)
                       (booleanp debug)))))))

(defun valid-frame-form-p (form)
  (declare (xargs :guard t))
  (and (true-listp form)
       (eq (car form) 'define-frame)
       (symbolp (cadr form))
       (valid-frame-body-p (cddr form))))


;;;; Parse `DEFINE-FRAME' Forms
(defun split-body (body)
  (declare (xargs :guard (valid-frame-body-p body)))
  (cond
    ((atom body)
     (mv nil nil))
    ((atom (car body))
     (mv nil body))
    (t
     (mv-let (fds kvl)
             (split-body (cdr body))
       (mv (cons (car body) fds) kvl)))))

(defun parse-fds (frame fds)
  (declare (xargs :guard (and (symbolp frame)
                              (valid-frame-body-p fds)
                              (alistp fds))))
  (if (consp fds)
      (mv-let (fields element-types recognizers fixers stobjs
                      initial-elements accessors updaters)
              (parse-fds frame (cdr fds))
        (let* ((descriptor (car fds))
               (field (car descriptor))
               (kvl (cdr descriptor))
               (element-type-supplied (assoc-keyword :element-type kvl))
               (element-type (if element-type-supplied
                                 (cadr element-type-supplied)
                                 't))
               (recognizer (cadr (assoc-keyword :recognizer kvl)))
               (fixer (cadr (assoc-keyword :fixer kvl)))
               (stobj (cadr (assoc-keyword :stobj kvl)))
               (initial-element (cadr (assoc-keyword :initial-element kvl)))
               (accessor (or (cadr (assoc-keyword :accessor kvl))
                             (symbolicate frame frame '- field)))
               (updater (or (cadr (assoc-keyword :updater kvl))
                            (symbolicate frame frame '- field '-set))))
          (mv (cons field fields)
              (cons element-type element-types)
              (cons recognizer recognizers)
              (cons fixer fixers)
              (cons stobj stobjs)
              (cons initial-element initial-elements)
              (cons accessor accessors)
              (cons updater updaters))))
      (mv nil nil nil nil
          nil nil nil nil)))

(defun parse-kvl (frame kvl)
  (declare (xargs :guard (and (symbolp frame)
                              (valid-frame-body-p kvl)
                              (keyword-value-listp kvl))))
  (let* ((inline-supplied (assoc-keyword :inline kvl))
         (inline (if inline-supplied
                     (cadr inline-supplied)
                     'nil))
         (memoizable (cadr (assoc-keyword :memoizable kvl)))
         (executable (cadr (assoc-keyword :executable kvl)))
         (recognizer (or (cadr (assoc-keyword :recognizer kvl))
                         (symbolicate frame frame (make-predicate-suffix frame))))
         (creator (or (cadr (assoc-keyword :creator kvl))
                      (symbolicate frame 'create- frame)))
         (fixer (or (cadr (assoc-keyword :fixer kvl))
                    (symbolicate frame frame '-fix)))
         (logic (cadr (assoc-keyword :logic kvl)))
         (exec (cadr (assoc-keyword :exec kvl)))
         (debug (cadr (assoc-keyword :debug kvl))))
    (mv inline memoizable executable
        recognizer creator fixer
        logic exec debug)))

(defun parse-form (form)
  (declare (xargs :guard (valid-frame-form-p form)))
  (let ((frame (cadr form))
        (body (cddr form)))
    (mv-let (fds kvl)
            (split-body body)
      (mv-let (inline memoizable executable
                      recognizer creator fixer
                      logic exec debug)
              (parse-kvl frame kvl)
        (mv-let (fields element-types recognizers fixers stobjs
                        initial-elements accessors updaters)
                (parse-fds frame fds)
          (mv recognizer creator fixer
              fields element-types recognizers fixers stobjs
              initial-elements accessors updaters
              inline memoizable executable
              logic exec debug))))))


;;;; `DEFINE-FRAME'
(defun make-field-descriptors$c (fields types elements)
  (declare (xargs :guard (and (symbol-listp fields)
                              (true-listp types)
                              (true-listp elements)
                              (= (len fields) (len types))
                              (= (len types) (len elements)))))
  (and (consp fields)
       (cons (list (car fields)
                   :element-type (car types)
                   :initial-element (car elements))
             (make-field-descriptors$c (cdr fields) (cdr types) (cdr elements)))))

(defun make-field-descriptors$a (fields recognizers fixers stobjs elements)
  (declare (xargs :guard (and (symbol-listp fields)
                              (symbol-listp recognizers)
                              (symbol-listp fixers)
                              (symbol-listp stobjs)
                              (true-listp elements)
                              (= (len fields) (len recognizers))
                              (= (len recognizers) (len fixers))
                              (= (len fixers) (len stobjs))
                              (= (len stobjs) (len elements)))))
  (and (consp fields)
       (cons (list (car fields)
                   :recognizer (car recognizers)
                   :fixer (car fixers)
                   :stobj (car stobjs)
                   :initial-element (car elements))
             (make-field-descriptors$a
              (cdr fields) (cdr recognizers) (cdr fixers) (cdr stobjs) (cdr elements)))))

(defun make-field-descriptors$abs (fields accessors updaters stobjs)
  (declare (xargs :guard (and (symbol-listp fields)
                              (symbol-listp accessors)
                              (symbol-listp updaters)
                              (symbol-listp stobjs)
                              (= (len fields) (len accessors))
                              (= (len accessors) (len updaters))
                              (= (len updaters) (len stobjs)))))
  (and (consp fields)
       (cons (list (car fields)
                   :accessor (car accessors)
                   :updater (car updaters)
                   :stobj (car stobjs))
             (make-field-descriptors$abs (cdr fields) (cdr accessors) (cdr updaters) (cdr stobjs)))))

(defmacro define-frame (&whole form frame &body body)
  (declare (xargs :guard (valid-frame-form-p form))
           (ignore body))
  (mv-let (recognizer creator fixer
                      fields element-types recognizers fixers stobjs
                      initial-elements accessors updaters
                      inline memoizable executable
                      logic exec debug)
          (parse-form form)
    (let* ((frame$a (or logic
                        (symbolicate frame frame '$a)))
           (frame$c (or exec
                        (symbolicate frame frame '$c))))

      `(with-output
         ,@(and (not debug)
                '#!acl2(:off (warning! observation prove event history proof-tree)
                             :summary-off (rules)
                             :gag-mode t))

         (make-event
           (let* ((field-descriptors$c (make-field-descriptors$c
                                        ',fields ',element-types ',initial-elements))
                  (field-descriptors$a (make-field-descriptors$a
                                        ',fields ',recognizers ',fixers ',stobjs ',initial-elements))
                  (field-descriptors$abs (make-field-descriptors$abs
                                          ',fields ',accessors ',updaters ',stobjs)))

             `(progn
                (define-frame$c ,',frame$c
                  ,@field-descriptors$c
                  :inline ,',inline
                  :memoizable ,',memoizable
                  :executable ,',executable
                  :debug ,',debug)

                (define-frame$a ,',frame$a
                  ,@field-descriptors$a
                  :debug ,',debug)

                (define-frame$corr ,',frame
                  :logic ,',frame$a
                  :exec ,',frame$c
                  :debug ,',debug)

                (define-frame$abs ,',frame
                  ,@field-descriptors$abs
                  :logic ,',frame$a
                  :exec ,',frame$c
                  :recognizer ,',recognizer
                  :creator ,',creator
                  :fixer ,',fixer
                  :executable ,',executable
                  :debug ,',debug)

                (in-theory (disable ,',(symbolicate frame$c frame$c '-theorems))))))))))


;;;; `DEFINE-FRAME-THEOREMS'
(deflabel define-frame-end)

(deftheory-static define-frame-theorems
  (set-difference-theories
   (set-difference-theories
    (current-theory 'define-frame-end)
    (current-theory 'define-frame-begin))
   (function-theory 'define-frame-end)))


;;;; Epilogue
(in-theory
  (union-theories (current-theory 'define-frame-begin)
                  (theory 'define-frame-theorems)))
