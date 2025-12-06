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

#|
(include-book "std/lists/top" :dir :system)
|#

(include-book "../type-spec")
(include-book "../utilities/top")
(include-book "frame-c")
(include-book "frame-a")
(include-book "frame-abs")


;;;; Constants
(defconst *field-keywords*
  '(:element-type :recognizer :fixer :equiv
    :initial-element :accessor :updater))

(defconst *body-keywords*
  '(:inline :memoizable :executable
    :recognizer :creator :fixer
    :logic :exec :package-witness :debug))


;;;; `DEFINE-FRAME' Predicates
(defun frame-descriptor-p (descriptor)
  (declare (xargs :guard t))
  (and (consp descriptor)
       (let ((name (car descriptor))
             (kvl (cdr descriptor)))
         (and (symbolp name)
              (keyword-value-listp kvl)
              (subsetp (evens kvl) *field-keywords* :test 'eq)
              (let ((element-type (assoc-keyword :element-type kvl))
                    (recognizer (cadr (assoc-keyword :recognizer kvl)))
                    (fixer (cadr (assoc-keyword :fixer kvl)))
                    (equiv (cadr (assoc-keyword :equiv kvl)))
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
                     (symbolp equiv)
                     (or (and (not recognizer)
                              (not fixer)
                              (not equiv))
                         (and recognizer
                              fixer
                              equiv))
                     (symbolp accessor)
                     (symbolp updater)))))))

(defun frame-descriptor-list-p (fds)
  (declare (xargs :guard t))
  (if (atom fds)
      (null fds)
      (and (frame-descriptor-p (car fds))
           (frame-descriptor-list-p (cdr fds)))))

(defun frame-body-p (body)
  (declare (xargs :guard t))
  (and (true-listp body)
       (if (consp (car body))
           (and (frame-descriptor-p (car body))
                (frame-body-p (cdr body)))
           (and (keyword-value-listp body)
                (subsetp (evens body) *body-keywords* :test 'eq)
                (let ((inline (cadr (assoc-keyword :inline body)))
                      (memoizable (cadr (assoc-keyword :memoizable body)))
                      (executable (cadr (assoc-keyword :executable body)))
                      (recognizer (cadr (assoc-keyword :recognizer body)))
                      (creator (cadr (assoc-keyword :creator body)))
                      (fixer (cadr (assoc-keyword :fixer body)))
                      (logic (cadr (assoc-keyword :logic body)))
                      (exec (cadr (assoc-keyword :exec body)))
                      (package-witness (cadr (assoc-keyword :package-witness body)))
                      (debug (cadr (assoc-keyword :debug body))))
                  (and (booleanp inline)
                       (booleanp memoizable)
                       (booleanp executable)
                       (symbolp recognizer)
                       (symbolp creator)
                       (symbolp fixer)
                       (symbolp logic)
                       (symbolp exec)
                       (package-witness-p package-witness)
                       (booleanp debug)))))))

(defthm frame-body-p-when-frame-descriptor-list-p
  (implies (frame-descriptor-list-p fds)
           (frame-body-p fds))
  :hints
  (("Goal"
    :induct (len fds))))

(defun frame-form-p (form)
  (declare (xargs :guard t))
  (and (true-listp form)
       (eq (car form) 'define-frame)
       (symbolp (cadr form))
       (frame-body-p (cddr form))))


;;;; `DEFINE-FRAME' Parser
(with-books (("std/lists/rev" :dir :system))
  (defun split-body (fds body)
    (declare (xargs :guard (and (frame-descriptor-list-p fds)
                                (frame-body-p body))))
    (if (or (endp body)
            (atom (car body)))
        (mv (reverse fds) body)
        (split-body (cons (car body) fds) (cdr body))))

  (local
    (defthm frame-descriptor-list-p-of-rev
      (implies (frame-descriptor-list-p fds)
               (frame-descriptor-list-p (acl2::rev fds)))
      :hints
      (("Goal"
        :in-theory (disable frame-descriptor-p)))))

  (defthm split-body-values
    (implies (and (frame-descriptor-list-p fds)
                  (frame-body-p body))
             (mv-let (fds kvl)
                     (split-body fds body)
               (and (frame-descriptor-list-p fds)
                    (frame-body-p kvl)
                    (keyword-value-listp kvl))))))

(defun parse-fds (fds fields element-types element-type-supplies
                  recognizers fixers equivs
                  initial-elements initial-element-supplies
                  accessors updaters)
  (declare (xargs :guard (and (frame-descriptor-list-p fds)
                              (symbol-listp fields)
                              (true-listp element-types)
                              (boolean-listp element-type-supplies)
                              (symbol-listp recognizers)
                              (symbol-listp fixers)
                              (symbol-listp equivs)
                              (true-listp initial-elements)
                              (boolean-listp initial-element-supplies)
                              (symbol-listp accessors)
                              (symbol-listp updaters))))
  (if (endp fds)
      (mv (reverse fields)
          (reverse element-types)
          (reverse element-type-supplies)
          (reverse recognizers)
          (reverse fixers)
          (reverse equivs)
          (reverse initial-elements)
          (reverse initial-element-supplies)
          (reverse accessors)
          (reverse updaters))
      (let* ((descriptor (car fds))
             (field (car descriptor))
             (kvl (cdr descriptor))
             (element-type (assoc-keyword :element-type kvl))
             (element-type-supplied-p (and element-type
                                           t))
             (element-type (if element-type
                               (cadr element-type)
                               't))
             (recognizer (cadr (assoc-keyword :recognizer kvl)))
             (fixer (cadr (assoc-keyword :fixer kvl)))
             (equiv (cadr (assoc-keyword :equiv kvl)))
             (initial-element (assoc-keyword :initial-element kvl))
             (initial-element-supplied-p (and initial-element
                                              t))
             (initial-element (cadr initial-element))
             (accessor (cadr (assoc-keyword :accessor kvl)))
             (updater (cadr (assoc-keyword :updater kvl))))
        (parse-fds (cdr fds)
                   (cons field fields)
                   (cons element-type element-types)
                   (cons element-type-supplied-p element-type-supplies)
                   (cons recognizer recognizers)
                   (cons fixer fixers)
                   (cons equiv equivs)
                   (cons initial-element initial-elements)
                   (cons initial-element-supplied-p initial-element-supplies)
                   (cons accessor accessors)
                   (cons updater updaters)))))

(defun parse-kvl (kvl)
  (declare (xargs :guard (and (frame-body-p kvl)
                              (keyword-value-listp kvl))))
  (let* ((inline (cadr (assoc-keyword :inline kvl)))
         (memoizable (cadr (assoc-keyword :memoizable kvl)))
         (executable (cadr (assoc-keyword :executable kvl)))
         (recognizer (cadr (assoc-keyword :recognizer kvl)))
         (creator (cadr (assoc-keyword :creator kvl)))
         (fixer (cadr (assoc-keyword :fixer kvl)))
         (logic (cadr (assoc-keyword :logic kvl)))
         (exec (cadr (assoc-keyword :exec kvl)))
         (package-witness-supplied-p (assoc-keyword :package-witness kvl))
         (package-witness (cadr package-witness-supplied-p))
         (package-witness-supplied-p (and package-witness-supplied-p
                                          t))
         (debug (cadr (assoc-keyword :debug kvl))))
    (mv inline memoizable executable
        recognizer creator fixer
        logic exec
        package-witness package-witness-supplied-p debug)))

(defun parse-form (form)
  (declare (xargs :guard (frame-form-p form)))
  (let ((body (cddr form)))
    (mv-let (fds kvl)
            (split-body () body)
      (mv-let (fields element-types element-type-supplies
                      recognizers fixers equivs
                      initial-elements initial-element-supplies
                      accessors updaters)
              (parse-fds fds () () () () () () () () () ())
        (mv-let (inline memoizable executable
                        recognizer creator fixer
                        logic exec
                        package-witness package-witness-supplied-p debug)
                (parse-kvl kvl)
          (mv fields element-types element-type-supplies
              recognizers fixers equivs
              initial-elements initial-element-supplies
              accessors updaters
              inline memoizable executable
              recognizer creator fixer
              logic exec
              package-witness package-witness-supplied-p debug))))))


;;;; `DEFINE-FRAME'
(defmacro define-frame (&whole form frame &body body)
  (declare (xargs :guard (frame-form-p form))
           (ignore body))
  (mv-let (fields element-types element-type-supplies
                  recognizers fixers equivs
                  initial-elements initial-element-supplies
                  accessors updaters
                  inline memoizable executable
                  recognizer creator fixer
                  logic exec
                  package-witness package-witness-supplied-p debug)
          (parse-form form)

    `(with-output
       ,@(and (not debug)
              *constructor-output*)

       (make-event
         (let* ((frame ',frame)
                (logic ',logic)
                (exec ',exec)
                (package-witness (if ',package-witness-supplied-p
                                     ',package-witness
                                     (current-package state)))
                (fields ',fields)
                (element-types ',element-types)
                (element-type-supplies ',element-type-supplies)
                (world (w state))
                (stobj-property-list (loop$ :for element-type :in element-types
                                           :collect (and (symbolp element-type)
                                                         (getprop element-type
                                                                  'acl2::stobj
                                                                  nil
                                                                  'acl2::current-acl2-world
                                                                  world))))
                (recognizers ',recognizers)
                (fixers ',fixers)
                (equivs ',equivs)
                (initial-elements ',initial-elements)
                (initial-element-supplies ',initial-element-supplies)

                (inline ',inline)
                (memoizable ',memoizable)
                (executable ',executable)

                (recognizer ',recognizer)
                (creator ',creator)
                (fixer ',fixer)
                (accessors ',accessors)
                (updaters ',updaters)

                (debug ',debug)

                (frame$a (or logic
                             (symbolicate package-witness frame "$A")))
                (frame$c (or exec
                             (symbolicate package-witness frame "$C")))
                (recognizer (or recognizer
                                (symbolicate package-witness frame (make-predicate-suffix frame))))
                (creator (or creator
                             (symbolicate package-witness "CREATE-" frame)))
                (fixer (or fixer
                           (symbolicate package-witness frame "-FIX"))))

           `(progn
              (define-frame$c ,frame$c
                ,@(loop$ :for field :in fields
                        :as element-type :in element-types
                        :as element-type-supplied-p :in element-type-supplies
                        :as initial-element :in initial-elements
                        :as initial-element-supplied-p :in initial-element-supplies
                        :collect `(,field ,@(and element-type-supplied-p
                                                 `(:element-type ,element-type))
                                          ,@(and initial-element-supplied-p
                                                 `(:initial-element ,initial-element))))
                ,@(and inline
                       `(:inline ,inline))
                ,@(and memoizable
                       `(:memoizable ,memoizable))
                ,@(and executable
                       `(:executable ,executable))
                ,@(and ,package-witness-supplied-p
                       `(:package-witness ,package-witness))
                :debug ,debug)

              (define-frame$a ,frame$a
                ,@(loop$ :for field :in fields
                        :as recognizer :in recognizers
                        :as fixer :in fixers
                        :as equiv :in equivs
                        :as element-type :in element-types
                        :as stobj-property :in stobj-property-list
                        :as initial-element :in initial-elements
                        :as initial-element-supplied-p :in initial-element-supplies
                        :collect `(,field ,@(and recognizer
                                                 `(:recognizer ,recognizer))
                                          ,@(and fixer
                                                 `(:fixer ,fixer))
                                          ,@(and equiv
                                                 `(:equiv ,equiv))
                                          ,@(and stobj-property
                                                 `(:stobj ,element-type))
                                          ,@(and initial-element-supplied-p
                                                 `(:initial-element ,initial-element))))
                ,@(and ,package-witness-supplied-p
                       `(:package-witness ,package-witness))
                :debug ,debug)

              (define-frame$corr ,frame
                :logic ,frame$a
                :exec ,frame$c
                ,@(and ,package-witness-supplied-p
                       `(:package-witness ,package-witness))
                :debug ,debug)

              (define-frame$abs ,frame
                ,@(loop$ :for field :in fields
                        :as accessor :in accessors
                        :as updater :in updaters
                        :as element-type :in element-types
                        :as stobj-property :in stobj-property-list
                        :collect `(,field ,@(and accessor
                                                 `(:accessor ,accessor))
                                          ,@(and updater
                                                 `(:updater ,updater))
                                          ,@(and stobj-property
                                                 `(:stobj ,element-type))))
                :logic ,frame$a
                :exec ,frame$c
                :recognizer ,recognizer
                :creator ,creator
                :fixer ,fixer
                ,@(and executable
                       `(:executable ,executable))
                ,@(and ,package-witness-supplied-p
                       `(:package-witness ,package-witness))
                :debug ,debug)

              (in-theory
                (disable ,(symbolicate (if ,package-witness-supplied-p
                                           package-witness
                                           frame$c)
                                       frame$c
                                       "-THEOREMS")))))))))
