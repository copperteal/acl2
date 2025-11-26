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

#||
(include-book "std/lists/top" :dir :system)
||#

(include-book "../type-spec")
(include-book "../utilities/top")


;;;; Constants
(defconst *field-keywords$a*
  '(:recognizer :fixer :stobj :initial-element :accessor :updater))

(defconst *body-keywords$a*
  '(:recognizer :creator :fixer :view
    :package-witness :debug))


;;;; `DEFINE-FRAME$A' Predicates
(defun frame$a-descriptor-p (descriptor)
  (declare (xargs :guard t))
  (and (consp descriptor)
       (let ((name (car descriptor))
             (kvl (cdr descriptor)))
         (and (symbolp name)
              (keyword-value-listp kvl)
              (subsetp (evens kvl) *field-keywords$a* :test 'eq)
              (let ((recognizer (cadr (assoc-keyword :recognizer kvl)))
                    (fixer (cadr (assoc-keyword :fixer kvl)))
                    (stobj (cadr (assoc-keyword :stobj kvl)))
                    (initial-element (cadr (assoc-keyword :initial-element kvl)))
                    (accessor (cadr (assoc-keyword :accessor kvl)))
                    (updater (cadr (assoc-keyword :updater kvl))))
                (declare (ignore initial-element))
                (and (symbolp recognizer)
                     (symbolp fixer)
                     (or (and (not recognizer)
                              (not fixer))
                         (and recognizer
                              fixer))
                     (symbolp stobj)
                     (symbolp accessor)
                     (symbolp updater)))))))

(defun frame$a-descriptor-list-p (fds)
  (declare (xargs :guard t))
  (if (atom fds)
      (null fds)
      (and (frame$a-descriptor-p (car fds))
           (frame$a-descriptor-list-p (cdr fds)))))

(defun frame$a-body-p (body)
  (declare (xargs :guard t))
  (and (true-listp body)
       (if (consp (car body))
           (and (frame$a-descriptor-p (car body))
                (frame$a-body-p (cdr body)))
           (and (keyword-value-listp body)
                (subsetp (evens body) *body-keywords$a* :test 'eq)
                (let ((recognizer (cadr (assoc-keyword :recognizer body)))
                      (creator (cadr (assoc-keyword :creator body)))
                      (fixer (cadr (assoc-keyword :fixer body)))
                      (view (cadr (assoc-keyword :view body)))
                      (package-witness (cadr (assoc-keyword :package-witness body)))
                      (debug (cadr (assoc-keyword :debug body))))
                  (and (symbolp recognizer)
                       (symbolp creator)
                       (symbolp fixer)
                       (symbolp view)
                       (package-witness-p package-witness)
                       (booleanp debug)))))))

(defthm frame$a-body-p-when-frame$a-descriptor-list-p
  (implies (frame$a-descriptor-list-p fds)
           (frame$a-body-p fds))
  :hints
  (("Goal"
    :induct (len fds))))

(defun frame$a-form-p (form)
  (declare (xargs :guard t))
  (and (true-listp form)
       (eq (car form) 'define-frame$a)
       (symbolp (cadr form))
       (frame$a-body-p (cddr form))))


;;;; `DEFINE-FRAME$A' Parser
(with-books (("std/lists/rev" :dir :system))
  (defun split-body$a (fds body)
    (declare (xargs :guard (and (frame$a-descriptor-list-p fds)
                                (frame$a-body-p body))))
    (if (or (endp body)
            (atom (car body)))
        (mv (reverse fds) body)
        (split-body$a (cons (car body) fds) (cdr body))))

  (local
    (defthm frame$a-descriptor-list-p-of-rev
      (implies (frame$a-descriptor-list-p fds)
               (frame$a-descriptor-list-p (acl2::rev fds)))
      :hints
      (("Goal"
        :in-theory (disable frame$a-descriptor-p)))))

  (defthm split-body$a-values
    (implies (and (frame$a-descriptor-list-p fds)
                  (frame$a-body-p body))
             (mv-let (fds kvl)
                     (split-body$a fds body)
               (and (frame$a-descriptor-list-p fds)
                    (frame$a-body-p kvl)
                    (keyword-value-listp kvl))))))

(defun parse-fds$a (fds fields recognizers fixers stobjs
                    initial-elements accessors updaters)
  (declare (xargs :guard (and (frame$a-descriptor-list-p fds)
                              (symbol-listp fields)
                              (symbol-listp recognizers)
                              (symbol-listp fixers)
                              (symbol-listp stobjs)
                              (true-listp initial-elements)
                              (symbol-listp accessors)
                              (symbol-listp updaters))))
  (if (endp fds)
      (mv (reverse fields)
          (reverse recognizers)
          (reverse fixers)
          (reverse stobjs)
          (reverse initial-elements)
          (reverse accessors)
          (reverse updaters))
      (let* ((descriptor (car fds))
             (field (car descriptor))
             (kvl (cdr descriptor))
             (recognizer (cadr (assoc-keyword :recognizer kvl)))
             (fixer (cadr (assoc-keyword :fixer kvl)))
             (stobj (cadr (assoc-keyword :stobj kvl)))
             (initial-element (cadr (assoc-keyword :initial-element kvl)))
             (accessor (cadr (assoc-keyword :accessor kvl)))
             (updater (cadr (assoc-keyword :updater kvl))))
        (parse-fds$a (cdr fds)
                     (cons field fields)
                     (cons recognizer recognizers)
                     (cons fixer fixers)
                     (cons stobj stobjs)
                     (cons initial-element initial-elements)
                     (cons accessor accessors)
                     (cons updater updaters)))))

(defun parse-kvl$a (kvl)
  (declare (xargs :guard (and (frame$a-body-p kvl)
                              (keyword-value-listp kvl))))
  (let* ((recognizer (cadr (assoc-keyword :recognizer kvl)))
         (creator (cadr (assoc-keyword :creator kvl)))
         (fixer (cadr (assoc-keyword :fixer kvl)))
         (view (cadr (assoc-keyword :view kvl)))
         (package-witness-supplied-p (assoc-keyword :package-witness kvl))
         (package-witness (cadr package-witness-supplied-p))
         (package-witness-supplied-p (and package-witness-supplied-p
                                          t))
         (debug (cadr (assoc-keyword :debug kvl))))
    (mv recognizer creator fixer view
        package-witness package-witness-supplied-p debug)))

(defun parse-form$a (form)
  (declare (xargs :guard (frame$a-form-p form)))
  (let ((body (cddr form)))
    (mv-let (fds kvl)
            (split-body$a () body)
      (mv-let (fields recognizers fixers stobjs
                      initial-elements accessors updaters)
              (parse-fds$a fds () () () () () () ())
        (mv-let (recognizer creator fixer view
                            package-witness package-witness-supplied-p debug)
                (parse-kvl$a kvl)
          (mv fields recognizers fixers stobjs
              initial-elements accessors updaters
              recognizer creator fixer view
              package-witness package-witness-supplied-p debug))))))


;;;; `DEFINE-FRAME$A'
(defmacro define-frame$a (&whole form frame &body body)
  (declare (xargs :guard (frame$a-form-p form))
           (ignore body))
  (mv-let (fields recognizers fixers stobjs
                  initial-elements accessors updaters
                  recognizer creator fixer view
                  package-witness package-witness-supplied-p debug)
          (parse-form$a form)

    `(with-output
       ,@(and (not debug)
              *constructor-output*)

       (make-event
         (let* ((frame ',frame)
                (package-witness (if ',package-witness-supplied-p
                                     ',package-witness
                                     (current-package state)))
                (fields ',fields)
                (%fields (loop$ :for field :in fields
                               :collect (symbolicate field "%" field)))

                (stobjs ',stobjs)
                (world (w state))
                (stobj-property-list (loop$ :for stobj :in stobjs
                                           :collect (getprop stobj
                                                             'acl2::stobj
                                                             nil
                                                             'acl2::current-acl2-world
                                                             world)))
                (absstobj-info-list (loop$ :for stobj :in stobjs
                                          :collect (and (symbolp stobj)
                                                        (getprop stobj
                                                                 'acl2::absstobj-info
                                                                 nil
                                                                 'acl2::current-acl2-world
                                                                 world))))
                (stobj$a-property-alist (table-alist 'stobj$a-property world))
                (stobj$a-property-list (loop$ :for stobj :in stobjs
                                             :collect (cdr (assoc stobj stobj$a-property-alist))))
                (recognizers ',recognizers)
                (recognizers (loop$ :for recognizer :in recognizers
                                   :as stobj$a-property :in stobj$a-property-list
                                   :collect (cond
                                              (recognizer)
                                              (stobj$a-property
                                               (first (second stobj$a-property))))))
                (guard-recognizers (loop$ :for stobj-property :in stobj-property-list
                                         :as recognizer :in recognizers
                                         :collect (if stobj-property
                                                      (caadr stobj-property)
                                                      recognizer)))
                (creators (loop$ :for stobj$a-property :in stobj$a-property-list
                                :collect (cond
                                           (stobj$a-property
                                            (second (second stobj$a-property))))))
                (fixer-alist (table-alist 'fixer world))
                (fixers ',fixers)
                (fixers (loop$ :for fixer :in fixers
                              :as stobj :in stobjs
                              :as stobj$a-property :in stobj$a-property-list
                              :collect (cond
                                         (fixer)
                                         (stobj$a-property
                                          (third (second stobj$a-property)))
                                         (t
                                          (cdr (assoc stobj fixer-alist))))))
                (initial-element-names (loop$ :for field :in fields
                                             :collect (symbolicate package-witness "*" frame "-" field "-INITIAL-ELEMENT*")))
                (initial-elements (loop$ :for initial-element-name :in initial-element-names
                                        :as creator :in creators
                                        :collect (if creator
                                                     `(,creator)
                                                     initial-element-name)))

                (recognizer ',recognizer)
                (creator ',creator)
                (fixer ',fixer)
                (view ',view)
                (accessors ',accessors)
                (updaters ',updaters)

                ;; Interface Symbols
                (recognizer (or recognizer
                                (symbolicate package-witness frame (make-predicate-suffix frame))))
                (creator (or creator
                             (symbolicate package-witness "CREATE-" frame)))
                (fixer (or fixer
                           (symbolicate package-witness frame "-FIX")))
                (view (or view
                          (symbolicate package-witness frame "-VIEW")))
                (accessors (loop$ :for field :in fields
                                 :as accessor :in accessors
                                 :collect (or accessor
                                              (symbolicate package-witness frame "-" field))))
                (updaters (loop$ :for field :in fields
                                :as updater :in updaters
                                :collect (or updater
                                             (symbolicate package-witness frame "-" field "-SET"))))

                ;; Prologue
                (frame-begin (symbolicate package-witness frame "-BEGIN"))
                (frame-end (symbolicate package-witness frame "-END"))
                (defconst-forms (loop$ :for initial-element-name :in initial-element-names
                                      :as initial-element :in ',initial-elements
                                      :as stobj-property :in stobj-property-list
                                      :when (not stobj-property)
                                      :collect `(defconst ,initial-element-name ',initial-element)))
                (prologue
                 `((deflabel ,frame-begin)

                   ,@defconst-forms))

                ;; Theorem Names
                (recognizer{type-prescription} (symbolicate package-witness recognizer "{TYPE-PRESCRIPTION}"))
                (recognizer{compound-recognizer} (symbolicate package-witness recognizer "{COMPOUND-RECOGNIZER}"))
                (recognizer-of-creator (symbolicate package-witness recognizer "-OF-" creator))
                (recognizer-of-fixer (symbolicate package-witness recognizer "-OF-" fixer))
                (recognizer-of-view (symbolicate package-witness recognizer "-OF-" view))

                (fixer{rewrite} (symbolicate package-witness fixer "{REWRITE}"))
                (fixer-when-recognizer (symbolicate package-witness fixer "-WHEN-" recognizer))
                (fixer-when-not-recognizer (symbolicate package-witness fixer "-WHEN-NOT-" recognizer))

                (view{type-prescription} (symbolicate package-witness view "{TYPE-PRESCRIPTION}"))
                (view-collapse (symbolicate package-witness view "-COLLAPSE"))
                (view{rewrite} (symbolicate package-witness view "{REWRITE}"))

                (%frame (symbolicate package-witness "%" frame))
                (frame-equal (symbolicate package-witness frame "-EQUAL"))
                (frame-equal{forward-chaining} (symbolicate package-witness frame-equal "{FORWARD-CHAINING}"))

                ;; Epilogue
                (frame-theorems (symbolicate package-witness frame "-THEOREMS"))
                (frame-definitions (symbolicate package-witness frame "-DEFINITIONS"))
                (frame-aggressive (symbolicate package-witness frame "-AGGRESSIVE"))
                (epilogue
                 `((in-theory
                     (enable ,view{rewrite}
                             ,@(loop$ :for updater :in updaters
                                     :collect (symbolicate package-witness updater "{REWRITE}"))))

                   (deflabel ,frame-end)

                   (deftheory-static ,frame-definitions
                     ',(append
                        (list recognizer
                              creator
                              fixer
                              view
                              frame-equal)
                        accessors
                        updaters))

                   (deftheory-static ,frame-theorems
                     (set-difference-theories
                      (set-difference-theories
                       (current-theory ',frame-end)
                       (current-theory ',frame-begin))
                      (theory ',frame-definitions)))

                   (deftheory-static ,frame-aggressive
                     ',(append
                        (list fixer{rewrite}
                              view-collapse)
                        (loop$ :for i :from 1 :to (len fields)
                              :as recognizer :in recognizers
                              :when recognizer
                              :collect (symbolicate package-witness view "-WHEN-NOT-" recognizer "-" i))
                        (loop$ :for accessor :in accessors
                              :collect (symbolicate package-witness accessor "-WHEN-NOT-" recognizer))))

                   (in-theory
                     (union-theories (current-theory ',frame-begin)
                                     (theory ',frame-theorems)))))

                (body
                 `(encapsulate ()

                    ,@(loop$ :for i :from 1 :to (len fields)
                            :as field :in fields
                            :as recognizer :in recognizers
                            :when recognizer
                            :collect `(local
                                        (defthm ,(symbolicate "ATOMIC-STOBJS" "BOOLEANP-OF-" recognizer "-" i)
                                          (booleanp (,recognizer ,field))
                                          :rule-classes
                                          (:rewrite
                                           :type-prescription))))

                    ,@(loop$ :for i :from 1 :to (len fields)
                            :as initial-element :in initial-elements
                            :as initial-element-name :in initial-element-names
                            :as recognizer :in recognizers
                            :when recognizer
                            :collect `(local
                                        (defthm ,(symbolicate "ATOMIC-STOBJS" recognizer "-OF-" initial-element "-" i)
                                          (,recognizer ,initial-element)
                                          ,@(and (equal initial-element initial-element-name)
                                                 `(:rule-classes nil)))))

                    ,@(loop$ :for i :from 1 :to (len fields)
                            :as field :in fields
                            :as initial-element :in initial-elements
                            :as recognizer :in recognizers
                            :as fixer :in fixers
                            :when (and recognizer
                                       fixer)
                            :collect `(local
                                        (defthm ,(symbolicate "ATOMIC-STOBJS" fixer "{REWRITE}" "-" i)
                                          (equal (,fixer ,field)
                                                 (if (,recognizer ,field)
                                                     ,field
                                                     ,initial-element)))))

                    (local
                      (in-theory
                        (union-theories (current-theory 'acl2::ground-zero)
                                        (set-difference-theories
                                         (universal-theory :here)
                                         (universal-theory ',frame-begin)))))

                    ,@(loop$ :for absstobj-info :in absstobj-info-list
                            :when absstobj-info
                            :collect `(local
                                        (in-theory
                                          (enable ,@(strip-cars (cdr absstobj-info))))))

                    ,@(let ((exec-recognizers (loop$ :for recognizer :in recognizers
                                                    :when recognizer
                                                    :collect `(:e ,recognizer)))
                            (exec-fixers (loop$ :for fixer :in fixers
                                               :when fixer
                                               :collect `(:e ,fixer))))
                        (and (or exec-recognizers
                                 exec-fixers)
                             `((in-theory
                                 (enable ,@exec-recognizers
                                         ,@exec-fixers)))))

                    (defun ,recognizer (,frame)
                      (declare (xargs :guard t))
                      (and (true-listp ,frame)
                           (= (len ,frame) ,(len fields))
                           ,@(loop$ :for i :from 0 :to (1- (len fields))
                                   :as recognizer :in recognizers
                                   :when recognizer
                                   :collect `(,recognizer (nth ,i ,frame)))
                           t))

                    (defun ,creator ()
                      (declare (xargs :guard t))
                      (list ,@initial-elements))

                    (in-theory
                      (disable (:e ,creator)))

                    (defun ,fixer (,frame)
                      (declare (xargs :guard (,recognizer ,frame)))
                      (if (,recognizer ,frame)
                          ,frame
                          (,creator)))

                    (defun-nx ,view (,@fields ,frame)
                      (declare (xargs :guard ,(if fields
                                                  `(and ,@(loop$ :for field :in fields
                                                                :as recognizer :in recognizers
                                                                :when recognizer
                                                                :collect `(,recognizer ,field))
                                                        (,recognizer ,frame))
                                                  `(,recognizer ,frame))))
                      (let (,@(loop$ :for field :in fields
                                    :as fixer :in fixers
                                    :when fixer
                                    :collect `(,field (,fixer ,field))))
                        (list ,@fields)))

                    ,@(loop$ :for i :from 0 :to (1- (len fields))
                            :as field-fixer :in fixers
                            :as accessor :in accessors
                            :collect `(defun ,accessor (,frame)
                                        (declare (xargs :guard (,recognizer ,frame)))
                                        (let ((,frame (,fixer ,frame)))
                                          ,(if field-fixer
                                               `(,field-fixer (nth ,i ,frame))
                                               `(nth ,i ,frame)))))

                    ,@(loop$ :for i :from 0 :to (1- (len fields))
                            :as field :in fields
                            :as guard-recognizer :in guard-recognizers
                            :as field-fixer :in fixers
                            :as updater :in updaters
                            :collect `(defun ,updater (,field ,frame)
                                        (declare (xargs :guard ,(if guard-recognizer
                                                                    `(and (,guard-recognizer ,field)
                                                                          (,recognizer ,frame))
                                                                    `(,recognizer ,frame))))
                                        (let (,@(and field-fixer
                                                     `((,field (,field-fixer ,field))))
                                              (,frame (,fixer ,frame)))
                                          (update-nth ,i ,field ,frame))))

                    ;; `RECOGNIZER'
                    (defthm ,recognizer{type-prescription}
                      (booleanp (,recognizer ,frame))
                      :rule-classes :type-prescription)

                    (defthm ,recognizer{compound-recognizer}
                      (implies (,recognizer ,frame)
                               ,(if (consp fields)
                                    `(and (consp ,frame)
                                          (true-listp ,frame))
                                    `(null ,frame)))
                      :rule-classes :compound-recognizer)

                    (defthm ,recognizer-of-creator
                      (,recognizer (,creator)))

                    (defthm ,recognizer-of-fixer
                      (,recognizer (,fixer ,frame)))

                    (defthm ,recognizer-of-view
                      (,recognizer (,view ,@fields ,frame)))

                    ;; `FIXER'
                    (with-books (("std/lists/nth" :dir :system))
                      (local
                        (defthm nth-of-cons
                          (equal (nth i (cons a d))
                                 (if (zp i)
                                     a
                                     (nth (1- i) d)))))

                      (local
                        (in-theory
                          (disable nth
                                   acl2::nth-when-zp)))

                      (defthmd ,fixer{rewrite}
                        (equal (,fixer ,frame)
                               (,view ,@(loop$ :for accessor :in accessors
                                              :collect `(,accessor ,frame))
                                      ,frame))
                        :hints
                        ((acl2::equal-by-nths-hint))))

                    (defthm ,fixer-when-recognizer
                      (implies (,recognizer ,frame)
                               (equal (,fixer ,frame)
                                      ,frame)))

                    (defthm ,fixer-when-not-recognizer
                      (implies (not (,recognizer ,frame))
                               (equal (,fixer ,frame)
                                      (,creator))))

                    ;; `VIEW'
                    (defthm ,view{type-prescription}
                      ,(if (consp fields)
                           `(and (consp (,view ,@fields ,frame))
                                 (true-listp (,view ,@fields ,frame)))
                           `(null (,view ,frame)))
                      :rule-classes :type-prescription)

                    (with-books (("std/lists/nth" :dir :system))
                      (local
                        (defthm nth-of-cons
                          (equal (nth i (cons a d))
                                 (if (zp i)
                                     a
                                     (nth (1- i) d)))))

                      (local
                        (in-theory
                          (disable nth
                                   acl2::nth-when-zp)))

                      (defthmd ,view-collapse
                        (implies (case-split (,recognizer ,%frame))
                                 (equal (,view ,@(loop$ :for accessor :in accessors
                                                       :collect `(,accessor ,%frame))
                                               ,frame)
                                        ,%frame))
                        :hints
                        ((acl2::equal-by-nths-hint))))

                    (defthmd ,view{rewrite}
                      (implies (syntaxp (not (and (consp ,frame)
                                                  (eq (car ,frame) ',creator))))
                               (equal (,view ,@fields ,frame)
                                      (,view ,@fields (,creator)))))

                    ,@(loop$ :for i :from 1 :to (len fields)
                            :as j :from 0 :to (1- (len fields))
                            :as field :in fields
                            :as recognizer :in recognizers
                            :as initial-element :in initial-elements
                            :when recognizer
                            :collect `(defthmd ,(symbolicate package-witness view "-WHEN-NOT-" recognizer "-" i)
                                        (implies (not (,recognizer ,field))
                                                 (equal (,view ,@fields ,frame)
                                                        (,view ,@(update-nth j initial-element fields) ,frame)))))

                    ,@(loop$ :for i :from 1 :to (len fields)
                            :as j :from 0 :to (1- (len fields))
                            :as field :in fields
                            :as fixer :in fixers
                            :when fixer
                            :collect `(defthm ,(symbolicate package-witness view "-OF-" fixer "-" i)
                                        (equal (,view ,@(update-nth j `(,fixer ,field) fields) ,frame)
                                               (,view ,@fields ,frame))))

                    ;; `ACCESSORS'
                    ,@(loop$ :for recognizer :in recognizers
                            :as accessor :in accessors
                            :when recognizer
                            :collect `(defthm ,(symbolicate package-witness recognizer "-OF-" accessor)
                                        (,recognizer (,accessor ,frame))
                                        :rule-classes
                                        (:rewrite
                                         :type-prescription)))

                    ,@(loop$ :for accessor :in accessors
                            :as initial-element :in initial-elements
                            :collect `(defthmd ,(symbolicate package-witness accessor "-WHEN-NOT-" recognizer)
                                        (implies (not (,recognizer ,frame))
                                                 (equal (,accessor ,frame)
                                                        ,initial-element))))

                    ,@(loop$ :for accessor :in accessors
                            :as initial-element :in initial-elements
                            :collect `(defthm ,(symbolicate package-witness accessor "-OF-" creator)
                                        (equal (,accessor (,creator))
                                               ,initial-element)))

                    ,@(loop$ :for accessor :in accessors
                            :collect `(defthm ,(symbolicate package-witness accessor "-OF-" fixer)
                                        (equal (,accessor (,fixer ,frame))
                                               (,accessor ,frame))))

                    ,@(loop$ :for field :in fields
                            :as fixer :in fixers
                            :as accessor :in accessors
                            :collect `(defthm ,(symbolicate package-witness accessor "-OF-" view)
                                        (equal (,accessor (,view ,@fields ,frame))
                                               ,(if fixer
                                                    `(,fixer ,field)
                                                    field))))

                    ;; `UPDATERS'
                    ,@(and fields
                           `((with-books (("std/lists/nth" :dir :system))
                               (local
                                 (defthm nth-of-cons
                                   (equal (nth i (cons a d))
                                          (if (zp i)
                                              a
                                              (nth (1- i) d)))))

                               (local
                                 (in-theory
                                   (disable nth
                                            acl2::nth-when-zp)))

                               ,@(let ((arguments (loop$ :for accessor :in accessors
                                                        :collect `(,accessor ,frame))))
                                   (loop$ :for i :from 0 :to (1- (len fields))
                                         :as field :in fields
                                         :as updater :in updaters
                                         :collect `(defthmd ,(symbolicate package-witness updater "{REWRITE}")
                                                     (implies (syntaxp (not (and (consp ,frame)
                                                                                 (eq (car ,frame) ',view))))
                                                              (equal (,updater ,field ,frame)
                                                                     (,view ,@(update-nth i field arguments) ,frame)))
                                                     :hints
                                                     ((acl2::equal-by-nths-hint))))))))

                    ,@(loop$ :for i :from 0 :to (1- (len fields))
                            :as %field :in %fields
                            :as updater :in updaters
                            :collect `(defthm ,(symbolicate package-witness updater "-OF-" view)
                                        (equal (,updater ,%field (,view ,@fields ,frame))
                                               (,view ,@(update-nth i %field fields) ,frame))))

                    ;; `FRAME-EQUAL'
                    (defun-nx ,frame-equal (,%frame ,frame)
                      (declare (xargs :guard t
                                      :verify-guards nil))
                      (and (,recognizer ,%frame)
                           (,recognizer ,frame)
                           ,@(loop$ :for accessor :in accessors
                                   :collect `(equal (,accessor ,%frame)
                                                    (,accessor ,frame)))))

                    (table equality ',frame ',frame-equal)

                    (with-books (("std/lists/nth" :dir :system))
                      (local
                        (defthm nth-of-cons
                          (equal (nth i (cons a d))
                                 (if (zp i)
                                     a
                                     (nth (1- i) d)))))

                      (local
                        (in-theory
                          (disable nth
                                   acl2::nth-when-zp)))

                      (defthm ,frame-equal{forward-chaining}
                        (implies (,frame-equal ,%frame ,frame)
                                 (equal ,%frame ,frame))
                        :rule-classes
                        ((:forward-chaining :trigger-terms
                                            ((,frame-equal ,%frame ,frame))
                                            :corollary
                                            (implies t
                                                     (implies (,frame-equal ,%frame ,frame)
                                                              (equal ,%frame ,frame)))))
                        :hints
                        ((acl2::equal-by-nths-hint)
                         ,@(and fields
                                `(("Subgoal 1"
                                   :cases ,(loop$ :for i :from 0 :to (1- (len fields))
                                                 :collect `(equal acl2::n ,i))))))))))

                (stobj$a-property `(,frame (,recognizer
                                            ,creator
                                            ,fixer)
                                           (,fields
                                            ,recognizers
                                            ,initial-element-names
                                            ,fixers
                                            ,stobjs
                                            ,accessors
                                            ,updaters
                                            (,view)))))

           `(progn
              ,@prologue

              ,body

              ,@epilogue

              (table stobj$a-property ',frame ',stobj$a-property)

              (table package-witness ',frame ',package-witness)))))))
