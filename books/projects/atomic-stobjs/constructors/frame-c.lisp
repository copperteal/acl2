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
(include-book "copy")


;;;; Constants
(defconst *field-keywords$c*
  '(:element-type :initial-element :recognizer :accessor :updater))

(defconst *body-keywords$c*
  '(:inline :memoizable :executable
    :recognizer :creator :fixer :view
    :package-witness :debug))


;;;; `DEFINE-FRAME$C' Predicates
(defun frame$c-descriptor-p (descriptor)
  (declare (xargs :guard t))
  (and (consp descriptor)
       (let ((name (car descriptor))
             (kvl (cdr descriptor)))
         (and (symbolp name)
              (keyword-value-listp kvl)
              (subsetp (evens kvl) *field-keywords$c* :test 'eq)
              (let ((element-type (assoc-keyword :element-type kvl))
                    (initial-element (cadr (assoc-keyword :initial-element kvl)))
                    (recognizer (cadr (assoc-keyword :recognizer kvl)))
                    (accessor (cadr (assoc-keyword :accessor kvl)))
                    (updater (cadr (assoc-keyword :updater kvl))))
                (and (or (not element-type)
                         (let ((element-type (cadr element-type)))
                           (if (acl2-type-spec-p element-type)
                               (typep$ initial-element element-type)
                               (symbolp element-type))))
                     (symbolp recognizer)
                     (symbolp accessor)
                     (symbolp updater)))))))

(defun frame$c-descriptor-list-p (fds)
  (declare (xargs :guard t))
  (if (atom fds)
      (null fds)
      (and (frame$c-descriptor-p (car fds))
           (frame$c-descriptor-list-p (cdr fds)))))

(defun frame$c-body-p (body)
  (declare (xargs :guard t))
  (and (true-listp body)
       (if (consp (car body))
           (and (frame$c-descriptor-p (car body))
                (frame$c-body-p (cdr body)))
           (and (keyword-value-listp body)
                (subsetp (evens body) *body-keywords$c* :test 'eq)
                (let ((inline (cadr (assoc-keyword :inline body)))
                      (memoizable (cadr (assoc-keyword :memoizable body)))
                      (executable (cadr (assoc-keyword :executable body)))
                      (recognizer (cadr (assoc-keyword :recognizer body)))
                      (creator (cadr (assoc-keyword :creator body)))
                      (fixer (cadr (assoc-keyword :fixer body)))
                      (view (cadr (assoc-keyword :view body)))
                      (package-witness (cadr (assoc-keyword :package-witness body)))
                      (debug (cadr (assoc-keyword :debug body))))
                  (and (booleanp inline)
                       (booleanp memoizable)
                       (booleanp executable)
                       (symbolp recognizer)
                       (symbolp creator)
                       (symbolp fixer)
                       (symbolp view)
                       (package-witness-p package-witness)
                       (booleanp debug)))))))

(defthm frame$c-body-p-when-frame$c-descriptor-list-p
  (implies (frame$c-descriptor-list-p fds)
           (frame$c-body-p fds))
  :hints
  (("Goal"
    :induct (len fds))))

(defun frame$c-form-p (form)
  (declare (xargs :guard t))
  (and (true-listp form)
       (eq (car form) 'define-frame$c)
       (symbolp (cadr form))
       (frame$c-body-p (cddr form))))


;;;; `DEFINE-FRAME$C' Parser
(with-books (("std/lists/rev" :dir :system))
  (defun split-body$c (fds body)
    (declare (xargs :guard (and (frame$c-descriptor-list-p fds)
                                (frame$c-body-p body))))
    (if (or (endp body)
            (atom (car body)))
        (mv (reverse fds) body)
        (split-body$c (cons (car body) fds) (cdr body))))

  (local
    (defthm frame$c-descriptor-list-p-of-rev
      (implies (frame$c-descriptor-list-p fds)
               (frame$c-descriptor-list-p (acl2::rev fds)))
      :hints
      (("Goal"
        :in-theory (disable frame$c-descriptor-p)))))

  (defthm split-body$c-values
    (implies (and (frame$c-descriptor-list-p fds)
                  (frame$c-body-p body))
             (mv-let (fds kvl)
                     (split-body$c fds body)
               (and (frame$c-descriptor-list-p fds)
                    (frame$c-body-p kvl)
                    (keyword-value-listp kvl))))))

(defun parse-fds$c (fds fields element-types initial-elements
                    recognizers accessors updaters)
  (declare (xargs :guard (and (frame$c-descriptor-list-p fds)
                              (symbol-listp fields)
                              (true-listp element-types)
                              (true-listp initial-elements)
                              (symbol-listp recognizers)
                              (symbol-listp accessors)
                              (symbol-listp updaters))))
  (if (endp fds)
      (mv (reverse fields)
          (reverse element-types)
          (reverse initial-elements)
          (reverse recognizers)
          (reverse accessors)
          (reverse updaters))
      (let* ((descriptor (car fds))
             (field (car descriptor))
             (kvl (cdr descriptor))
             (element-type-supplied (assoc-keyword :element-type kvl))
             (element-type (if element-type-supplied
                               (cadr element-type-supplied)
                               't))
             (initial-element (cadr (assoc-keyword :initial-element kvl)))
             (accessor (cadr (assoc-keyword :accessor kvl)))
             (recognizer (cadr (assoc-keyword :recognizer kvl)))
             (updater (cadr (assoc-keyword :updater kvl))))
        (parse-fds$c (cdr fds)
                     (cons field fields)
                     (cons element-type element-types)
                     (cons initial-element initial-elements)
                     (cons recognizer recognizers)
                     (cons accessor accessors)
                     (cons updater updaters)))))

(defun parse-kvl$c (kvl)
  (declare (xargs :guard (and (frame$c-body-p kvl)
                              (keyword-value-listp kvl))))
  (let* ((inline (cadr (assoc-keyword :inline kvl)))
         (memoizable (cadr (assoc-keyword :memoizable kvl)))
         (executable (cadr (assoc-keyword :executable kvl)))
         (recognizer (cadr (assoc-keyword :recognizer kvl)))
         (creator (cadr (assoc-keyword :creator kvl)))
         (fixer (cadr (assoc-keyword :fixer kvl)))
         (view (cadr (assoc-keyword :view kvl)))
         (package-witness-supplied-p (assoc-keyword :package-witness kvl))
         (package-witness (cadr package-witness-supplied-p))
         (package-witness-supplied-p (and package-witness-supplied-p
                                          t))
         (debug (cadr (assoc-keyword :debug kvl))))
    (mv inline memoizable executable
        recognizer creator fixer view
        package-witness package-witness-supplied-p debug)))

(defun parse-form$c (form)
  (declare (xargs :guard (frame$c-form-p form)))
  (let ((body (cddr form)))
    (mv-let (fds kvl)
            (split-body$c () body)
      (mv-let (fields element-types initial-elements
                      recognizers accessors updaters)
              (parse-fds$c fds () () () () () ())
        (mv-let (inline memoizable executable
                        recognizer creator fixer view
                        package-witness package-witness-supplied-p debug)
                (parse-kvl$c kvl)
          (mv fields element-types initial-elements
              recognizers accessors updaters
              inline memoizable executable
              recognizer creator fixer view
              package-witness package-witness-supplied-p debug))))))


;;;; `DEFINE-FRAME$C'
(defmacro define-frame$c (&whole form frame &body body)
  (declare (xargs :guard (frame$c-form-p form))
           (ignore body))
  (mv-let (fields element-types initial-elements
                  recognizers accessors updaters
                  inline memoizable executable
                  recognizer creator fixer view
                  package-witness package-witness-supplied-p debug)
          (parse-form$c form)

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

                (element-types ',element-types)
                (world (w state))
                (stobj-property-list (loop$ :for element-type :in element-types
                                           :collect (and (symbolp element-type)
                                                         (getprop element-type
                                                                  'acl2::stobj
                                                                  nil
                                                                  'acl2::current-acl2-world
                                                                  world))))
                (absstobj-info-list (loop$ :for element-type :in element-types
                                          :collect (and (symbolp element-type)
                                                        (getprop element-type
                                                                 'acl2::absstobj-info
                                                                 nil
                                                                 'acl2::current-acl2-world
                                                                 world))))
                (stobj$a-property-alist (table-alist 'stobj$a-property world))
                (stobj$a-property-list (loop$ :for element-type :in element-types
                                             :collect (and (symbolp element-type)
                                                           (cdr (assoc element-type stobj$a-property-alist)))))
                (stobj-recognizers (loop$ :for stobj-property :in stobj-property-list
                                         :as stobj$a-property :in stobj$a-property-list
                                         :collect (cond
                                                    (stobj$a-property
                                                     (first (second stobj$a-property)))
                                                    (stobj-property
                                                     (caadr stobj-property)))))
                (stobj-creators (loop$ :for stobj-property :in stobj-property-list
                                      :as stobj$a-property :in stobj$a-property-list
                                      :collect (cond
                                                 (stobj$a-property
                                                  (second (second stobj$a-property)))
                                                 (stobj-property
                                                  (cdadr stobj-property)))))
                (stobj-coupled-p-alist (table-alist 'coupledp world))
                (stobj-coupled-p-list (loop$ :for element-type :in element-types
                                            :collect (and (symbolp element-type)
                                                          (cdr (assoc element-type stobj-coupled-p-alist)))))
                (stobj-copy-alist (table-alist 'copy world))
                (stobj-copy-list (loop$ :for element-type :in element-types
                                       :collect (and (symbolp element-type)
                                                     (cdr (assoc element-type stobj-copy-alist)))))
                (initial-elements ',initial-elements)
                (initial-element-names (loop$ :for field :in fields
                                             :collect (symbolicate package-witness "*" frame "-" field "-INITIAL-ELEMENT*")))

                (inline ',inline)
                (memoizable ',memoizable)
                (executable ',executable)

                (recognizer ',recognizer)
                (creator ',creator)
                (fixer ',fixer)
                (view ',view)
                (recognizers ',recognizers)
                (accessors ',accessors)
                (updaters ',updaters)

                ;; Interface Symbols
                (recognizer-stobj-default (symbolicate package-witness frame "P"))
                (recognizer (or recognizer
                                (symbolicate package-witness frame (make-predicate-suffix frame))))
                (creator-stobj-default (symbolicate package-witness "CREATE-" frame))
                (creator (or creator
                             (symbolicate package-witness "CREATE-" frame)))
                (fixer (or fixer
                           (symbolicate package-witness frame "-FIX")))
                (view (or view
                          (symbolicate package-witness frame "-VIEW")))
                (recognizer-stobj-defaults (loop$ :for field :in fields
                                                 :collect (symbolicate package-witness frame "-" field "P")))
                (recognizers (loop$ :for field :in fields
                                   :as recognizer :in recognizers
                                   :collect (or recognizer
                                                (symbolicate package-witness frame "-" field "-P"))))
                (accessor-stobj-defaults (loop$ :for field :in fields
                                               :collect (symbolicate package-witness frame "-" field)))
                (accessors (loop$ :for field :in fields
                                 :as accessor :in accessors
                                 :collect (or accessor
                                              (symbolicate package-witness frame "-" field))))
                (updater-stobj-defaults (loop$ :for field :in fields
                                              :collect (symbolicate package-witness "UPDATE-" frame "-" field)))
                (updaters (loop$ :for field :in fields
                                :as updater :in updaters
                                :collect (or updater
                                             (symbolicate package-witness frame "-" field "-SET"))))

                ;; Make Doublets
                (doublets (append (and (not (eq recognizer recognizer-stobj-default))
                                       `((,recognizer-stobj-default ,recognizer)))
                                  (and (not (eq creator creator-stobj-default))
                                       `((,creator-stobj-default ,creator)))
                                  (loop$ :for recognizer :in recognizers
                                        :as recognizer-stobj-default :in recognizer-stobj-defaults
                                        :when (not (eq recognizer recognizer-stobj-default))
                                        :collect `(,recognizer-stobj-default ,recognizer))
                                  (loop$ :for accessor :in accessors
                                        :as accessor-stobj-default :in accessor-stobj-defaults
                                        :when (not (eq accessor accessor-stobj-default))
                                        :collect `(,accessor-stobj-default ,accessor))
                                  (loop$ :for updater :in updaters
                                        :as updater-stobj-default :in updater-stobj-defaults
                                        :when (not (eq updater updater-stobj-default))
                                        :collect `(,updater-stobj-default ,updater))))

                ;; Prologue
                (frame-begin (symbolicate package-witness frame "-BEGIN"))
                (frame-end (symbolicate package-witness frame "-END"))
                (defconst-forms (loop$ :for initial-element-name :in initial-element-names
                                      :as initial-element :in initial-elements
                                      :as stobj-property :in stobj-property-list
                                      :when (not stobj-property)
                                      :collect `(defconst ,initial-element-name ',initial-element)))
                (defstobj-descriptors (loop$ :for accessor :in accessors
                                            :as element-type :in element-types
                                            :as stobj-property :in stobj-property-list
                                            :as initial-element :in initial-elements
                                            :collect `(,accessor
                                                       :type ,element-type
                                                       ,@(and (not stobj-property)
                                                              `(:initially ,initial-element)))))
                (prologue
                 `((deflabel ,frame-begin)

                   ,@defconst-forms

                   (defstobj ,frame
                     ,@defstobj-descriptors
                     :renaming ,doublets
                     :inline ,inline
                     :non-memoizable ,(not memoizable)
                     :non-executable ,(not executable))))

                ;; Theorem Names
                (len-of-cons (symbolicate "ATOMIC-STOBJS" "LEN-OF-CONS"))
                (nth-of-cons (symbolicate "ATOMIC-STOBJS" "NTH-OF-CONS"))

                (recognizer-tp (symbolicate package-witness recognizer "-TP"))
                (recognizer-cr (symbolicate package-witness recognizer "-CR"))
                (recognizer-of-creator (symbolicate package-witness recognizer "-OF-" creator))
                (view-tp (symbolicate package-witness view "-TP"))
                (recognizer-of-view (symbolicate package-witness recognizer "-OF-" view))
                (view-rw (symbolicate package-witness view "-RW"))
                (fixer-rw (symbolicate package-witness fixer "-RW"))

                ;; Epilogue
                (frame-theorems (symbolicate package-witness frame "-THEOREMS"))
                (epilogue
                 `((in-theory
                     (enable ,view-rw
                             ,@(loop$ :for updater :in updaters
                                     :collect (symbolicate package-witness updater "-RW"))))

                   (deflabel ,frame-end)

                   (deftheory-static ,frame-theorems
                     (set-difference-theories
                      (set-difference-theories
                       (current-theory ',frame-end)
                       (current-theory ',frame-begin))
                      ',(append
                         (list recognizer
                               creator
                               view
                               fixer)
                         recognizers
                         accessors
                         updaters)))

                   (in-theory
                     (union-theories (current-theory ',frame-begin)
                                     (theory ',frame-theorems)))))

                (body
                 `(encapsulate ()

                    (local
                      (defthm ,len-of-cons
                        (equal (len (cons a d))
                               (1+ (len d)))))

                    (local
                      (defthm ,nth-of-cons
                        (equal (nth n (cons a d))
                               (if (zp n)
                                   a
                                   (nth (1- n) d)))))

                    ,@(loop$ :for stobj-copy :in stobj-copy-list
                            :as stobj-recognizer :in stobj-recognizers
                            :as field :in fields
                            :as %field :in %fields
                            :as i :from 1 :to (len fields)
                            :when stobj-copy
                            :collect `(local
                                        (defthm ,(symbolicate "ATOMIC-STOBJS" stobj-recognizer "-OF-" stobj-copy "-" i)
                                          (,stobj-recognizer (,stobj-copy ,%field ,field)))))

                    ,@(loop$ :for stobj-copy :in stobj-copy-list
                            :as stobj-coupled-p :in stobj-coupled-p-list
                            :as field :in fields
                            :as %field :in %fields
                            :as i :from 1 :to (len fields)
                            :when (and stobj-copy
                                       stobj-coupled-p)
                            :collect `(local
                                        (defthm ,(symbolicate "ATOMIC-STOBJS" stobj-coupled-p "-OF-" stobj-copy "-" i)
                                          (,stobj-coupled-p (,stobj-copy ,%field ,field)))))

                    ,@(loop$ :for stobj-coupled-p :in stobj-coupled-p-list
                            :as stobj-copy :in stobj-copy-list
                            :as stobj-recognizer :in stobj-recognizers
                            :as field :in fields
                            :as %field :in %fields
                            :as i :from 1 :to (len fields)
                            :when stobj-copy
                            :collect `(local
                                        (defthm ,(symbolicate "ATOMIC-STOBJS" stobj-copy "-RW-" i)
                                          (implies (and (,stobj-recognizer ,field)
                                                        ,@(and stobj-coupled-p
                                                               `((,stobj-coupled-p ,field))))
                                                   (equal (,stobj-copy ,%field ,field)
                                                          ,field)))))

                    ,@(loop$ :for stobj-copy :in stobj-copy-list
                            :as field :in fields
                            :as %field :in %fields
                            :as stobj-recognizer :in stobj-recognizers
                            :as stobj-creator :in stobj-creators
                            :as i :from 1 :to (len fields)
                            :when stobj-copy
                            :collect `(local
                                        (defthm ,(symbolicate "ATOMIC-STOBJS" stobj-copy "-IGNORES-1-" i)
                                          (implies (syntaxp (not (and (consp ,%field)
                                                                      (eq (car ,%field) ',stobj-creator))))
                                                   (equal (,stobj-copy ,%field ,field)
                                                          (,stobj-copy (,stobj-creator) ,field))))))

                    (local
                      (deflabel end-of-prologue))

                    (local
                      (include-book "std/lists/nth" :dir :system))

                    (local
                      (table acl2::theory-invariant-table nil nil :clear))

                    (local
                      (in-theory
                        (union-theories (current-theory 'acl2::ground-zero)
                                        (set-difference-theories
                                         (universal-theory 'end-of-prologue)
                                         (universal-theory ',frame-begin)))))

                    ,@(loop$ :for absstobj-info :in absstobj-info-list
                            :when absstobj-info
                            :collect `(local
                                        (in-theory
                                          (enable ,@(strip-cars (cdr absstobj-info))))))

                    (local
                      (in-theory
                        (enable type-spec-theory)))

                    (local
                      (in-theory
                        (disable len
                                 nth
                                 update-nth)))

                    ;; Field Recognizers
                    ,@(loop$ :for field :in fields
                            :as recognizer :in recognizers
                            :as element-type :in element-types
                            :as stobj-recognizer :in stobj-recognizers
                            :collect `(defthm ,(symbolicate package-witness recognizer "-RW")
                                        (equal (,recognizer ,field)
                                               ,(if stobj-recognizer
                                                    `(,stobj-recognizer ,field)
                                                    (typep$transform field element-type)))))

                    ;; `RECOGNIZER'
                    (defthm ,recognizer-tp
                      (booleanp (,recognizer ,frame))
                      :rule-classes :type-prescription)

                    (defthm ,recognizer-cr
                      (implies (,recognizer ,frame)
                               ,(if (consp fields)
                                    `(and (consp ,frame)
                                          (true-listp ,frame))
                                    `(null ,frame)))
                      :rule-classes :compound-recognizer)

                    (defthm ,recognizer-of-creator
                      (,recognizer (,creator)))

                    ;; Field Accessors
                    ,@(loop$ :for accessor :in accessors
                            :as stobj-recognizer :in stobj-recognizers
                            :as element-type :in element-types
                            :when (not (eq element-type t))
                            :collect `(defthm ,(symbolicate package-witness (or stobj-recognizer "TYPEP$") "-OF-" accessor)
                                        (implies (,recognizer ,frame)
                                                 ,(if stobj-recognizer
                                                      `(,stobj-recognizer (,accessor ,frame))
                                                      (typep$transform `(,accessor ,frame) element-type)))
                                        :rule-classes
                                        (:rewrite
                                         :type-prescription)))

                    ,@(loop$ :for accessor :in accessors
                            :as initial-element-name :in initial-element-names
                            :as stobj-creator :in stobj-creators
                            :collect `(defthm ,(symbolicate package-witness accessor "-OF-" creator)
                                        (equal (,accessor (,creator))
                                               ,(if stobj-creator
                                                    `(,stobj-creator)
                                                    initial-element-name))))

                    ,@(loop$ :for accessor :in accessors
                            :append (loop$ :for updater :in updaters
                                          :as %accessor :in accessors
                                          :as field :in fields
                                          :collect `(defthm ,(symbolicate package-witness accessor "-OF-" updater)
                                                      (equal (,accessor (,updater ,field ,frame))
                                                             ,(if (eq accessor %accessor)
                                                                  field
                                                                  `(,accessor ,frame))))))

                    ;; Field Updaters
                    ,@(loop$ :for updater :in updaters
                            :as field :in fields
                            :as element-type :in element-types
                            :as stobj-recognizer :in stobj-recognizers
                            :collect `(defthm ,(symbolicate package-witness recognizer "-OF-" updater)
                                        (implies ,(cond
                                                    ((equal element-type t)
                                                     `(,recognizer ,frame))
                                                    (stobj-recognizer
                                                     `(and (,recognizer ,frame)
                                                           (,stobj-recognizer ,field)))
                                                    (t
                                                     `(and (,recognizer ,frame)
                                                           ,(typep$transform field element-type))))
                                                 (,recognizer (,updater ,field ,frame)))))

                    ;; `VIEW'
                    (defun ,view ,(append (loop$ :for field :in fields
                                                :as element-type :in element-types
                                                :as stobj-property :in stobj-property-list
                                                :collect (if stobj-property
                                                             element-type
                                                             field))
                                          (list frame))
                      ;; TODO: Eliminate most concrete theorems and just use
                      ;; nth/update-nth for defabsstobj proofs!  This removes
                      ;; dependence of frame on `COPY' and `COUPLEDP' and
                      ;; significantly reduces theorems needed.
                      (declare (xargs :stobjs ,(append (loop$ :for element-type :in element-types
                                                             :as stobj-property :in stobj-property-list
                                                             :when stobj-property
                                                             :collect element-type)
                                                       (list frame))
                                      ,@(let* ((guard (loop$ :for field :in fields
                                                            :as element-type :in element-types
                                                            :as stobj-property :in stobj-property-list
                                                            :when (and (not stobj-property)
                                                                       (not (eq element-type t)))
                                                            :collect (typep$transform field element-type)))
                                               (guard (if (consp (cdr guard))
                                                          (cons 'and guard)
                                                          (car guard))))
                                          (and guard
                                               (list :guard guard)))))
                      ,(let ((conditional (if (consp fields)
                                              `(and ,@(loop$ :for field :in fields
                                                            :as element-type :in element-types
                                                            :as stobj-property :in stobj-property-list
                                                            :collect (if stobj-property
                                                                         `(,(caadr stobj-property) ,element-type)
                                                                         (typep$transform field element-type)))
                                                    (,recognizer ,frame))
                                              `(,recognizer ,frame)))
                             (body (loop$ :with body := frame
                                         :with fields := fields
                                         :with element-types := element-types
                                         :with stobj-property-list := stobj-property-list
                                         :with stobj-copy-list := stobj-copy-list
                                         :with accessors := accessors
                                         :with updaters := updaters
                                         :do
                                         (progn
                                           (cond
                                             ((endp fields)
                                              (return body))
                                             ((car stobj-property-list)
                                              (let* ((st (car element-types))
                                                     (%st (symbolicate st "%" st))
                                                     (stobj-copy (car stobj-copy-list)))
                                                (setq body `(stobj-let ((,%st (,(car accessors) ,frame) ,(car updaters)))
                                                                       (,%st)
                                                                       (,stobj-copy ,%st ,st)
                                                              ,body))))
                                             (t
                                              (setq body `(let ((,frame (,(car updaters) ,(car fields) ,frame)))
                                                            ,body))))
                                           (setq fields (cdr fields))
                                           (setq element-types (cdr element-types))
                                           (setq stobj-property-list (cdr stobj-property-list))
                                           (setq stobj-copy-list (cdr stobj-copy-list))
                                           (setq accessors (cdr accessors))
                                           (setq updaters (cdr updaters))))))
                         `(mbe :logic (if ,conditional
                                          ,body
                                          (,creator))
                               :exec ,body)))

                    (table view ',frame ',view)

                    (defthm ,view-tp
                      ,(if (consp fields)
                           `(and (consp (,view ,@fields ,frame))
                                 (true-listp (,view ,@fields ,frame)))
                           `(null (,view ,@fields ,frame)))
                      :rule-classes :type-prescription)

                    (defthm ,recognizer-of-view
                      (,recognizer (,view ,@fields ,frame)))

                    (defthmd ,view-rw
                      (implies (and (syntaxp (not (and (consp ,frame)
                                                       (eq (car ,frame) ',creator))))
                                    (,recognizer ,frame))
                               (equal (,view ,@fields ,frame)
                                      (,view ,@fields (,creator))))
                      :hints
                      ((acl2::equal-by-nths-hint)))

                    ,@(let ((hypotheses (loop$ :for field :in fields
                                              :as element-type :in element-types
                                              :as stobj-recognizer :in stobj-recognizers
                                              :when (not (eq element-type t))
                                              :collect (if stobj-recognizer
                                                           `(,stobj-recognizer ,field)
                                                           (typep$transform field element-type)))))
                        (loop$ :for field :in fields
                              :as accessor :in accessors
                              :as stobj-copy :in stobj-copy-list
                              :as stobj-creator :in stobj-creators
                              :as initial-element-name :in initial-element-names
                              :collect `(defthm ,(symbolicate package-witness accessor "-OF-" view)
                                          (implies ,(if hypotheses
                                                        `(and (,recognizer ,frame)
                                                              ,@hypotheses)
                                                        `(,recognizer ,frame))
                                                   (equal (,accessor (,view ,@fields ,frame))
                                                          ,(if stobj-copy
                                                               `(,stobj-copy ,(if stobj-creator
                                                                                  `(,stobj-creator)
                                                                                  initial-element-name)
                                                                             ,field)
                                                               field))))))

                    ,@(let ((arguments (loop$ :for accessor :in accessors
                                             :collect `(,accessor ,frame))))
                        (loop$ :for updater :in updaters
                              :as element-type :in element-types
                              :as stobj-recognizer :in stobj-recognizers
                              :as stobj-coupled-p :in stobj-coupled-p-list
                              :as field :in fields
                              :as i :from 0 :to (1- (len fields))
                              :collect `(defthmd ,(symbolicate package-witness updater "-RW")
                                          (implies (and (syntaxp (not (and (consp ,frame)
                                                                           (eq (car ,frame) ',view))))
                                                        (,recognizer ,frame)
                                                        ,@(and (not (eq element-type t))
                                                               `(,(if stobj-recognizer
                                                                      `(,stobj-recognizer ,field)
                                                                      (typep$transform field element-type))))
                                                        ,@(and stobj-coupled-p
                                                               `((,stobj-coupled-p ,field)))
                                                        ,@(loop$ :for arg :in arguments
                                                                :as stobj-coupled-p :in stobj-coupled-p-list
                                                                :as %field :in fields
                                                                :when (and stobj-coupled-p
                                                                           (not (eq field %field)))
                                                                :collect `(,stobj-coupled-p ,arg)))
                                                   (equal (,updater ,field ,frame)
                                                          (,view ,@(update-nth i field arguments) ,frame)))
                                          :hints
                                          ((acl2::equal-by-nths-hint)))))

                    ,@(let ((hypotheses (loop$ :for field :in fields
                                              :as element-type :in element-types
                                              :as stobj-recognizer :in stobj-recognizers
                                              :when (not (eq element-type t))
                                              :collect (if stobj-recognizer
                                                           `(,stobj-recognizer ,field)
                                                           (typep$transform field element-type)))))
                        (loop$ :for updater :in updaters
                              :as element-type :in element-types
                              :as stobj-recognizer :in stobj-recognizers
                              :as stobj-coupled-p :in stobj-coupled-p-list
                              :as %field :in %fields
                              :as i :from 0 :to (1- (len fields))
                              :collect `(defthm ,(symbolicate package-witness updater "-OF-" view)
                                          (implies ,(if (or (not (eq element-type t))
                                                            hypotheses
                                                            stobj-coupled-p)
                                                        `(and (,recognizer,frame)
                                                              ,@(and (not (eq element-type t))
                                                                     `(,(if stobj-recognizer
                                                                            `(,stobj-recognizer ,%field)
                                                                            (typep$transform %field element-type))))
                                                              ,@hypotheses
                                                              ,@(and stobj-coupled-p
                                                                     `((,stobj-coupled-p ,%field))))
                                                        `(,recognizer,frame))
                                                   (equal (,updater ,%field (,view ,@fields ,frame))
                                                          (,view ,@(update-nth i %field fields) ,frame)))
                                          :hints
                                          ((acl2::equal-by-nths-hint)))))

                    ;; `FIXER'
                    (defun-inline ,fixer (,frame)
                      (declare (xargs :stobjs ,frame))
                      (mbe :logic (if (,recognizer ,frame)
                                      ,frame
                                      (,creator))
                           :exec ,frame))

                    (table fixer ',frame ',fixer)

                    (defthm ,fixer-rw
                      ,(let* ((hypotheses (loop$ :for accessor :in accessors
                                                :as stobj-coupled-p :in stobj-coupled-p-list
                                                :when stobj-coupled-p
                                                :collect `(,stobj-coupled-p (,accessor ,frame))))
                              (hypotheses (if (consp (cdr hypotheses))
                                              (cons 'and hypotheses)
                                              (car hypotheses))))
                         (if hypotheses
                             `(implies ,hypotheses
                                       (equal (,fixer ,frame)
                                              (,view ,@(loop$ :for accessor :in accessors
                                                             :collect `(,accessor ,frame))
                                                     ,frame)))
                             `(equal (,fixer ,frame)
                                     (,view ,@(loop$ :for accessor :in accessors
                                                    :collect `(,accessor ,frame))
                                            ,frame))))
                      :hints
                      ((acl2::equal-by-nths-hint))))))

           `(progn
              ,@prologue

              ,body

              ,@epilogue

              (table package-witness ',frame ',package-witness)))))))
