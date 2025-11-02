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
(include-book "../accessors/top")
(include-book "../utilities/top")
(include-book "copy")
(include-book "frame$c")

(defthm symbol-list-listp{compound-recognizer}
  ;; TODO: move this. where?
  (implies (symbol-list-listp x)
           (true-listp x))
  :rule-classes :compound-recognizer)

(deflabel define-frame-begin)


;;;; Constants
(defconst define-frame::*field-keywords$a*
  '(:recognizer :fixer :stobj :initial-element :accessor :updater))

(defconst define-frame::*body-keywords$a*
  '(:recognizer :creator :fixer :testp :debug))

(defconst define-frame::*field-keywords$abs*
  '(:accessor :updater :stobj))

(defconst define-frame::*body-keywords$abs*
  '(:logic :exec :recognizer :creator :fixer
    :executable :debug))

(defconst define-frame::*field-keywords*
  '(:element-type :recognizer :fixer :stobj
    :initial-element :accessor :updater))

(defconst define-frame::*body-keywords*
  '(:inline :memoizable :executable
    :recognizer :creator :fixer
    :logic :exec :debug))


;;;; `DEFINE-FRAME$C'
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


;;;; `VALID-FRAME$A' Predicates
(defun valid-frame$a-descriptor-p (descriptor)
  (declare (xargs :guard t))
  (and (consp descriptor)
       (let ((name (car descriptor))
             (kvl (cdr descriptor)))
         (and (symbolp name)
              (keyword-value-listp kvl)
              (subsetp (evens kvl) define-frame::*field-keywords$a*
                       :test 'eq)
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

(defun valid-frame$a-body-p (body)
  (declare (xargs :guard t))
  (and (true-listp body)
       (if (consp (car body))
           (and (valid-frame$a-descriptor-p (car body))
                (valid-frame$a-body-p (cdr body)))
           (and (keyword-value-listp body)
                (subsetp (evens body) define-frame::*body-keywords$a*
                         :test 'eq)
                (let ((recognizer (cadr (assoc-keyword :recognizer body)))
                      (creator (cadr (assoc-keyword :creator body)))
                      (fixer (cadr (assoc-keyword :fixer body)))
                      (testp (cadr (assoc-keyword :testp body)))
                      (debug (cadr (assoc-keyword :debug body))))
                  (and (symbolp recognizer)
                       (symbolp creator)
                       (symbolp fixer)
                       (booleanp testp)
                       (booleanp debug)))))))

(defun valid-frame$a-form-p (form)
  (declare (xargs :guard t))
  (and (true-listp form)
       (eq (car form) 'define-frame$a)
       (symbolp (cadr form))
       (valid-frame$a-body-p (cddr form))))


;;;; Parse `DEFINE-FRAME$A' Forms
(defun define-frame::split-body$a (body)
  (declare (xargs :guard (valid-frame$a-body-p body)))
  (cond
    ((atom body)
     (mv nil nil))
    ((atom (car body))
     (mv nil body))
    (t
     (mv-let (fds kvl)
             (define-frame::split-body$a (cdr body))
       (mv (cons (car body) fds) kvl)))))

(defun define-frame::parse-fds$a (frame fds)
  (declare (xargs :guard (and (symbolp frame)
                              (valid-frame$a-body-p fds)
                              (alistp fds))))
  (if (consp fds)
      (mv-let (fields recognizers fixers
                      stobjs initial-elements
                      accessors updaters)
              (define-frame::parse-fds$a frame (cdr fds))
        (let* ((descriptor (car fds))
               (field (car descriptor))
               (kvl (cdr descriptor))
               (recognizer (cadr (assoc-keyword :recognizer kvl)))
               (fixer (cadr (assoc-keyword :fixer kvl)))
               (stobj (cadr (assoc-keyword :stobj kvl)))
               (initial-element (cadr (assoc-keyword :initial-element kvl)))
               (accessor (or (cadr (assoc-keyword :accessor kvl))
                             (symbolicate frame frame '- field)))
               (updater (or (cadr (assoc-keyword :updater kvl))
                            (symbolicate frame frame '- field '-set))))
          (mv (cons field fields)
              (cons recognizer recognizers)
              (cons fixer fixers)
              (cons stobj stobjs)
              (cons initial-element initial-elements)
              (cons accessor accessors)
              (cons updater updaters))))
      (mv nil nil nil
          nil nil
          nil nil)))

(defun define-frame::parse-kvl$a (frame kvl)
  (declare (xargs :guard (and (symbolp frame)
                              (valid-frame$a-body-p kvl)
                              (keyword-value-listp kvl))))
  (let* ((recognizer (or (cadr (assoc-keyword :recognizer kvl))
                         (symbolicate frame frame (make-predicate-suffix frame))))
         (creator (or (cadr (assoc-keyword :creator kvl))
                      (symbolicate frame 'create- frame)))
         (fixer (or (cadr (assoc-keyword :fixer kvl))
                    (symbolicate frame frame '-fix)))
         (testp (cadr (assoc-keyword :testp kvl)))
         (debug (cadr (assoc-keyword :debug kvl))))
    (mv recognizer creator fixer
        testp debug)))

(defun define-frame::parse-form$a (form)
  (declare (xargs :guard (valid-frame$a-form-p form)))
  (let ((frame (cadr form))
        (body (cddr form)))
    (mv-let (fds kvl)
            (define-frame::split-body$a body)
      (mv-let (recognizer creator fixer
                          testp debug)
              (define-frame::parse-kvl$a frame kvl)
        (mv-let (fields recognizers fixers
                        stobjs initial-elements
                        accessors updaters)
                (define-frame::parse-fds$a frame fds)
          (mv recognizer creator fixer
              fields recognizers fixers stobjs
              initial-elements accessors updaters
              testp debug))))))


;;;; `DEFINE-FRAME$A'
(defun make-rewrite-corollaries (clauses)
  ;; TODO: move this. where?
  (declare (xargs :guard (true-listp clauses)))
  (and (consp clauses)
       (cons (list :rewrite :corollary (car clauses))
             (make-rewrite-corollaries (cdr clauses)))))

(defmacro define-frame$a (&whole form frame &body body)
  (declare (xargs :guard (valid-frame$a-form-p form))
           (ignore body))
  (mv-let (recognizer creator fixer
                      fields recognizers fixers stobjs
                      initial-elements accessors updaters
                      testp debug)
          (define-frame::parse-form$a form)
    `(with-output
       ,@(and (not debug)
              '#!acl2(:off (warning! observation prove event history proof-tree)
                           :summary-off (rules)
                           :gag-mode t))

       (make-event
         (let* ((frame ',frame)
                (recognizer ',recognizer)
                (creator ',creator)
                (fixer ',fixer)
                (fields ',fields)
                (recognizers ',recognizers)
                (fixers ',fixers)
                (stobjs ',stobjs)
                (initial-elements ',initial-elements)
                (accessors ',accessors)
                (updaters ',updaters)

                (view (symbolicate frame frame '-view))
                (world (w state))
                (stobj$a-property-alist (stobj$a-property-alist world))
                (stobj$a-lookup-alist (stobj$a-lookup-alist world))
                (stobjs$a (loop$ :for stobj :in stobjs
                                :collect (getprop stobj 'stobj$a
                                                  nil 'acl2::current-acl2-world
                                                  stobj$a-lookup-alist)))
                (stobj$a-properties (loop$ :for stobj$a :in stobjs$a
                                          :collect (getprop stobj$a 'stobj$a
                                                            nil 'acl2::current-acl2-world
                                                            stobj$a-property-alist)))
                (recognizers$a (loop$ :for stobj$a :in stobjs$a
                                     :as recognizer :in recognizers
                                     :as property$a :in stobj$a-properties
                                     :collect (if stobj$a
                                                  (first (second property$a))
                                                  recognizer)))
                (fixers$a (loop$ :for stobj$a :in stobjs$a
                                :as fixer :in fixers
                                :as property$a :in stobj$a-properties
                                :collect (if stobj$a
                                             (third (second property$a))
                                             fixer)))
                ;; TODO: ensure args are ignored if stobj is provided
                (initial-elements$a initial-elements)
                (initial-element-names (loop$ :for accessor :in accessors
                                             :collect (symbolicate frame '* accessor '-initial-element*)))

                (booleanp-of-recognizers (loop$ :for field :in fields
                                               :as stobj :in stobjs
                                               :as recognizer$a :in recognizers$a
                                               :when recognizer$a
                                               :collect
                                               `(booleanp (,recognizer$a ,field))))
                (recognizers-of-fixers (loop$ :for recognizer$a :in recognizers$a
                                             :as fixer$a :in fixers$a
                                             :as field :in fields
                                             :when recognizer$a
                                             :collect `(,recognizer$a (,fixer$a ,field))))
                (fixers-when-recognizers (loop$ :for field :in fields
                                               :as recognizer$a :in recognizers$a
                                               :as fixer$a :in fixers$a
                                               :when recognizer$a
                                               :collect `(implies (,recognizer$a ,field)
                                                                  (equal (,fixer$a ,field) ,field))))
                (fixers-when-not-recognizers (loop$ :for field :in fields
                                                   :as stobj :in stobjs
                                                   :as recognizer$a :in recognizers$a
                                                   :as fixer$a :in fixers$a
                                                   :as element :in initial-elements$a
                                                   :as name :in initial-element-names
                                                   :when recognizer$a
                                                   :collect `(implies (not (,recognizer$a ,field))
                                                                      (equal (,fixer$a ,field) ,(if (or ',testp
                                                                                                        stobj)
                                                                                                    element
                                                                                                    name)))))
                (frame-field-guard
                 `(defthm ,(symbolicate frame frame '-field-guard)
                    (and ,@booleanp-of-recognizers
                         ,@(loop$ :for recognizer$a :in recognizers$a
                                 :as stobj :in stobjs
                                 :as element :in initial-elements$a
                                 :as name :in initial-element-names
                                 :when recognizer$a
                                 :collect (list recognizer$a (if (or ',testp
                                                                     stobj)
                                                                 element
                                                                 name)))
                         ,@recognizers-of-fixers
                         ,@fixers-when-recognizers
                         ,@fixers-when-not-recognizers)
                    :rule-classes
                    (,@(loop$ :for clause :in booleanp-of-recognizers
                             :collect (list :rewrite :corollary clause))
                       ,@(loop$ :for clause :in recognizers-of-fixers
                               :collect (list :rewrite :corollary clause))
                       ,@(loop$ :for clause :in fixers-when-recognizers
                               :collect (list :rewrite :corollary clause))
                       ,@(loop$ :for clause :in fixers-when-not-recognizers
                               :collect (list :rewrite :corollary clause)))
                    ,@(and ',(not testp)
                           `(:hints
                             (("Goal"
                               :in-theory (disable ,@(remove nil recognizers$a)
                                                   ,@(remove nil fixers$a))))))))
                (view-guard (let ((guard (loop$ :for recognizer :in recognizers
                                               :as field :in fields
                                               :when recognizer
                                               :collect (list recognizer field))))
                              (if (consp guard)
                                  `(and ,@guard
                                        (,recognizer ,frame))
                                  `(,recognizer ,frame))))
                (view-body (loop$ :with body := frame
                                 :with fields := (reverse fields)
                                 :with updaters := (reverse updaters)
                                 :do
                                 (progn
                                   (if (consp fields)
                                       (setq body `(let ((,frame (,(car updaters) ,(car fields) ,frame)))
                                                     ,body))
                                       (return body))
                                   (setq fields (cdr fields))
                                   (setq updaters (cdr updaters)))))

                (frame-begin (symbolicate frame frame '-begin))
                (frame-end (symbolicate frame frame '-end))
                (frame-theorems (symbolicate frame frame '-theorems))
                (frame-definitions (symbolicate frame frame '-definitions))
                (frame-aggressive (symbolicate frame frame '-aggressive))

                (defconsts (loop$ :for name :in initial-element-names
                                 :as element :in initial-elements$a
                                 :collect `(defconst ,name ',element)))

                (%fields (loop$ :for field :in fields
                               :collect (symbolicate frame '% field)))
                (%frame (symbolicate frame '% frame))
                (frame-equal (symbolicate frame frame '-equal))
                (updater-rewrite-theorem-names (loop$ :for updater :in updaters
                                                     :collect (symbolicate frame updater '{rewrite})))
                (accessor-when-not-recognizer-theorem-names
                 (loop$ :for accessor :in accessors
                       :collect (symbolicate frame accessor '-when-not- recognizer)))
                (view-when-not-recognizer$a-theorem-names
                 (loop$ :for field :in fields
                       :as recognizer$a :in recognizers$a
                       :collect (and recognizer$a
                                     (symbolicate frame view '-when-not- recognizer$a '-of- field))))
                (view{rewrite} (symbolicate frame view '{rewrite}))
                (view-collapse (symbolicate frame view '-collapse))

                (prologue
                 `((deflabel ,frame-begin)

                   ,@defconsts))
                (epilogue
                 `((deflabel ,frame-end)

                   (deftheory-static ,frame-theorems
                     (set-difference-theories
                      (set-difference-theories
                       (current-theory ',frame-end)
                       (current-theory ',frame-begin))
                      (function-theory ',frame-end)))

                   (deftheory-static ,frame-definitions
                     (set-difference-theories
                      (set-difference-theories
                       (current-theory ',frame-end)
                       (current-theory ',frame-begin))
                      (theory ',frame-theorems)))

                   (deftheory-static ,frame-aggressive
                     ',(append accessor-when-not-recognizer-theorem-names
                               (list view-collapse)
                               (remove nil view-when-not-recognizer$a-theorem-names)))

                   (in-theory
                     (union-theories (current-theory ',frame-begin)
                                     (theory ',frame-theorems)))))
                (body
                 `(with-books (("std/lists/nth" :dir :system))

                    (local
                      (in-theory
                        (disable nth
                                 update-nth
                                 acl2::nth-when-zp
                                 )))

                    ,@(and (remove nil recognizers$a :test 'eq)
                           `((local
                               ,frame-field-guard)))

                    ,@(and (and ',(not testp)
                                (remove nil recognizers$a :test 'eq))
                           `((local
                               (in-theory
                                 (disable ,@(loop$ :for recognizer$a :in recognizers$a
                                                  :when recognizer$a
                                                  :collect (list :d recognizer$a))
                                          ,@(loop$ :for fixer$a :in fixers$a
                                                  :when fixer$a
                                                  :collect (list :d fixer$a)))))))

                    (defun ,recognizer (,frame)
                      (declare (xargs :guard t))
                      (and (true-listp ,frame)
                           (= (len ,frame) ,(len fields))
                           ,@(loop$ :for i :from 0 :to (1- (len fields))
                                   :as recognizer$a :in recognizers$a
                                   :when recognizer$a
                                   :collect `(,recognizer$a (nth ,i ,frame)))))

                    (defthm ,(symbolicate frame recognizer '{compound-recognizer})
                      (implies (,recognizer ,frame)
                               ,(if (zp (len fields))
                                    `(not ,frame)
                                    `(and (consp ,frame)
                                          (true-listp ,frame))))
                      :rule-classes :compound-recognizer)

                    (defun ,creator ()
                      (declare (xargs :guard t))
                      (list ,@(loop$ :for element :in initial-elements$a
                                    :as stobj :in stobjs
                                    :as name :in initial-element-names
                                    :collect (if (or ',testp
                                                     stobj)
                                                 element
                                                 name))))

                    (local
                      (defthm nth-of-list
                        (implies (and (natp n)
                                      (< n ,(len fields)))
                                 (equal (nth n (list ,@fields))
                                        (case n
                                          ,@(loop$ :for i :from 0 :to (1- (len fields))
                                                  :as field :in fields
                                                  :collect (list i field)))))
                        :hints
                        (("Goal"
                          :in-theory (enable nth)))))

                    (in-theory
                      (disable (:e ,creator)))

                    (defthm ,(symbolicate frame recognizer '-of- creator)
                      (,recognizer (,creator)))

                    (defun ,fixer (,frame)
                      (declare (xargs :guard (,recognizer ,frame)))
                      (if (,recognizer ,frame)
                          ,frame
                          (,creator)))

                    (local
                      (defthm ,(symbolicate frame 'nth-of- fixer)
                        (implies (and (natp n)
                                      (< n ,(len fields)))
                                 (equal (nth n (,fixer ,frame))
                                        (case n
                                          ,@(loop$ :for i :from 0 :to (1- (len fields))
                                                  :as fixer$a :in fixers$a
                                                  :as element :in initial-elements$a
                                                  :as stobj :in stobjs
                                                  :as name :in initial-element-names
                                                  :collect `(,i (if (,recognizer ,frame)
                                                                    ,(if fixer$a
                                                                         `(,fixer$a (nth ,i ,frame))
                                                                         `(nth ,i ,frame))
                                                                    ,(if (or ',testp
                                                                             stobj)
                                                                         element
                                                                         name)))))))))

                    (defthm ,(symbolicate frame recognizer '-of- fixer)
                      (,recognizer (,fixer ,frame)))

                    (defthm ,(symbolicate frame fixer '-when- recognizer)
                      (implies (,recognizer ,frame)
                               (equal (,fixer ,frame) ,frame)))

                    (defthm ,(symbolicate frame fixer '-when-not- recognizer)
                      (implies (not (,recognizer ,frame))
                               (equal (,fixer ,frame) (,creator))))

                    (local
                      (defthm ,(symbolicate frame 'len-of- fixer)
                        (equal (len (,fixer ,frame)) ,(len fields))))

                    (in-theory
                      (disable ,fixer))

                    ,@(loop$ :for i :from 0 :to (1- (len fields))
                            :as fixer$a :in fixers$a
                            :as accessor :in accessors
                            :collect
                            `(defun ,accessor (,frame)
                               (declare (xargs :guard (,recognizer ,frame)))
                               (let ((,frame (,fixer ,frame)))
                                 ,(if fixer$a
                                      `(,fixer$a (nth ,i ,frame))
                                      `(nth ,i ,frame)))))

                    ,@(loop$ :for theorem-name :in accessor-when-not-recognizer-theorem-names
                            :as accessor :in accessors
                            :as stobj :in stobjs
                            :as element :in initial-elements$a
                            :as name :in initial-element-names
                            :collect
                            `(defthmd ,theorem-name
                               (implies (not (,recognizer ,frame))
                                        (equal (,accessor ,frame) ,(if (or ',testp
                                                                           stobj)
                                                                       element
                                                                       name)))))

                    ,@(loop$ :for accessor :in accessors
                            :collect `(defthm ,(symbolicate frame accessor '-of- fixer)
                                        (equal (,accessor (,fixer ,frame))
                                               (,accessor ,frame))))

                    ,@(loop$ :for i :from 0 :to (1- (len fields))
                            :as field :in fields
                            :as updater :in updaters
                            :as field-recognizer :in recognizers
                            :as fixer$a :in fixers$a
                            :collect
                            `(defun ,updater (,field ,frame)
                               (declare (xargs :guard ,(if field-recognizer
                                                           `(and (,field-recognizer ,field)
                                                                 (,recognizer ,frame))
                                                           `(,recognizer ,frame))))
                               (let (,@(and fixer$a
                                            `((,field (,fixer$a ,field))))
                                     (,frame (,fixer ,frame)))
                                 (update-nth ,i ,field ,frame))))

                    ,@(loop$ :for updater :in updaters
                            :as field :in fields
                            :collect `(defthm ,(symbolicate frame updater '-of- fixer)
                                        (equal (,updater ,field (,fixer ,frame))
                                               (,updater ,field ,frame))))

                    (defun ,view (,@fields ,frame)
                      (declare (xargs :guard ,view-guard))
                      ,view-body)

                    ,@(loop$ :for recognizer$a :in recognizers$a
                            :as accessor :in accessors
                            :when recognizer$a
                            :collect `(defthm ,(symbolicate frame recognizer$a '-of- accessor)
                                        (,recognizer$a (,accessor ,frame))))

                    ,@(loop$ :for accessor :in accessors
                            :as element :in initial-elements$a
                            :as stobj :in stobjs
                            :as name :in initial-element-names
                            :collect `(defthm ,(symbolicate frame accessor '-of- creator)
                                        (equal (,accessor (,creator))
                                               ,(if (or ',testp
                                                        stobj)
                                                    element
                                                    name))))

                    (defthm ,(symbolicate frame recognizer '-of- view)
                      (,recognizer (,view ,@fields ,frame))
                      :hints
                      (("Goal"
                        :cases ((,recognizer ,frame)))))

                    (defthmd ,view{rewrite}
                      (implies (syntaxp (not (and (consp ,frame)
                                                  (eq (car ,frame) ',creator)
                                                  (null (cdr ,frame)))))
                               (equal (,view ,@fields ,frame)
                                      (,view ,@fields (,creator))))
                      :hints
                      ((acl2::equal-by-nths-hint)
                       ("Subgoal 1"
                        :cases ((,recognizer ,frame)))))

                    (local
                      (defthm ,(symbolicate frame recognizer '-of-update-nth)
                        (implies (,recognizer ,frame)
                                 (and ,@(loop$ :for i :from 0 :to (1- (len fields))
                                              :as field :in fields
                                              :as recognizer$a :in recognizers$a
                                              :collect
                                              (if recognizer$a
                                                  `(equal (,recognizer (update-nth ,i ,field ,frame))
                                                          (,recognizer$a ,field))
                                                  `(,recognizer (update-nth ,i ,field ,frame))))))))

                    (local
                      (defthm ,(symbolicate frame recognizer '{forward-chaining})
                        (implies (,recognizer ,frame)
                                 (and ,@(loop$ :for i :from 0 :to (1- (len fields))
                                              :as recognizer$a :in recognizers$a
                                              :when recognizer$a
                                              :collect
                                              `(,recognizer$a (nth ,i ,frame)))))
                        :rule-classes :forward-chaining))

                    (defthmd ,view-collapse
                      (equal (,view ,@(loop$ :for accessor :in accessors
                                            :collect (list accessor frame))
                                    ,%frame)
                             (,fixer ,frame))
                      :hints
                      ((acl2::equal-by-nths-hint)
                       ("Subgoal 1"
                        :cases ((,recognizer ,frame)
                                (,recognizer ,%frame))
                        :in-theory (disable acl2::nth-when-too-large-cheap
                                            ,fixer
                                            ,recognizer))
                       ("Subgoal 1.2"
                        :cases ,(loop$ :for i :from 0 :to (1- (len fields))
                                      :collect `(equal n ,i)))))

                    ,@(loop$ :for i :from 0 :to (1- (len fields))
                            :as field :in fields
                            :as recognizer$a :in recognizers$a
                            :as stobj :in stobjs
                            :as element :in initial-elements$a
                            :as name :in initial-element-names
                            :as theorem-name :in view-when-not-recognizer$a-theorem-names
                            :when recognizer$a
                            :collect
                            `(defthmd ,theorem-name
                               (implies (and (syntaxp (not (quotep ,field)))
                                             (not (,recognizer$a ,field)))
                                        (equal (,view ,@fields ,frame)
                                               (,view ,@(update-nth i (if (or ',testp
                                                                              stobj)
                                                                          element
                                                                          name)
                                                                    fields)
                                                      ,frame)))
                               :hints
                               ((acl2::equal-by-nths-hint)
                                ("Subgoal 1"
                                 :cases ((,recognizer ,frame))))))

                    ,@(loop$ :for accessor :in accessors
                            :as field :in fields
                            :as fixer$a :in fixers$a
                            :collect `(defthm ,(symbolicate frame accessor '-of- view)
                                        (equal (,accessor (,view ,@fields ,frame))
                                               ,(if fixer$a
                                                    `(,fixer$a ,field)
                                                    field))))

                    ,@(let ((args (loop$ :for accessor :in accessors
                                        :collect (list accessor frame))))
                        (loop$ :for i :from 0 :to (1- (len fields))
                              :as field :in fields
                              :as name :in updater-rewrite-theorem-names
                              :as updater :in updaters
                              :collect `(defthmd ,name
                                          (implies (syntaxp (not (and (consp ,frame)
                                                                      (eq (car ,frame) ',view))))
                                                   (equal (,updater ,field ,frame)
                                                          (,view ,@(update-nth i field args) ,frame)))
                                          :hints
                                          ((acl2::equal-by-nths-hint)
                                           ("Subgoal 1"
                                            :cases ((,recognizer ,frame)))))))

                    ,@(loop$ :for i :from 0 :to (1- (len fields))
                            :as updater :in updaters
                            :as %field :in %fields
                            :collect `(defthm ,(symbolicate frame updater '-of- view)
                                        (equal (,updater ,%field (,view ,@fields ,frame))
                                               (,view ,@(update-nth i %field fields) ,frame))
                                        :hints
                                        ((acl2::equal-by-nths-hint)
                                         ("Subgoal 1"
                                          :cases ((,recognizer ,frame))))))

                    (defun-nx ,frame-equal (,%frame ,frame)
                      (declare (xargs :guard t
                                      :verify-guards nil))
                      (and (,recognizer ,%frame)
                           (,recognizer ,frame)
                           ,@(loop$ :for accessor :in accessors
                                   :collect `(equal (,accessor ,%frame) (,accessor ,frame)))))

                    (defthm ,(symbolicate frame frame-equal '{forward-chaining})
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
                       ("Subgoal 1"
                        :cases ,(loop$ :for i :from 0 :to (1- (len fields))
                                      :collect `(equal n ,i)))))

                    (in-theory
                      (e/d (,view{rewrite}
                            ,@updater-rewrite-theorem-names)
                           ((:d ,recognizer)
                            (:d ,creator)
                            (:d ,fixer)
                            ,@(loop$ :for accessor :in accessors
                                    :collect (list :d accessor))
                            ,@(loop$ :for updater :in updaters
                                    :collect (list :d updater))
                            (:d ,view))))))
                (stobj$a-property `(stobj$a-property (,recognizer
                                                      ,creator
                                                      ,fixer
                                                      ,frame-equal)
                                                     (,recognizers
                                                      ,fixers
                                                      ,fields
                                                      ,initial-element-names
                                                      ,stobjs
                                                      ,accessors
                                                      ,updaters
                                                      (,view)))))

           `(progn
              ,@prologue

              ,body

              ,@epilogue

              (table stobj$a
                     'stobj$a-property-alist
                     (putprop ',',frame
                              'stobj$a
                              ',stobj$a-property
                              (stobj$a-property-alist world)))))))))


;;;; `DEFINE-FRAME$CORR'
(defmacro define-frame$corr (frame
                             &key
                               (logic 'nil)
                               (exec 'nil)

                               (debug 'nil))
  (declare (xargs :guard (and (symbolp frame)
                              (symbolp logic)
                              (symbolp exec)
                              (booleanp debug))))
  `(with-output
     ,@(and (not debug)
            '#!acl2(:off (warning! observation prove event history proof-tree)
                         :summary-off (rules)
                         :gag-mode t))

     (make-event
       (let* ((frame ',frame)
              (logic ',logic)
              (exec ',exec)
              (frame$a (or logic
                           (symbolicate frame frame '$a)))
              (frame$c (or exec
                           (symbolicate frame frame '$c)))
              (frame$corr (symbolicate frame frame '$corr))
              (recognizer$c (stobj-recognizer frame$c))
              (recognizer$a (stobj$a-recognizer frame$a))
              (accessors$c (stobj$c-frame-accessors frame$c))
              (accessors$a (stobj$a-frame-accessors frame$a)))

         `(defun-nx ,frame$corr (,frame$c ,frame$a)
            (declare (xargs :stobjs ,frame$c
                            :guard (,recognizer$a ,frame$a)
                            :verify-guards nil))
            (and (,recognizer$c ,frame$c)
                 (,recognizer$a ,frame$a)
                 ,@(loop$ :for accessor$c :in accessors$c
                         :as accessor$a :in accessors$a
                         :collect `(equal (,accessor$c ,frame$c) (,accessor$a ,frame$a)))))))))


;;;; `VALID-FRAME$ABS' Predicates
(defun valid-frame$abs-descriptor-p (descriptor)
  (declare (xargs :guard t))
  (and (consp descriptor)
       (let ((name (car descriptor))
             (kvl (cdr descriptor)))
         (and (symbolp name)
              (keyword-value-listp kvl)
              (subsetp (evens kvl) define-frame::*field-keywords$abs*
                       :test 'eq)
              (let ((accessor (cadr (assoc-keyword :accessor kvl)))
                    (updater (cadr (assoc-keyword :updater kvl)))
                    (stobj (cadr (assoc-keyword :stobj kvl))))
                (and (symbolp accessor)
                     (symbolp updater)
                     (symbolp stobj)))))))

(defun valid-frame$abs-body-p (body)
  (declare (xargs :guard t))
  (and (true-listp body)
       (if (consp (car body))
           (and (valid-frame$abs-descriptor-p (car body))
                (valid-frame$abs-body-p (cdr body)))
           (and (keyword-value-listp body)
                (subsetp (evens body) define-frame::*body-keywords$abs*
                         :test 'eq)
                (let ((frame$a (cadr (assoc-keyword :logic body)))
                      (frame$c (cadr (assoc-keyword :exec body)))
                      (recognizer (cadr (assoc-keyword :recognizer body)))
                      (creator (cadr (assoc-keyword :creator body)))
                      (fixer (cadr (assoc-keyword :fixer body)))
                      (executable (cadr (assoc-keyword :executable body)))
                      (debug (cadr (assoc-keyword :debug body))))
                  (and (symbolp frame$a)
                       (symbolp frame$c)
                       (symbolp recognizer)
                       (symbolp creator)
                       (symbolp fixer)
                       (booleanp executable)
                       (booleanp debug)))))))

(defun valid-frame$abs-form-p (form)
  (declare (xargs :guard t))
  (and (true-listp form)
       (eq (car form) 'define-frame$abs)
       (symbolp (cadr form))
       (valid-frame$abs-body-p (cddr form))))


;;;; Parse `DEFINE-FRAME$ABS' Forms
(defun define-frame::split-body$abs (body)
  (declare (xargs :guard (valid-frame$abs-body-p body)))
  (cond
    ((atom body)
     (mv nil nil))
    ((atom (car body))
     (mv nil body))
    (t
     (mv-let (fds kvl)
             (define-frame::split-body$abs (cdr body))
       (mv (cons (car body) fds) kvl)))))

(defun define-frame::parse-fds$abs (frame fds)
  (declare (xargs :guard (and (symbolp frame)
                              (valid-frame$abs-body-p fds)
                              (alistp fds))))
  (if (consp fds)
      (mv-let (accessors updaters stobjs)
              (define-frame::parse-fds$abs frame (cdr fds))
        (let* ((descriptor (car fds))
               (field (car descriptor))
               (kvl (cdr descriptor))
               (accessor (or (cadr (assoc-keyword :accessor kvl))
                             (symbolicate frame frame '- field)))
               (updater (or (cadr (assoc-keyword :updater kvl))
                            (symbolicate frame frame '- field '-set)))
               (stobj (cadr (assoc-keyword :stobj kvl))))
          (mv (cons accessor accessors)
              (cons updater updaters)
              (cons stobj stobjs))))
      (mv nil nil nil)))

(defun define-frame::parse-kvl$abs (frame kvl)
  (declare (xargs :guard (and (symbolp frame)
                              (valid-frame$abs-body-p kvl)
                              (keyword-value-listp kvl))))
  (let* ((executable (cadr (assoc-keyword :executable kvl)))
         (frame$a (or (cadr (assoc-keyword :logic kvl))
                      (symbolicate frame frame '$a)))
         (frame$c (or (cadr (assoc-keyword :exec kvl))
                      (symbolicate frame frame '$c)))
         (recognizer (or (cadr (assoc-keyword :recognizer kvl))
                         (symbolicate frame frame (make-predicate-suffix frame))))
         (creator (or (cadr (assoc-keyword :creator kvl))
                      (symbolicate frame 'create- frame)))
         (fixer (or (cadr (assoc-keyword :fixer kvl))
                    (symbolicate frame frame '-fix)))
         (debug (cadr (assoc-keyword :debug kvl))))
    (mv frame$a frame$c recognizer creator fixer
        executable debug)))

(defun define-frame::parse-form$abs (form)
  (declare (xargs :guard (valid-frame$abs-form-p form)))
  (let ((frame (cadr form))
        (body (cddr form)))
    (mv-let (fds kvl)
            (define-frame::split-body$abs body)
      (mv-let (frame$a frame$c recognizer creator fixer
                       executable debug)
              (define-frame::parse-kvl$abs frame kvl)
        (mv-let (accessors updaters stobjs)
                (define-frame::parse-fds$abs frame fds)
          (mv frame$a frame$c recognizer creator fixer
              accessors updaters stobjs
              executable debug))))))


;;;; `DEFINE-FRAME$ABS'
(defun define-frame::accessor-correspondence-theorems$abs
    (frame$corr frame$c frame recognizer$a
     accessors accessors$c accessors$a)
  (declare (xargs :guard (and (symbolp frame$corr)
                              (symbolp frame$c)
                              (symbolp frame)
                              (symbolp recognizer$a)
                              (symbol-listp accessors)
                              (symbol-listp accessors$c)
                              (symbol-listp accessors$a)
                              (= (len accessors) (len accessors$c))
                              (= (len accessors$c) (len accessors$a)))))
  (and (consp accessors)
       (cons `(defthm ,(symbolicate frame (car accessors) '{correspondence})
                (implies (and (,frame$corr ,frame$c ,frame)
                              (,recognizer$a ,frame))
                         (equal (,(car accessors$c) ,frame$c)
                                (,(car accessors$a) ,frame)))
                :rule-classes nil)
             (define-frame::accessor-correspondence-theorems$abs
              frame$corr frame$c frame recognizer$a
              (cdr accessors) (cdr accessors$c) (cdr accessors$a)))))

(defun define-frame::updater-correspondence-theorems$abs
    (frame$corr frame$c frame recognizer$a
     recognizers$a updaters updaters$c updaters$a)
  (declare (xargs :guard (and (symbolp frame$corr)
                              (symbolp frame$c)
                              (symbolp frame)
                              (symbolp recognizer$a)
                              (symbol-listp recognizers$a)
                              (symbol-listp updaters)
                              (symbol-listp updaters$c)
                              (symbol-listp updaters$a)
                              (= (len recognizers$a) (len updaters))
                              (= (len updaters) (len updaters$c))
                              (= (len updaters$c) (len updaters$a)))))
  (and (consp updaters)
       (cons `(defthm ,(symbolicate frame (car updaters) '{correspondence})
                (implies (and (,frame$corr ,frame$c ,frame)
                              ,@(and (car recognizers$a)
                                     `((,(car recognizers$a) v)))
                              (,recognizer$a ,frame))
                         (,frame$corr (,(car updaters$c) v ,frame$c)
                                      (,(car updaters$a) v ,frame)))
                :rule-classes nil)
             (define-frame::updater-correspondence-theorems$abs
              frame$corr frame$c frame recognizer$a
              (cdr recognizers$a) (cdr updaters) (cdr updaters$c) (cdr updaters$a)))))

(defun define-frame::updater$c-guards (updaters$c state)
  (declare (xargs :stobjs state
                  :guard (symbol-listp updaters$c)
                  :mode :program))
  (and (consp updaters$c)
       (cons (let* ((guard (getpropc (car updaters$c) 'guard))
                    (guard (cadr (untranslate guard nil (w state)))))
               guard)
             (define-frame::updater$c-guards (cdr updaters$c) state))))

(defun define-frame::updater-guard-theorems$abs
    (frame$corr frame$c frame recognizer$a
     recognizers$a updaters stobjs updater$c-guards)
  (declare (xargs :guard (and (symbolp frame$corr)
                              (symbolp frame$c)
                              (symbolp frame)
                              (symbolp recognizer$a)
                              (symbol-listp recognizers$a)
                              (symbol-listp updaters)
                              (symbol-listp stobjs)
                              (true-listp updater$c-guards)
                              (= (len recognizers$a) (len updaters))
                              (= (len updaters) (len stobjs))
                              (= (len stobjs) (len updater$c-guards)))))
  (and (consp updaters)
       (cons `(defthm ,(symbolicate frame (car updaters) '{guard-thm})
                (implies (and (,frame$corr ,frame$c ,frame)
                              ,@(and (car recognizers$a)
                                     `((,(car recognizers$a) ,(or (car stobjs)
                                                                  'v))))
                              (,recognizer$a ,frame))
                         ,(car updater$c-guards))
                :rule-classes nil)
             (define-frame::updater-guard-theorems$abs
              frame$corr frame$c frame recognizer$a
              (cdr recognizers$a) (cdr updaters) (cdr stobjs) (cdr updater$c-guards)))))

(defun define-frame::updater-preserved-theorems$abs
    (recognizer$a frame recognizers$a updaters updaters$a)
  (declare (xargs :guard (and (symbolp recognizer$a)
                              (symbolp frame)
                              (symbol-listp recognizers$a)
                              (symbol-listp updaters)
                              (symbol-listp updaters$a)
                              (= (len recognizers$a) (len updaters))
                              (= (len updaters) (len updaters$a)))))
  (and (consp updaters)
       (cons `(defthm ,(symbolicate frame (car updaters) '{preserved})
                (implies ,(if (car recognizers$a)
                              `(and (,(car recognizers$a) v)
                                    (,recognizer$a ,frame))
                              `(,recognizer$a ,frame))
                         (,recognizer$a (,(car updaters$a) v ,frame)))
                :rule-classes nil)
             (define-frame::updater-preserved-theorems$abs
              recognizer$a frame (cdr recognizers$a) (cdr updaters) (cdr updaters$a)))))

(defun define-frame::exports$abs
    (accessors updaters
     stobjs updaters0
     accessors$c updaters$c
     accessors$a updaters$a)
  (declare (xargs :guard (and (symbol-listp accessors)
                              (symbol-listp updaters)
                              (symbol-listp stobjs)
                              (symbol-listp updaters0)
                              (symbol-listp accessors$c)
                              (symbol-listp updaters$c)
                              (symbol-listp accessors$a)
                              (symbol-listp updaters$a)
                              (= (len accessors) (len accessors$c))
                              (= (len accessors$c) (len accessors$a))
                              (= (len accessors) (len stobjs))
                              (= (len stobjs) (len updaters0))
                              (= (len updaters) (len updaters$c))
                              (= (len updaters$c) (len updaters$a)))
                  :measure (make-ord 1 (1+ (len accessors)) (1+ (len updaters)))))
  (cond
    ((consp accessors)
     (cons `(,(car accessors)
              :logic ,(car accessors$a)
              :exec ,(car accessors$c)
              ,@(and (car stobjs)
                     `(:updater ,(car updaters0))))
           (define-frame::exports$abs
            (cdr accessors) updaters
            (cdr stobjs) (cdr updaters0)
            (cdr accessors$c) updaters$c
            (cdr accessors$a) updaters$a)))
    ((consp updaters)
     (cons `(,(car updaters)
              :logic ,(car updaters$a)
              :exec ,(car updaters$c))
           (define-frame::exports$abs
            accessors (cdr updaters)
            stobjs updaters0
            accessors$c (cdr updaters$c)
            accessors$a (cdr updaters$a))))
    (t
     nil)))

(defmacro define-frame$abs (&whole form frame &body body)
  (declare (xargs :guard (valid-frame$abs-form-p form))
           (ignore body))
  (mv-let (frame$a frame$c recognizer creator fixer
                   accessors updaters stobjs
                   executable debug)
          (define-frame::parse-form$abs form)
    (let* ((frame$corr (symbolicate frame frame '$corr))
           (frame-element-guard (symbolicate frame frame '-element-guard))
           (creator{correspondence} (symbolicate frame creator '{correspondence}))
           (creator{preserved} (symbolicate frame creator '{preserved}))
           (fixer{correspondence} (symbolicate frame fixer '{correspondence}))
           (fixer{preserved} (symbolicate frame fixer '{preserved})))

      `(with-output
         ,@(and (not debug)
                '#!acl2(:off (warning! observation prove event history proof-tree)
                             :summary-off (rules)
                             :gag-mode t))

         (make-event
           (let* ((recognizer$c (stobj-recognizer ',frame$c))
                  (recognizer$a (stobj$a-recognizer ',frame$a))
                  (creator$c (stobj-creator ',frame$c))
                  (creator$a (stobj$a-creator ',frame$a))
                  (fixer$c (symbolicate ',frame$c ',frame$c '-fix))
                  (fixer$c$inline (symbolicate fixer$c fixer$c '$inline))
                  (fixer$a (stobj$a-fixer ',frame$a))

                  (field-recognizers (stobj$a-frame-recognizers ',frame$a))
                  (field-fixers (stobj$a-frame-fixers ',frame$a))
                  (world (w state))
                  (stobj$a-property-alist (stobj$a-property-alist world))
                  (stobj$a-lookup-alist (stobj$a-lookup-alist world))
                  (stobjs$a (loop$ :for stobj :in ',stobjs
                                  :collect (getprop stobj 'stobj$a
                                                    nil 'acl2::current-acl2-world
                                                    stobj$a-lookup-alist)))
                  (stobj$a-properties (loop$ :for stobj$a :in stobjs$a
                                            :collect (getprop stobj$a 'stobj$a
                                                              nil 'acl2::current-acl2-world
                                                              stobj$a-property-alist)))
                  (field-recognizers$a (loop$ :for stobj$a :in stobjs$a
                                             :as recognizer :in field-recognizers
                                             :as property$a :in stobj$a-properties
                                             :collect (if stobj$a
                                                          (first (second property$a))
                                                          recognizer)))
                  (field-fixers$a (loop$ :for stobj$a :in stobjs$a
                                        :as fixer :in field-fixers
                                        :as property$a :in stobj$a-properties
                                        :collect (if stobj$a
                                                     (third (second property$a))
                                                     fixer)))

                  (accessors$c (stobj$c-frame-accessors ',frame$c))
                  (accessors$a (stobj$a-frame-accessors ',frame$a))
                  (updaters$c (stobj$c-frame-updaters ',frame$c))
                  (updaters$a (stobj$a-frame-updaters ',frame$a))
                  (coupled$c (stobj-coupled ',frame$c))

                  (accessor-correspondence-theorems
                   (define-frame::accessor-correspondence-theorems$abs
                    ',frame$corr ',frame$c ',frame recognizer$a
                    ',accessors accessors$c accessors$a))

                  (updater-correspondence-theorems
                   (define-frame::updater-correspondence-theorems$abs
                    ',frame$corr ',frame$c ',frame recognizer$a
                    field-recognizers ',updaters updaters$c updaters$a))

                  (updater$c-guards (define-frame::updater$c-guards
                                     updaters$c state))

                  (updater-guard-theorems
                   (define-frame::updater-guard-theorems$abs
                    ',frame$corr ',frame$c ',frame recognizer$a
                    field-recognizers ',updaters ',stobjs updater$c-guards))

                  (updater-preserved-theorems
                   (define-frame::updater-preserved-theorems$abs
                    recognizer$a ',frame field-recognizers ',updaters updaters$a))

                  (exports (define-frame::exports$abs
                            ',accessors ',updaters
                            ',stobjs ',updaters
                            accessors$c updaters$c
                            accessors$a updaters$a))
                  (exports (cons `(,',fixer :logic ,fixer$a
                                            :exec ,fixer$c$inline)
                                 exports)))

             `(encapsulate ()
                ,@(and (or (remove nil field-recognizers$a)
                           (remove nil field-fixers$a))
                       `((local
                           (in-theory
                             (disable ,@(remove nil field-recognizers$a)
                                      ,@(remove nil field-fixers$a))))))

                (local
                  (defthm ,',frame-element-guard
                    (equal (len (list ,@accessors$c)) (len (list ,@accessors$a)))
                    :rule-classes nil))

                ;; Proof Obligations
                (lprogn
                  ,@(and coupled$c
                         `((in-theory
                             (disable (:e force)))))

                  (defthm ,',creator{correspondence}
                    (,',frame$corr (,creator$c) (,creator$a))
                    :rule-classes nil)

                  (defthm ,',creator{preserved}
                    (,recognizer$a (,creator$a))
                    :rule-classes nil)

                  (defthm ,',fixer{correspondence}
                    (implies (and (,',frame$corr ,',frame$c ,',frame)
                                  (,recognizer$a ,',frame))
                             (,',frame$corr (,fixer$c ,',frame$c)
                                            (,fixer$a ,',frame)))
                    :rule-classes nil)

                  (defthm ,',fixer{preserved}
                    (implies (,recognizer$a ,',frame)
                             (,recognizer$a (,fixer$a ,',frame)))
                    :rule-classes nil)

                  ,@accessor-correspondence-theorems

                  ,@updater-correspondence-theorems

                  ,@updater-guard-theorems

                  ,@updater-preserved-theorems)

                (defabsstobj ,',frame
                  :foundation ,',frame$c
                  :recognizer (,',recognizer :logic ,recognizer$a
                                             :exec ,recognizer$c)
                  :creator (,',creator :logic ,creator$a
                                       :exec ,creator$c)
                  :corr-fn ,',frame$corr
                  :non-executable ,',(not executable)
                  :exports ,exports)

                (table stobj$a
                       'stobj$a-lookup-alist
                       (putprop ',',frame
                                'stobj$a
                                ',',frame$a
                                (stobj$a-lookup-alist world))))))))))


;;;; `VALID-FRAME' Predicates
(defun valid-frame-descriptor-p (descriptor)
  (declare (xargs :guard t))
  (and (consp descriptor)
       (let ((name (car descriptor))
             (kvl (cdr descriptor)))
         (and (symbolp name)
              (keyword-value-listp kvl)
              (subsetp (evens kvl) define-frame::*field-keywords*
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
                (subsetp (evens body) define-frame::*body-keywords*
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
(defun define-frame::split-body (body)
  (declare (xargs :guard (valid-frame-body-p body)))
  (cond
    ((atom body)
     (mv nil nil))
    ((atom (car body))
     (mv nil body))
    (t
     (mv-let (fds kvl)
             (define-frame::split-body (cdr body))
       (mv (cons (car body) fds) kvl)))))

(defun define-frame::parse-fds (frame fds)
  (declare (xargs :guard (and (symbolp frame)
                              (valid-frame-body-p fds)
                              (alistp fds))))
  (if (consp fds)
      (mv-let (fields element-types recognizers fixers stobjs
                      initial-elements accessors updaters)
              (define-frame::parse-fds frame (cdr fds))
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

(defun define-frame::parse-kvl (frame kvl)
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

(defun define-frame::parse-form (form)
  (declare (xargs :guard (valid-frame-form-p form)))
  (let ((frame (cadr form))
        (body (cddr form)))
    (mv-let (fds kvl)
            (define-frame::split-body body)
      (mv-let (inline memoizable executable
                      recognizer creator fixer
                      logic exec debug)
              (define-frame::parse-kvl frame kvl)
        (mv-let (fields element-types recognizers fixers stobjs
                        initial-elements accessors updaters)
                (define-frame::parse-fds frame fds)
          (mv recognizer creator fixer
              fields element-types recognizers fixers stobjs
              initial-elements accessors updaters
              inline memoizable executable
              logic exec debug))))))


;;;; `DEFINE-FRAME'
(defun define-frame::make-field-descriptors$c (fields types elements)
  (declare (xargs :guard (and (symbol-listp fields)
                              (true-listp types)
                              (true-listp elements)
                              (= (len fields) (len types))
                              (= (len types) (len elements)))))
  (and (consp fields)
       (cons (list (car fields)
                   :element-type (car types)
                   :initial-element (car elements))
             (define-frame::make-field-descriptors$c (cdr fields) (cdr types) (cdr elements)))))

(defun define-frame::make-field-descriptors$a (fields recognizers fixers stobjs elements)
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
             (define-frame::make-field-descriptors$a
              (cdr fields) (cdr recognizers) (cdr fixers) (cdr stobjs) (cdr elements)))))

(defun define-frame::make-field-descriptors$abs (fields accessors updaters stobjs)
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
             (define-frame::make-field-descriptors$abs (cdr fields) (cdr accessors) (cdr updaters) (cdr stobjs)))))

(defmacro define-frame (&whole form frame &body body)
  (declare (xargs :guard (valid-frame-form-p form))
           (ignore body))
  (mv-let (recognizer creator fixer
                      fields element-types recognizers fixers stobjs
                      initial-elements accessors updaters
                      inline memoizable executable
                      logic exec debug)
          (define-frame::parse-form form)
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
           (let* ((field-descriptors$c (define-frame::make-field-descriptors$c
                                        ',fields ',element-types ',initial-elements))
                  (field-descriptors$a (define-frame::make-field-descriptors$a
                                        ',fields ',recognizers ',fixers ',stobjs ',initial-elements))
                  (field-descriptors$abs (define-frame::make-field-descriptors$abs
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
