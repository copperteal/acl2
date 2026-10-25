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

(include-book "../utilities/top")


;;;; Constants
(defconst *field-keywords$abs*
  '(:accessor :updater :stobj))

(defconst *body-keywords$abs*
  '(:logic :exec
    :recognizer :creator :fixer
    :executable :pkg-witness :pkg-witness$a :pkg-witness$c
    :debug))


;;;; `DEFINE-FRAME$CORR'
(defmacro define-frame$corr (frame
                             &key
                               (logic 'nil)
                               (exec 'nil)

                               (pkg-witness 'nil pkg-witness-supplied-p)
                               (pkg-witness$a 'nil pkg-witness$a-supplied-p)
                               (pkg-witness$c 'nil pkg-witness$c-supplied-p)
                               (debug 'nil))

  (declare (xargs :guard (and (symbolp frame)
                              (symbolp logic)
                              (symbolp exec)
                              ;; (pkg-witness-p pkg-witness)
                              ;; (pkg-witness-p pkg-witness$a)
                              ;; (pkg-witness-p pkg-witness$c)
                              (booleanp debug))))

  `(with-output
     ,@(and (not debug)
            *constructor-output*)

     (make-event
       (let* ((frame ',frame)
              (logic ',logic)
              (exec ',exec)
              (pkg-witness (pkg-witness-fix (if ',pkg-witness-supplied-p
                                                ',pkg-witness
                                                (current-package state))))
              (pkg-witness$a (pkg-witness-fix (if ',pkg-witness$a-supplied-p
                                                  ',pkg-witness$a
                                                  pkg-witness)))
              (pkg-witness$c (pkg-witness-fix (if ',pkg-witness$c-supplied-p
                                                  ',pkg-witness$c
                                                  pkg-witness)))

              (frame$corr (symbolicate$ pkg-witness frame "$CORR"))

              (frame$a (or logic
                           (symbolicate$ pkg-witness$a frame "$A")))
              (frame$c (or exec
                           (symbolicate$ pkg-witness$c frame "$C")))

              (stobj$c-property (stobj$c-property frame$c (w state)))
              (recognizer$c (access frame$c-property
                                    stobj$c-property
                                    :recognizer))
              (accessors$c (access frame$c-property
                                   stobj$c-property
                                   :accessors))

              (stobj$a-property (stobj$a-property frame$a (w state)))
              (recognizer$a (access frame$a-property stobj$a-property :recognizer))
              (accessors$a (access frame$a-property stobj$a-property :accessors)))

         `(progn
            (defun-nx ,frame$corr (,frame$c ,frame$a)
              (declare (xargs :stobjs ,frame$c
                              :guard (,recognizer$a ,frame$a)
                              :verify-guards nil))
              (and (,recognizer$c ,frame$c)
                   (,recognizer$a ,frame$a)
                   ,@(loop$ :for accessor$c :in accessors$c
                           :as accessor$a :in accessors$a
                           :collect `(equal (,accessor$c ,frame$c)
                                            (,accessor$a ,frame$a)))))

            (table corr ',frame ',frame$corr))))))


;;;; `FRAME$ABS' Predicates
(defun frame$abs-descriptor-p (descriptor)
  (declare (xargs :guard t))
  (and (consp descriptor)
       (let ((name (car descriptor))
             (kvl (cdr descriptor)))
         (and (symbolp name)
              (keyword-value-listp kvl)
              (subsetp (evens kvl) *field-keywords$abs* :test 'eq)
              (let ((accessor (cadr (assoc-keyword :accessor kvl)))
                    (updater (cadr (assoc-keyword :updater kvl)))
                    (stobj (cadr (assoc-keyword :stobj kvl))))
                (and (symbolp accessor)
                     (symbolp updater)
                     (symbolp stobj)))))))

(defun frame$abs-descriptor-list-p (fds)
  (declare (xargs :guard t))
  (if (atom fds)
      (null fds)
      (and (frame$abs-descriptor-p (car fds))
           (frame$abs-descriptor-list-p (cdr fds)))))

(defun frame$abs-body-p (body)
  (declare (xargs :guard t))
  (and (true-listp body)
       (if (consp (car body))
           (and (frame$abs-descriptor-p (car body))
                (frame$abs-body-p (cdr body)))
           (and (keyword-value-listp body)
                (subsetp (evens body) *body-keywords$abs* :test 'eq)
                (let ((frame$a (cadr (assoc-keyword :logic body)))
                      (frame$c (cadr (assoc-keyword :exec body)))
                      (recognizer (cadr (assoc-keyword :recognizer body)))
                      (creator (cadr (assoc-keyword :creator body)))
                      (fixer (cadr (assoc-keyword :fixer body)))
                      (executable (cadr (assoc-keyword :executable body)))
                      (pkg-witness (pkg-witness-fix (cadr (assoc-keyword :pkg-witness body))))
                      (pkg-witness$a (pkg-witness-fix (cadr (assoc-keyword :pkg-witness$a body))))
                      (pkg-witness$c (pkg-witness-fix (cadr (assoc-keyword :pkg-witness$c body))))
                      (debug (cadr (assoc-keyword :debug body))))
                  (and (symbolp frame$a)
                       (symbolp frame$c)
                       (symbolp recognizer)
                       (symbolp creator)
                       (symbolp fixer)
                       (booleanp executable)
                       (pkg-witness-p pkg-witness)
                       (pkg-witness-p pkg-witness$a)
                       (pkg-witness-p pkg-witness$c)
                       (booleanp debug)))))))

(defthm frame$abs-body-p-when-frame$abs-descriptor-list-p
  (implies (frame$abs-descriptor-list-p fds)
           (frame$abs-body-p fds))
  :hints
  (("Goal"
    :induct (len fds))))

(defun frame$abs-form-p (form)
  (declare (xargs :guard t))
  (and (true-listp form)
       (eq (car form) 'define-frame$abs)
       (symbolp (cadr form))
       (frame$abs-body-p (cddr form))))


;;;; `DEFINE-FRAME$ABS' Parser
(with-books (("std/lists/rev" :dir :system))
  (defun split-body$abs (fds body)
    (declare (xargs :guard (and (frame$abs-descriptor-list-p fds)
                                (frame$abs-body-p body))))
    (if (or (endp body)
            (atom (car body)))
        (mv (reverse fds) body)
        (split-body$abs (cons (car body) fds) (cdr body))))

  (local
    (defthm frame$abs-descriptor-list-p-of-rev
      (implies (frame$abs-descriptor-list-p fds)
               (frame$abs-descriptor-list-p (acl2::rev fds)))
      :hints
      (("Goal"
        :in-theory (disable frame$abs-descriptor-p)))))

  (defthm split-body$abs-values
    (implies (and (frame$abs-descriptor-list-p fds)
                  (frame$abs-body-p body))
             (mv-let (fds kvl)
                     (split-body$abs fds body)
               (and (frame$abs-descriptor-list-p fds)
                    (frame$abs-body-p kvl)
                    (keyword-value-listp kvl))))))

(defun parse-fds$abs (fds fields accessors updaters stobjs)
  (declare (xargs :guard (and (frame$abs-descriptor-list-p fds)
                              (symbol-listp fields)
                              (symbol-listp accessors)
                              (symbol-listp updaters)
                              (symbol-listp stobjs))))
  (if (endp fds)
      (mv (reverse fields)
          (reverse accessors)
          (reverse updaters)
          (reverse stobjs))
      (let* ((descriptor (car fds))
             (field (car descriptor))
             (kvl (cdr descriptor))
             (accessor (cadr (assoc-keyword :accessor kvl)))
             (updater (cadr (assoc-keyword :updater kvl)))
             (stobj (cadr (assoc-keyword :stobj kvl))))
        (parse-fds$abs (cdr fds)
                       (cons field fields)
                       (cons accessor accessors)
                       (cons updater updaters)
                       (cons stobj stobjs)))))

(defun parse-kvl$abs (kvl)
  (declare (xargs :guard (and (frame$abs-body-p kvl)
                              (keyword-value-listp kvl))))
  (let* ((executable (cadr (assoc-keyword :executable kvl)))
         (logic (cadr (assoc-keyword :logic kvl)))
         (exec (cadr (assoc-keyword :exec kvl)))
         (recognizer (cadr (assoc-keyword :recognizer kvl)))
         (creator (cadr (assoc-keyword :creator kvl)))
         (fixer (cadr (assoc-keyword :fixer kvl)))
         (pkg-witness-supplied-p (assoc-keyword :pkg-witness kvl))
         (pkg-witness (cadr pkg-witness-supplied-p))
         (pkg-witness-supplied-p (and pkg-witness-supplied-p
                                      t))
         (pkg-witness$a-supplied-p (assoc-keyword :pkg-witness$a kvl))
         (pkg-witness$a (cadr pkg-witness$a-supplied-p))
         (pkg-witness$a-supplied-p (and pkg-witness$a-supplied-p
                                        t))
         (pkg-witness$c-supplied-p (assoc-keyword :pkg-witness$c kvl))
         (pkg-witness$c (cadr pkg-witness$c-supplied-p))
         (pkg-witness$c-supplied-p (and pkg-witness$c-supplied-p
                                        t))
         (debug (cadr (assoc-keyword :debug kvl))))
    (mv logic exec
        recognizer creator fixer
        executable
        pkg-witness pkg-witness-supplied-p
        pkg-witness$a pkg-witness$a-supplied-p
        pkg-witness$c pkg-witness$c-supplied-p
        debug)))

(defun parse-form$abs (form)
  (declare (xargs :guard (frame$abs-form-p form)))
  (let ((body (cddr form)))
    (mv-let (fds kvl)
            (split-body$abs () body)
      (mv-let (fields accessors updaters stobjs)
              (parse-fds$abs fds () () () ())
        (mv-let (logic exec
                       recognizer creator fixer
                       executable
                       pkg-witness pkg-witness-supplied-p
                       pkg-witness$a pkg-witness$a-supplied-p
                       pkg-witness$c pkg-witness$c-supplied-p
                       debug)
                (parse-kvl$abs kvl)
          (mv fields accessors updaters stobjs
              logic exec
              recognizer creator fixer
              executable
              pkg-witness pkg-witness-supplied-p
              pkg-witness$a pkg-witness$a-supplied-p
              pkg-witness$c pkg-witness$c-supplied-p
              debug))))))


;;;; `DEFINE-FRAME$ABS'
(defun frame$abs-updater$c-guards (updaters$c acc state)
  (declare (xargs :mode :program
                  :stobjs state
                  :guard (and (symbol-listp updaters$c)
                              (true-listp acc))))
  (if (endp updaters$c)
      (reverse acc)
      (frame$abs-updater$c-guards (cdr updaters$c)
                                  (cons (cadr (untranslate (getpropc (car updaters$c) 'acl2::guard)
                                                           nil
                                                           (w state)))
                                        acc)
                                  state)))

(defun frame$abs-updater$c-fields (updaters$c acc state)
  (declare (xargs :mode :program
                  :stobjs state
                  :guard (and (symbol-listp updaters$c)
                              (true-listp acc))))
  (if (endp updaters$c)
      (reverse acc)
      (frame$abs-updater$c-fields (cdr updaters$c)
                                  (cons (car (getpropc (car updaters$c) 'acl2::formals))
                                        acc)
                                  state)))

(defmacro define-frame$abs (&whole form frame &body body)
  (declare (xargs :guard (frame$abs-form-p form))
           (ignore body))
  (mv-let (fields accessors updaters stobjs
                  logic exec
                  recognizer creator fixer
                  executable
                  pkg-witness pkg-witness-supplied-p
                  pkg-witness$a pkg-witness$a-supplied-p
                  pkg-witness$c pkg-witness$c-supplied-p
                  debug)
          (parse-form$abs form)

    `(with-output
       ,@(and (not debug)
              *constructor-output*)

       (make-event
         (let* ((frame ',frame)
                (logic ',logic)
                (exec ',exec)
                (recognizer ',recognizer)
                (creator ',creator)
                (fixer ',fixer)
                (fields ',fields)
                (accessors ',accessors)
                (updaters ',updaters)
                (stobjs ',stobjs)
                (executable ',executable)
                (pkg-witness (pkg-witness-fix (if ',pkg-witness-supplied-p
                                                  ',pkg-witness
                                                  (current-package state))))
                (pkg-witness$a (pkg-witness-fix (if ',pkg-witness$a-supplied-p
                                                    ',pkg-witness$a
                                                    pkg-witness)))
                (pkg-witness$c (pkg-witness-fix (if ',pkg-witness$c-supplied-p
                                                    ',pkg-witness$c
                                                    pkg-witness)))

                ;; Interface Symbols
                (frame$a (or logic
                             (symbolicate$ pkg-witness$a frame "$A")))
                (frame$c (or exec
                             (symbolicate$ pkg-witness$c frame "$C")))
                (recognizer (or recognizer
                                (symbolicate$ pkg-witness frame (make-predicate-suffix frame))))
                (creator (or creator
                             (symbolicate$ pkg-witness "CREATE-" frame)))
                (fixer (or fixer
                           (symbolicate$ pkg-witness frame "-FIX")))
                (accessors (loop$ :for field :in fields
                                 :as accessor :in accessors
                                 :collect (or accessor
                                              (symbolicate$ pkg-witness frame "-" field))))
                (updaters (loop$ :for field :in fields
                                :as updater :in updaters
                                :collect (or updater
                                             (symbolicate$ pkg-witness frame "-" field "-SET"))))

                (world (w state))
                (frame$corr (cdr (assoc frame (table-alist 'corr world))))

                ;; `FRAME$C'
                (stobj$c-property (stobj$c-property frame$c (w state)))
                (recognizer$c (access frame$c-property
                                      stobj$c-property
                                      :recognizer))
                (creator$c (access frame$c-property
                                   stobj$c-property
                                   :creator))
                (fixer$c (access frame$c-property
                                 stobj$c-property
                                 :fixer))
                (fixer$c$inline (or (cdr (assoc fixer$c (table-alist 'acl2::macro-aliases-table world)))
                                    fixer$c))
                (recognizers$c (access frame$c-property
                                       stobj$c-property
                                       :recognizers))
                (accessors$c (access frame$c-property
                                     stobj$c-property
                                     :accessors))
                (updaters$c (access frame$c-property
                                    stobj$c-property
                                    :updaters))

                ;; `FRAME$A'
                (stobj$a-property (stobj$a-property frame$a world))
                (recognizer$a (access frame$a-property stobj$a-property :recognizer))
                (creator$a (access frame$a-property stobj$a-property :creator))
                (fixer$a (access frame$a-property stobj$a-property :fixer))
                (frame$a-theorems (symbolicate$ frame$a frame$a "-THEOREMS"))
                (stobj-property-list (loop$ :for stobj :in stobjs
                                           :collect (and stobj
                                                         (getprop stobj
                                                                  'acl2::stobj
                                                                  nil
                                                                  'acl2::current-acl2-world
                                                                  world))))

                (recognizers (loop$ :for stobj-property :in stobj-property-list
                                   :as recognizer$a :in (access frame$a-property stobj$a-property :recognizers)
                                   :collect (if stobj-property
                                                (caadr stobj-property)
                                                recognizer$a)))
                (absstobj-info-list (loop$ :for stobj :in stobjs
                                          :collect (and stobj
                                                        (getprop stobj
                                                                 'acl2::absstobj-info
                                                                 nil
                                                                 'acl2::current-acl2-world
                                                                 world))))
                (recognizers$a (access frame$a-property stobj$a-property :recognizers))
                (stobj$a-property-list (loop$ :for stobj :in stobjs
                                             :collect (and stobj
                                                           (stobj$a-property stobj world))))
                (creators$a (loop$ :for stobj$a-property :in stobj$a-property-list
                                  :collect (and stobj$a-property
                                                (access stobj$a-property stobj$a-property :creator))))
                (initial-element-names (access frame$a-property stobj$a-property :initial-elements))
                (fixers$a (access frame$a-property stobj$a-property :fixers))
                (equivs$a (access frame$a-property stobj$a-property :equivs))
                (accessors$a (access frame$a-property stobj$a-property :accessors))
                (updaters$a (access frame$a-property stobj$a-property :updaters))

                ;; Theorem Names
                (len-of-cons (symbolicate$ "ATOMIC-STOBJS" "LEN-OF-CONS"))
                (nth-of-cons (symbolicate$ "ATOMIC-STOBJS" "NTH-OF-CONS"))

                (creator{correspondence} (symbolicate$ pkg-witness creator "{CORRESPONDENCE}"))
                (creator{preserved} (symbolicate$ pkg-witness creator "{PRESERVED}"))
                (fixer{correspondence} (symbolicate$ pkg-witness fixer "{CORRESPONDENCE}"))
                (fixer{preserved} (symbolicate$ pkg-witness fixer "{PRESERVED}"))

                ;; Exports
                (exports `((,fixer :logic ,fixer$a
                                   :exec ,fixer$c$inline)
                           ,@(loop$ :for accessor :in accessors
                                   :as accessor$a :in accessors$a
                                   :as accessor$c :in accessors$c
                                   :as updater :in updaters
                                   :as stobj :in stobjs
                                   :collect `(,accessor :logic ,accessor$a
                                                        :exec ,accessor$c
                                                        ,@(and stobj
                                                               `(:updater ,updater))))
                           ,@(loop$ :for updater :in updaters
                                   :as updater$a :in updaters$a
                                   :as updater$c :in updaters$c
                                   :collect `(,updater :logic ,updater$a
                                                       :exec ,updater$c))))

                ;; Miscellaneous
                (updater$c-guards (frame$abs-updater$c-guards updaters$c () state))

                (updater$c-fields (frame$abs-updater$c-fields updaters$c () state)))

           `(encapsulate ()

              (local
                (deflabel start-of-prologue))

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

              ,@(loop$ :for i :from 1 :to (len fields)
                      :as field :in fields
                      :as recognizer$c :in recognizers$c
                      :as recognizer$a :in recognizers$a
                      :as updater$c-guard :in updater$c-guards
                      :as updater$c-field :in updater$c-fields
                      :as creator :in creators$a
                      :as initial-element-name :in initial-element-names
                      :when recognizer$a
                      :collect `(local
                                  (defthm ,(symbolicate$ "ATOMIC-STOBJS" recognizer$a "-CONSTRAINTS-" i)
                                    (and (booleanp (,recognizer$a ,field))
                                         (,recognizer$a ,(or initial-element-name
                                                             `(,creator)))
                                         (implies (,recognizer$a ,updater$c-field)
                                                  (,recognizer$c ,updater$c-field))
                                         ;; This is an ugly hack for the
                                         ;; situation that the field has
                                         ;; concrete type `T'
                                         ,@(and (not (eq updater$c-guard frame$c))
                                                `((implies (,recognizer$a ,updater$c-field)
                                                           ,updater$c-guard))))
                                    :rule-classes
                                    ((:rewrite :corollary
                                               (booleanp (,recognizer$a ,field)))
                                     ,@(and (not initial-element-name)
                                            `((:rewrite :corollary
                                                        (,recognizer$a (,creator)))))
                                     (:rewrite :corollary
                                               (implies (,recognizer$a ,updater$c-field)
                                                        (,recognizer$c ,updater$c-field)))
                                     ,@(and (not (eq updater$c-guard frame$c))
                                            `((:forward-chaining :corollary
                                                                 (implies (,recognizer$a ,updater$c-field)
                                                                          ,updater$c-guard))))))))

              ,@(loop$ :for i :from 1 :to (len fields)
                      :as field :in fields
                      :as recognizer :in recognizers$a
                      :as creator :in creators$a
                      :as initial-element-name :in initial-element-names
                      :as fixer :in fixers$a
                      :when (and recognizer
                                 fixer)
                      :collect `(local
                                  (defthm ,(symbolicate$ "ATOMIC-STOBJS" fixer "-CONSTRAINTS-" i)
                                    (equal (,fixer ,field)
                                           (if (,recognizer ,field)
                                               ,field
                                               ,(or initial-element-name
                                                    `(,creator)))))))

              ,@(loop$ :for i :from 1 :to (len fields)
                      :as equiv :in equivs$a
                      :as field :in fields
                      :as fixer :in fixers$a
                      :when fixer
                      :collect (let ((%field (symbolicate$ "ATOMIC-STOBJS" "%" field)))
                                 `(local
                                    (defthm ,(symbolicate$ "ATOMIC-STOBJS" equiv "-CONSTRAINTS-" i)
                                      (equal (,equiv ,%field ,field)
                                             (equal (,fixer ,%field)
                                                    (,fixer ,field)))
                                      :hints
                                      (("Goal"
                                        :in-theory (enable ,equiv)))))))

              (local
                (deflabel end-of-prologue))

              (local
                (table acl2::theory-invariant-table nil nil :clear))

              (local
                (in-theory
                  (union-theories
                   (union-theories (current-theory 'acl2::ground-zero)
                                   (theory ',frame$a-theorems))
                   (set-difference-theories (universal-theory 'end-of-prologue)
                                            (universal-theory 'start-of-prologue)))))

              ,@(loop$ :for stobj-property :in stobj-property-list
                      :as recognizer :in recognizers$a
                      :as fixer :in fixers$a
                      :as equiv :in equivs$a
                      :when (and (not stobj-property)
                                 recognizer
                                 fixer
                                 equiv)
                      :collect `(local
                                  (in-theory
                                    (disable ,recognizer
                                             ,fixer
                                             ,equiv))))

              (local
                (in-theory
                  (enable ,recognizer$c
                          ,creator$c
                          ,@(loop$ :for recognizer$c :in recognizers$c
                                  :collect `(:e ,recognizer$c))
                          ,@accessors$c
                          ,@updaters$c
                          ,frame$corr
                          ,@(loop$ :for stobj$a-property :in stobj$a-property-list
                                  :when stobj$a-property
                                  :collect (let ((stobj$a (access stobj$a-property stobj$a-property :name)))
                                             (symbolicate$ stobj$a stobj$a "-THEOREMS"))))))

              ,@(loop$ :for absstobj-info :in absstobj-info-list
                      :when absstobj-info
                      :collect `(local
                                  (in-theory
                                    (enable ,@(strip-cars (cdr absstobj-info))))))

              (local
                (in-theory
                  (disable len
                           nth
                           update-nth
                           signed-byte-p
                           unsigned-byte-p)))

              (local
                (progn
                  (defthm ,creator{correspondence}
                    (,frame$corr (,creator$c) (,creator$a))
                    :rule-classes nil)

                  (defthm ,creator{preserved}
                    (,recognizer$a (,creator$a))
                    :rule-classes nil)

                  (defthm ,fixer{correspondence}
                    (implies (and (,frame$corr ,frame$c ,frame)
                                  (,recognizer$a ,frame))
                             (,frame$corr (,fixer$c ,frame$c)
                                          (,fixer$a ,frame)))
                    :rule-classes nil
                    :hints
                    (("Goal"
                      :in-theory (enable ,fixer$c))))

                  (defthm ,fixer{preserved}
                    (implies (,recognizer$a ,frame)
                             (,recognizer$a (,fixer$a ,frame)))
                    :rule-classes nil)

                  ,@(loop$ :for accessor :in accessors
                          :as accessor$c :in accessors$c
                          :as accessor$a :in accessors$a
                          :collect `(defthm ,(symbolicate$ pkg-witness accessor "{CORRESPONDENCE}")
                                      (implies (and (,frame$corr ,frame$c ,frame)
                                                    (,recognizer$a ,frame))
                                               (equal (,accessor$c ,frame$c)
                                                      (,accessor$a ,frame)))
                                      :rule-classes nil))

                  ,@(loop$ :for updater :in updaters
                          :as updater$c :in updaters$c
                          :as updater$a :in updaters$a
                          :as updater$c-field :in updater$c-fields
                          :as field-recognizer :in recognizers
                          :collect `(defthm ,(symbolicate$ pkg-witness updater "{CORRESPONDENCE}")
                                      (implies (and (,frame$corr ,frame$c ,frame)
                                                    ,@(and field-recognizer
                                                           `((,field-recognizer ,updater$c-field)))
                                                    (,recognizer$a ,frame))
                                               (,frame$corr (,updater$c ,updater$c-field ,frame$c)
                                                            (,updater$a ,updater$c-field ,frame)))
                                      :rule-classes nil))

                  ,@(loop$ :for updater :in updaters
                          :as updater$c-guard :in updater$c-guards
                          :as updater$c-field :in updater$c-fields
                          :as field-recognizer :in recognizers
                          :collect `(defthm ,(symbolicate$ pkg-witness updater "{GUARD-THM}")
                                      (implies (and (,frame$corr ,frame$c ,frame)
                                                    ,@(and field-recognizer
                                                           `((,field-recognizer ,updater$c-field)))
                                                    (,recognizer$a ,frame))
                                               ,updater$c-guard)
                                      :rule-classes nil))

                  ,@(loop$ :for updater :in updaters
                          :as updater$a :in updaters$a
                          :as updater$c-field :in updater$c-fields
                          :as field-recognizer :in recognizers
                          :collect `(defthm ,(symbolicate$ pkg-witness updater "{PRESERVED}")
                                      (implies ,(if field-recognizer
                                                    `(and (,field-recognizer ,updater$c-field)
                                                          (,recognizer$a ,frame))
                                                    `(,recognizer$a ,frame))
                                               (,recognizer$a (,updater$a ,updater$c-field ,frame)))
                                      :rule-classes nil))))

              (defabsstobj ,frame
                :foundation ,frame$c
                :recognizer (,recognizer :logic ,recognizer$a
                                         :exec ,recognizer$c)
                :creator (,creator :logic ,creator$a
                                   :exec ,creator$c)
                :corr-fn ,frame$corr
                :non-executable ,(not executable)
                :exports ,exports)

              (table stobj$a ',frame ',stobj$a-property)))))))
