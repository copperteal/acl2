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

#||
(include-book "std/lists/top" :dir :system)
||#

(include-book "../utilities/top")


;;;; Constants
(defconst *field-keywords$abs*
  '(:accessor :updater :stobj))

(defconst *body-keywords$abs*
  '(:logic :exec
    :recognizer :creator :fixer
    :executable :debug))


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
            *constructor-output*)

     (make-event
       (let* ((frame ',frame)
              (logic ',logic)
              (exec ',exec)
              (frame$corr (symbolicate frame frame "$CORR"))

              (frame$a (or logic
                           (symbolicate frame frame "$A")))
              (frame$c (or exec
                           (symbolicate frame frame "$C")))

              (stobj-property (getpropc frame$c 'acl2::stobj))
              (recognizer$c (caadr stobj-property))
              (n (floor (len (third stobj-property)) 4))
              (accessors$c (loop$ :for i :from 0 :to n
                                 :collect (nth (+ n (* 2 i)) (third stobj-property))))

              (stobj$a-property (cdr (assoc frame$a (table-alist 'stobj$a-property (w state)))))
              (recognizer$a (first (second stobj$a-property)))
              (accessors$a (sixth (third stobj$a-property))))

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
                      (debug (cadr (assoc-keyword :debug body))))
                  (and (symbolp frame$a)
                       (symbolp frame$c)
                       (symbolp recognizer)
                       (symbolp creator)
                       (symbolp fixer)
                       (booleanp executable)
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
         (debug (cadr (assoc-keyword :debug kvl))))
    (mv logic exec
        recognizer creator fixer
        executable debug)))

(defun parse-form$abs (form)
  (declare (xargs :guard (frame$abs-form-p form)))
  (let ((body (cddr form)))
    (mv-let (fds kvl)
            (split-body$abs () body)
      (mv-let (fields accessors updaters stobjs)
              (parse-fds$abs fds () () () ())
        (mv-let (logic exec
                       recognizer creator fixer
                       executable debug)
                (parse-kvl$abs kvl)
          (mv fields accessors updaters stobjs
              logic exec
              recognizer creator fixer
              executable debug))))))


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
                  executable debug)
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

                ;; Interface Symbols
                (frame$a (or logic
                             (symbolicate frame frame "$A")))
                (frame$c (or exec
                             (symbolicate frame frame "$C")))
                (recognizer (or recognizer
                                (symbolicate frame frame (make-predicate-suffix frame))))
                (creator (or creator
                             (symbolicate frame "CREATE-" frame)))
                (fixer (or fixer
                           (symbolicate frame frame "-FIX")))
                (accessors (loop$ :for field :in fields
                                 :as accessor :in accessors
                                 :collect (or accessor
                                              (symbolicate frame frame "-" field))))
                (updaters (loop$ :for field :in fields
                                :as updater :in updaters
                                :collect (or updater
                                             (symbolicate frame frame "-" field "-SET"))))

                (world (w state))
                (frame$corr (cdr (assoc frame (table-alist 'corr world))))

                ;; `FRAME$C'
                (stobj-property (getpropc frame$c 'acl2::stobj))
                (recognizer$c (caadr stobj-property))
                (creator$c (cdadr stobj-property))
                (fixer$c (cdr (assoc frame$c (table-alist 'fixer world))))
                (fixer$c$inline (or (cdr (assoc fixer$c (table-alist 'acl2::macro-aliases-table world)))
                                    fixer$c))
                (n (floor (len (third stobj-property)) 4))
                (accessors$c (loop$ :for i :from 0 :to n
                                   :collect (nth (+ n (* 2 i)) (third stobj-property))))
                (updaters$c (loop$ :for i :from 0 :to n
                                  :collect (nth (+ 1 n (* 2 i)) (third stobj-property))))

                ;; `FRAME$A'
                (stobj$a-property (cdr (assoc frame$a (table-alist 'stobj$a-property world))))
                (recognizer$a (first (second stobj$a-property)))
                (creator$a (second (second stobj$a-property)))
                (fixer$a (third (second stobj$a-property)))

                (stobj-property-list (loop$ :for stobj :in stobjs
                                           :collect (and stobj
                                                         (getprop stobj
                                                                  'acl2::stobj
                                                                  nil
                                                                  'acl2::current-acl2-world
                                                                  world))))
                (recognizers$a (loop$ :for stobj-property :in stobj-property-list
                                     :as recognizer$a :in (second (third stobj$a-property))
                                     :collect (if stobj-property
                                                  (caadr stobj-property)
                                                  recognizer$a)))
                (accessors$a (sixth (third stobj$a-property)))
                (updaters$a (seventh (third stobj$a-property)))

                ;; Theorem Names
                (creator{correspondence} (symbolicate frame creator "{CORRESPONDENCE}"))
                (creator{preserved} (symbolicate frame creator "{PRESERVED}"))
                (fixer{correspondence} (symbolicate frame fixer "{CORRESPONDENCE}"))
                (fixer{preserved} (symbolicate frame fixer "{PRESERVED}"))

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
                          :collect `(defthm ,(symbolicate frame accessor "{CORRESPONDENCE}")
                                      (implies (and (,frame$corr ,frame$c ,frame)
                                                    (,recognizer$a ,frame))
                                               (equal (,accessor$c ,frame$c)
                                                      (,accessor$a ,frame)))
                                      :rule-classes nil))

                  ,@(loop$ :for updater :in updaters
                          :as updater$c :in updaters$c
                          :as updater$a :in updaters$a
                          :as updater$c-field :in updater$c-fields
                          :as field-recognizer$a :in recognizers$a
                          :collect `(defthm ,(symbolicate frame updater "{CORRESPONDENCE}")
                                      (implies (and (,frame$corr ,frame$c ,frame)
                                                    ,@(and field-recognizer$a
                                                           `((,field-recognizer$a ,updater$c-field)))
                                                    (,recognizer$a ,frame))
                                               (,frame$corr (,updater$c ,updater$c-field ,frame$c)
                                                            (,updater$a ,updater$c-field ,frame)))
                                      :rule-classes nil))

                  ,@(loop$ :for updater :in updaters
                          :as updater$c-guard :in updater$c-guards
                          :as updater$c-field :in updater$c-fields
                          :as field-recognizer$a :in recognizers$a
                          :collect `(defthm ,(symbolicate frame updater "{GUARD-THM}")
                                      (implies (and (,frame$corr ,frame$c ,frame)
                                                    ,@(and field-recognizer$a
                                                           `((,field-recognizer$a ,updater$c-field)))
                                                    (,recognizer$a ,frame))
                                               ,updater$c-guard)
                                      :rule-classes nil))

                  ,@(loop$ :for updater :in updaters
                          :as updater$a :in updaters$a
                          :as updater$c-field :in updater$c-fields
                          :as field-recognizer$a :in recognizers$a
                          :collect `(defthm ,(symbolicate frame updater "{PRESERVED}")
                                      (implies ,(if field-recognizer$a
                                                    `(and (,field-recognizer$a ,updater$c-field)
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

              (table stobj$a-property ',frame ',stobj$a-property)))))))
