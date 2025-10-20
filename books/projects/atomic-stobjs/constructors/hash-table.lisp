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

(include-book "misc/total-order" :dir :system)
(include-book "std/osets/top" :dir :system) ; TODO: delete?
(include-book "std/omaps/core" :dir :system) ; TODO: delete?

(include-book "../type-spec")
(include-book "../accessors/top")
(include-book "../utilities/top")

(deflabel define-hash-table-begin)


;;;; `HASH-TABLE' Guard Predicates
(defun valid-hash-table-test-p (test)
  (declare (xargs :guard t))
; TODO: refactor into separate file
  (and (member test '(eq eql hons-equal equal))
       t))

(defthm valid-hash-table-test-p{compound-recognizer}
; TODO: Is this theorem useful?
  (implies (valid-hash-table-test-p test)
           (and (symbolp test)
                (not (booleanp test))))
  :rule-classes :compound-recognizer)

(defun valid-hash-table-size-p (size)
  (declare (xargs :guard t))
; TODO: refactor into separate file
  (or (null size)
      (natp size)))

(defthm valid-hash-table-size-p{compound-recognizer}
; TODO: Is this theorem useful?
  (implies (valid-hash-table-size-p size)
           (or (null size)
               (natp size)))
  :rule-classes :compound-recognizer)

(include-book "hash-table$c")
(include-book "hash-table$a")


;;;; `DEFINE-HASH-TABLE$CORR'
(defmacro define-hash-table$corr (hash-table
                                  &key
                                    (logic 'nil)
                                    (exec 'nil)
                                    (copyable 't)

                                    (debug 'nil))
  (declare (xargs :guard (and (symbolp hash-table)
                              (symbolp logic)
                              (symbolp exec)
                              (booleanp copyable)
                              (booleanp debug))))
  (let* ((hash-table$a (or logic
                           (symbolicate hash-table hash-table '$a)))
         (hash-table$c (or exec
                           (symbolicate hash-table hash-table '$c)))
         (hash-table$corr (symbolicate hash-table hash-table '$corr))
         (hash-table$corr-keys (symbolicate hash-table hash-table$corr '-keys))
         (hash-table$corr-vals (symbolicate hash-table hash-table$corr '-vals)))

    `(with-output
       ,@(and (not debug)
              '#!acl2(:off (warning! observation prove event history proof-tree)
                           :summary-off (rules)
                           :gag-mode t))

       (make-event
         (let* ((recognizer$c (stobj-recognizer ',hash-table$c))
                (recognizer$a (stobj$a-recognizer ',hash-table$a))
                (count$c (stobj$c-hash-table-count ',hash-table$c ,copyable))
                (count$a (stobj$a-hash-table-count ',hash-table$a))
                (boundp$c (stobj$c-hash-table-boundp ',hash-table$c ,copyable))
                (boundp$a (stobj$a-hash-table-boundp ',hash-table$a))
                (accessor$c (stobj$c-hash-table-accessor ',hash-table$c ,copyable))
                (accessor$a (stobj$a-hash-table-accessor ',hash-table$a))
                (keys$c (stobj$c-hash-table-keys ',hash-table$c ,copyable))
                (keys$a (stobj$a-hash-table-keys ',hash-table$a))
                (key-recognizer (stobj$a-hash-table-key-recognizer ',hash-table$a)))

           `(progn
              (defun-sk ,',hash-table$corr-keys (,',hash-table$c ,',hash-table$a)
                (declare (xargs :stobjs ,',hash-table$c
                                :guard t
                                :verify-guards nil))
                (forall k
                  ,(let ((identity `(equal (,boundp$c k ,',hash-table$c)
                                           (,boundp$a k ,',hash-table$a))))
                     (if key-recognizer
                         `(implies (,key-recognizer k)
                                   ,identity)
                         identity)))
                :rewrite :direct)

              (defun-sk ,',hash-table$corr-vals (,',hash-table$c ,',hash-table$a)
                (declare (xargs :stobjs ,',hash-table$c
                                :guard t
                                :verify-guards nil))
                (forall k
                  ,(let ((identity `(equal (,accessor$c k ,',hash-table$c)
                                           (,accessor$a k ,',hash-table$a))))
                     (if key-recognizer
                         `(implies (,key-recognizer k)
                                   ,identity)
                         identity)))
                :rewrite :direct)

              (defun-nx ,',hash-table$corr (,',hash-table$c ,',hash-table$a)
                (declare (xargs :stobjs ,',hash-table$c
                                :guard (,recognizer$a ,',hash-table$a)
                                :verify-guards nil))
                (and (,recognizer$c ,',hash-table$c)
                     (,recognizer$a ,',hash-table$a)
                     (= (,count$c ,',hash-table$c)
                        (,count$a ,',hash-table$a))
                     ,@(and ,copyable
                            `((equal (,keys$c ,',hash-table$c)
                                     (,keys$a ,',hash-table$a))))
                     (,',hash-table$corr-keys ,',hash-table$c ,',hash-table$a)
                     (,',hash-table$corr-vals ,',hash-table$c ,',hash-table$a)))))))))


;;;; `DEFINE-HASH-TABLE$ABS'
(defmacro define-hash-table$abs
    (hash-table test
     &key
       (logic 'nil)
       (exec 'nil)
       (copyable 't)

       (recognizer 'nil)
       (creator 'nil)
       (fixer 'nil)
       (accessor 'nil)
       (updater 'nil)
       (boundp 'nil)
       (getp 'nil)
       (remover 'nil)
       (count 'nil)
       (clear 'nil)
       (init 'nil)
       (keys 'nil)
       (keys-set 'nil)

       (executable 'nil)

       (debug 'nil))

  (declare (xargs :guard (and (symbolp hash-table)
                              (valid-hash-table-test-p test)
                              (symbolp logic)
                              (symbolp exec)
                              (booleanp copyable)
                              (symbol-listp (list recognizer
                                                  creator
                                                  fixer
                                                  accessor
                                                  updater
                                                  boundp
                                                  getp
                                                  remover
                                                  count
                                                  clear
                                                  init
                                                  keys
                                                  keys-set))
                              (or copyable
                                  (and (not keys)
                                       (not keys-set)))
                              (booleanp executable)
                              (booleanp debug))))

  (let* ((hash-table$a (or logic
                           (symbolicate hash-table hash-table '$a)))
         (hash-table$c (or exec
                           (symbolicate hash-table hash-table '$c)))

         (recognizer (or recognizer
                         (symbolicate hash-table hash-table (make-predicate-suffix hash-table))))
         (creator (or creator
                      (symbolicate hash-table 'create- hash-table)))
         (fixer (or fixer
                    (symbolicate hash-table hash-table '-fix)))
         (accessor (or accessor
                       (symbolicate hash-table hash-table '-get)))
         (updater (or updater
                      (symbolicate hash-table hash-table '-put)))
         (boundp (or boundp
                     (symbolicate hash-table hash-table '-boundp)))
         (getp (or getp
                   (symbolicate hash-table hash-table '-getp)))
         (remover (or remover
                      (symbolicate hash-table hash-table '-rem)))
         (count (or count
                    (symbolicate hash-table hash-table '-count)))
         (clear (or clear
                    (symbolicate hash-table hash-table '-clear)))
         (init (or init
                   (symbolicate hash-table hash-table '-init)))
         (keys (or keys
                   (symbolicate hash-table hash-table '-keys)))
         (keys-set (or keys-set
                       (symbolicate hash-table hash-table '-keys-set)))

         (hash-table$corr (symbolicate hash-table hash-table '$corr))
         (hash-table$corr-keys (symbolicate hash-table hash-table$corr '-keys))
         (hash-table$corr-keys-witness (symbolicate hash-table hash-table$corr-keys '-witness))
         (hash-table$corr-vals (symbolicate hash-table hash-table$corr '-vals))
         (hash-table$corr-vals-witness (symbolicate hash-table hash-table$corr-vals '-witness))

         (creator{correspondence} (symbolicate hash-table creator '{correspondence}))
         (creator{preserved} (symbolicate hash-table creator '{preserved}))
         (fixer{correspondence} (symbolicate hash-table fixer '{correspondence}))
         (fixer{preserved} (symbolicate hash-table fixer '{preserved}))
         (accessor{correspondence} (symbolicate hash-table accessor '{correspondence}))
         (accessor{guard-thm} (symbolicate hash-table accessor '{guard-thm}))
         (updater{correspondence} (symbolicate hash-table updater '{correspondence}))
         (updater{guard-thm} (symbolicate hash-table updater '{guard-thm}))
         (updater{preserved} (symbolicate hash-table updater '{preserved}))
         (boundp{correspondence} (symbolicate hash-table boundp '{correspondence}))
         (boundp{guard-thm} (symbolicate hash-table boundp '{guard-thm}))
         (getp{correspondence} (symbolicate hash-table getp '{correspondence}))
         (getp{guard-thm} (symbolicate hash-table getp '{guard-thm}))
         (remover{correspondence} (symbolicate hash-table remover '{correspondence}))
         (remover{guard-thm} (symbolicate hash-table remover '{guard-thm}))
         (remover{preserved} (symbolicate hash-table remover '{preserved}))
         (count{correspondence} (symbolicate hash-table count '{correspondence}))
         (clear{correspondence} (symbolicate hash-table clear '{correspondence}))
         (clear{preserved} (symbolicate hash-table clear '{preserved}))
         (init{correspondence} (symbolicate hash-table init '{correspondence}))
         (init{guard-thm} (symbolicate hash-table init '{guard-thm}))
         (init{preserved} (symbolicate hash-table init '{preserved}))
         (keys{correspondence} (symbolicate hash-table keys '{correspondence}))
         (keys-set{correspondence} (symbolicate hash-table keys-set '{correspondence}))
         (keys-set{preserved} (symbolicate hash-table keys-set '{preserved})))

    `(with-output
       ,@(and (not debug)
              '#!acl2(:off (warning! observation prove event history proof-tree)
                           :summary-off (rules)
                           :gag-mode t))

       (make-event
         (let* ((recognizer$c (stobj-recognizer ',hash-table$c))
                (recognizer$a (stobj$a-recognizer ',hash-table$a))
                (creator$c (stobj-creator ',hash-table$c))
                (creator$a (stobj$a-creator ',hash-table$a))
                (fixer$c (symbolicate ',hash-table$c ',hash-table$c '-fix))
                (fixer$c$inline (symbolicate fixer$c fixer$c '$inline))
                (fixer$a (stobj$a-fixer ',hash-table$a))
                (accessor$c (stobj$c-hash-table-accessor ',hash-table$c ,copyable))
                (accessor$a (stobj$a-hash-table-accessor ',hash-table$a))
                (updater$c (stobj$c-hash-table-updater ',hash-table$c ,copyable))
                (updater$a (stobj$a-hash-table-updater ',hash-table$a))
                (boundp$c (stobj$c-hash-table-boundp ',hash-table$c ,copyable))
                (boundp$a (stobj$a-hash-table-boundp ',hash-table$a))
                (getp$c (stobj$c-hash-table-getp ',hash-table$c ,copyable))
                (getp$a (stobj$a-hash-table-getp ',hash-table$a))
                (remover$c (stobj$c-hash-table-remover ',hash-table$c ,copyable))
                (remover$a (stobj$a-hash-table-remover ',hash-table$a))
                (count$c (stobj$c-hash-table-count ',hash-table$c ,copyable))
                (count$a (stobj$a-hash-table-count ',hash-table$a))
                (clear$c (stobj$c-hash-table-clear ',hash-table$c ,copyable))
                (clear$c (if ,copyable
                             (symbolicate clear$c
                                          (coerce (remove #\% (coerce (symbol-name clear$c)
                                                                      'list))
                                                  'acl2::string))
                             clear$c))
                (clear$a (stobj$a-hash-table-clear ',hash-table$a))
                (init$c (stobj$c-hash-table-init ',hash-table$c ,copyable))
                (init$c (if ,copyable
                            (symbolicate init$c
                                         (coerce (remove #\% (coerce (symbol-name init$c)
                                                                     'list))
                                                 'acl2::string))
                            init$c))
                (init$a (stobj$a-hash-table-init ',hash-table$a))
                (keys$c (stobj$c-hash-table-keys ',hash-table$c ,copyable))
                (keys$a (stobj$a-hash-table-keys ',hash-table$a))
                (keys-set$c (stobj$c-hash-table-keys-set ',hash-table$c ,copyable))
                (keys-set$a (stobj$a-hash-table-keys-set ',hash-table$a))

                (key-recognizer (stobj$a-hash-table-key-recognizer ',hash-table$a))
                (key-fixer (stobj$a-hash-table-key-fixer ',hash-table$a))
                (val-recognizer (stobj$a-hash-table-val-recognizer ',hash-table$a))
                (val-fixer (stobj$a-hash-table-val-fixer ',hash-table$a))
                (val (stobj$a-hash-table-val ',hash-table$a))
                (default-val (stobj$a-hash-table-default-val ',hash-table$a))
                (val-type-is-stobj (stobj-p val))
                (val-stobj$a (stobj$a-lookup val))
                (val-recognizer$a (if val-stobj$a
                                      (stobj$a-recognizer val-stobj$a)
                                      val-recognizer))
                (val-fixer$a (if val-stobj$a
                                 (stobj$a-fixer val-stobj$a)
                                 val-fixer))

                (exports `((,',fixer :logic ,fixer$a
                                     :exec ,fixer$c$inline)
                           (,',accessor :logic ,accessor$a
                                        :exec ,accessor$c
                                        ,@(and val-type-is-stobj
                                               `(:updater ,',updater)))
                           (,',updater :logic ,updater$a
                                       :exec ,updater$c)
                           (,',boundp :logic ,boundp$a
                                      :exec ,boundp$c)
                           (,',getp :logic ,getp$a
                                    :exec ,getp$c)
                           (,',remover :logic ,remover$a
                                       :exec ,remover$c)
                           (,',count :logic ,count$a
                                     :exec ,count$c)
                           (,',clear :logic ,clear$a
                                     :exec ,clear$c
                                     ,@(and ',copyable
                                            `(:protect t)))
                           (,',init :logic ,init$a
                                    :exec ,init$c
                                    ,@(and ',copyable
                                           `(:protect t)))
                           ,@(and ,copyable
                                  `((,',keys :logic ,keys$a
                                             :exec ,keys$c)
                                    (,',keys-set :logic ,keys-set$a
                                                 :exec ,keys-set$c)))))

                (updater$c-guard
                 (cdr (untranslate (getpropc updater$c 'guard)
                                   nil
                                   (w state))))
                (updater$c-guard (if val-type-is-stobj
                                     (cddr updater$c-guard)
                                     (cdr updater$c-guard))))

           `(encapsulate ()
              ,@(and (or key-recognizer
                         key-fixer)
                     `((local
                         (in-theory
                           (disable ,key-recognizer
                                    ,key-fixer)))))

              ,@(and (or val-recognizer$a
                         val-fixer$a)
                     `((local
                         (in-theory
                           (disable ,val-recognizer$a
                                    ,val-fixer$a)))))

              ;; Proof Obligations
              (lprogn
                (defthm ,',creator{correspondence}
                  (,',hash-table$corr (,creator$c)
                                      (,creator$a))
                  :rule-classes nil)

                (defthm ,',creator{preserved}
                  (,recognizer$a (,creator$a))
                  :rule-classes nil)

                (defthm ,',fixer{correspondence}
                  (implies (and (,',hash-table$corr ,',hash-table$c ,',hash-table)
                                (,recognizer$a ,',hash-table))
                           (,',hash-table$corr (,fixer$c ,',hash-table$c)
                                               (,fixer$a ,',hash-table)))
                  :rule-classes nil)

                (defthm ,',fixer{preserved}
                  (implies (,recognizer$a ,',hash-table)
                           (,recognizer$a (,fixer$a ,',hash-table)))
                  :rule-classes nil)

                (defthm ,',accessor{correspondence}
                  (implies (and (,',hash-table$corr ,',hash-table$c ,',hash-table)
                                ,@(and key-recognizer
                                       `((,key-recognizer k)))
                                (,recognizer$a ,',hash-table))
                           (equal (,accessor$c k ,',hash-table$c)
                                  (,accessor$a k ,',hash-table)))
                  :rule-classes nil
                  :hints
                  (("Goal"
                    :in-theory (disable ,',hash-table$corr-vals))))

                ,@(and ',(or (eq test 'eq)
                             (eq test 'eql))
                       `((defthm ,',accessor{guard-thm}
                           (implies (and (,',hash-table$corr ,',hash-table$c ,',hash-table)
                                         ,@(and key-recognizer
                                                `((,key-recognizer k)))
                                         (,recognizer$a ,',hash-table))
                                    ,(if ',(eq test 'eq)
                                         '(symbolp k)
                                         '(eqlablep k)))
                           :rule-classes nil)))

                (defthm ,',updater{correspondence}
                  (implies (and (,',hash-table$corr ,',hash-table$c ,',hash-table)
                                ,@(and key-recognizer
                                       `((,key-recognizer k)))
                                ,@(and val-recognizer
                                       `((,val-recognizer v)))
                                (,recognizer$a ,',hash-table))
                           (,',hash-table$corr (,updater$c k v ,',hash-table$c)
                                               (,updater$a k v ,',hash-table)))
                  :rule-classes nil
                  :hints
                  (("Goal"
                    :do-not-induct t
                    :in-theory (disable ,',hash-table$corr-keys
                                        ,',hash-table$corr-vals))
                   ("Subgoal 3"
                    :cases ((,boundp$c k ,',hash-table$c)))
                   ("Subgoal 2"
                    :cases ((equal k (,',hash-table$corr-vals-witness
                                      (,updater$c k v ,',hash-table$c)
                                      (,updater$a k v ,',hash-table))))
                    :expand ((,',hash-table$corr-vals (,updater$c k v ,',hash-table$c)
                                                      (,updater$a k v ,',hash-table))
                             (,',hash-table$corr-vals (,updater$c k ,default-val ,',hash-table$c)
                                                      (,updater$a k ,default-val ,',hash-table))))
                   ("Subgoal 1"
                    :cases ((equal k (,',hash-table$corr-keys-witness
                                      (,updater$c k v ,',hash-table$c)
                                      (,updater$a k v ,',hash-table))))
                    :expand ((,',hash-table$corr-keys (,updater$c k v ,',hash-table$c)
                                                      (,updater$a k v ,',hash-table))
                             (,',hash-table$corr-keys (,updater$c k ,default-val ,',hash-table$c)
                                                      (,updater$a k ,default-val ,',hash-table))))))

                ,@(and updater$c-guard
                       `((defthm ,',updater{guard-thm}
                           (implies (and (,',hash-table$corr ,',hash-table$c ,',hash-table)
                                         ,@(and key-recognizer
                                                `((,key-recognizer k)))
                                         ,@(and val-recognizer
                                                `((,val-recognizer v)))
                                         (,recognizer$a ,',hash-table))
                                    ,(if (null (cdr updater$c-guard))
                                         (car updater$c-guard)
                                         (cons 'and updater$c-guard)))
                           :rule-classes nil)))

                (defthm ,',updater{preserved}
                  (implies (and ,@(and key-recognizer
                                       `((,key-recognizer k)))
                                ,@(and val-recognizer
                                       `((,val-recognizer v)))
                                (,recognizer$a ,',hash-table))
                           (,recognizer$a (,updater$a k v ,',hash-table)))
                  :rule-classes nil)

                (defthm ,',boundp{correspondence}
                  (implies (and (,',hash-table$corr ,',hash-table$c ,',hash-table)
                                ,@(and key-recognizer
                                       `((,key-recognizer k)))
                                (,recognizer$a ,',hash-table))
                           (equal (,boundp$c k ,',hash-table$c)
                                  (,boundp$a k ,',hash-table)))
                  :rule-classes nil
                  :hints
                  (("Goal"
                    :in-theory (disable ,',hash-table$corr-keys))))

                ,@(and ',(or (eq test 'eq)
                             (eq test 'eql))
                       `((defthm ,',boundp{guard-thm}
                           (implies (and (,',hash-table$corr ,',hash-table$c ,',hash-table)
                                         ,@(and key-recognizer
                                                `((,key-recognizer k)))
                                         (,recognizer$a ,',hash-table))
                                    ,(if ',(eq test 'eq)
                                         '(symbolp k)
                                         '(eqlablep k)))
                           :rule-classes nil)))

                (defthm ,',getp{correspondence}
                  (implies (and (,',hash-table$corr ,',hash-table$c ,',hash-table)
                                ,@(and key-recognizer
                                       `((,key-recognizer k)))
                                (,recognizer$a ,',hash-table))
                           (let ((lhs (,getp$c k ,',hash-table$c))
                                 (rhs (,getp$a k ,',hash-table)))
                             (and (equal (mv-nth 0 lhs) (mv-nth 0 rhs))
                                  (equal (mv-nth 1 lhs) (mv-nth 1 rhs)))))
                  :rule-classes nil
                  :hints
                  (("Goal"
                    :in-theory (disable ,',hash-table$corr-keys
                                        ,',hash-table$corr-vals))))

                ,@(and ',(or (eq test 'eq)
                             (eq test 'eql))
                       `((defthm ,',getp{guard-thm}
                           (implies (and (,',hash-table$corr ,',hash-table$c ,',hash-table)
                                         ,@(and key-recognizer
                                                `((,key-recognizer k)))
                                         (,recognizer$a ,',hash-table))
                                    ,(if ',(eq test 'eq)
                                         '(symbolp k)
                                         '(eqlablep k)))
                           :rule-classes nil)))

                (defthm ,',remover{correspondence}
                  (implies (and (,',hash-table$corr ,',hash-table$c ,',hash-table)
                                ,@(and key-recognizer
                                       `((,key-recognizer k)))
                                (,recognizer$a ,',hash-table))
                           (,',hash-table$corr (,remover$c k ,',hash-table$c)
                                               (,remover$a k ,',hash-table)))
                  :rule-classes nil
                  :hints
                  (("Goal"
                    :do-not-induct t
                    :in-theory (disable ,',hash-table$corr-keys
                                        ,',hash-table$corr-vals))
                   ("Subgoal 3"
                    :cases ((,boundp$c k ,',hash-table$c)))
                   ("Subgoal 2"
                    :cases ((equal k (,',hash-table$corr-vals-witness
                                      (,remover$c k ,',hash-table$c)
                                      (,remover$a k ,',hash-table))))
                    :expand ((,',hash-table$corr-vals (,remover$c k ,',hash-table$c)
                                                      (,remover$a k ,',hash-table))))
                   ("Subgoal 1"
                    :cases ((equal k (,',hash-table$corr-keys-witness
                                      (,remover$c k ,',hash-table$c)
                                      (,remover$a k ,',hash-table))))
                    :expand ((,',hash-table$corr-keys (,remover$c k ,',hash-table$c)
                                                      (,remover$a k ,',hash-table))))))

                ,@(and ',(or (eq test 'eq)
                             (eq test 'eql))
                       `((defthm ,',remover{guard-thm}
                           (implies (and (,',hash-table$corr ,',hash-table$c ,',hash-table)
                                         ,@(and key-recognizer
                                                `((,key-recognizer k)))
                                         (,recognizer$a ,',hash-table))
                                    ,(if ',(eq test 'eq)
                                         '(symbolp k)
                                         '(eqlablep k)))
                           :rule-classes nil)))

                (defthm ,',remover{preserved}
                  (implies (and ,@(and key-recognizer
                                       `((,key-recognizer k)))
                                (,recognizer$a ,',hash-table))
                           (,recognizer$a (,remover$a k ,',hash-table)))
                  :rule-classes nil)

                (defthm ,',count{correspondence}
                  (implies (and (,',hash-table$corr ,',hash-table$c ,',hash-table)
                                (,recognizer$a ,',hash-table))
                           (equal (,count$c ,',hash-table$c)
                                  (,count$a ,',hash-table)))
                  :rule-classes nil)

                (defthm ,',clear{correspondence}
                  (implies (and (,',hash-table$corr ,',hash-table$c ,',hash-table)
                                (,recognizer$a ,',hash-table))
                           (,',hash-table$corr (,clear$c ,',hash-table$c)
                                               (,clear$a ,',hash-table)))
                  :rule-classes nil)

                (defthm ,',clear{preserved}
                  (implies (,recognizer$a ,',hash-table)
                           (,recognizer$a (,clear$a ,',hash-table)))
                  :rule-classes nil)

                (defthm ,',init{correspondence}
                  (implies (and (,',hash-table$corr ,',hash-table$c ,',hash-table)
                                (,recognizer$a ,',hash-table)
                                (or (natp ht-size)
                                    (not ht-size))
                                (or (and (rationalp rehash-size)
                                         (<= 1 rehash-size))
                                    (not rehash-size))
                                (or (and (rationalp rehash-threshold)
                                         (<= 0 rehash-threshold)
                                         (<= rehash-threshold 1))
                                    (not rehash-threshold)))
                           (,',hash-table$corr (,init$c ht-size
                                                        rehash-size
                                                        rehash-threshold
                                                        ,',hash-table$c)
                                               (,init$a ht-size
                                                        rehash-size
                                                        rehash-threshold
                                                        ,',hash-table)))
                  :rule-classes nil)

                (defthm ,',init{guard-thm}
                  (implies (and (,',hash-table$corr ,',hash-table$c ,',hash-table)
                                (,recognizer$a ,',hash-table)
                                (or (natp ht-size)
                                    (not ht-size))
                                (or (and (rationalp rehash-size)
                                         (<= 1 rehash-size))
                                    (not rehash-size))
                                (or (and (rationalp rehash-threshold)
                                         (<= 0 rehash-threshold)
                                         (<= rehash-threshold 1))
                                    (not rehash-threshold)))
                           (and (or (natp ht-size) (not ht-size))
                                (or (and (rationalp rehash-size)
                                         (<= 1 rehash-size))
                                    (not rehash-size))
                                (or (and (rationalp rehash-threshold)
                                         (<= 0 rehash-threshold)
                                         (<= rehash-threshold 1))
                                    (not rehash-threshold))))
                  :rule-classes nil)

                (defthm ,',init{preserved}
                  (implies (and (,recognizer$a ,',hash-table)
                                (or (natp ht-size)
                                    (not ht-size))
                                (or (and (rationalp rehash-size)
                                         (<= 1 rehash-size))
                                    (not rehash-size))
                                (or (and (rationalp rehash-threshold)
                                         (<= 0 rehash-threshold)
                                         (<= rehash-threshold 1))
                                    (not rehash-threshold)))
                           (,recognizer$a (,init$a ht-size
                                                   rehash-size
                                                   rehash-threshold
                                                   ,',hash-table)))
                  :rule-classes nil)

                ,@(and ',copyable
                       `((defthm ,',keys{correspondence}
                           (implies (and (,',hash-table$corr ,',hash-table$c,',hash-table)
                                         (,recognizer$a ,',hash-table))
                                    (equal (,keys$c ,',hash-table$c)
                                           (,keys$a ,',hash-table)))
                           :rule-classes nil)

                         (defthm ,',keys-set{correspondence}
                           (implies (and (,',hash-table$corr ,',hash-table$c,',hash-table)
                                         (set::setp v)
                                         (,recognizer$a ,',hash-table))
                                    (,',hash-table$corr (,keys-set$c v ,',hash-table$c)
                                                        (,keys-set$a v ,',hash-table)))
                           :rule-classes nil
                           :hints
                           (("Goal"
                             :in-theory (disable ,',hash-table$corr-keys
                                                 ,',hash-table$corr-vals))
                            ("Subgoal 2"
                             :expand (,',hash-table$corr-keys (,keys-set$c v ,',hash-table$c)
                                                              (,keys-set$a v ,',hash-table)))
                            ("Subgoal 1"
                             :expand (,',hash-table$corr-vals (,keys-set$c v ,',hash-table$c)
                                                              (,keys-set$a v ,',hash-table)))))

                         (defthm ,',keys-set{preserved}
                           (implies (and (set::setp v)
                                         (,recognizer$a ,',hash-table))
                                    (,recognizer$a (,keys-set$a v ,',hash-table)))
                           :rule-classes nil))))

              (defabsstobj ,',hash-table
                :foundation ,',hash-table$c
                :recognizer (,',recognizer :logic ,recognizer$a
                                           :exec ,recognizer$c)
                :creator (,',creator :logic ,creator$a
                                     :exec ,creator$c)
                :corr-fn ,',hash-table$corr
                :non-executable ,',(not executable)
                :exports ,exports)

              (table stobj$a
                     'stobj$a-lookup-alist
                     (putprop ',',hash-table
                              'stobj$a
                              ',',hash-table$a
                              (stobj$a-lookup-alist world)))))))))


;;;; `DEFINE-HASH-TABLE'
(defmacro define-hash-table
    (hash-table test
     &key
       (size 'nil)
       (element-type 't)
       (key-recognizer 'nil)
       (key-fixer 'nil)
       (key 'key)
       (default-key 'nil)
       (val-recognizer 'nil)
       (val-fixer 'nil)
       (val 'val)
       (default-val 'nil)
       (copyable 't)

       (inline 'nil)
       (memoizable 'nil)
       (executable 'nil)

       (recognizer 'nil)
       (creator 'nil)
       (accessor 'nil)
       (updater 'nil)
       (boundp 'nil)
       (getp 'nil)
       (remover 'nil)
       (count 'nil)
       (clear 'nil)
       (init 'nil)
       (keys 'nil)
       (keys-set 'nil)

       (logic 'nil)
       (exec 'nil)

       (debug 'nil))

  (declare (xargs :guard (and (symbolp hash-table)
                              (valid-hash-table-test-p test)
                              (valid-hash-table-size-p size)
                              (if (acl2-type-spec-p element-type)
                                  (typep$ default-val element-type)
                                  (symbolp element-type))
                              (booleanp copyable)
                              (symbol-listp (list key-recognizer
                                                  key-fixer
                                                  key
                                                  val-recognizer
                                                  val-fixer
                                                  val))
                              (or (and (not key-recognizer)
                                       (not key-fixer)
                                       (not (or (eq test 'eq)
                                                (eq test 'eql))))
                                  (and key-recognizer
                                       key-fixer))
                              (or (and (not val-recognizer)
                                       (not val-fixer))
                                  (and val-recognizer
                                       val-fixer))
                              (booleanp inline)
                              (booleanp memoizable)
                              (booleanp executable)
                              (symbol-listp (list recognizer
                                                  creator
                                                  accessor
                                                  updater
                                                  boundp
                                                  getp
                                                  remover
                                                  count
                                                  clear
                                                  init
                                                  keys
                                                  keys-set))
                              (or copyable
                                  (and (not keys)
                                       (not keys-set)))
                              (symbolp logic)
                              (symbolp exec)
                              (booleanp debug))))

  (let* ((hash-table$a (or logic
                           (symbolicate hash-table hash-table '$a)))
         (hash-table$c (or exec
                           (symbolicate hash-table hash-table '$c)))
         (recognizer (or recognizer
                         (symbolicate hash-table hash-table (make-predicate-suffix hash-table))))
         (creator (or creator
                      (symbolicate hash-table 'create- hash-table)))
         (accessor (or accessor
                       (symbolicate hash-table hash-table '-get)))
         (updater (or updater
                      (symbolicate hash-table hash-table '-put)))
         (boundp (or boundp
                     (symbolicate hash-table hash-table '-boundp)))
         (getp (or getp
                   (symbolicate hash-table hash-table '-getp)))
         (remover (or remover
                      (symbolicate hash-table hash-table '-rem)))
         (count (or count
                    (symbolicate hash-table hash-table '-count)))
         (clear (or clear
                    (symbolicate hash-table hash-table '-clear)))
         (init (or init
                   (symbolicate hash-table hash-table '-init)))
         (keys (or keys
                   (symbolicate hash-table hash-table '-keys)))
         (keys-set (or keys-set
                       (symbolicate hash-table hash-table '-keys-set))))

    `(with-output
       ,@(and (not debug)
              '#!acl2(:off (warning! observation prove event history proof-tree)
                           :summary-off (rules)
                           :gag-mode t))

       (make-event
         `(progn
            (define-hash-table$c ,',hash-table$c ,',test
              :size ,',size
              :element-type ,',element-type
              :default-value ,',default-val
              :copyable ,',copyable
              :inline ,',inline
              :memoizable ,',memoizable
              :executable ,',executable
              :debug ,',debug)

            (define-hash-table$a ,',hash-table$a ,',test
              :key-recognizer ,',key-recognizer
              :key-fixer ,',key-fixer
              :key ,',key
              :default-key ,',default-key
              :val-recognizer ,',val-recognizer
              :val-fixer ,',val-fixer
              :val ,',val
              :default-val ,',default-val
              :copyable ,',copyable
              :debug ,',debug)

            (define-hash-table$corr ,',hash-table
              :logic ,',hash-table$a
              :exec ,',hash-table$c
              :copyable ,',copyable
              :debug ,',debug)

            (define-hash-table$abs ,',hash-table ,',test
              :logic ,',hash-table$a
              :exec ,',hash-table$c
              :copyable ,',copyable
              :recognizer ,',recognizer
              :creator ,',creator
              :accessor ,',accessor
              :updater ,',updater
              :boundp ,',boundp
              :getp ,',getp
              :remover ,',remover
              :count ,',count
              :clear ,',clear
              :init ,',init
              ,@(and ',copyable
                     `(:keys ,',keys
                             :keys-set ,',keys-set))
              :executable ,',executable
              :debug ,',debug)

            (in-theory
              (disable ,',(symbolicate hash-table$c hash-table$c '-theorems))))))))


;;;; `HASH-TABLE-THEOREMS'
(deflabel define-hash-table-end)

(deftheory-static define-hash-table-theorems
  (set-difference-theories
   (set-difference-theories
    (current-theory 'define-hash-table-end)
    (current-theory 'define-hash-table-begin))
   (function-theory 'define-hash-table-end)))


;;;; Epilogue
(in-theory
  (union-theories (current-theory 'define-hash-table-begin)
                  (theory 'define-hash-table-theorems)))
