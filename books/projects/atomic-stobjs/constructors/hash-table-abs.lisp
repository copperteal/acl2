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

(include-book "std/osets/top" :dir :system)

(include-book "../utilities/top")


;;;; `DEFINE-HASH-TABLE$CORR'
(defmacro define-hash-table$corr (hash-table
                                  &key
                                    (logic 'nil)
                                    (exec 'nil)
                                    (copyable 't)

                                    (package-witness 'nil package-witness-supplied-p)
                                    (package-witness$a 'nil package-witness$a-supplied-p)
                                    (package-witness$c 'nil package-witness$c-supplied-p)
                                    (debug 'nil))
  (declare (xargs :guard (and (symbolp hash-table)
                              (symbolp logic)
                              (symbolp exec)
                              (booleanp copyable)
                              (package-witness-p package-witness)
                              (package-witness-p package-witness$a)
                              (package-witness-p package-witness$c)
                              (booleanp debug))))

  `(with-output
     ,@(and (not debug)
            *constructor-output*)

     (make-event
       (let* ((hash-table ',hash-table)
              (logic ',logic)
              (exec ',exec)
              (package-witness (if ',package-witness-supplied-p
                                   ',package-witness
                                   (current-package state)))
              (package-witness$a (if ',package-witness$a-supplied-p
                                     ',package-witness$a
                                     package-witness))
              (package-witness$c (if ',package-witness$c-supplied-p
                                     ',package-witness$c
                                     package-witness))

              (copyable ',copyable)
              (hash-table$corr (symbolicate package-witness hash-table "$CORR"))
              (hash-table$corr-keys (symbolicate package-witness hash-table$corr "-KEYS"))
              (hash-table$corr-vals (symbolicate package-witness hash-table$corr "-VALS"))

              (hash-table$a (or logic
                                (symbolicate package-witness$a hash-table "$A")))
              (hash-table$c (or exec
                                (symbolicate package-witness$c hash-table "$C")))

              (stobj-property (getpropc hash-table$c 'acl2::stobj))
              (recognizer$c (caadr stobj-property))
              (accessor$c (if copyable
                              (third (third stobj-property))
                              (second (third stobj-property))))
              (boundp$c  (if copyable
                             (fifth (third stobj-property))
                             (fourth (third stobj-property))))
              (count$c (if copyable
                           (eighth (third stobj-property))
                           (seventh (third stobj-property))))
              (keys$c (and copyable
                           (nth 10 (third stobj-property))))

              (stobj$a-property (cdr (assoc hash-table$a (table-alist 'stobj$a-property (w state)))))
              (recognizer$a (first (second stobj$a-property)))
              (key-recognizer (second (first (third stobj$a-property))))
              (accessor$a (first (fourth (third stobj$a-property))))
              (boundp$a (third (fourth (third stobj$a-property))))
              (count$a (sixth (fourth (third stobj$a-property))))
              (keys$a (and copyable
                           (first (fifth (third stobj$a-property))))))

         `(progn
            (defun-sk ,hash-table$corr-keys (,hash-table$c ,hash-table$a)
              (declare (xargs :stobjs ,hash-table$c
                              :guard t
                              :verify-guards nil))
              (forall k
                ,(let ((identity `(equal (,boundp$c k ,hash-table$c)
                                         (,boundp$a k ,hash-table$a))))
                   (if key-recognizer
                       `(implies (,key-recognizer k)
                                 ,identity)
                       identity)))
              :rewrite :direct)

            (defun-sk ,hash-table$corr-vals (,hash-table$c ,hash-table$a)
              (declare (xargs :stobjs ,hash-table$c
                              :guard t
                              :verify-guards nil))
              (forall k
                ,(let ((identity `(equal (,accessor$c k ,hash-table$c)
                                         (,accessor$a k ,hash-table$a))))
                   (if key-recognizer
                       `(implies (,key-recognizer k)
                                 ,identity)
                       identity)))
              :rewrite :direct)

            (defun-nx ,hash-table$corr (,hash-table$c ,hash-table$a)
              (declare (xargs :stobjs ,hash-table$c
                              :guard (,recognizer$a ,hash-table$a)
                              :verify-guards nil))
              (and (,recognizer$c ,hash-table$c)
                   (,recognizer$a ,hash-table$a)
                   ,@(and ,copyable
                          `((equal (,keys$c ,hash-table$c)
                                   (,keys$a ,hash-table$a))))
                   (= (,count$c ,hash-table$c)
                      (,count$a ,hash-table$a))
                   (,hash-table$corr-keys ,hash-table$c ,hash-table$a)
                   (,hash-table$corr-vals ,hash-table$c ,hash-table$a)))

            (table corr ',hash-table ',(list hash-table$corr-keys
                                             hash-table$corr-vals
                                             hash-table$corr)))))))


;;;; `DEFINE-HASH-TABLE$ABS'
(defmacro define-hash-table$abs
    (hash-table
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

       (package-witness 'nil package-witness-supplied-p)
       (package-witness$a 'nil package-witness$a-supplied-p)
       (package-witness$c 'nil package-witness$c-supplied-p)
       (debug 'nil))

  (declare (xargs :guard (and (symbolp hash-table)
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
                              (package-witness-p package-witness)
                              (package-witness-p package-witness$a)
                              (package-witness-p package-witness$c)
                              (booleanp debug))))

  `(with-output
     ,@(and (not debug)
            *constructor-output*)

     (make-event
       (let* ((hash-table ',hash-table)
              (logic ',logic)
              (exec ',exec)
              (copyable ',copyable)
              (recognizer ',recognizer)
              (creator ',creator)
              (fixer ',fixer)
              (accessor ',accessor)
              (updater ',updater)
              (boundp ',boundp)
              (getp ',getp)
              (remover ',remover)
              (count ',count)
              (clear ',clear)
              (init ',init)
              (keys ',keys)
              (keys-set ',keys-set)
              (executable ',executable)
              (package-witness (if ',package-witness-supplied-p
                                   ',package-witness
                                   (current-package state)))
              (package-witness$a (if ',package-witness$a-supplied-p
                                     ',package-witness$a
                                     package-witness))
              (package-witness$c (if ',package-witness$c-supplied-p
                                     ',package-witness$c
                                     package-witness))

              ;; Interface Symbols
              (hash-table$a (or logic
                                (symbolicate package-witness$a hash-table "$A")))
              (hash-table$c (or exec
                                (symbolicate package-witness$c hash-table "$C")))
              (recognizer (or recognizer
                              (symbolicate package-witness hash-table (make-predicate-suffix hash-table))))
              (creator (or creator
                           (symbolicate package-witness "CREATE-" hash-table)))
              (fixer (or fixer
                         (symbolicate package-witness hash-table "-FIX")))
              (accessor (or accessor
                            (symbolicate package-witness hash-table "-GET")))
              (updater (or updater
                           (symbolicate package-witness hash-table "-PUT")))
              (boundp (or boundp
                          (symbolicate package-witness hash-table "-BNDP")))
              (getp (or getp
                        (symbolicate package-witness hash-table "-GETP")))
              (remover (or remover
                           (symbolicate package-witness hash-table "-REM")))
              (count (or count
                         (symbolicate package-witness hash-table "-CNT")))
              (clear (or clear
                         (symbolicate package-witness hash-table "-CLR")))
              (init (or init
                        (symbolicate package-witness hash-table "-INIT")))
              (keys (or keys
                        (symbolicate package-witness hash-table "-KEYS")))
              (keys-set (or keys-set
                            (symbolicate package-witness hash-table "-KEYS-SET")))

              (world (w state))
              (hash-table$corr-list (cdr (assoc hash-table (table-alist 'corr world))))
              (hash-table$corr-keys (first hash-table$corr-list))
              (hash-table$corr-vals (second hash-table$corr-list))
              (hash-table$corr (third hash-table$corr-list))

              ;; `HASH-TABLE$C'
              (stobj-property (getpropc hash-table$c 'acl2::stobj))
              (recognizer$c (caadr stobj-property))
              (creator$c (cdadr stobj-property))
              (fixer$c (cdr (assoc hash-table$c (table-alist 'fixer world))))
              (fixer$c$inline (or (cdr (assoc fixer$c (table-alist 'acl2::macro-aliases-table world)))
                                  fixer$c))
              (accessor$c (if copyable
                              (third (third stobj-property))
                              (second (third stobj-property))))
              (updater$c (if copyable
                             (fourth (third stobj-property))
                             (third (third stobj-property))))
              (boundp$c (if copyable
                            (fifth (third stobj-property))
                            (fourth (third stobj-property))))
              (getp$c (if copyable
                          (sixth (third stobj-property))
                          (fifth (third stobj-property))))
              (remover$c (if copyable
                             (seventh (third stobj-property))
                             (sixth (third stobj-property))))
              (count$c (if copyable
                           (eighth (third stobj-property))
                           (seventh (third stobj-property))))
              (clear$c (if copyable
                           (cdr (assoc hash-table$c (table-alist 'clear world)))
                           (eighth (third stobj-property))))
              (init$c (if copyable
                          (cdr (assoc hash-table$c (table-alist 'init world)))
                          (ninth (third stobj-property))))
              (keys$c (and copyable
                           (nth 10 (third stobj-property))))
              (keys-set$c (and copyable
                               (nth 11 (third stobj-property))))

              ;; `HASH-TABLE$A'
              (stobj$a-property (cdr (assoc hash-table$a (table-alist 'stobj$a-property world))))
              (recognizer$a (first (second stobj$a-property)))
              (creator$a (second (second stobj$a-property)))
              (fixer$a (third (second stobj$a-property)))
              (accessor$a (first (fourth (third stobj$a-property))))
              (updater$a (second (fourth (third stobj$a-property))))
              (boundp$a (third (fourth (third stobj$a-property))))
              (getp$a (fourth (fourth (third stobj$a-property))))
              (remover$a (fifth (fourth (third stobj$a-property))))
              (count$a (sixth (fourth (third stobj$a-property))))
              (clear$a (seventh (fourth (third stobj$a-property))))
              (init$a (eighth (fourth (third stobj$a-property))))
              (keys$a (and copyable
                           (first (fifth (third stobj$a-property)))))
              (keys-set$a (and copyable
                               (second (fifth (third stobj$a-property)))))
              (keys$ap (and copyable
                            (third (fifth (third stobj$a-property)))))

              (key-recognizer (second (first (third stobj$a-property))))
              (val (first (second (third stobj$a-property))))
              (val-stobj-property (getpropc val 'acl2::stobj))
              (val-recognizer (if val-stobj-property
                                  (caadr val-stobj-property)
                                  (second (second (third stobj$a-property)))))
              (test (first (third (third stobj$a-property))))

              ;; Theorem Names
              (creator{correspondence} (symbolicate package-witness creator "{CORRESPONDENCE}"))
              (creator{preserved} (symbolicate package-witness creator "{PRESERVED}"))
              (fixer{correspondence} (symbolicate package-witness fixer "{CORRESPONDENCE}"))
              (fixer{preserved} (symbolicate package-witness fixer "{PRESERVED}"))
              (accessor{correspondence} (symbolicate package-witness accessor "{CORRESPONDENCE}"))
              (accessor{guard-thm} (symbolicate package-witness accessor "{GUARD-THM}"))
              (updater{correspondence} (symbolicate package-witness updater "{CORRESPONDENCE}"))
              (updater{guard-thm} (symbolicate package-witness updater "{GUARD-THM}"))
              (updater{preserved} (symbolicate package-witness updater "{PRESERVED}"))
              (boundp{correspondence} (symbolicate package-witness boundp "{CORRESPONDENCE}"))
              (boundp{guard-thm} (symbolicate package-witness boundp "{GUARD-THM}"))
              (getp{correspondence} (symbolicate package-witness getp "{CORRESPONDENCE}"))
              (getp{guard-thm} (symbolicate package-witness getp "{GUARD-THM}"))
              (remover{correspondence} (symbolicate package-witness remover "{CORRESPONDENCE}"))
              (remover{guard-thm} (symbolicate package-witness remover "{GUARD-THM}"))
              (remover{preserved} (symbolicate package-witness remover "{PRESERVED}"))
              (count{correspondence} (symbolicate package-witness count "{CORRESPONDENCE}"))
              (clear{correspondence} (symbolicate package-witness clear "{CORRESPONDENCE}"))
              (clear{preserved} (symbolicate package-witness clear "{PRESERVED}"))
              (init{correspondence} (symbolicate package-witness init "{CORRESPONDENCE}"))
              (init{guard-thm} (symbolicate package-witness init "{GUARD-THM}"))
              (init{preserved} (symbolicate package-witness init "{PRESERVED}"))
              (keys{correspondence} (symbolicate package-witness keys "{CORRESPONDENCE}"))
              (keys-set{correspondence} (symbolicate package-witness keys-set "{CORRESPONDENCE}"))
              (keys-set{preserved} (symbolicate package-witness keys-set "{PRESERVED}"))

              ;; Exports
              (exports `((,fixer :logic ,fixer$a
                                 :exec ,fixer$c$inline)
                         (,accessor :logic ,accessor$a
                                    :exec ,accessor$c
                                    ,@(and val-stobj-property
                                           `(:updater ,updater)))
                         (,updater :logic ,updater$a
                                   :exec ,updater$c)
                         (,boundp :logic ,boundp$a
                                  :exec ,boundp$c)
                         (,getp :logic ,getp$a
                                :exec ,getp$c)
                         (,remover :logic ,remover$a
                                   :exec ,remover$c)
                         (,count :logic ,count$a
                                 :exec ,count$c)
                         (,clear :logic ,clear$a
                                 :exec ,clear$c
                                 ,@(and ',copyable
                                        `(:protect t)))
                         (,init :logic ,init$a
                                :exec ,init$c
                                ,@(and ',copyable
                                       `(:protect t)))
                         ,@(and ,copyable
                                `((,keys :logic ,keys$a
                                         :exec ,keys$c)
                                  (,keys-set :logic ,keys-set$a
                                             :exec ,keys-set$c)))))

              ;; Miscellaneous
              (updater$c-guard
               (cdr (untranslate (getpropc updater$c 'acl2::guard) nil world)))
              (updater$c-guard (if val-stobj-property
                                   (cddr updater$c-guard)
                                   (cdr updater$c-guard)))

              (aggressive$a (symbolicate package-witness$a hash-table$a "-AGGRESSIVE"))
              (accessor$c-key (car (getpropc accessor$c 'acl2::formals)))
              (updater$c-key (car (getpropc updater$c 'acl2::formals)))
              (updater$c-val (cadr (getpropc updater$c 'acl2::formals)))
              (boundp$c-key (car (getpropc boundp$c 'acl2::formals)))
              (getp$c-key (car (getpropc getp$c 'acl2::formals)))
              (remover$c-key (car (getpropc remover$c 'acl2::formals)))
              (keys-set$c-set (and keys-set$c
                                   (car (getpropc keys-set$c 'acl2::formals)))))

         `(encapsulate ()

            (local
              (progn
                (defthm ,creator{correspondence}
                  (,hash-table$corr (,creator$c) (,creator$a))
                  :rule-classes nil)

                (defthm ,creator{preserved}
                  (,recognizer$a (,creator$a))
                  :rule-classes nil)

                (defthm ,fixer{correspondence}
                  (implies (and (,hash-table$corr ,hash-table$c ,hash-table)
                                (,recognizer$a ,hash-table))
                           (,hash-table$corr (,fixer$c ,hash-table$c)
                                             (,fixer$a ,hash-table)))
                  :rule-classes nil)

                (defthm ,fixer{preserved}
                  (implies (,recognizer$a ,hash-table)
                           (,recognizer$a (,fixer$a ,hash-table)))
                  :rule-classes nil)

                (defthm ,accessor{correspondence}
                  (implies (and (,hash-table$corr ,hash-table$c ,hash-table)
                                ,@(and key-recognizer
                                       `((,key-recognizer ,accessor$c-key)))
                                (,recognizer$a ,hash-table))
                           (equal (,accessor$c ,accessor$c-key ,hash-table$c)
                                  (,accessor$a ,accessor$c-key ,hash-table)))
                  :rule-classes nil
                  :hints
                  (("Goal"
                    :in-theory (disable ,hash-table$corr-vals))))

                ,@(and (or (eq test 'eq)
                           (eq test 'eql))
                       `((defthm ,accessor{guard-thm}
                           (implies (and (,hash-table$corr ,hash-table$c ,hash-table)
                                         ,@(and key-recognizer
                                                `((,key-recognizer ,accessor$c-key)))
                                         (,recognizer$a ,hash-table))
                                    ,(if (eq test 'eq)
                                         `(symbolp ,accessor$c-key)
                                         `(eqlablep ,accessor$c-key)))
                           :rule-classes nil)))

                (defthm ,updater{correspondence}
                  (implies (and (,hash-table$corr ,hash-table$c ,hash-table)
                                ,@(and key-recognizer
                                       `((,key-recognizer ,updater$c-key)))
                                ,@(and val-recognizer
                                       `((,val-recognizer ,updater$c-val)))
                                (,recognizer$a ,hash-table))
                           (,hash-table$corr (,updater$c ,updater$c-key ,updater$c-val ,hash-table$c)
                                             (,updater$a ,updater$c-key ,updater$c-val ,hash-table)))
                  :rule-classes nil
                  :hints
                  (("Goal"
                    :in-theory (e/d (,aggressive$a)
                                    (,hash-table$corr-keys
                                     ,hash-table$corr-vals))
                    :expand ((,hash-table$corr-keys (,updater$c ,updater$c-key ,updater$c-val ,hash-table$c)
                                                    (,updater$a ,updater$c-key ,updater$c-val ,hash-table))
                             (,hash-table$corr-vals (,updater$c ,updater$c-key ,updater$c-val ,hash-table$c)
                                                    (,updater$a ,updater$c-key ,updater$c-val ,hash-table))))))

                ,@(and updater$c-guard
                       `((defthm ,updater{guard-thm}
                           (implies (and (,hash-table$corr ,hash-table$c ,hash-table)
                                         ,@(and key-recognizer
                                                `((,key-recognizer ,accessor$c-key)))
                                         ,@(and val-recognizer
                                                `((,val-recognizer ,updater$c-val)))
                                         (,recognizer$a ,hash-table))
                                    ,(if (null (cdr updater$c-guard))
                                         (car updater$c-guard)
                                         (cons 'and updater$c-guard)))
                           :rule-classes nil)))

                (defthm ,updater{preserved}
                  (implies (and ,@(and key-recognizer
                                       `((,key-recognizer ,accessor$c-key)))
                                ,@(and val-recognizer
                                       `((,val-recognizer ,updater$c-val)))
                                (,recognizer$a ,hash-table))
                           (,recognizer$a (,updater$a ,accessor$c-key ,updater$c-val ,hash-table)))
                  :rule-classes nil)

                (defthm ,boundp{correspondence}
                  (implies (and (,hash-table$corr ,hash-table$c ,hash-table)
                                ,@(and key-recognizer
                                       `((,key-recognizer ,boundp$c-key)))
                                (,recognizer$a ,hash-table))
                           (equal (,boundp$c ,boundp$c-key ,hash-table$c)
                                  (,boundp$a ,boundp$c-key ,hash-table)))
                  :rule-classes nil
                  :hints
                  (("Goal"
                    :in-theory (disable ,hash-table$corr-keys))))

                ,@(and (or (eq test 'eq)
                           (eq test 'eql))
                       `((defthm ,boundp{guard-thm}
                           (implies (and (,hash-table$corr ,hash-table$c ,hash-table)
                                         ,@(and key-recognizer
                                                `((,key-recognizer ,boundp$c-key)))
                                         (,recognizer$a ,hash-table))
                                    ,(if (eq test 'eq)
                                         `(symbolp ,boundp$c-key)
                                         `(eqlablep ,boundp$c-key)))
                           :rule-classes nil)))

                (defthm ,getp{correspondence}
                  (implies (and (,hash-table$corr ,hash-table$c ,hash-table)
                                ,@(and key-recognizer
                                       `((,key-recognizer ,getp$c-key)))
                                (,recognizer$a ,hash-table))
                           (let ((lhs (,getp$c ,getp$c-key ,hash-table$c))
                                 (rhs (,getp$a ,getp$c-key ,hash-table)))
                             (and (equal (mv-nth 0 lhs) (mv-nth 0 rhs))
                                  (equal (mv-nth 1 lhs) (mv-nth 1 rhs)))))
                  :rule-classes nil
                  :hints
                  (("Goal"
                    :in-theory (disable ,hash-table$corr-keys
                                        ,hash-table$corr-vals))))

                ,@(and (or (eq test 'eq)
                           (eq test 'eql))
                       `((defthm ,getp{guard-thm}
                           (implies (and (,hash-table$corr ,hash-table$c ,hash-table)
                                         ,@(and key-recognizer
                                                `((,key-recognizer ,getp$c-key)))
                                         (,recognizer$a ,hash-table))
                                    ,(if (eq test 'eq)
                                         `(symbolp ,getp$c-key)
                                         `(eqlablep ,getp$c-key)))
                           :rule-classes nil)))

                (defthm ,remover{correspondence}
                  (implies (and (,hash-table$corr ,hash-table$c ,hash-table)
                                ,@(and key-recognizer
                                       `((,key-recognizer ,remover$c-key)))
                                (,recognizer$a ,hash-table))
                           (,hash-table$corr (,remover$c ,remover$c-key ,hash-table$c)
                                             (,remover$a ,remover$c-key ,hash-table)))
                  :rule-classes nil
                  :hints
                  (("Goal"
                    :in-theory (e/d (,aggressive$a)
                                    (,hash-table$corr-keys
                                     ,hash-table$corr-vals))
                    :expand ((,hash-table$corr-keys (,remover$c ,remover$c-key ,hash-table$c)
                                                    (,remover$a ,remover$c-key ,hash-table))
                             (,hash-table$corr-vals (,remover$c ,remover$c-key ,hash-table$c)
                                                    (,remover$a ,remover$c-key ,hash-table))))))

                ,@(and (or (eq test 'eq)
                           (eq test 'eql))
                       `((defthm ,remover{guard-thm}
                           (implies (and (,hash-table$corr ,hash-table$c ,hash-table)
                                         ,@(and key-recognizer
                                                `((,key-recognizer ,remover$c-key)))
                                         (,recognizer$a ,hash-table))
                                    ,(if (eq test 'eq)
                                         `(symbolp ,remover$c-key)
                                         `(eqlablep ,remover$c-key)))
                           :rule-classes nil)))

                (defthm ,remover{preserved}
                  (implies (and ,@(and key-recognizer
                                       `((,key-recognizer ,remover$c-key)))
                                (,recognizer$a ,hash-table))
                           (,recognizer$a (,remover$a ,remover$c-key ,hash-table)))
                  :rule-classes nil)

                (defthm ,count{correspondence}
                  (implies (and (,hash-table$corr ,hash-table$c ,hash-table)
                                (,recognizer$a ,hash-table))
                           (equal (,count$c ,hash-table$c)
                                  (,count$a ,hash-table)))
                  :rule-classes nil)

                (defthm ,clear{correspondence}
                  (implies (and (,hash-table$corr ,hash-table$c ,hash-table)
                                (,recognizer$a ,hash-table))
                           (,hash-table$corr (,clear$c ,hash-table$c)
                                             (,clear$a ,hash-table)))
                  :rule-classes nil)

                (defthm ,clear{preserved}
                  (implies (,recognizer$a ,hash-table)
                           (,recognizer$a (,clear$a ,hash-table)))
                  :rule-classes nil)

                (defthm ,init{correspondence}
                  (implies (and (,hash-table$corr ,hash-table$c ,hash-table)
                                (,recognizer$a ,hash-table)
                                (or (natp ht-size)
                                    (not ht-size))
                                (or (and (rationalp rehash-size)
                                         (<= 1 rehash-size))
                                    (not rehash-size))
                                (or (and (rationalp rehash-threshold)
                                         (<= 0 rehash-threshold)
                                         (<= rehash-threshold 1))
                                    (not rehash-threshold)))
                           (,hash-table$corr (,init$c ht-size
                                                      rehash-size
                                                      rehash-threshold
                                                      ,hash-table$c)
                                             (,init$a ht-size
                                                      rehash-size
                                                      rehash-threshold
                                                      ,hash-table)))
                  :rule-classes nil)

                (defthm ,init{guard-thm}
                  (implies (and (,hash-table$corr ,hash-table$c ,hash-table)
                                (,recognizer$a ,hash-table)
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

                (defthm ,init{preserved}
                  (implies (and (,recognizer$a ,hash-table)
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
                                                   ,hash-table)))
                  :rule-classes nil)

                ,@(and copyable
                       `((defthm ,keys{correspondence}
                           (implies (and (,hash-table$corr ,hash-table$c,hash-table)
                                         (,recognizer$a ,hash-table))
                                    (equal (,keys$c ,hash-table$c)
                                           (,keys$a ,hash-table)))
                           :rule-classes nil)

                         (defthm ,keys-set{correspondence}
                           (implies (and (,hash-table$corr ,hash-table$c,hash-table)
                                         (,keys$ap ,keys-set$c-set)
                                         (,recognizer$a ,hash-table))
                                    (,hash-table$corr (,keys-set$c ,keys-set$c-set ,hash-table$c)
                                                      (,keys-set$a ,keys-set$c-set ,hash-table)))
                           :rule-classes nil
                           :hints
                           (("Goal"
                             :in-theory (e/d (,aggressive$a)
                                             (,hash-table$corr-keys
                                              ,hash-table$corr-vals))
                             :expand ((,hash-table$corr-keys (,keys-set$c ,keys-set$c-set ,hash-table$c)
                                                             (,keys-set$a ,keys-set$c-set ,hash-table))
                                      (,hash-table$corr-vals (,keys-set$c ,keys-set$c-set ,hash-table$c)
                                                             (,keys-set$a ,keys-set$c-set ,hash-table))))))

                         (defthm ,keys-set{preserved}
                           (implies (and (,keys$ap v)
                                         (,recognizer$a ,hash-table))
                                    (,recognizer$a (,keys-set$a v ,hash-table)))
                           :rule-classes nil)))))

            (defabsstobj ,hash-table
              :foundation ,hash-table$c
              :recognizer (,recognizer :logic ,recognizer$a
                                       :exec ,recognizer$c)
              :creator (,creator :logic ,creator$a
                                 :exec ,creator$c)
              :corr-fn ,hash-table$corr
              :non-executable ,(not executable)
              :exports ,exports)

            (table stobj$a-property ',hash-table ',stobj$a-property)

            (table package-witness ',hash-table ',package-witness))))))
