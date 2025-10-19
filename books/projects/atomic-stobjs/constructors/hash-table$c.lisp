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
(include-book "../lemmas/hash-table$c")
||#

(include-book "../type-spec")
(include-book "../utilities/top")


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


;;;; `DEFINE-HASH-TABLE$C'
(defmacro define-hash-table$c
    (hash-table test
     &key
       (size 'nil)
       (element-type 't)
       (default-value 'nil)
       (copyable 't)

       (inline 'nil)
       (memoizable 'nil)
       (executable 'nil)

       (contents 'nil)
       (contents-recognizer 'nil)
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

       (debug 'nil))

  (declare (xargs :guard (and (symbolp hash-table)
                              (valid-hash-table-test-p test)
                              (valid-hash-table-size-p size)
                              (if (acl2-type-spec-p element-type)
                                  (typep$ default-value element-type)
                                  (symbolp element-type))
                              (boolean-listp (list copyable
                                                   inline
                                                   memoizable
                                                   executable))
                              (symbol-listp (list contents
                                                  contents-recognizer
                                                  recognizer
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
                              (booleanp debug))))

  (let* ((hash-table-begin (symbolicate hash-table hash-table '-begin))
         (hash-table-end (symbolicate hash-table hash-table '-end))
         (hash-table-theorems (symbolicate hash-table hash-table '-theorems))

         (element-type-is-stobj (not (acl2-type-spec-p element-type)))
         (element-type-is-t (eq element-type t))

         (default-value-name (symbolicate hash-table '* hash-table '-default-value*))

         (contents (or contents
                       (symbolicate hash-table hash-table '-contents)))
         (contents-recognizer-stobj-default (symbolicate hash-table contents 'p))
         (contents-recognizer (or contents-recognizer
                                  (symbolicate hash-table contents (make-predicate-suffix contents))))
         (recognizer-stobj-default (symbolicate hash-table hash-table 'p))
         (recognizer (or recognizer
                         (symbolicate hash-table hash-table (make-predicate-suffix hash-table))))
         (creator-stobj-default (symbolicate hash-table 'create- hash-table))
         (creator (or creator
                      (symbolicate hash-table 'create- hash-table)))
         (fixer (or fixer
                    (symbolicate hash-table hash-table '-fix)))
         (accessor-stobj-default (symbolicate hash-table contents '-get))
         (accessor (or accessor
                       (symbolicate hash-table hash-table '-get)))
         (updater-stobj-default (symbolicate hash-table contents '-put))
         (updater (or updater
                      (symbolicate hash-table hash-table '-put)))
         (boundp-stobj-default (symbolicate hash-table contents '-boundp))
         (boundp (or boundp
                     (symbolicate hash-table hash-table '-boundp)))
         (getp-stobj-default (symbolicate hash-table contents '-get?))
         (getp (or getp
                   (symbolicate hash-table hash-table '-getp)))
         (remover-stobj-default (symbolicate hash-table contents '-rem))
         (remover (or remover
                      (symbolicate hash-table hash-table '-rem)))
         (count-stobj-default (symbolicate hash-table contents '-count))
         (count (or count
                    (symbolicate hash-table hash-table '-count)))
         (clear-stobj-default (symbolicate hash-table contents '-clear))
         (clear (or clear
                    (symbolicate hash-table hash-table '-clear)))
         (%clear (symbolicate hash-table hash-table '-%clear))
         (init-stobj-default (symbolicate hash-table contents '-init))
         (init (or init
                   (symbolicate hash-table hash-table '-init)))
         (%init (symbolicate hash-table hash-table '-%init))
         (keys (or keys
                   (symbolicate hash-table hash-table '-keys)))
         (keys-set-stobj-default (symbolicate hash-table 'update- keys))
         (keys-set (or keys-set
                       (symbolicate hash-table keys '-set)))

         (doublets (append (and (not (eq contents-recognizer contents-recognizer-stobj-default))
                                `((,contents-recognizer-stobj-default ,contents-recognizer)))
                           (and (not (eq recognizer recognizer-stobj-default))
                                `((,recognizer-stobj-default ,recognizer)))
                           (and (not (eq creator creator-stobj-default))
                                `((,creator-stobj-default ,creator)))
                           (and (not (eq accessor accessor-stobj-default))
                                `((,accessor-stobj-default ,accessor)))
                           (and (not (eq updater updater-stobj-default))
                                `((,updater-stobj-default ,updater)))
                           (and (not (eq boundp boundp-stobj-default))
                                `((,boundp-stobj-default ,boundp)))
                           (and (not (eq getp getp-stobj-default))
                                `((,getp-stobj-default ,getp)))
                           (and (not (eq remover remover-stobj-default))
                                `((,remover-stobj-default ,remover)))
                           (and (not (eq count count-stobj-default))
                                `((,count-stobj-default ,count)))
                           (and (not (eq clear clear-stobj-default))
                                `((,clear-stobj-default ,(if copyable
                                                             %clear
                                                             clear))))
                           (and (not (eq init init-stobj-default))
                                `((,init-stobj-default ,(if copyable
                                                            %init
                                                            init))))
                           (and copyable
                                (not (eq keys-set keys-set-stobj-default))
                                `((,keys-set-stobj-default ,keys-set)))))

         (contents-recognizer-of-alist-fix (symbolicate hash-table contents-recognizer '-of-alist-fix))

         (recognizer{compound-recognizer} (symbolicate hash-table recognizer '{compound-recognizer}))
         (recognizer-of-creator (symbolicate hash-table recognizer '-of- creator))
         (typep$-of-accessor (symbolicate hash-table 'typep$-of- accessor))
         (typep$-of-accessor/lemma (symbolicate hash-table typep$-of-accessor '/lemma))
         (recognizer-of-updater (symbolicate hash-table recognizer '-of- updater))
         (contents-recognizer-of-hons-remove-assoc (symbolicate hash-table contents-recognizer '-of-hons-remove-assoc))
         (recognizer-of-remover (symbolicate hash-table recognizer '-of- remover))

         (recognizer-of-fixer (symbolicate hash-table recognizer '-of- fixer))
         (fixer-when-recognizer (symbolicate hash-table fixer '-when- recognizer))
         (fixer-when-not-recognizer (symbolicate hash-table fixer '-when-not- recognizer))

         (accessor-of-creator (symbolicate hash-table accessor '-of- creator))
         (accessor-of-updater-same (symbolicate hash-table accessor '-of- updater '-same))
         (accessor-of-updater-diff (symbolicate hash-table accessor '-of- updater '-diff))
         (accessor-when-not-boundp (symbolicate hash-table accessor '-when-not- boundp))
         (accessor-of-remover-same (symbolicate hash-table accessor '-of- remover '-same))
         (accessor-of-remover-diff (symbolicate hash-table accessor '-of- remover '-diff))
         (accessor-of-keys-set (symbolicate hash-table accessor '-of- keys-set))

         (keys-set-of-updater (symbolicate hash-table keys-set '-of- updater))

         (boundp-of-creator (symbolicate hash-table boundp '-of- creator))
         (boundp-of-updater-same (symbolicate hash-table boundp '-of- updater '-same))
         (boundp-of-updater-diff (symbolicate hash-table boundp '-of- updater '-diff))
         (boundp-of-remover-same (symbolicate hash-table boundp '-of- remover '-same))
         (boundp-of-remover-diff (symbolicate hash-table boundp '-of- remover '-diff))
         (boundp-of-keys-set (symbolicate hash-table boundp '-of- keys-set))

         (getp{rewrite} (symbolicate hash-table getp '{rewrite}))

         (remover-of-creator (symbolicate hash-table remover '-of- creator))
         (remover-of-updater-same (symbolicate hash-table remover '-of- updater '-same))
         (remover-of-updater-diff (symbolicate hash-table remover '-of- updater '-diff))
         (remover-of-remover (symbolicate hash-table remover '-of- remover))
         (remover-of-remover-same (symbolicate hash-table remover-of-remover '-same))
         (remover-of-remover-diff (symbolicate hash-table remover-of-remover '-diff))
         (keys-set-of-remover (symbolicate hash-table keys-set '-of- remover))

         (count-of-creator (symbolicate hash-table count '-of- creator))
         (count-of-updater-when-boundp (symbolicate hash-table count '-of- updater '-when- boundp))
         (count-of-updater-when-not-boundp (symbolicate hash-table count '-of- updater '-when-not- boundp))
         (count-when-boundp (symbolicate hash-table count '-when- boundp))
         (count-of-remover-when-boundp (symbolicate hash-table count '-of- remover '-when- boundp))
         (count-of-remover-when-not-boundp (symbolicate hash-table count '-of- remover '-when-not- boundp))
         (count-of-keys-set (symbolicate hash-table count '-of- keys-set))

         (clear{rewrite} (symbolicate hash-table clear '{rewrite}))

         (init{rewrite} (symbolicate hash-table init '{rewrite}))

         (keys-of-creator (symbolicate hash-table keys '-of- creator))
         (keys-of-updater (symbolicate hash-table keys '-of- updater))
         (keys-of-remover (symbolicate hash-table keys '-of- remover))
         (recognizer-of-keys-set (symbolicate hash-table recognizer '-of- keys-set))
         (keys-of-keys-set (symbolicate hash-table keys '-of- keys-set))
         (keys-set-of-keys-set (symbolicate hash-table keys-set '-of- keys-set)))

    `(with-output
       ,@(and (not debug)
              '#!acl2(:off (warning! observation prove event history proof-tree)
                           :summary-off (rules)
                           :gag-mode t))

       (make-event
         (let* ((element-type-is-stobj (and ,element-type-is-stobj
                                            (stobj-p ',element-type)))
                (prologue
                 `((deflabel ,',hash-table-begin)

                   ,@(and (not element-type-is-stobj)
                          `((defconst ,',default-value-name ',',default-value)))

                   (defstobj ,',hash-table
                     (,',contents :type (hash-table ,',test ,',size ,',element-type)
                                  ,@(and (not element-type-is-stobj)
                                         `(:initially ,',default-value)))
                     ,@(and ',copyable
                            `((,',keys)))
                     :renaming ,',doublets
                     :inline ,',inline
                     :non-memoizable ,',(not memoizable)
                     :non-executable ,',(not executable))))
                (epilogue
                 '((deflabel ,hash-table-end)

                   (deftheory-static ,hash-table-theorems
                     (set-difference-theories
                      (set-difference-theories
                       (current-theory ',hash-table-end)
                       (current-theory ',hash-table-begin))
                      (function-theory ',hash-table-end)))

                   (in-theory
                     (union-theories (current-theory ',hash-table-begin)
                                     (theory ',hash-table-theorems)))))
                (body
                 `(with-books (("std/alists/hons-assoc-equal" :dir :system)
                               ("std/alists/hons-remove-assoc" :dir :system)
                               ("projects/atomic-stobjs/lemmas/std" :dir :system)
                               ("projects/atomic-stobjs/lemmas/omaps" :dir :system))

                    ;; `CONTENTS-RECOGNIZER' rewrites to `T'
                    (local
                      (defthm ,',contents-recognizer-of-alist-fix
                        (implies (,',contents-recognizer ,',contents)
                                 (,',contents-recognizer (alist-fix ,',contents)))))

                    ;; `RECOGNIZER'
                    (defthm ,',recognizer{compound-recognizer}
                      (implies (,',recognizer ,',hash-table)
                               (and (consp ,',hash-table)
                                    (true-listp ,',hash-table)))
                      :rule-classes :compound-recognizer)

                    (defthm ,',recognizer-of-creator
                      (,',recognizer (,',creator)))

                    (defun-inline ,',fixer (,',hash-table)
                      (declare (xargs :stobjs ,',hash-table))
                      (mbe :logic (if (,',recognizer ,',hash-table)
                                      ,',hash-table
                                      (,',creator))
                           :exec ,',hash-table))

                    (defthm ,',recognizer-of-fixer
                      (,',recognizer (,',fixer ,',hash-table)))

                    (defthm ,',fixer-when-recognizer
                      (implies (,',recognizer ,',hash-table)
                               (equal (,',fixer ,',hash-table) ,',hash-table)))

                    (defthm ,',fixer-when-not-recognizer
                      (implies (not (,',recognizer ,',hash-table))
                               (equal (,',fixer ,',hash-table) (,',creator))))

                    ,@(and ',(not element-type-is-t)
                           `((local
                               (defthmd ,',typep$-of-accessor/lemma
                                 (implies (and (,',contents-recognizer ,',contents)
                                               (hons-assoc-equal k ,',contents))
                                          ,(if element-type-is-stobj
                                               `(,(stobj-recognizer ',element-type)
                                                  (cdr (hons-assoc-equal k ,',contents)))
                                               (typep$transform/member-fix `(cdr (hons-assoc-equal k ,',contents))
                                                                           ',element-type)))
                                 :hints
                                 (("Goal"
                                   :induct (hons-assoc-equal k ,',contents)))))

                             (defthm ,',typep$-of-accessor
                               (implies (,',recognizer ,',hash-table)
                                        ,(if element-type-is-stobj
                                             `(,(stobj-recognizer ',element-type)
                                                (,',accessor k ,',hash-table))
                                             (typep$transform/member-fix `(,',accessor k ,',hash-table)
                                                                         ',element-type)))
                               :hints
                               (("Goal"
                                 :use ((:instance ,',typep$-of-accessor/lemma
                                                  (,',contents (car ,',hash-table)))))))))

                    (defthm ,',recognizer-of-updater
                      (implies ,(if ',element-type-is-t
                                    `(,',recognizer ,',hash-table)
                                    `(and (,',recognizer ,',hash-table)
                                          ,(if element-type-is-stobj
                                               `(,(stobj-recognizer ',element-type) v)
                                               (typep$transform/member-fix 'v ',element-type))))
                               (,',recognizer (,',updater k v ,',hash-table))))

                    ,@(and ',(not element-type-is-t)
                           `((local
                               (defthm ,',contents-recognizer-of-hons-remove-assoc
                                 ;; NOTE: Let ACL2 figure out the induction.
                                 (implies (,',contents-recognizer ,',contents)
                                          (,',contents-recognizer (hons-remove-assoc k ,',contents)))))))

                    (defthm ,',recognizer-of-remover
                      (implies (,',recognizer ,',hash-table)
                               (,',recognizer (,',remover k ,',hash-table))))

                    ;; `ACCESSOR'
                    (defthm ,',accessor-of-creator
                      (equal (,',accessor k (,',creator))
                             ,(if element-type-is-stobj
                                  `(,(stobj-creator ',element-type))
                                  ',default-value-name)))

                    (defthm ,',accessor-of-updater-same
                      (implies (equal k l)
                               (equal (,',accessor k (,',updater l v ,',hash-table))
                                      v)))

                    (defthm ,',accessor-of-updater-diff
                      (implies (not (equal k l))
                               (equal (,',accessor k (,',updater l v ,',hash-table))
                                      (,',accessor k ,',hash-table))))

                    (defthmd ,',accessor-when-not-boundp
                      (implies (not (,',boundp k ,',hash-table))
                               (equal (,',accessor k ,',hash-table)
                                      ,(if element-type-is-stobj
                                           `(,(stobj-creator ',element-type))
                                           ',default-value-name))))

                    (defthm ,',accessor-of-remover-same
                      (implies (equal k l)
                               (equal (,',accessor k (,',remover l ,',hash-table))
                                      ,(if element-type-is-stobj
                                           `(,(stobj-creator ',element-type))
                                           ',default-value-name))))

                    (defthm ,',accessor-of-remover-diff
                      (implies (not (equal k l))
                               (equal (,',accessor k (,',remover l ,',hash-table))
                                      (,',accessor k ,',hash-table))))

                    ,@(and ',copyable
                           `((defthm ,',accessor-of-keys-set
                               (equal (,',accessor k (,',keys-set keys ,',hash-table))
                                      (,',accessor k ,',hash-table)))))

                    ;; `BOUNDP'
                    (defthm ,',boundp-of-creator
                      (not (,',boundp k (,',creator))))

                    (defthm ,',boundp-of-updater-same
                      (implies (equal k l)
                               (equal (,',boundp k (,',updater l v ,',hash-table))
                                      t)))

                    (defthm ,',boundp-of-updater-diff
                      (implies (not (equal k l))
                               (equal (,',boundp k (,',updater l v ,',hash-table))
                                      (,',boundp k ,',hash-table))))

                    (defthm ,',boundp-of-remover-same
                      (implies (equal k l)
                               (not (,',boundp k (,',remover l ,',hash-table)))))

                    (defthm ,',boundp-of-remover-diff
                      (implies (not (equal k l))
                               (equal (,',boundp k (,',remover l ,',hash-table))
                                      (,',boundp k ,',hash-table))))

                    ,@(and ',copyable
                           `((defthm ,',boundp-of-keys-set
                               (equal (,',boundp k (,',keys-set keys ,',hash-table))
                                      (,',boundp k ,',hash-table)))))

                    ;; `GETP'
                    (defthm ,',getp{rewrite}
                      (mv-let (v w) (,',getp k ,',hash-table)
                        (and (equal v (,',accessor k ,',hash-table))
                             (equal w (,',boundp k ,',hash-table)))))

                    ;; `REMOVER'
                    (defthm ,',remover-of-creator
                      (equal (,',remover k (,',creator)) (,',creator)))

                    (with-books (("std/lists/remove" :dir :system))
                      (local
                        (defthm cdr-of-update-nth
                          (implies (posp k)
                                   (equal (cdr (update-nth k v list))
                                          (update-nth (1- k) v (cdr list))))))

                      (defthm ,',remover-of-updater-same
                        (implies (equal k l)
                                 (equal (,',remover k (,',updater l v ,',hash-table))
                                        (,',remover k ,',hash-table))))

                      (defthm ,',remover-of-updater-diff
                        (implies (not (equal k l))
                                 (equal (,',remover k (,',updater l v ,',hash-table))
                                        (,',updater l v (,',remover k ,',hash-table)))))

                      (defthm ,',remover-of-remover-same
                        (implies (equal k l)
                                 (equal (,',remover k (,',remover l ,',hash-table))
                                        (,',remover k ,',hash-table))))

                      (defthm ,',remover-of-remover-diff
                        (implies (not (equal k l))
                                 (equal (,',remover k (,',remover l ,',hash-table))
                                        (,',remover l (,',remover k ,',hash-table))))
                        :rule-classes
                        ((:rewrite :loop-stopper ((k l ,',remover))))))

                    ;; `COUNT'
                    (defthm ,',count-of-creator
                      (equal (,',count (,',creator)) 0))

                    (defthm ,',count-of-updater-when-boundp
                      (implies (,',boundp k ,',hash-table)
                               (equal (,',count (,',updater k v ,',hash-table))
                                      (,',count ,',hash-table))))

                    (defthm ,',count-of-updater-when-not-boundp
                      (implies (not (,',boundp k ,',hash-table))
                               (equal (,',count (,',updater k v ,',hash-table))
                                      (1+ (,',count ,',hash-table)))))

                    (defthm ,',count-when-boundp
                      (implies (,',boundp k ,',hash-table)
                               (and (integerp (,',count ,',hash-table))
                                    (< 0 (,',count ,',hash-table))))
                      :rule-classes :type-prescription)

                    (defthm ,',count-of-remover-when-boundp
                      (implies (,',boundp k ,',hash-table)
                               (equal (,',count (,',remover k ,',hash-table))
                                      (1- (,',count ,',hash-table)))))

                    (defthm ,',count-of-remover-when-not-boundp
                      (implies (not (,',boundp k ,',hash-table))
                               (equal (,',count (,',remover k ,',hash-table))
                                      (,',count ,',hash-table))))

                    ,@(and ',copyable
                           `((defthm ,',count-of-keys-set
                               (equal (,',count (,',keys-set keys ,',hash-table))
                                      (,',count ,',hash-table)))))

                    (with-books (("std/lists/len" :dir :system)
                                 ("std/lists/nth" :dir :system))
                      (local
                        (defthm cdr-of-update-nth
                          (implies (posp k)
                                   (equal (cdr (update-nth k v list))
                                          (update-nth (1- k) v (cdr list))))))

                      ;; `CLEAR'
                      ,@(and ',copyable
                             `((defun ,',clear (,',hash-table)
                                 (declare (xargs :stobjs ,',hash-table))
                                 (let* ((,',hash-table (,',fixer ,',hash-table))
                                        (,',hash-table (,',keys-set '() ,',hash-table))
                                        (,',hash-table (,',%clear ,',hash-table)))
                                   ,',hash-table))))

                      (defthm ,',clear{rewrite}
                        (implies (,',recognizer ,',hash-table)
                                 (equal (,',clear ,',hash-table)
                                        (,',creator)))
                        :hints
                        ((acl2::equal-by-nths-hint)))

                      ;; `INIT'
                      ,@(and ',copyable
                             `((defun ,',init (ht-size rehash-size rehash-threshold ,',hash-table)
                                 (declare (xargs :stobjs ,',hash-table
                                                 :guard (and (or (natp ht-size)
                                                                 (not ht-size))
                                                             (or (and (rationalp rehash-size)
                                                                      (<= 1 rehash-size))
                                                                 (not rehash-size))
                                                             (or (and (rationalp rehash-threshold)
                                                                      (<= 0 rehash-threshold)
                                                                      (<= rehash-threshold 1))
                                                                 (not rehash-threshold)))))
                                 (let* ((,',hash-table (,',fixer ,',hash-table))
                                        (,',hash-table (,',keys-set '() ,',hash-table))
                                        (,',hash-table (,',%init ht-size rehash-size rehash-threshold ,',hash-table)))
                                   ,',hash-table))))

                      (defthm ,',init{rewrite}
                        (implies (,',recognizer ,',hash-table)
                                 (equal (,',init ht-size
                                                 rehash-size
                                                 rehash-threshold
                                                 ,',hash-table)
                                        (,',creator)))
                        :hints
                        ((acl2::equal-by-nths-hint))))

                    ,@(and ',copyable
                           `((defthm ,',keys-of-creator
                               (not (,',keys (,',creator))))

                             (encapsulate ()
                               (local
                                 (defthm cdr-of-update-nth
                                   (implies (posp k)
                                            (equal (cdr (update-nth k v list))
                                                   (update-nth (1- k) v (cdr list))))))

                               (defthm ,',keys-of-updater
                                 (equal (,',keys (,',updater k v ,',hash-table))
                                        (,',keys ,',hash-table)))

                               (defthm ,',keys-of-remover
                                 (equal (,',keys (,',remover k ,',hash-table))
                                        (,',keys ,',hash-table)))

                               (defthm ,',recognizer-of-keys-set
                                 (implies (,',recognizer ,',hash-table)
                                          (,',recognizer (,',keys-set set ,',hash-table))))

                               (defthm ,',keys-of-keys-set
                                 (equal (,',keys (,',keys-set set ,',hash-table))
                                        set))

                               (defthm ,',keys-set-of-updater
                                 (equal (,',keys-set set (,',updater k v ,',hash-table))
                                        (,',updater k v (,',keys-set set ,',hash-table))))

                               (defthm ,',keys-set-of-remover
                                 (equal (,',keys-set set (,',remover k ,',hash-table))
                                        (,',remover k (,',keys-set set ,',hash-table))))

                               (with-books (("std/lists/update-nth" :dir :system))
                                 (defthm ,',keys-set-of-keys-set
                                   (equal (,',keys-set %set (,',keys-set set ,',hash-table))
                                          (,',keys-set %set ,',hash-table))))))))))

           `(progn
              ,@prologue

              ,body

              ,@epilogue))))))
