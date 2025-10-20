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
(include-book "../lemmas/hash-table$a")
||#

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


;;;; `DEFINE-HASH-TABLE$A'
(defmacro define-hash-table$a
    (hash-table test
     &key
       (key-recognizer 'nil)
       (key-fixer 'nil)
       (key 'key)
       (default-key 'nil)
       (val-recognizer 'nil)
       (val-fixer 'nil)
       (val 'val)
       (default-val 'nil)
       (copyable 't)

       (contents 'nil)
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

       (testp 'nil)
       (debug 'nil))

  (declare (xargs :guard (and (symbolp hash-table)
                              (valid-hash-table-test-p test)
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
                              (booleanp copyable)
                              (symbol-listp (list recognizer
                                                  fixer
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
                              (booleanp testp)
                              (booleanp debug))))

  (let* ((hash-table-begin (symbolicate hash-table hash-table '-begin))
         (hash-table-end (symbolicate hash-table hash-table '-end))
         (hash-table-theorems (symbolicate hash-table hash-table '-theorems))
         (hash-table-definitions (symbolicate hash-table hash-table '-definitions))
         (hash-table-aggressive (symbolicate hash-table hash-table '-aggressive))

         (hash-table-entry-guard (symbolicate hash-table hash-table '-entry-guard))
         (default-key-name (symbolicate hash-table '* hash-table '-default-key*))
         (default-val-name (symbolicate hash-table '* hash-table '-default-val*))
         (%key (symbolicate hash-table '% key))
         (%val (symbolicate hash-table '% val))

         (contents (if copyable
                       (or contents
                           (symbolicate hash-table hash-table '-contents))
                       hash-table))
         (recognizer (or recognizer
                         (symbolicate hash-table hash-table (make-predicate-suffix hash-table))))
         (contents-recognizer (if copyable
                                  (symbolicate hash-table contents '-p)
                                  recognizer))
         (fixer (or fixer
                    (symbolicate hash-table hash-table '-fix)))
         (contents-fixer (if copyable
                             (symbolicate hash-table contents '-fix)
                             fixer))
         (creator (or creator
                      (symbolicate hash-table 'create- hash-table)))
         (contents-creator (if copyable
                               (symbolicate hash-table 'create- contents)
                               creator))
         (accessor (or accessor
                       (symbolicate hash-table hash-table '-get)))
         (contents-accessor (if copyable
                                (symbolicate hash-table contents '-get)
                                accessor))
         (updater (or updater
                      (symbolicate hash-table hash-table '-put)))
         (contents-updater (if copyable
                               (symbolicate hash-table contents '-put)
                               updater))
         (boundp (or boundp
                     (symbolicate hash-table hash-table '-boundp)))
         (contents-boundp (if copyable
                              (symbolicate hash-table contents '-boundp)
                              boundp))
         (getp (or getp
                   (symbolicate hash-table hash-table '-getp)))
         (remover (or remover
                      (symbolicate hash-table hash-table '-rem)))
         (contents-remover (if copyable
                               (symbolicate hash-table contents '-rem)
                               remover))
         (count (or count
                    (symbolicate hash-table hash-table '-count)))
         (contents-count (if copyable
                             (symbolicate hash-table contents '-count)
                             count))
         (clear (or clear
                    (symbolicate hash-table hash-table '-clear)))
         (init (or init
                   (symbolicate hash-table hash-table '-init)))
         (keys (or keys
                   (symbolicate hash-table hash-table '-keys)))
         (keys-set (or keys-set
                       (symbolicate hash-table hash-table '-keys-set)))

         (recognizer{compound-recognizer} (symbolicate hash-table recognizer '{compound-recognizer}))
         (contents-recognizer{compound-recognizer}
          (symbolicate hash-table contents-recognizer '{compound-recognizer}))

         (recognizer-of-fixer (symbolicate hash-table recognizer '-of- fixer))
         (contents-recognizer-of-contents-fixer
          (symbolicate hash-table contents-recognizer '-of- contents-fixer))
         (fixer-when-recognizer (symbolicate hash-table fixer '-when- recognizer))
         (contents-fixer-when-contents-recognizer
          (symbolicate hash-table contents-fixer '-when- contents-recognizer))
         (fixer-when-not-recognizer (symbolicate hash-table fixer '-when-not- recognizer))
         (contents-fixer-when-not-contents-recognizer
          (symbolicate hash-table contents-fixer '-when-not- contents-recognizer))

         (recognizer-of-creator (symbolicate hash-table recognizer '-of- creator))
         (emptyp-of-creator (symbolicate hash-table 'emptyp-of- creator))

         (accessor-of-key-fixer (symbolicate hash-table accessor '-of- key-fixer))
         (contents-accessor-of-key-fixer
          (symbolicate hash-table contents-accessor '-of- key-fixer))
         (accessor-of-fixer (symbolicate hash-table accessor '-of- fixer))
         (contents-accessor-of-contents-fixer
          (symbolicate hash-table contents-accessor '-of- contents-fixer))
         (accessor-when-not-key-recognizer (symbolicate hash-table accessor '-when-not- key-recognizer))
         (contents-accessor-when-not-key-recognizer (symbolicate hash-table contents-accessor '-when-not- key-recognizer))

         (recognizer-of-updater (symbolicate hash-table recognizer '-of- updater))
         (contents-recognizer-of-contents-updater
          (symbolicate hash-table contents-recognizer '-of- contents-updater))
         (updater-of-key-fixer (symbolicate hash-table updater '-of- key-fixer))
         (updater-of-fixer (symbolicate hash-table updater '-of- fixer))
         (contents-updater-of-contents-fixer
          (symbolicate hash-table contents-updater '-of- contents-fixer))
         (updater-when-not-key-recognizer (symbolicate hash-table updater '-when-not- key-recognizer))
         (contents-updater-when-not-key-recognizer (symbolicate hash-table contents-updater '-when-not- key-recognizer))

         (boundp-of-key-fixer (symbolicate hash-table boundp '-of- key-fixer))
         (contents-boundp-of-key-fixer
          (symbolicate hash-table contents-boundp '-of- key-fixer))
         (boundp-of-fixer (symbolicate hash-table boundp '-of- fixer))
         (contents-boundp-of-contents-fixer
          (symbolicate hash-table contents-boundp '-of- contents-fixer))
         (boundp-when-not-key-recognizer (symbolicate hash-table boundp '-when-not- key-recognizer))
         (contents-boundp-when-not-key-recognizer (symbolicate hash-table contents-boundp '-when-not- key-recognizer))
         (boundp-when-not-recognizer (symbolicate hash-table boundp '-when-not- recognizer))
         (contents-boundp-when-not-contents-recognizer
          (symbolicate hash-table contents-boundp '-when-not- contents-recognizer))

         (getp{rewrite} (symbolicate hash-table getp '{rewrite}))

         (recognizer-of-remover (symbolicate hash-table recognizer '-of- remover))
         (contents-recognizer-of-contents-remover
          (symbolicate hash-table contents-recognizer '-of- contents-remover))
         (remover-of-key-fixer (symbolicate hash-table remover '-of- key-fixer))
         (contents-remover-of-key-fixer
          (symbolicate hash-table contents-remover '-of- key-fixer))
         (remover-of-fixer (symbolicate hash-table remover '-of- fixer))
         (contents-remover-of-contents-fixer
          (symbolicate hash-table contents-remover '-of- contents-fixer))
         (remover-when-not-key-recognizer (symbolicate hash-table remover '-when-not- key-recognizer))
         (contents-remover-when-not-key-recognizer (symbolicate hash-table contents-remover '-when-not- key-recognizer))

         (count-of-fixer (symbolicate hash-table count '-of- fixer))
         (contents-count-of-contents-fixer
          (symbolicate hash-table contents-count '-of- contents-fixer))
         (count-when-not-recognizer (symbolicate hash-table count '-when-not- recognizer))
         (contents-count-when-not-contents-recognizer
          (symbolicate hash-table contents-count '-when-not- contents-recognizer))

         (clear{rewrite} (symbolicate hash-table clear '{rewrite}))

         (init{rewrite} (symbolicate hash-table init '{rewrite}))

         (accessor-of-creator (symbolicate hash-table accessor '-of- creator))
         (accessor-of-updater (symbolicate hash-table accessor '-of- updater))
         (accessor-of-updater-same (symbolicate hash-table accessor-of-updater '-same))
         (accessor-of-updater-diff (symbolicate hash-table accessor-of-updater '-diff))
         (accessor-when-not-boundp (symbolicate hash-table accessor '-when-not- boundp))
         (accessor-of-remover (symbolicate hash-table accessor '-of- remover))
         (accessor-of-remover-same (symbolicate hash-table accessor-of-remover '-same))
         (accessor-of-remover-diff (symbolicate hash-table accessor-of-remover '-diff))

         (contents-accessor-of-contents-creator (symbolicate hash-table contents-accessor '-of- contents-creator))
         (contents-accessor-of-contents-updater (symbolicate hash-table contents-accessor '-of- contents-updater))
         (contents-accessor-of-contents-updater-same (symbolicate hash-table contents-accessor-of-contents-updater '-same))
         (contents-accessor-of-contents-updater-diff (symbolicate hash-table contents-accessor-of-contents-updater '-diff))
         (contents-accessor-when-not-contents-boundp (symbolicate hash-table contents-accessor '-when-not- contents-boundp))
         (contents-accessor-of-contents-remover (symbolicate hash-table contents-accessor '-of- contents-remover))
         (contents-accessor-of-contents-remover-same (symbolicate hash-table contents-accessor-of-contents-remover '-same))
         (contents-accessor-of-contents-remover-diff (symbolicate hash-table contents-accessor-of-contents-remover '-diff))

         (updater-of-accessor (symbolicate hash-table updater '-of- accessor))
         (updater-of-accessor-when-boundp (symbolicate hash-table updater-of-accessor '-when- boundp))
         (updater-of-accessor-when-not-boundp (symbolicate hash-table updater-of-accessor '-when-not- boundp))
         (updater-of-updater (symbolicate hash-table updater '-of- updater))
         (updater-of-updater-same (symbolicate hash-table updater-of-updater '-same))
         (updater-of-updater-diff (symbolicate hash-table updater-of-updater '-diff))
         (updater-of-remover (symbolicate hash-table updater '-of- remover))

         (contents-updater-of-contents-accessor (symbolicate hash-table contents-updater '-of- contents-accessor))
         (contents-updater-of-contents-accessor-when-contents-boundp (symbolicate hash-table contents-updater-of-contents-accessor '-when- contents-boundp))
         (contents-updater-of-contents-accessor-when-not-contents-boundp (symbolicate hash-table contents-updater-of-contents-accessor '-when-not- contents-boundp))
         (contents-updater-of-contents-updater (symbolicate hash-table contents-updater '-of- contents-updater))
         (contents-updater-of-contents-updater-same (symbolicate hash-table contents-updater-of-contents-updater '-same))
         (contents-updater-of-contents-updater-diff (symbolicate hash-table contents-updater-of-contents-updater '-diff))
         (contents-updater-of-contents-remover (symbolicate hash-table contents-updater '-of- contents-remover))

         (boundp-of-creator (symbolicate hash-table boundp '-of- creator))
         (boundp-of-updater (symbolicate hash-table boundp '-of- updater))
         (boundp-of-updater-same (symbolicate hash-table boundp-of-updater '-same))
         (boundp-of-updater-diff (symbolicate hash-table boundp-of-updater '-diff))
         (boundp-of-remover (symbolicate hash-table boundp '-of- remover))
         (boundp-of-remover-same (symbolicate hash-table boundp-of-remover '-same))
         (boundp-of-remover-diff (symbolicate hash-table boundp-of-remover '-diff))
         (boundp-when-zp-count (symbolicate hash-table boundp '-when-zp- count))
         (contents-boundp-when-zp-contents-count (symbolicate hash-table contents-boundp '-when-zp- contents-count))

         (contents-boundp-of-contents-creator (symbolicate hash-table contents-boundp '-of- contents-creator))
         (contents-boundp-of-contents-updater (symbolicate hash-table contents-boundp '-of- contents-updater))
         (contents-boundp-of-contents-updater-same (symbolicate hash-table contents-boundp-of-contents-updater '-same))
         (contents-boundp-of-contents-updater-diff (symbolicate hash-table contents-boundp-of-contents-updater '-diff))
         (contents-boundp-of-contents-remover (symbolicate hash-table contents-boundp '-of- contents-remover))
         (contents-boundp-of-contents-remover-same (symbolicate hash-table contents-boundp-of-contents-remover '-same))
         (contents-boundp-of-contents-remover-diff (symbolicate hash-table contents-boundp-of-contents-remover '-diff))

         (remover-of-creator (symbolicate hash-table remover '-of- creator))
         (remover-of-updater (symbolicate hash-table remover '-of- updater))
         (remover-of-updater-same (symbolicate hash-table remover-of-updater '-same))
         (remover-of-updater-diff (symbolicate hash-table remover-of-updater '-diff))
         (remover-when-not-boundp (symbolicate hash-table remover '-when-not- boundp))
         (remover-of-remover (symbolicate hash-table remover '-of- remover))
         (remover-of-remover-same (symbolicate hash-table remover-of-remover '-same))
         (remover-of-remover-diff (symbolicate hash-table remover-of-remover '-diff))

         (contents-remover-of-contents-creator (symbolicate hash-table contents-remover '-of- contents-creator))
         (contents-remover-of-contents-updater (symbolicate hash-table contents-remover '-of- contents-updater))
         (contents-remover-of-contents-updater-same (symbolicate hash-table contents-remover-of-contents-updater '-same))
         (contents-remover-of-contents-updater-diff (symbolicate hash-table contents-remover-of-contents-updater '-diff))
         (contents-remover-when-not-contents-boundp (symbolicate hash-table contents-remover '-when-not- contents-boundp))
         (contents-remover-of-contents-remover (symbolicate hash-table contents-remover '-of- contents-remover))
         (contents-remover-of-contents-remover-same (symbolicate hash-table contents-remover-of-contents-remover '-same))
         (contents-remover-of-contents-remover-diff (symbolicate hash-table contents-remover-of-contents-remover '-diff))

         (count-of-creator (symbolicate hash-table count '-of- creator))
         (count-of-updater (symbolicate hash-table count '-of- updater))
         (count-of-updater-when-boundp (symbolicate hash-table count-of-updater '-when- boundp))
         (count-of-updater-when-not-boundp (symbolicate hash-table count-of-updater '-when-not- boundp))
         (count-of-remover (symbolicate hash-table count '-of- remover))
         (count-of-remover-when-boundp (symbolicate hash-table count-of-remover '-when- boundp))
         (count-of-remover-when-not-boundp (symbolicate hash-table count-of-remover '-when-not- boundp))

         (contents-count-of-contents-creator (symbolicate hash-table contents-count '-of- contents-creator))
         (contents-count-of-contents-updater (symbolicate hash-table contents-count '-of- contents-updater))
         (contents-count-of-contents-updater-when-contents-boundp (symbolicate hash-table contents-count-of-contents-updater '-when- contents-boundp))
         (contents-count-of-contents-updater-when-not-contents-boundp (symbolicate hash-table contents-count-of-contents-updater '-when-not- contents-boundp))
         (contents-count-of-contents-remover (symbolicate hash-table contents-count '-of- contents-remover))
         (contents-count-of-contents-remover-when-contents-boundp (symbolicate hash-table contents-count-of-contents-remover '-when- contents-boundp))
         (contents-count-of-contents-remover-when-not-contents-boundp (symbolicate hash-table contents-count-of-contents-remover '-when-not- contents-boundp))

         (setp-of-keys (symbolicate hash-table 'setp-of- keys))
         (keys-of-creator (symbolicate hash-table keys '-of- creator))
         (keys-of-fixer (symbolicate hash-table keys '-of- fixer))
         (keys-when-not-recognizer (symbolicate hash-table keys '-when-not- recognizer))
         (keys-of-updater (symbolicate hash-table keys '-of- updater))
         (keys-of-remover (symbolicate hash-table keys '-of- remover))
         (keys-of-keys-set (symbolicate hash-table keys '-of- keys-set))
         (recognizer-of-keys-set (symbolicate hash-table recognizer '-of- keys-set))
         (keys-set-of-sfix (symbolicate hash-table keys-set '-of-sfix))
         (keys-set-of-fixer (symbolicate hash-table keys-set '-of- fixer))
         (accessor-of-keys-set (symbolicate hash-table accessor '-of- keys-set))
         (keys-set-of-updater (symbolicate hash-table keys-set '-of- updater))
         (boundp-of-keys-set (symbolicate hash-table boundp '-of- keys-set))
         (keys-set-of-remover (symbolicate hash-table keys-set '-of- remover))
         (count-of-keys-set (symbolicate hash-table count '-of- keys-set))
         (keys-set-of-keys-set (symbolicate hash-table keys-set '-of- keys-set))
         (keys-set-of-keys (symbolicate hash-table keys-set '-of- keys))
         (keys-set-of-keys-free (symbolicate hash-table keys-set-of-keys '-free))

         (%contents (symbolicate hash-table '% contents))
         (%hash-table (symbolicate hash-table '% hash-table))
         (keys-equal (symbolicate hash-table hash-table '-keys-equal))
         (contents-keys-equal (if copyable
                                  (symbolicate hash-table contents '-keys-equal)
                                  keys-equal))
         (keys-equal-witness (symbolicate hash-table keys-equal '-witness))
         (contents-keys-equal-witness (if copyable
                                          (symbolicate hash-table contents-keys-equal '-witness)
                                          keys-equal-witness))
         (keys-equal-necc (symbolicate hash-table keys-equal '-necc))
         (contents-keys-equal-lemma-0 (symbolicate hash-table contents-keys-equal '-lemma-0))
         (contents-keys-equal-lemma-1 (symbolicate hash-table contents-keys-equal '-lemma-1))
         (keys-equal-implies-contents-keys-equal (symbolicate hash-table keys-equal '-implies- contents-keys-equal))
         (vals-equal (symbolicate hash-table hash-table '-vals-equal))
         (contents-vals-equal (if copyable
                                  (symbolicate hash-table contents '-vals-equal)
                                  vals-equal))
         (contents-vals-equal-witness (symbolicate hash-table contents-vals-equal '-witness))
         (vals-equal-necc (symbolicate hash-table vals-equal '-necc))
         (contents-vals-equal-lemma-0 (symbolicate hash-table contents-vals-equal '-lemma-0))
         (contents-vals-equal-lemma-1 (symbolicate hash-table contents-vals-equal '-lemma-1))
         (vals-equal-implies-contents-vals-equal (symbolicate hash-table vals-equal '-implies- contents-vals-equal))
         (hash-table-equal (symbolicate hash-table hash-table '-equal))
         (contents-equal (if copyable
                             (symbolicate hash-table contents '-equal)
                             hash-table-equal))
         (hash-table-equal{forward-chaining} (symbolicate hash-table hash-table-equal '{forward-chaining}))
         (contents-equal{forward-chaining} (if copyable
                                               (symbolicate hash-table contents-equal '{forward-chaining})
                                               hash-table-equal{forward-chaining})))

    `(with-output
       ,@(and (not debug)
              '#!acl2(:off (warning! observation prove event history proof-tree)
                           :summary-off (rules)
                           :gag-mode t))

       (make-event
         (let* ((val-type-is-stobj (stobj-p ',val))
                (val$a (stobj$a-lookup ',val))
                (val-recognizer (if val$a
                                    (stobj$a-recognizer val$a)
                                    ',val-recognizer))
                (val-fixer (if val$a
                               (stobj$a-fixer val$a)
                               ',val-fixer))
                (val-recognizer-of-accessor (symbolicate ',hash-table val-recognizer '-of- ',accessor))
                (val-recognizer-of-contents-accessor
                 (symbolicate ',hash-table val-recognizer '-of- ',contents-accessor))
                (updater-of-val-fixer (symbolicate ',hash-table ',updater '-of- val-fixer))
                (updater-when-not-val-recognizer (symbolicate ',hash-table ',updater '-when-not- val-recognizer))
                (contents-updater-when-not-val-recognizer (symbolicate ',hash-table ',contents-updater '-when-not- val-recognizer))
                (updater-when-not-key-recognizer
                 (if (eq ',updater-when-not-key-recognizer updater-when-not-val-recognizer)
                     ',(symbolicate hash-table updater-when-not-key-recognizer "-0")
                     ',updater-when-not-key-recognizer))
                (updater-when-not-val-recognizer
                 (if (eq ',updater-when-not-key-recognizer updater-when-not-val-recognizer)
                     (symbolicate ',hash-table updater-when-not-val-recognizer "-1")
                     updater-when-not-val-recognizer))
                (contents-updater-when-not-key-recognizer
                 (if (eq ',contents-updater-when-not-key-recognizer contents-updater-when-not-val-recognizer)
                     ',(symbolicate hash-table contents-updater-when-not-key-recognizer "-0")
                     ',contents-updater-when-not-key-recognizer))
                (contents-updater-when-not-val-recognizer
                 (if (eq ',contents-updater-when-not-key-recognizer contents-updater-when-not-val-recognizer)
                     (symbolicate ',hash-table contents-updater-when-not-val-recognizer "-1")
                     contents-updater-when-not-val-recognizer))
                (prologue
                 `((deflabel ,',hash-table-begin)

                   (defconst ,',default-key-name ',',default-key)

                   ,@(and (not val-type-is-stobj)
                          `((defconst ,',default-val-name ',',default-val)))))
                (epilogue
                 `((deflabel ,',hash-table-end)

                   (deftheory-static ,',hash-table-theorems
                     (set-difference-theories
                      (set-difference-theories
                       (current-theory ',',hash-table-end)
                       (current-theory ',',hash-table-begin))
                      (union-theories (function-theory ',',hash-table-end)
                                      '((:i ,',contents-recognizer)
                                        (:i ,',contents-accessor)
                                        (:i ,',contents-updater)
                                        (:i ,',contents-boundp)
                                        (:i ,',contents-remover)
                                        (:i ,',contents-count)))))

                   (deftheory-static ,',hash-table-definitions
                     (set-difference-theories
                      (set-difference-theories
                       (set-difference-theories
                        (current-theory ',',hash-table-end)
                        (current-theory ',',hash-table-begin))
                       (theory ',',hash-table-theorems))
                      '(,',keys-equal
                        ,',vals-equal)))

                   (deftheory-static ,',hash-table-aggressive
                     (append
                      (and ',',key-recognizer
                           (list ',updater-when-not-key-recognizer))
                      (and ',',val-recognizer
                           (list ',updater-when-not-val-recognizer))
                      ',',(append
                           (list count-of-updater
                                 count-of-remover
                                 count-when-not-recognizer
                                 accessor-of-updater
                                 accessor-when-not-boundp
                                 accessor-of-remover
                                 updater-of-accessor
                                 updater-of-updater
                                 boundp-of-updater
                                 boundp-of-remover
                                 boundp-when-not-recognizer
                                 remover-of-updater
                                 remover-when-not-boundp
                                 remover-of-remover)
                           (and copyable
                                (list keys-when-not-recognizer
                                      boundp-when-zp-count
                                      keys-set-of-keys-free))
                           (and key-recognizer
                                (list accessor-when-not-key-recognizer
                                      boundp-when-not-key-recognizer
                                      remover-when-not-key-recognizer)))))

                   (in-theory
                     (union-theories (current-theory ',',hash-table-begin)
                                     (theory ',',hash-table-theorems)))
                   (in-theory
                     (enable ,',keys-equal
                             ,',vals-equal))))
                (default-key (cond
                               (',testp
                                ',default-key)
                               (t
                                ',default-key-name)))
                (default-val (cond
                               (',testp
                                ',default-val)
                               (val-type-is-stobj
                                `(,(stobj-creator ',val)))
                               (t
                                ',default-val-name)))
                (updater-of-key-fixer (if (eq ',updater-of-key-fixer updater-of-val-fixer)
                                          (symbolicate ',updater-of-key-fixer ',updater-of-key-fixer "-0")
                                          ',updater-of-key-fixer))
                (contents-updater-of-key-fixer (symbolicate ',contents ',contents "-" updater-of-key-fixer))
                (updater-of-val-fixer (if (eq ',updater-of-key-fixer updater-of-val-fixer)
                                          (symbolicate updater-of-val-fixer updater-of-val-fixer "-1")
                                          updater-of-val-fixer))
                (contents-updater-of-val-fixer (symbolicate ',contents ',contents "-" updater-of-val-fixer))
                (body
                 `(with-books (("projects/atomic-stobjs/lemmas/define-hash-table-lemmas" :dir :system))

                    ,@(and (or ',(and key-recognizer
                                      key-fixer)
                               (and val-recognizer
                                    val-fixer)
                               val-type-is-stobj)
                           `((local
                               (defthm ,',hash-table-entry-guard
                                 (and ,@(and ',(and key-recognizer
                                                    key-fixer)
                                             `((booleanp (,',key-recognizer ,',key))
                                               (,',key-recognizer ,default-key)
                                               (,',key-recognizer (,',key-fixer ,',key))
                                               (implies (,',key-recognizer ,',key)
                                                        (equal (,',key-fixer ,',key) ,',key))
                                               (implies (not (,',key-recognizer ,',key))
                                                        (equal (,',key-fixer ,',key) ,default-key))))
                                      ,@(and ',(or (eq test 'eq)
                                                   (eq test 'eql))
                                             `((implies (,',key-recognizer ,',key)
                                                        ,(case ',test
                                                           (eq
                                                            `(symbolp ,',key))
                                                           (eql
                                                            `(eqlablep ,',key))))))
                                      ,@(and ',(and val-recognizer
                                                    val-fixer)
                                             `((booleanp (,val-recognizer ,',val))
                                               (,val-recognizer ,default-val)
                                               (,val-recognizer (,val-fixer ,',val))
                                               (implies (,val-recognizer ,',val)
                                                        (equal (,val-fixer ,',val) ,',val))
                                               (implies (not (,val-recognizer ,',val))
                                                        (equal (,val-fixer ,',val) ,default-val))))
                                      ,@(and val-type-is-stobj
                                             `((equal ,',default-val ,default-val))))
                                 :rule-classes
                                 (,@(and ',(and key-recognizer
                                                key-fixer)
                                         `((:rewrite :corollary
                                                     (booleanp (,',key-recognizer ,',key)))
                                           (:rewrite :corollary
                                                     (,',key-recognizer (,',key-fixer ,',key)))
                                           (:rewrite :corollary
                                                     (implies (,',key-recognizer ,',key)
                                                              (equal (,',key-fixer ,',key) ,',key)))
                                           (:rewrite :corollary
                                                     (implies (not (,',key-recognizer ,',key))
                                                              (equal (,',key-fixer ,',key) ,default-key)))))
                                    ,@(and ',(or (eq test 'eq)
                                                 (eq test 'eql))
                                           `((:rewrite :corollary
                                                       (implies (,',key-recognizer ,',key)
                                                                ,(case ',test
                                                                   (eq
                                                                    `(symbolp ,',key))
                                                                   (eql
                                                                    `(eqlablep ,',key)))))))
                                    ,@(and ',(and val-recognizer
                                                  val-fixer)
                                           `((:rewrite :corollary
                                                       (booleanp (,val-recognizer ,',val)))
                                             (:rewrite :corollary
                                                       (,val-recognizer (,val-fixer ,',val)))
                                             (:rewrite :corollary
                                                       (implies (,val-recognizer ,',val)
                                                                (equal (,val-fixer ,',val) ,',val)))
                                             (:rewrite :corollary
                                                       (implies (not (,val-recognizer ,',val))
                                                                (equal (,val-fixer ,',val) ,default-val))))))
                                 :hints
                                 (("Goal"
                                   ,@(and ',(not testp)
                                          `(:in-theory (disable ,@(and ',key-recognizer
                                                                       '(,key-recognizer
                                                                         ,key-fixer))
                                                                ,@(and val-recognizer
                                                                       '(,val-recognizer
                                                                         ,val-fixer)))))))))))

                    ,@(and ',(not testp)
                           ',(or key-recognizer
                                 val-recognizer)
                           '((local
                               (in-theory
                                 (disable ,@(and key-recognizer
                                                 `((:d ,key-recognizer)
                                                   (:d ,key-fixer)
                                                   (:e ,key-fixer)))
                                          ,@(and val-recognizer
                                                 `((:d ,val-recognizer)
                                                   (:d ,val-fixer)
                                                   (:e ,val-fixer))))))))

                    (defun ,',contents-recognizer (,',contents)
                      (declare (xargs :guard t))
                      (if (consp ,',contents)
                          (let ((a (car ,',contents))
                                (d (cdr ,',contents)))
                            (and (consp a)
                                 (let ((,',key (car a))
                                       ,@(and val-recognizer
                                              `((,',val (cdr a)))))
                                   (and ,@(and ',key-recognizer
                                               `((,',key-recognizer ,',key)))
                                        ,@(and val-recognizer
                                               `((,val-recognizer ,',val)))
                                        (or (null d)
                                            (and (consp d)
                                                 (consp (car d))
                                                 (<< ,',key (caar d))
                                                 (,',contents-recognizer d)))))))
                          (null ,',contents)))

                    ,@(and ',copyable
                           `((defun ,',recognizer (,',hash-table)
                               (declare (xargs :guard t))
                               (and (consp ,',hash-table)
                                    (set::setp (car ,',hash-table))
                                    (,',contents-recognizer (cdr ,',hash-table))))))

                    (defun ,',contents-creator ()
                      (declare (xargs :guard t))
                      '())

                    ,@(and ',copyable
                           `((defun ,',creator ()
                               (declare (xargs :guard t))
                               (cons '() (,',contents-creator)))))

                    ,@(and ',copyable
                           `((defun ,',contents-fixer (,',contents)
                               (declare (xargs :guard (,',contents-recognizer ,',contents)))
                               (and (,',contents-recognizer ,',contents)
                                    ,',contents))))

                    (defun ,',fixer (,',hash-table)
                      (declare (xargs :guard (,',recognizer ,',hash-table)))
                      (if (,',recognizer ,',hash-table)
                          ,',hash-table
                          (,',creator)))

                    (defun ,',contents-accessor (,',key ,',contents)
                      (declare (xargs :guard (and ,@(and ',key-recognizer
                                                         `((,',key-recognizer ,',key)))
                                                  (,',contents-recognizer ,',contents))
                                      :measure (len ,',contents)))
                      (let (,@(and ',key-fixer
                                   `((,',key (,',key-fixer ,',key))))
                            (,',contents (,',contents-fixer ,',contents)))
                        (cond
                          ((or (null ,',contents)
                               (<< ,',key (caar ,',contents)))
                           ,(if val-type-is-stobj
                                ',default-val
                                default-val))
                          ((,',test ,',key (caar ,',contents))
                           ,(if val-fixer
                                `(,val-fixer (cdar ,',contents))
                                `(cdar ,',contents)))
                          (t
                           (,',contents-accessor ,',key (cdr ,',contents))))))

                    ,@(and ',copyable
                           `((defun ,',accessor (,',key ,',hash-table)
                               (declare (xargs :guard (and ,@(and ',key-recognizer
                                                                  `((,',key-recognizer ,',key)))
                                                           (,',recognizer ,',hash-table))))
                               (let (,@(and ',key-fixer
                                            `((,',key (,',key-fixer ,',key))))
                                     (,',hash-table (,',fixer ,',hash-table)))
                                 (,',contents-accessor ,',key (cdr ,',hash-table))))))

                    (defun ,',contents-updater (,',key ,',val ,',contents)
                      (declare (xargs :guard (and ,@(and ',key-recognizer
                                                         `((,',key-recognizer ,',key)))
                                                  ,@(and val-recognizer
                                                         `((,(if ',copyable
                                                                 val-recognizer
                                                                 ',val-recognizer)
                                                             ,',val)))
                                                  (,',contents-recognizer ,',contents))
                                      :measure (len ,',contents)))
                      (let (,@(and ',key-fixer
                                   `((,',key (,',key-fixer ,',key))))
                            ,@(and val-fixer
                                   `((,',val (,val-fixer ,',val))))
                              (,',contents (,',contents-fixer ,',contents)))
                        (if (endp ,',contents)
                            (list (cons ,',key ,',val))
                            (let* ((a (car ,',contents))
                                   (d (cdr ,',contents))
                                   (k (car a)))
                              (cond
                                ((<< ,',key k)
                                 (cons (cons ,',key ,',val)
                                       ,',contents))
                                ((,',test ,',key k)
                                 (cons (cons ,',key ,',val) d))
                                (t
                                 (cons a (,',contents-updater ,',key ,',val d))))))))

                    ,@(and ',copyable
                           `((defun ,',updater (,',key ,',val ,',hash-table)
                               (declare (xargs :guard (and ,@(and ',key-recognizer
                                                                  `((,',key-recognizer ,',key)))
                                                           ,@(and val-recognizer
                                                                  `((,',val-recognizer ,',val)))
                                                           (,',recognizer ,',hash-table))))
                               (let (,@(and ',key-fixer
                                            `((,',key (,',key-fixer ,',key))))
                                     ,@(and val-fixer
                                            `((,',val (,val-fixer ,',val))))
                                       (,',hash-table (,',fixer ,',hash-table)))
                                 (cons (car ,',hash-table)
                                       (,',contents-updater ,',key ,',val (cdr ,',hash-table)))))))

                    (defun ,',contents-boundp (,',key ,',contents)
                      (declare (xargs :guard (and ,@(and ',key-recognizer
                                                         `((,',key-recognizer ,',key)))
                                                  (,',contents-recognizer ,',contents))
                                      :measure (len ,',contents)))
                      (let (,@(and ',key-fixer
                                   `((,',key (,',key-fixer ,',key))))
                            (,',contents (,',contents-fixer ,',contents)))
                        (cond
                          ((or (null ,',contents)
                               (<< ,',key (caar ,',contents)))
                           'nil)
                          ((,',test ,',key (caar ,',contents))
                           't)
                          (t
                           (,',contents-boundp ,',key (cdr ,',contents))))))

                    ,@(and ',copyable
                           `((defun ,',boundp (,',key ,',hash-table)
                               (declare (xargs :guard (and ,@(and ',key-recognizer
                                                                  `((,',key-recognizer ,',key)))
                                                           (,',recognizer ,',hash-table))))
                               (let (,@(and ',key-fixer
                                            `((,',key (,',key-fixer ,',key))))
                                     (,',hash-table (,',fixer ,',hash-table)))
                                 (,',contents-boundp ,',key (cdr ,',hash-table))))))

                    (defun ,',contents-remover (,',key ,',contents)
                      (declare (xargs :guard (and ,@(and ',key-recognizer
                                                         `((,',key-recognizer ,',key)))
                                                  (,',contents-recognizer ,',contents))
                                      :measure (len ,',contents)))
                      (let (,@(and ',key-fixer
                                   `((,',key (,',key-fixer ,',key))))
                            (,',contents (,',contents-fixer ,',contents)))
                        (cond
                          ((null ,',contents)
                           (,',contents-creator))
                          ((<< ,',key (caar ,',contents))
                           ,',contents)
                          ((,',test ,',key (caar ,',contents))
                           (cdr ,',contents))
                          (t
                           (cons (car ,',contents) (,',contents-remover ,',key (cdr ,',contents)))))))

                    ,@(and ',copyable
                           `((defun ,',remover (,',key ,',hash-table)
                               (declare (xargs :guard (and ,@(and ',key-recognizer
                                                                  `((,',key-recognizer ,',key)))
                                                           (,',recognizer ,',hash-table))))
                               (let (,@(and ',key-fixer
                                            `((,',key (,',key-fixer ,',key))))
                                     (,',hash-table (,',fixer ,',hash-table)))
                                 (cons (car ,',hash-table)
                                       (,',contents-remover ,',key (cdr ,',hash-table)))))))

                    (defun ,',contents-count (,',contents)
                      (declare (xargs :guard (,',contents-recognizer ,',contents)))
                      (let ((,',contents (,',contents-fixer ,',contents)))
                        (if (consp ,',contents)
                            (1+ (,',contents-count (cdr ,',contents)))
                            0)))

                    ,@(and ',copyable
                           `((defun ,',count (,',hash-table)
                               (declare (xargs :guard (,',recognizer ,',hash-table)))
                               (let ((,',hash-table (,',fixer ,',hash-table)))
                                 (,',contents-count (cdr ,',hash-table))))))

                    (defun ,',getp (,',key ,',hash-table)
                      (declare (xargs :guard (and ,@(and ',key-recognizer
                                                         `((,',key-recognizer ,',key)))
                                                  (,',recognizer ,',hash-table))))
                      (mv (,',accessor ,',key ,',hash-table)
                          (,',boundp ,',key ,',hash-table)))

                    (defthm ,',getp{rewrite}
                      (mv-let (v w)
                              (,',getp ,',key ,',hash-table)
                        (and (equal v (,',accessor ,',key ,',hash-table))
                             (equal w (,',boundp ,',key ,',hash-table))))
                      :hints
                      (("Goal"
                        :in-theory (disable ,',accessor
                                            ,',boundp
                                            ,',recognizer
                                            ,@(and ',(and key-recognizer
                                                          (not testp))
                                                   '(,key-recognizer))))))

                    (defun ,',clear (,',hash-table)
                      (declare (xargs :guard (,',recognizer ,',hash-table))
                               (ignore ,',hash-table))
                      (,',creator))

                    (defthm ,',clear{rewrite}
                      (equal (,',clear ,',hash-table)
                             (,',creator))
                      :hints
                      (("Goal"
                        :in-theory (disable ,',creator))))

                    (defun ,',init (ht-size rehash-size rehash-threshold ,',hash-table)
                      (declare (xargs :guard (and (,',recognizer ,',hash-table)
                                                  (or (natp ht-size)
                                                      (not ht-size))
                                                  (or (and (rationalp rehash-size)
                                                           (<= 1 rehash-size))
                                                      (not rehash-size))
                                                  (or (and (rationalp rehash-threshold)
                                                           (<= 0 rehash-threshold)
                                                           (<= rehash-threshold 1))
                                                      (not rehash-threshold))))
                               (ignore ht-size rehash-size rehash-threshold ,',hash-table))
                      (,',creator))

                    (defthm ,',init{rewrite}
                      (equal (,',init ht-size rehash-size rehash-threshold ,',hash-table)
                             (,',creator))
                      :hints
                      (("Goal"
                        :in-theory (disable ,',creator))))

                    ,(let ((thm `(defthm ,',contents-recognizer{compound-recognizer}
                                   (implies (,',contents-recognizer ,',contents)
                                            (true-listp ,',contents))
                                   :rule-classes :compound-recognizer)))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',recognizer{compound-recognizer}
                               (implies (,',recognizer ,',hash-table)
                                        (and (consp ,',hash-table)
                                             (true-listp ,',hash-table)))
                               :rule-classes :compound-recognizer
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-recognizer))))))

                    (in-theory
                      (disable (:e ,',creator)
                               ,@(and ',copyable
                                      `((:e ,',contents-creator)))))

                    (defthm ,',recognizer-of-creator
                      (,',recognizer (,',creator)))

                    (local
                      (defthm ,',emptyp-of-creator
                        (omap::emptyp (,',creator))))

                    ,(let ((thm `(defthm ,',contents-recognizer-of-contents-fixer
                                   (,',contents-recognizer (,',contents-fixer ,',contents))
                                   :hints
                                   (("Goal"
                                     :in-theory (disable (:e ,',contents-accessor))
                                     :by (:functional-instance
                                          define-hash-table::recognizer-of-fixer
                                          (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::key-fixer ,(or ',key-fixer
                                                                             'identity))
                                          (define-hash-table::key-default (lambda () ,default-key))
                                          (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::val-fixer ,(or val-fixer
                                                                             'identity))
                                          (define-hash-table::val-default (lambda () ,default-val))
                                          (define-hash-table::recognizer ,',contents-recognizer)
                                          (define-hash-table::creator ,',contents-creator)
                                          (define-hash-table::fixer ,',contents-fixer)
                                          (define-hash-table::accessor ,',contents-accessor)
                                          (define-hash-table::updater ,',contents-updater)
                                          (define-hash-table::boundp ,',contents-boundp)
                                          (define-hash-table::remover ,',contents-remover)
                                          (define-hash-table::count ,',contents-count)
                                          (define-hash-table::hash-table (lambda () ,',contents))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',recognizer-of-fixer
                               (,',recognizer (,',fixer ,',hash-table))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',recognizer))))))

                    ,(let ((thm `(defthm ,',contents-fixer-when-contents-recognizer
                                   (implies (,',contents-recognizer ,',contents)
                                            (equal (,',contents-fixer ,',contents) ,',contents))
                                   :hints
                                   (("Goal"
                                     :by (:functional-instance
                                          define-hash-table::fixer-when-recognizer
                                          (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::key-fixer ,(or ',key-fixer
                                                                             'identity))
                                          (define-hash-table::key-default (lambda () ,default-key))
                                          (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::val-fixer ,(or val-fixer
                                                                             'identity))
                                          (define-hash-table::val-default (lambda () ,default-val))
                                          (define-hash-table::recognizer ,',contents-recognizer)
                                          (define-hash-table::creator ,',contents-creator)
                                          (define-hash-table::fixer ,',contents-fixer)
                                          (define-hash-table::accessor ,',contents-accessor)
                                          (define-hash-table::updater ,',contents-updater)
                                          (define-hash-table::boundp ,',contents-boundp)
                                          (define-hash-table::remover ,',contents-remover)
                                          (define-hash-table::count ,',contents-count)
                                          (define-hash-table::hash-table (lambda () ,',contents))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',fixer-when-recognizer
                               (implies (,',recognizer ,',hash-table)
                                        (equal (,',fixer ,',hash-table) ,',hash-table))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',recognizer))))))

                    ,(let ((thm `(defthm ,',contents-fixer-when-not-contents-recognizer
                                   (implies (not (,',contents-recognizer ,',contents))
                                            (equal (,',contents-fixer ,',contents) (,',contents-creator)))
                                   :hints
                                   (("Goal"
                                     :by (:functional-instance
                                          define-hash-table::fixer-when-not-recognizer
                                          (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::key-fixer ,(or ',key-fixer
                                                                             'identity))
                                          (define-hash-table::key-default (lambda () ,default-key))
                                          (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::val-fixer ,(or val-fixer
                                                                             'identity))
                                          (define-hash-table::val-default (lambda () ,default-val))
                                          (define-hash-table::recognizer ,',contents-recognizer)
                                          (define-hash-table::creator ,',contents-creator)
                                          (define-hash-table::fixer ,',contents-fixer)
                                          (define-hash-table::accessor ,',contents-accessor)
                                          (define-hash-table::updater ,',contents-updater)
                                          (define-hash-table::boundp ,',contents-boundp)
                                          (define-hash-table::remover ,',contents-remover)
                                          (define-hash-table::count ,',contents-count)
                                          (define-hash-table::hash-table (lambda () ,',contents))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',fixer-when-not-recognizer
                               (implies (not (,',recognizer ,',hash-table))
                                        (equal (,',fixer ,',hash-table) (,',creator)))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',recognizer))))))

                    ,@(and val-recognizer
                           (append
                            (list (let ((thm `(defthm ,val-recognizer-of-contents-accessor
                                                (,val-recognizer (,',contents-accessor ,',key ,',contents))
                                                :hints
                                                (("Goal"
                                                  :by (:functional-instance
                                                       define-hash-table::val-recognizer-of-accessor
                                                       (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                               '(lambda (x) t)))
                                                       (define-hash-table::key-fixer ,(or ',key-fixer
                                                                                          'identity))
                                                       (define-hash-table::key-default (lambda () ,default-key))
                                                       (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                               '(lambda (x) t)))
                                                       (define-hash-table::val-fixer ,(or val-fixer
                                                                                          'identity))
                                                       (define-hash-table::val-default (lambda () ,default-val))
                                                       (define-hash-table::recognizer ,',contents-recognizer)
                                                       (define-hash-table::creator ,',contents-creator)
                                                       (define-hash-table::fixer ,',contents-fixer)
                                                       (define-hash-table::accessor ,',contents-accessor)
                                                       (define-hash-table::updater ,',contents-updater)
                                                       (define-hash-table::boundp ,',contents-boundp)
                                                       (define-hash-table::remover ,',contents-remover)
                                                       (define-hash-table::count ,',contents-count)
                                                       (define-hash-table::hash-table (lambda () ,',contents))
                                                       (define-hash-table::key (lambda () ,',key))))))))
                                    (if ',copyable
                                        `(local ,thm)
                                        thm)))

                            (and ',copyable
                                 `((defthm ,val-recognizer-of-accessor
                                     (,val-recognizer (,',accessor ,',key ,',hash-table))
                                     :hints
                                     (("Goal"
                                       :in-theory (disable ,',contents-accessor))))))))

                    ,@(and ',key-fixer
                           (append
                            (list (let ((thm `(defthm ,',contents-accessor-of-key-fixer
                                                (equal (,',contents-accessor (,',key-fixer ,',key) ,',contents)
                                                       (,',contents-accessor ,',key ,',contents))
                                                :hints
                                                (("Goal"
                                                  :by (:functional-instance
                                                       define-hash-table::accessor-of-key-fixer
                                                       (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                               '(lambda (x) t)))
                                                       (define-hash-table::key-fixer ,(or ',key-fixer
                                                                                          'identity))
                                                       (define-hash-table::key-default (lambda () ,default-key))
                                                       (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                               '(lambda (x) t)))
                                                       (define-hash-table::val-fixer ,(or val-fixer
                                                                                          'identity))
                                                       (define-hash-table::val-default (lambda () ,default-val))
                                                       (define-hash-table::recognizer ,',contents-recognizer)
                                                       (define-hash-table::creator ,',contents-creator)
                                                       (define-hash-table::fixer ,',contents-fixer)
                                                       (define-hash-table::accessor ,',contents-accessor)
                                                       (define-hash-table::updater ,',contents-updater)
                                                       (define-hash-table::boundp ,',contents-boundp)
                                                       (define-hash-table::remover ,',contents-remover)
                                                       (define-hash-table::count ,',contents-count)
                                                       (define-hash-table::hash-table (lambda () ,',contents))
                                                       (define-hash-table::key (lambda () ,',key))))))))
                                    (if ',copyable
                                        `(local ,thm)
                                        thm)))

                            (and ',copyable
                                 `((defthm ,',accessor-of-key-fixer
                                     (equal (,',accessor (,',key-fixer ,',key) ,',hash-table)
                                            (,',accessor ,',key ,',hash-table))
                                     :hints
                                     (("Goal"
                                       :in-theory (disable ,',contents-accessor))))))))

                    ,(let ((thm `(defthm ,',contents-accessor-of-contents-fixer
                                   (equal (,',contents-accessor ,',key (,',contents-fixer ,',contents))
                                          (,',contents-accessor ,',key ,',contents))
                                   :hints
                                   (("Goal"
                                     :by (:functional-instance
                                          define-hash-table::accessor-of-fixer
                                          (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::key-fixer ,(or ',key-fixer
                                                                             'identity))
                                          (define-hash-table::key-default (lambda () ,default-key))
                                          (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::val-fixer ,(or val-fixer
                                                                             'identity))
                                          (define-hash-table::val-default (lambda () ,default-val))
                                          (define-hash-table::recognizer ,',contents-recognizer)
                                          (define-hash-table::creator ,',contents-creator)
                                          (define-hash-table::fixer ,',contents-fixer)
                                          (define-hash-table::accessor ,',contents-accessor)
                                          (define-hash-table::updater ,',contents-updater)
                                          (define-hash-table::boundp ,',contents-boundp)
                                          (define-hash-table::remover ,',contents-remover)
                                          (define-hash-table::count ,',contents-count)
                                          (define-hash-table::hash-table (lambda () ,',contents))
                                          (define-hash-table::key (lambda () ,',key))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',accessor-of-fixer
                               (equal (,',accessor ,',key (,',fixer ,',hash-table))
                                      (,',accessor ,',key ,',hash-table))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-accessor
                                                     ,',contents-fixer))))))

                    ,@(and ',key-recognizer
                           (let ((thm `(defthmd ,',contents-accessor-when-not-key-recognizer
                                         (implies (and (syntaxp (not (quotep ,',key)))
                                                       (not (,',key-recognizer ,',key)))
                                                  (equal (,',contents-accessor ,',key ,',contents)
                                                         (,',contents-accessor ,default-key ,',contents)))
                                         :hints
                                         (("Goal"
                                           :by (:functional-instance
                                                define-hash-table::accessor-when-not-key-recognizer
                                                (define-hash-table::key-recognizer ,',key-recognizer)
                                                (define-hash-table::key-fixer ,(or ',key-fixer
                                                                                   'identity))
                                                (define-hash-table::key-default (lambda () ,default-key))
                                                (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                        '(lambda (x) t)))
                                                (define-hash-table::val-fixer ,(or val-fixer
                                                                                   'identity))
                                                (define-hash-table::val-default (lambda () ,default-val))
                                                (define-hash-table::recognizer ,',contents-recognizer)
                                                (define-hash-table::creator ,',contents-creator)
                                                (define-hash-table::fixer ,',contents-fixer)
                                                (define-hash-table::accessor ,',contents-accessor)
                                                (define-hash-table::updater ,',contents-updater)
                                                (define-hash-table::boundp ,',contents-boundp)
                                                (define-hash-table::remover ,',contents-remover)
                                                (define-hash-table::count ,',contents-count)
                                                (define-hash-table::hash-table (lambda () ,',contents))
                                                (define-hash-table::key (lambda () ,',key))
                                                (define-hash-table::val (lambda () ,',val))))))))
                             (list (if ',copyable
                                       `(local ,thm)
                                       thm))))

                    ,@(and ',(and copyable
                                  key-recognizer)
                           `((defthmd ,',accessor-when-not-key-recognizer
                               (implies (and (syntaxp (not (quotep ,',key)))
                                             (not (,',key-recognizer ,',key)))
                                        (equal (,',accessor ,',key ,',hash-table)
                                               (,',accessor ,default-key ,',hash-table)))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-accessor
                                                     ,',fixer)
                                 :use ((:instance ,',contents-accessor-when-not-key-recognizer
                                                  (,',contents (cdr (,',fixer ,',hash-table))))))))))

                    ,(let ((thm `(defthm ,',contents-recognizer-of-contents-updater
                                   (,',contents-recognizer (,',contents-updater ,',key ,',val ,',contents))
                                   :hints
                                   (("Goal"
                                     :by (:functional-instance
                                          define-hash-table::recognizer-of-updater
                                          (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::key-fixer ,(or ',key-fixer
                                                                             'identity))
                                          (define-hash-table::key-default (lambda () ,default-key))
                                          (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::val-fixer ,(or val-fixer
                                                                             'identity))
                                          (define-hash-table::val-default (lambda () ,default-val))
                                          (define-hash-table::recognizer ,',contents-recognizer)
                                          (define-hash-table::creator ,',contents-creator)
                                          (define-hash-table::fixer ,',contents-fixer)
                                          (define-hash-table::accessor ,',contents-accessor)
                                          (define-hash-table::updater ,',contents-updater)
                                          (define-hash-table::boundp ,',contents-boundp)
                                          (define-hash-table::remover ,',contents-remover)
                                          (define-hash-table::count ,',contents-count)
                                          (define-hash-table::hash-table (lambda () ,',contents))
                                          (define-hash-table::key (lambda () ,',key))
                                          (define-hash-table::val (lambda () ,',val))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',recognizer-of-updater
                               (,',recognizer (,',updater ,',key ,',val ,',hash-table))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-recognizer
                                                     ,',contents-updater))))))

                    ,@(and ',key-fixer
                           (append
                            (list (let ((thm `(defthm ,contents-updater-of-key-fixer
                                                (equal (,',contents-updater (,',key-fixer ,',key) ,',val ,',contents)
                                                       (,',contents-updater ,',key ,',val ,',contents))
                                                :hints
                                                (("Goal"
                                                  :by (:functional-instance
                                                       define-hash-table::updater-of-key-fixer
                                                       (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                               '(lambda (x) t)))
                                                       (define-hash-table::key-fixer ,(or ',key-fixer
                                                                                          'identity))
                                                       (define-hash-table::key-default (lambda () ,default-key))
                                                       (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                               '(lambda (x) t)))
                                                       (define-hash-table::val-fixer ,(or val-fixer
                                                                                          'identity))
                                                       (define-hash-table::val-default (lambda () ,default-val))
                                                       (define-hash-table::recognizer ,',contents-recognizer)
                                                       (define-hash-table::creator ,',contents-creator)
                                                       (define-hash-table::fixer ,',contents-fixer)
                                                       (define-hash-table::accessor ,',contents-accessor)
                                                       (define-hash-table::updater ,',contents-updater)
                                                       (define-hash-table::boundp ,',contents-boundp)
                                                       (define-hash-table::remover ,',contents-remover)
                                                       (define-hash-table::count ,',contents-count)
                                                       (define-hash-table::hash-table (lambda () ,',contents))
                                                       (define-hash-table::key (lambda () ,',key))
                                                       (define-hash-table::val (lambda () ,',val))))))))
                                    (if ',copyable
                                        `(local ,thm)
                                        thm)))

                            (and ',copyable
                                 `((defthm ,updater-of-key-fixer
                                     (equal (,',updater (,',key-fixer ,',key) ,',val ,',hash-table)
                                            (,',updater ,',key ,',val ,',hash-table))
                                     :hints
                                     (("Goal"
                                       :in-theory (disable ,',contents-updater))))))))

                    ,@(and val-fixer
                           (append
                            (list (let ((thm `(defthm ,contents-updater-of-val-fixer
                                                (equal (,',contents-updater ,',key (,val-fixer ,',val) ,',contents)
                                                       (,',contents-updater ,',key ,',val ,',contents))
                                                :hints
                                                (("Goal"
                                                  :by (:functional-instance
                                                       define-hash-table::updater-of-val-fixer
                                                       (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                               '(lambda (x) t)))
                                                       (define-hash-table::key-fixer ,(or ',key-fixer
                                                                                          'identity))
                                                       (define-hash-table::key-default (lambda () ,default-key))
                                                       (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                               '(lambda (x) t)))
                                                       (define-hash-table::val-fixer ,(or val-fixer
                                                                                          'identity))
                                                       (define-hash-table::val-default (lambda () ,default-val))
                                                       (define-hash-table::recognizer ,',contents-recognizer)
                                                       (define-hash-table::creator ,',contents-creator)
                                                       (define-hash-table::fixer ,',contents-fixer)
                                                       (define-hash-table::accessor ,',contents-accessor)
                                                       (define-hash-table::updater ,',contents-updater)
                                                       (define-hash-table::boundp ,',contents-boundp)
                                                       (define-hash-table::remover ,',contents-remover)
                                                       (define-hash-table::count ,',contents-count)
                                                       (define-hash-table::hash-table (lambda () ,',contents))
                                                       (define-hash-table::key (lambda () ,',key))
                                                       (define-hash-table::val (lambda () ,',val))))))))
                                    (if ',copyable
                                        `(local ,thm)
                                        thm)))

                            (and ',copyable
                                 `((defthm ,updater-of-val-fixer
                                     (equal (,',updater ,',key (,val-fixer ,',val) ,',hash-table)
                                            (,',updater ,',key ,',val ,',hash-table))
                                     :hints
                                     (("Goal"
                                       :in-theory (disable ,',contents-updater))))))))

                    ,(let ((thm `(defthm ,',contents-updater-of-contents-fixer
                                   (equal (,',contents-updater ,',key ,',val (,',contents-fixer ,',contents))
                                          (,',contents-updater ,',key ,',val ,',contents))
                                   :hints
                                   (("Goal"
                                     :by (:functional-instance
                                          define-hash-table::updater-of-fixer
                                          (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::key-fixer ,(or ',key-fixer
                                                                             'identity))
                                          (define-hash-table::key-default (lambda () ,default-key))
                                          (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::val-fixer ,(or val-fixer
                                                                             'identity))
                                          (define-hash-table::val-default (lambda () ,default-val))
                                          (define-hash-table::recognizer ,',contents-recognizer)
                                          (define-hash-table::creator ,',contents-creator)
                                          (define-hash-table::fixer ,',contents-fixer)
                                          (define-hash-table::accessor ,',contents-accessor)
                                          (define-hash-table::updater ,',contents-updater)
                                          (define-hash-table::boundp ,',contents-boundp)
                                          (define-hash-table::remover ,',contents-remover)
                                          (define-hash-table::count ,',contents-count)
                                          (define-hash-table::hash-table (lambda () ,',contents))
                                          (define-hash-table::key (lambda () ,',key))
                                          (define-hash-table::val (lambda () ,',val))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',updater-of-fixer
                               (equal (,',updater ,',key ,',val (,',fixer ,',hash-table))
                                      (,',updater ,',key ,',val ,',hash-table))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-updater
                                                     ,',contents-fixer))))))

                    ,@(and ',key-recognizer
                           (let ((thm `(defthmd ,contents-updater-when-not-key-recognizer
                                         (implies (and (syntaxp (not (quotep ,',key)))
                                                       (not (,',key-recognizer ,',key)))
                                                  (equal (,',contents-updater ,',key ,',val ,',contents)
                                                         (,',contents-updater ,default-key ,',val ,',contents)))
                                         :hints
                                         (("Goal"
                                           :by (:functional-instance
                                                define-hash-table::updater-when-not-key-recognizer
                                                (define-hash-table::key-recognizer ,',key-recognizer)
                                                (define-hash-table::key-fixer ,(or ',key-fixer
                                                                                   'identity))
                                                (define-hash-table::key-default (lambda () ,default-key))
                                                (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                        '(lambda (x) t)))
                                                (define-hash-table::val-fixer ,(or val-fixer
                                                                                   'identity))
                                                (define-hash-table::val-default (lambda () ,default-val))
                                                (define-hash-table::recognizer ,',contents-recognizer)
                                                (define-hash-table::creator ,',contents-creator)
                                                (define-hash-table::fixer ,',contents-fixer)
                                                (define-hash-table::accessor ,',contents-accessor)
                                                (define-hash-table::updater ,',contents-updater)
                                                (define-hash-table::boundp ,',contents-boundp)
                                                (define-hash-table::remover ,',contents-remover)
                                                (define-hash-table::count ,',contents-count)
                                                (define-hash-table::hash-table (lambda () ,',contents))
                                                (define-hash-table::key (lambda () ,',key))
                                                (define-hash-table::val (lambda () ,',val))))))))
                             (list (if ',copyable
                                       `(local ,thm)
                                       thm))))

                    ,@(and ',(and copyable
                                  key-recognizer)
                           `((defthmd ,updater-when-not-key-recognizer
                               (implies (and (syntaxp (not (quotep ,',key)))
                                             (not (,',key-recognizer ,',key)))
                                        (equal (,',updater ,',key ,',val ,',hash-table)
                                               (,',updater ,default-key ,',val ,',hash-table)))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-updater
                                                     ,',fixer)
                                 :use ((:instance ,contents-updater-when-not-key-recognizer
                                                  (,',contents (cdr (,',fixer ,',hash-table))))
                                       (:instance ,contents-updater-when-not-key-recognizer
                                                  (,',contents (cdr (,',fixer ,',hash-table)))
                                                  (,',val ,default-val))))))))

                    ,@(and ',val-recognizer
                           (let ((thm `(defthmd ,contents-updater-when-not-val-recognizer
                                         (implies (and (syntaxp (not (quotep ,',val)))
                                                       (not (,val-recognizer ,',val)))
                                                  (equal (,',contents-updater ,',key ,',val ,',contents)
                                                         (,',contents-updater ,',key ,default-val ,',contents)))
                                         :hints
                                         (("Goal"
                                           :by (:functional-instance
                                                define-hash-table::updater-when-not-val-recognizer
                                                (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                        '(lambda (x) t)))
                                                (define-hash-table::key-fixer ,(or ',key-fixer
                                                                                   'identity))
                                                (define-hash-table::key-default (lambda () ,default-key))
                                                (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                        '(lambda (x) t)))
                                                (define-hash-table::val-fixer ,(or val-fixer
                                                                                   'identity))
                                                (define-hash-table::val-default (lambda () ,default-val))
                                                (define-hash-table::recognizer ,',contents-recognizer)
                                                (define-hash-table::creator ,',contents-creator)
                                                (define-hash-table::fixer ,',contents-fixer)
                                                (define-hash-table::accessor ,',contents-accessor)
                                                (define-hash-table::updater ,',contents-updater)
                                                (define-hash-table::boundp ,',contents-boundp)
                                                (define-hash-table::remover ,',contents-remover)
                                                (define-hash-table::count ,',contents-count)
                                                (define-hash-table::hash-table (lambda () ,',contents))
                                                (define-hash-table::key (lambda () ,',key))
                                                (define-hash-table::val (lambda () ,',val))))))))
                             (list (if ',copyable
                                       `(local ,thm)
                                       thm))))

                    ,@(and ',(and copyable
                                  val-recognizer)
                           `((defthmd ,updater-when-not-val-recognizer
                               (implies (and (syntaxp (not (quotep ,',val)))
                                             (not (,val-recognizer ,',val)))
                                        (equal (,',updater ,',key ,',val ,',hash-table)
                                               (,',updater ,',key ,default-val ,',hash-table)))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-updater
                                                     ,',fixer)
                                 :use ((:instance ,contents-updater-when-not-val-recognizer
                                                  (,',contents (cdr (,',fixer ,',hash-table))))))))))

                    ,@(and ',key-fixer
                           (append
                            (list (let ((thm `(defthm ,',contents-boundp-of-key-fixer
                                                (equal (,',contents-boundp (,',key-fixer ,',key) ,',contents)
                                                       (,',contents-boundp ,',key ,',contents))
                                                :hints
                                                (("Goal"
                                                  :by (:functional-instance
                                                       define-hash-table::boundp-of-key-fixer
                                                       (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                               '(lambda (x) t)))
                                                       (define-hash-table::key-fixer ,(or ',key-fixer
                                                                                          'identity))
                                                       (define-hash-table::key-default (lambda () ,default-key))
                                                       (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                               '(lambda (x) t)))
                                                       (define-hash-table::val-fixer ,(or val-fixer
                                                                                          'identity))
                                                       (define-hash-table::val-default (lambda () ,default-val))
                                                       (define-hash-table::recognizer ,',contents-recognizer)
                                                       (define-hash-table::creator ,',contents-creator)
                                                       (define-hash-table::fixer ,',contents-fixer)
                                                       (define-hash-table::accessor ,',contents-accessor)
                                                       (define-hash-table::updater ,',contents-updater)
                                                       (define-hash-table::boundp ,',contents-boundp)
                                                       (define-hash-table::remover ,',contents-remover)
                                                       (define-hash-table::count ,',contents-count)
                                                       (define-hash-table::hash-table (lambda () ,',contents))
                                                       (define-hash-table::key (lambda () ,',key))
                                                       (define-hash-table::val (lambda () ,',val))))))))
                                    (if ',copyable
                                        `(local ,thm)
                                        thm)))

                            (and ',copyable
                                 `((defthm ,',boundp-of-key-fixer
                                     (equal (,',boundp (,',key-fixer ,',key) ,',hash-table)
                                            (,',boundp ,',key ,',hash-table))
                                     :hints
                                     (("Goal"
                                       :in-theory (disable ,',contents-boundp))))))))

                    ,(let ((thm `(defthm ,',contents-boundp-of-contents-fixer
                                   (equal (,',contents-boundp ,',key (,',contents-fixer ,',contents))
                                          (,',contents-boundp ,',key ,',contents))
                                   :hints
                                   (("Goal"
                                     :by (:functional-instance
                                          define-hash-table::boundp-of-fixer
                                          (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::key-fixer ,(or ',key-fixer
                                                                             'identity))
                                          (define-hash-table::key-default (lambda () ,default-key))
                                          (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::val-fixer ,(or val-fixer
                                                                             'identity))
                                          (define-hash-table::val-default (lambda () ,default-val))
                                          (define-hash-table::recognizer ,',contents-recognizer)
                                          (define-hash-table::creator ,',contents-creator)
                                          (define-hash-table::fixer ,',contents-fixer)
                                          (define-hash-table::accessor ,',contents-accessor)
                                          (define-hash-table::updater ,',contents-updater)
                                          (define-hash-table::boundp ,',contents-boundp)
                                          (define-hash-table::remover ,',contents-remover)
                                          (define-hash-table::count ,',contents-count)
                                          (define-hash-table::hash-table (lambda () ,',contents))
                                          (define-hash-table::key (lambda () ,',key))
                                          (define-hash-table::val (lambda () ,',val))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',boundp-of-fixer
                               (equal (,',boundp ,',key (,',fixer ,',hash-table))
                                      (,',boundp ,',key ,',hash-table))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-boundp
                                                     ,',contents-fixer))))))

                    ,@(and ',key-recognizer
                           (let ((thm `(defthmd ,',contents-boundp-when-not-key-recognizer
                                         (implies (and (syntaxp (not (quotep ,',key)))
                                                       (not (,',key-recognizer ,',key)))
                                                  (equal (,',contents-boundp ,',key ,',contents)
                                                         (,',contents-boundp ,default-key ,',contents)))
                                         :hints
                                         (("Goal"
                                           :by (:functional-instance
                                                define-hash-table::boundp-when-not-key-recognizer
                                                (define-hash-table::key-recognizer ,',key-recognizer)
                                                (define-hash-table::key-fixer ,(or ',key-fixer
                                                                                   'identity))
                                                (define-hash-table::key-default (lambda () ,default-key))
                                                (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                        '(lambda (x) t)))
                                                (define-hash-table::val-fixer ,(or val-fixer
                                                                                   'identity))
                                                (define-hash-table::val-default (lambda () ,default-val))
                                                (define-hash-table::recognizer ,',contents-recognizer)
                                                (define-hash-table::creator ,',contents-creator)
                                                (define-hash-table::fixer ,',contents-fixer)
                                                (define-hash-table::accessor ,',contents-accessor)
                                                (define-hash-table::updater ,',contents-updater)
                                                (define-hash-table::boundp ,',contents-boundp)
                                                (define-hash-table::remover ,',contents-remover)
                                                (define-hash-table::count ,',contents-count)
                                                (define-hash-table::hash-table (lambda () ,',contents))
                                                (define-hash-table::key (lambda () ,',key))
                                                (define-hash-table::val (lambda () ,',val))))))))
                             (list (if ',copyable
                                       `(local ,thm)
                                       thm))))

                    ,@(and ',(and copyable
                                  key-recognizer)
                           `((defthmd ,',boundp-when-not-key-recognizer
                               (implies (and (syntaxp (not (quotep ,',key)))
                                             (not (,',key-recognizer ,',key)))
                                        (equal (,',boundp ,',key ,',hash-table)
                                               (,',boundp ,default-key ,',hash-table)))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-boundp
                                                     ,',fixer)
                                 :use ((:instance ,',contents-boundp-when-not-key-recognizer
                                                  (,',contents (cdr (,',fixer ,',hash-table))))))))))

                    ,(let ((thm `(defthmd ,',contents-boundp-when-not-contents-recognizer
                                   (implies (not (,',contents-recognizer ,',contents))
                                            (not (,',contents-boundp ,',key ,',contents))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthmd ,',boundp-when-not-recognizer
                               (implies (not (,',recognizer ,',hash-table))
                                        (not (,',boundp ,',key ,',hash-table)))
                               :hints
                               (("Goal"
                                 :use ((:instance ,',contents-boundp-when-not-contents-recognizer
                                                  (,',contents (cdr ,',hash-table)))))))))

                    ,(let ((thm `(defthm ,',contents-recognizer-of-contents-remover
                                   (,',contents-recognizer (,',contents-remover ,',key ,',contents))
                                   :hints
                                   (("Goal"
                                     :by (:functional-instance
                                          define-hash-table::recognizer-of-remover
                                          (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::key-fixer ,(or ',key-fixer
                                                                             'identity))
                                          (define-hash-table::key-default (lambda () ,default-key))
                                          (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::val-fixer ,(or val-fixer
                                                                             'identity))
                                          (define-hash-table::val-default (lambda () ,default-val))
                                          (define-hash-table::recognizer ,',contents-recognizer)
                                          (define-hash-table::creator ,',contents-creator)
                                          (define-hash-table::fixer ,',contents-fixer)
                                          (define-hash-table::accessor ,',contents-accessor)
                                          (define-hash-table::updater ,',contents-updater)
                                          (define-hash-table::boundp ,',contents-boundp)
                                          (define-hash-table::remover ,',contents-remover)
                                          (define-hash-table::count ,',contents-count)
                                          (define-hash-table::hash-table (lambda () ,',contents))
                                          (define-hash-table::key (lambda () ,',key))
                                          (define-hash-table::val (lambda () ,',val))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',recognizer-of-remover
                               (,',recognizer (,',remover ,',key ,',hash-table))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-recognizer
                                                     ,',contents-remover))))))

                    ,@(and ',key-fixer
                           (append
                            (list (let ((thm `(defthm ,',contents-remover-of-key-fixer
                                                (equal (,',contents-remover (,',key-fixer ,',key) ,',contents)
                                                       (,',contents-remover ,',key ,',contents))
                                                :hints
                                                (("Goal"
                                                  :by (:functional-instance
                                                       define-hash-table::remover-of-key-fixer
                                                       (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                               '(lambda (x) t)))
                                                       (define-hash-table::key-fixer ,(or ',key-fixer
                                                                                          'identity))
                                                       (define-hash-table::key-default (lambda () ,default-key))
                                                       (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                               '(lambda (x) t)))
                                                       (define-hash-table::val-fixer ,(or val-fixer
                                                                                          'identity))
                                                       (define-hash-table::val-default (lambda () ,default-val))
                                                       (define-hash-table::recognizer ,',contents-recognizer)
                                                       (define-hash-table::creator ,',contents-creator)
                                                       (define-hash-table::fixer ,',contents-fixer)
                                                       (define-hash-table::accessor ,',contents-accessor)
                                                       (define-hash-table::updater ,',contents-updater)
                                                       (define-hash-table::boundp ,',contents-boundp)
                                                       (define-hash-table::remover ,',contents-remover)
                                                       (define-hash-table::count ,',contents-count)
                                                       (define-hash-table::hash-table (lambda () ,',contents))
                                                       (define-hash-table::key (lambda () ,',key))
                                                       (define-hash-table::val (lambda () ,',val))))))))
                                    (if ',copyable
                                        `(local ,thm)
                                        thm)))

                            (and ',copyable
                                 `((defthm ,',remover-of-key-fixer
                                     (equal (,',remover (,',key-fixer ,',key) ,',hash-table)
                                            (,',remover ,',key ,',hash-table))
                                     :hints
                                     (("Goal"
                                       :in-theory (disable ,',contents-recognizer))))))))

                    ,(let ((thm `(defthm ,',contents-remover-of-contents-fixer
                                   (equal (,',contents-remover ,',key (,',contents-fixer ,',contents))
                                          (,',contents-remover ,',key ,',contents))
                                   :hints
                                   (("Goal"
                                     :by (:functional-instance
                                          define-hash-table::remover-of-fixer
                                          (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::key-fixer ,(or ',key-fixer
                                                                             'identity))
                                          (define-hash-table::key-default (lambda () ,default-key))
                                          (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::val-fixer ,(or val-fixer
                                                                             'identity))
                                          (define-hash-table::val-default (lambda () ,default-val))
                                          (define-hash-table::recognizer ,',contents-recognizer)
                                          (define-hash-table::creator ,',contents-creator)
                                          (define-hash-table::fixer ,',contents-fixer)
                                          (define-hash-table::accessor ,',contents-accessor)
                                          (define-hash-table::updater ,',contents-updater)
                                          (define-hash-table::boundp ,',contents-boundp)
                                          (define-hash-table::remover ,',contents-remover)
                                          (define-hash-table::count ,',contents-count)
                                          (define-hash-table::hash-table (lambda () ,',contents))
                                          (define-hash-table::key (lambda () ,',key))
                                          (define-hash-table::val (lambda () ,',val))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',remover-of-fixer
                               (equal (,',remover ,',key (,',fixer ,',hash-table))
                                      (,',remover ,',key ,',hash-table))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-recognizer
                                                     ,',contents-fixer))))))

                    ,@(and ',key-recognizer
                           (let ((thm `(defthmd ,',contents-remover-when-not-key-recognizer
                                         (implies (and (syntaxp (not (quotep ,',key)))
                                                       (not (,',key-recognizer ,',key)))
                                                  (equal (,',contents-remover ,',key ,',contents)
                                                         (,',contents-remover ,default-key ,',contents)))
                                         :hints
                                         (("Goal"
                                           :by (:functional-instance
                                                define-hash-table::remover-when-not-key-recognizer
                                                (define-hash-table::key-recognizer ,',key-recognizer)
                                                (define-hash-table::key-fixer ,(or ',key-fixer
                                                                                   'identity))
                                                (define-hash-table::key-default (lambda () ,default-key))
                                                (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                        '(lambda (x) t)))
                                                (define-hash-table::val-fixer ,(or val-fixer
                                                                                   'identity))
                                                (define-hash-table::val-default (lambda () ,default-val))
                                                (define-hash-table::recognizer ,',contents-recognizer)
                                                (define-hash-table::creator ,',contents-creator)
                                                (define-hash-table::fixer ,',contents-fixer)
                                                (define-hash-table::accessor ,',contents-accessor)
                                                (define-hash-table::updater ,',contents-updater)
                                                (define-hash-table::boundp ,',contents-boundp)
                                                (define-hash-table::remover ,',contents-remover)
                                                (define-hash-table::count ,',contents-count)
                                                (define-hash-table::hash-table (lambda () ,',contents))
                                                (define-hash-table::key (lambda () ,',key))
                                                (define-hash-table::val (lambda () ,',val))))))))
                             (list (if ',copyable
                                       `(local ,thm)
                                       thm))))

                    ,@(and ',(and copyable
                                  key-recognizer)
                           `((defthmd ,',remover-when-not-key-recognizer
                               (implies (and (syntaxp (not (quotep ,',key)))
                                             (not (,',key-recognizer ,',key)))
                                        (equal (,',remover ,',key ,',hash-table)
                                               (,',remover ,default-key ,',hash-table)))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-remover
                                                     ,',fixer)
                                 :use ((:instance ,',contents-remover-when-not-key-recognizer
                                                  (,',contents (cdr (,',fixer ,',hash-table))))))))))

                    ,(let ((thm `(defthm ,',contents-count-of-contents-fixer
                                   (equal (,',contents-count (,',contents-fixer ,',contents))
                                          (,',contents-count ,',contents))
                                   :hints
                                   (("Goal"
                                     :by (:functional-instance
                                          define-hash-table::count-of-fixer
                                          (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::key-fixer ,(or ',key-fixer
                                                                             'identity))
                                          (define-hash-table::key-default (lambda () ,default-key))
                                          (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::val-fixer ,(or val-fixer
                                                                             'identity))
                                          (define-hash-table::val-default (lambda () ,default-val))
                                          (define-hash-table::recognizer ,',contents-recognizer)
                                          (define-hash-table::creator ,',contents-creator)
                                          (define-hash-table::fixer ,',contents-fixer)
                                          (define-hash-table::accessor ,',contents-accessor)
                                          (define-hash-table::updater ,',contents-updater)
                                          (define-hash-table::boundp ,',contents-boundp)
                                          (define-hash-table::remover ,',contents-remover)
                                          (define-hash-table::count ,',contents-count)
                                          (define-hash-table::hash-table (lambda () ,',contents))
                                          (define-hash-table::key (lambda () ,',key))
                                          (define-hash-table::val (lambda () ,',val))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',count-of-fixer
                               (equal (,',count (,',fixer ,',hash-table))
                                      (,',count ,',hash-table))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-count
                                                     ,',contents-fixer))))))

                    ,(let ((thm `(defthmd ,',contents-count-when-not-contents-recognizer
                                   (implies (not (,',contents-recognizer ,',contents))
                                            (equal (,',contents-count ,',contents) 0)))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthmd ,',count-when-not-recognizer
                               (implies (not (,',recognizer ,',hash-table))
                                        (equal (,',count ,',hash-table) 0))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-recognizer
                                                     ,',contents-count)
                                 :use ((:instance ,',contents-count-when-not-contents-recognizer
                                                  (,',contents (cdr ,',hash-table)))))))))

                    ,(let ((thm `(defthm ,',contents-accessor-of-contents-creator
                                   (equal (,',contents-accessor ,',key (,',contents-creator))
                                          ,default-val)
                                   :hints
                                   (("Goal"
                                     :by (:functional-instance
                                          define-hash-table::accessor-of-creator
                                          (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::key-fixer ,(or ',key-fixer
                                                                             'identity))
                                          (define-hash-table::key-default (lambda () ,default-key))
                                          (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::val-fixer ,(or val-fixer
                                                                             'identity))
                                          (define-hash-table::val-default (lambda () ,default-val))
                                          (define-hash-table::recognizer ,',contents-recognizer)
                                          (define-hash-table::creator ,',contents-creator)
                                          (define-hash-table::fixer ,',contents-fixer)
                                          (define-hash-table::accessor ,',contents-accessor)
                                          (define-hash-table::updater ,',contents-updater)
                                          (define-hash-table::boundp ,',contents-boundp)
                                          (define-hash-table::remover ,',contents-remover)
                                          (define-hash-table::count ,',contents-count)
                                          (define-hash-table::hash-table (lambda () ,',contents))
                                          (define-hash-table::key (lambda () ,',key))
                                          (define-hash-table::val (lambda () ,',val))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',accessor-of-creator
                               (equal (,',accessor ,',key (,',creator))
                                      ,default-val))))

                    ,(let ((thm `(defthm ,',contents-boundp-of-contents-creator
                                   (not (,',contents-boundp ,',key (,',contents-creator)))
                                   :hints
                                   (("Goal"
                                     :by (:functional-instance
                                          define-hash-table::boundp-of-creator
                                          (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::key-fixer ,(or ',key-fixer
                                                                             'identity))
                                          (define-hash-table::key-default (lambda () ,default-key))
                                          (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::val-fixer ,(or val-fixer
                                                                             'identity))
                                          (define-hash-table::val-default (lambda () ,default-val))
                                          (define-hash-table::recognizer ,',contents-recognizer)
                                          (define-hash-table::creator ,',contents-creator)
                                          (define-hash-table::fixer ,',contents-fixer)
                                          (define-hash-table::accessor ,',contents-accessor)
                                          (define-hash-table::updater ,',contents-updater)
                                          (define-hash-table::boundp ,',contents-boundp)
                                          (define-hash-table::remover ,',contents-remover)
                                          (define-hash-table::count ,',contents-count)
                                          (define-hash-table::hash-table (lambda () ,',contents))
                                          (define-hash-table::key (lambda () ,',key))
                                          (define-hash-table::val (lambda () ,',val))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',boundp-of-creator
                               (not (,',boundp ,',key (,',creator))))))

                    ,(let ((thm `(defthm ,',contents-remover-of-contents-creator
                                   (equal (,',contents-remover ,',key (,',contents-creator))
                                          (,',contents-creator))
                                   :hints
                                   (("Goal"
                                     :by (:functional-instance
                                          define-hash-table::remover-of-creator
                                          (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::key-fixer ,(or ',key-fixer
                                                                             'identity))
                                          (define-hash-table::key-default (lambda () ,default-key))
                                          (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::val-fixer ,(or val-fixer
                                                                             'identity))
                                          (define-hash-table::val-default (lambda () ,default-val))
                                          (define-hash-table::recognizer ,',contents-recognizer)
                                          (define-hash-table::creator ,',contents-creator)
                                          (define-hash-table::fixer ,',contents-fixer)
                                          (define-hash-table::accessor ,',contents-accessor)
                                          (define-hash-table::updater ,',contents-updater)
                                          (define-hash-table::boundp ,',contents-boundp)
                                          (define-hash-table::remover ,',contents-remover)
                                          (define-hash-table::count ,',contents-count)
                                          (define-hash-table::hash-table (lambda () ,',contents))
                                          (define-hash-table::key (lambda () ,',key))
                                          (define-hash-table::val (lambda () ,',val))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',remover-of-creator
                               (equal (,',remover ,',key (,',creator))
                                      (,',creator)))))

                    ,(let ((thm `(defthm ,',contents-count-of-contents-creator
                                   (equal (,',contents-count (,',contents-creator)) 0)
                                   :hints
                                   (("Goal"
                                     :by (:functional-instance
                                          define-hash-table::count-of-creator
                                          (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::key-fixer ,(or ',key-fixer
                                                                             'identity))
                                          (define-hash-table::key-default (lambda () ,default-key))
                                          (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::val-fixer ,(or val-fixer
                                                                             'identity))
                                          (define-hash-table::val-default (lambda () ,default-val))
                                          (define-hash-table::recognizer ,',contents-recognizer)
                                          (define-hash-table::creator ,',contents-creator)
                                          (define-hash-table::fixer ,',contents-fixer)
                                          (define-hash-table::accessor ,',contents-accessor)
                                          (define-hash-table::updater ,',contents-updater)
                                          (define-hash-table::boundp ,',contents-boundp)
                                          (define-hash-table::remover ,',contents-remover)
                                          (define-hash-table::count ,',contents-count)
                                          (define-hash-table::hash-table (lambda () ,',contents))
                                          (define-hash-table::key (lambda () ,',key))
                                          (define-hash-table::val (lambda () ,',val))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',count-of-creator
                               (equal (,',count (,',creator)) 0))))

                    ,@(and ',copyable
                           `((defun ,',keys (,',hash-table)
                               (declare (xargs :guard (,',recognizer ,',hash-table)))
                               (let ((,',hash-table (,',fixer ,',hash-table)))
                                 (car ,',hash-table)))

                             (defun ,',keys-set (set ,',hash-table)
                               (declare (xargs :guard (and (set::setp set)
                                                           (,',recognizer ,',hash-table))))
                               (let ((set (set::sfix set))
                                     (,',hash-table (,',fixer ,',hash-table)))
                                 (cons set (cdr ,',hash-table))))

                             (defthm ,',setp-of-keys
                               (set::setp (,',keys ,',hash-table)))

                             (defthm ,',keys-of-creator
                               (not (,',keys (,',creator))))

                             (defthm ,',keys-of-fixer
                               (equal (,',keys (,',fixer ,',hash-table))
                                      (,',keys ,',hash-table)))

                             (defthmd ,',keys-when-not-recognizer
                               (implies (not (,',recognizer ,',hash-table))
                                        (not (,',keys ,',hash-table))))

                             (defthm ,',keys-of-updater
                               (equal (,',keys (,',updater ,',key ,',val ,',hash-table))
                                      (,',keys ,',hash-table)))

                             (defthm ,',keys-of-remover
                               (equal (,',keys (,',remover ,',key ,',hash-table))
                                      (,',keys ,',hash-table)))

                             (defthm ,',keys-of-keys-set
                               (equal (,',keys (,',keys-set set ,',hash-table))
                                      (set::sfix set)))

                             (defthm ,',recognizer-of-keys-set
                               (,',recognizer (,',keys-set set ,',hash-table)))

                             (defthm ,',keys-set-of-sfix
                               (equal (,',keys-set (set::sfix set) ,',hash-table)
                                      (,',keys-set set ,',hash-table)))

                             (defthm ,',keys-set-of-fixer
                               (equal (,',keys-set set (,',fixer ,',hash-table))
                                      (,',keys-set set ,',hash-table)))

                             (defthm ,',accessor-of-keys-set
                               (equal (,',accessor ,',key (,',keys-set set ,',hash-table))
                                      (,',accessor ,',key ,',hash-table)))

                             (defthm ,',keys-set-of-updater
                               (equal (,',keys-set set (,',updater ,',key ,',val ,',hash-table))
                                      (,',updater ,',key ,',val (,',keys-set set ,',hash-table))))

                             (defthm ,',boundp-of-keys-set
                               (equal (,',boundp ,',key (,',keys-set set ,',hash-table))
                                      (,',boundp ,',key ,',hash-table)))

                             (defthm ,',keys-set-of-remover
                               (equal (,',keys-set set (,',remover ,',key ,',hash-table))
                                      (,',remover ,',key (,',keys-set set ,',hash-table))))

                             (defthm ,',count-of-keys-set
                               (equal (,',count (,',keys-set set ,',hash-table))
                                      (,',count ,',hash-table)))

                             (defthm ,',keys-set-of-keys-set
                               (equal (,',keys-set %set (,',keys-set set ,',hash-table))
                                      (,',keys-set %set ,',hash-table)))

                             (defthmd ,',keys-set-of-keys-free
                               (implies (equal set (,',keys ,',hash-table))
                                        (equal (,',keys-set set ,',hash-table)
                                               (,',fixer ,',hash-table))))

                             (defthm ,',keys-set-of-keys
                               (equal (,',keys-set (,',keys ,',hash-table) ,',hash-table)
                                      (,',fixer ,',hash-table))
                               :hints
                               (("Goal"
                                 :in-theory (e/d (,',keys-set-of-keys-free)
                                                 (,',recognizer
                                                  ,',keys
                                                  ,',keys-set
                                                  ,',fixer)))))))

                    ,(let ((thm `(defthm ,',contents-count-of-contents-updater-when-contents-boundp
                                   (implies (,',contents-boundp ,',key ,',contents)
                                            (equal (,',contents-count (,',contents-updater ,',key ,',val ,',contents))
                                                   (,',contents-count ,',contents)))
                                   :hints
                                   (("Goal"
                                     :by (:functional-instance
                                          define-hash-table::count-of-updater-when-boundp
                                          (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::key-fixer ,(or ',key-fixer
                                                                             'identity))
                                          (define-hash-table::key-default (lambda () ,default-key))
                                          (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::val-fixer ,(or val-fixer
                                                                             'identity))
                                          (define-hash-table::val-default (lambda () ,default-val))
                                          (define-hash-table::recognizer ,',contents-recognizer)
                                          (define-hash-table::creator ,',contents-creator)
                                          (define-hash-table::fixer ,',contents-fixer)
                                          (define-hash-table::accessor ,',contents-accessor)
                                          (define-hash-table::updater ,',contents-updater)
                                          (define-hash-table::boundp ,',contents-boundp)
                                          (define-hash-table::remover ,',contents-remover)
                                          (define-hash-table::count ,',contents-count)
                                          (define-hash-table::hash-table (lambda () ,',contents))
                                          (define-hash-table::key (lambda () ,',key))
                                          (define-hash-table::val (lambda () ,',val))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',count-of-updater-when-boundp
                               (implies (,',boundp ,',key ,',hash-table)
                                        (equal (,',count (,',updater ,',key ,',val ,',hash-table))
                                               (,',count ,',hash-table)))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-count-of-contents-updater-when-contents-boundp)
                                 :use ((:instance ,',contents-count-of-contents-updater-when-contents-boundp
                                                  (,',contents (cdr ,',hash-table)))
                                       (:instance ,',contents-count-of-contents-updater-when-contents-boundp
                                                  (,',contents (cdr ,',hash-table))
                                                  (,',val ,default-val))))))))

                    ,(let ((thm `(defthm ,',contents-count-of-contents-updater-when-not-contents-boundp
                                   (implies (not (,',contents-boundp ,',key ,',contents))
                                            (equal (,',contents-count (,',contents-updater ,',key ,',val ,',contents))
                                                   (1+ (,',contents-count ,',contents))))
                                   :hints
                                   (("Goal"
                                     :by (:functional-instance
                                          define-hash-table::count-of-updater-when-not-boundp
                                          (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::key-fixer ,(or ',key-fixer
                                                                             'identity))
                                          (define-hash-table::key-default (lambda () ,default-key))
                                          (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::val-fixer ,(or val-fixer
                                                                             'identity))
                                          (define-hash-table::val-default (lambda () ,default-val))
                                          (define-hash-table::recognizer ,',contents-recognizer)
                                          (define-hash-table::creator ,',contents-creator)
                                          (define-hash-table::fixer ,',contents-fixer)
                                          (define-hash-table::accessor ,',contents-accessor)
                                          (define-hash-table::updater ,',contents-updater)
                                          (define-hash-table::boundp ,',contents-boundp)
                                          (define-hash-table::remover ,',contents-remover)
                                          (define-hash-table::count ,',contents-count)
                                          (define-hash-table::hash-table (lambda () ,',contents))
                                          (define-hash-table::key (lambda () ,',key))
                                          (define-hash-table::val (lambda () ,',val))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',count-of-updater-when-not-boundp
                               (implies (not (,',boundp ,',key ,',hash-table))
                                        (equal (,',count (,',updater ,',key ,',val ,',hash-table))
                                               (1+ (,',count ,',hash-table))))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-count-of-contents-updater-when-not-contents-boundp)
                                 :use ((:instance ,',contents-count-of-contents-updater-when-not-contents-boundp
                                                  (,',contents (cdr ,',hash-table)))
                                       (:instance ,',contents-count-of-contents-updater-when-not-contents-boundp
                                                  (,',contents (cdr ,',hash-table))
                                                  (,',val ,default-val))))))))

                    (defthmd ,',count-of-updater
                      (equal (,',count (,',updater ,',key ,',val ,',hash-table))
                             (if (,',boundp ,',key ,',hash-table)
                                 (,',count ,',hash-table)
                                 (1+ (,',count ,',hash-table))))
                      :hints
                      (("Goal"
                        :cases ((,',boundp ,',key ,',hash-table))
                        :in-theory (disable ,',contents-count
                                            ,',contents-updater
                                            ,',contents-boundp))))

                    ,(let ((thm `(defthm ,',contents-count-of-contents-remover-when-contents-boundp
                                   (implies (,',contents-boundp ,',key ,',contents)
                                            (equal (,',contents-count (,',contents-remover ,',key ,',contents))
                                                   (1- (,',contents-count ,',contents))))
                                   :hints
                                   (("Goal"
                                     :by (:functional-instance
                                          define-hash-table::count-of-remover-when-boundp
                                          (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::key-fixer ,(or ',key-fixer
                                                                             'identity))
                                          (define-hash-table::key-default (lambda () ,default-key))
                                          (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::val-fixer ,(or val-fixer
                                                                             'identity))
                                          (define-hash-table::val-default (lambda () ,default-val))
                                          (define-hash-table::recognizer ,',contents-recognizer)
                                          (define-hash-table::creator ,',contents-creator)
                                          (define-hash-table::fixer ,',contents-fixer)
                                          (define-hash-table::accessor ,',contents-accessor)
                                          (define-hash-table::updater ,',contents-updater)
                                          (define-hash-table::boundp ,',contents-boundp)
                                          (define-hash-table::remover ,',contents-remover)
                                          (define-hash-table::count ,',contents-count)
                                          (define-hash-table::hash-table (lambda () ,',contents))
                                          (define-hash-table::key (lambda () ,',key))
                                          (define-hash-table::val (lambda () ,',val))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',count-of-remover-when-boundp
                               (implies (,',boundp ,',key ,',hash-table)
                                        (equal (,',count (,',remover ,',key ,',hash-table))
                                               (1- (,',count ,',hash-table))))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-count-of-contents-remover-when-contents-boundp)
                                 :use ((:instance ,',contents-count-of-contents-remover-when-contents-boundp
                                                  (,',contents (cdr ,',hash-table)))))))))

                    ,(let ((thm `(defthm ,',contents-count-of-contents-remover-when-not-contents-boundp
                                   (implies (not (,',contents-boundp ,',key ,',contents))
                                            (equal (,',contents-count (,',contents-remover ,',key ,',contents))
                                                   (,',contents-count ,',contents)))
                                   :hints
                                   (("Goal"
                                     :by (:functional-instance
                                          define-hash-table::count-of-remover-when-not-boundp
                                          (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::key-fixer ,(or ',key-fixer
                                                                             'identity))
                                          (define-hash-table::key-default (lambda () ,default-key))
                                          (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::val-fixer ,(or val-fixer
                                                                             'identity))
                                          (define-hash-table::val-default (lambda () ,default-val))
                                          (define-hash-table::recognizer ,',contents-recognizer)
                                          (define-hash-table::creator ,',contents-creator)
                                          (define-hash-table::fixer ,',contents-fixer)
                                          (define-hash-table::accessor ,',contents-accessor)
                                          (define-hash-table::updater ,',contents-updater)
                                          (define-hash-table::boundp ,',contents-boundp)
                                          (define-hash-table::remover ,',contents-remover)
                                          (define-hash-table::count ,',contents-count)
                                          (define-hash-table::hash-table (lambda () ,',contents))
                                          (define-hash-table::key (lambda () ,',key))
                                          (define-hash-table::val (lambda () ,',val))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',count-of-remover-when-not-boundp
                               (implies (not (,',boundp ,',key ,',hash-table))
                                        (equal (,',count (,',remover ,',key ,',hash-table))
                                               (,',count ,',hash-table)))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-count-of-contents-remover-when-not-contents-boundp)
                                 :use ((:instance ,',contents-count-of-contents-remover-when-not-contents-boundp
                                                  (,',contents (cdr ,',hash-table)))))))))

                    (defthmd ,',count-of-remover
                      (equal (,',count (,',remover ,',key ,',hash-table))
                             (if (,',boundp ,',key ,',hash-table)
                                 (1- (,',count ,',hash-table))
                                 (,',count ,',hash-table)))
                      :hints
                      (("Goal"
                        :cases ((,',boundp ,',key ,',hash-table))
                        :in-theory (disable ,',contents-count
                                            ,',contents-remover
                                            ,',contents-boundp))))

                    ,(let ((thm `(defthm ,',contents-accessor-of-contents-updater-same
                                   (implies ,(if ',key-fixer
                                                 `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                                 `(equal ,',key ,',%key))
                                            (equal (,',contents-accessor ,',key (,',contents-updater ,',%key ,',val ,',contents))
                                                   ,(if val-fixer
                                                        `(,val-fixer ,',val)
                                                        ',val)))
                                   :hints
                                   (("Goal"
                                     :use ((:functional-instance
                                            define-hash-table::accessor-of-updater-same
                                            (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::key-fixer ,(or ',key-fixer
                                                                               'identity))
                                            (define-hash-table::key-default (lambda () ,default-key))
                                            (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::val-fixer ,(or val-fixer
                                                                               'identity))
                                            (define-hash-table::val-default (lambda () ,default-val))
                                            (define-hash-table::recognizer ,',contents-recognizer)
                                            (define-hash-table::creator ,',contents-creator)
                                            (define-hash-table::fixer ,',contents-fixer)
                                            (define-hash-table::accessor ,',contents-accessor)
                                            (define-hash-table::updater ,',contents-updater)
                                            (define-hash-table::boundp ,',contents-boundp)
                                            (define-hash-table::remover ,',contents-remover)
                                            (define-hash-table::count ,',contents-count)
                                            (define-hash-table::hash-table (lambda () ,',contents))
                                            (define-hash-table::key (lambda () ,',key))
                                            (define-hash-table::%key (lambda () ,',%key))
                                            (define-hash-table::val (lambda () ,',val)))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',accessor-of-updater-same
                               (implies ,(if ',key-fixer
                                             `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                             `(equal ,',key ,',%key))
                                        (equal (,',accessor ,',key (,',updater ,',%key ,',val ,',hash-table))
                                               ,(if val-fixer
                                                    `(,val-fixer ,',val)
                                                    ',val)))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-accessor-of-contents-updater-same)
                                 :use ((:instance ,',contents-accessor-of-contents-updater-same
                                                  (,',contents (cdr ,',hash-table)))
                                       (:instance ,',contents-accessor-of-contents-updater-same
                                                  (,',contents (cdr ,',hash-table))
                                                  (,',val ,default-val))))))))

                    ,(let ((thm `(defthm ,',contents-accessor-of-contents-updater-diff
                                   (implies ,(if ',key-fixer
                                                 `(not (equal (,',key-fixer ,',key) (,',key-fixer ,',%key)))
                                                 `(not (equal ,',key ,',%key)))
                                            (equal (,',contents-accessor ,',key (,',contents-updater ,',%key ,',val ,',contents))
                                                   (,',contents-accessor ,',key ,',contents)))
                                   :hints
                                   (("Goal"
                                     :use ((:functional-instance
                                            define-hash-table::accessor-of-updater-diff
                                            (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::key-fixer ,(or ',key-fixer
                                                                               'identity))
                                            (define-hash-table::key-default (lambda () ,default-key))
                                            (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::val-fixer ,(or val-fixer
                                                                               'identity))
                                            (define-hash-table::val-default (lambda () ,default-val))
                                            (define-hash-table::recognizer ,',contents-recognizer)
                                            (define-hash-table::creator ,',contents-creator)
                                            (define-hash-table::fixer ,',contents-fixer)
                                            (define-hash-table::accessor ,',contents-accessor)
                                            (define-hash-table::updater ,',contents-updater)
                                            (define-hash-table::boundp ,',contents-boundp)
                                            (define-hash-table::remover ,',contents-remover)
                                            (define-hash-table::count ,',contents-count)
                                            (define-hash-table::hash-table (lambda () ,',contents))
                                            (define-hash-table::key (lambda () ,',key))
                                            (define-hash-table::%key (lambda () ,',%key))
                                            (define-hash-table::val (lambda () ,',val)))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',accessor-of-updater-diff
                               (implies ,(if ',key-fixer
                                             `(not (equal (,',key-fixer ,',key) (,',key-fixer ,',%key)))
                                             `(not (equal ,',key ,',%key)))
                                        (equal (,',accessor ,',key (,',updater ,',%key ,',val ,',hash-table))
                                               (,',accessor ,',key ,',hash-table)))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-accessor-of-contents-updater-diff)
                                 :use ((:instance ,',contents-accessor-of-contents-updater-diff
                                                  (,',contents (cdr ,',hash-table)))
                                       (:instance ,',contents-accessor-of-contents-updater-diff
                                                  (,',contents (cdr ,',hash-table))
                                                  (,',val ,default-val))))))))

                    (defthmd ,',accessor-of-updater
                      (equal (,',accessor ,',key (,',updater ,',%key ,',val ,',hash-table))
                             (if ,(if ',key-fixer
                                      `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                      `(equal ,',key ,',%key))
                                 ,(if val-fixer
                                      `(,val-fixer ,',val)
                                      ',val)
                                 (,',accessor ,',key ,',hash-table)))
                      :hints
                      (("Goal"
                        :cases (,(if ',key-fixer
                                     `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                     `(equal ,',key ,',%key)))
                        :in-theory (disable ,',contents-accessor
                                            ,',contents-updater))))

                    ,(let ((thm `(defthmd ,',contents-accessor-when-not-contents-boundp
                                   (implies (not (,',contents-boundp ,',key ,',contents))
                                            (equal (,',contents-accessor ,',key ,',contents)
                                                   ,default-val))
                                   :hints
                                   (("Goal"
                                     :by (:functional-instance
                                          define-hash-table::accessor-when-not-boundp
                                          (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::key-fixer ,(or ',key-fixer
                                                                             'identity))
                                          (define-hash-table::key-default (lambda () ,default-key))
                                          (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::val-fixer ,(or val-fixer
                                                                             'identity))
                                          (define-hash-table::val-default (lambda () ,default-val))
                                          (define-hash-table::recognizer ,',contents-recognizer)
                                          (define-hash-table::creator ,',contents-creator)
                                          (define-hash-table::fixer ,',contents-fixer)
                                          (define-hash-table::accessor ,',contents-accessor)
                                          (define-hash-table::updater ,',contents-updater)
                                          (define-hash-table::boundp ,',contents-boundp)
                                          (define-hash-table::remover ,',contents-remover)
                                          (define-hash-table::count ,',contents-count)
                                          (define-hash-table::hash-table (lambda () ,',contents))
                                          (define-hash-table::key (lambda () ,',key))
                                          (define-hash-table::%key (lambda () ,',%key))
                                          (define-hash-table::val (lambda () ,',val))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthmd ,',accessor-when-not-boundp
                               (implies (not (,',boundp ,',key ,',hash-table))
                                        (equal (,',accessor ,',key ,',hash-table)
                                               ,default-val))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-accessor-when-not-contents-boundp)
                                 :use ((:instance ,',contents-accessor-when-not-contents-boundp
                                                  (,',contents (cdr ,',hash-table)))))))))

                    ,(let ((thm `(defthm ,',contents-accessor-of-contents-remover-same
                                   (implies ,(if ',key-fixer
                                                 `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                                 `(equal ,',key ,',%key))
                                            (equal (,',contents-accessor ,',key (,',contents-remover ,',%key ,',contents))
                                                   ,default-val))
                                   :hints
                                   (("Goal"
                                     :use ((:functional-instance
                                            define-hash-table::accessor-of-remover-same
                                            (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::key-fixer ,(or ',key-fixer
                                                                               'identity))
                                            (define-hash-table::key-default (lambda () ,default-key))
                                            (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::val-fixer ,(or val-fixer
                                                                               'identity))
                                            (define-hash-table::val-default (lambda () ,default-val))
                                            (define-hash-table::recognizer ,',contents-recognizer)
                                            (define-hash-table::creator ,',contents-creator)
                                            (define-hash-table::fixer ,',contents-fixer)
                                            (define-hash-table::accessor ,',contents-accessor)
                                            (define-hash-table::updater ,',contents-updater)
                                            (define-hash-table::boundp ,',contents-boundp)
                                            (define-hash-table::remover ,',contents-remover)
                                            (define-hash-table::count ,',contents-count)
                                            (define-hash-table::hash-table (lambda () ,',contents))
                                            (define-hash-table::key (lambda () ,',key))
                                            (define-hash-table::%key (lambda () ,',%key))
                                            (define-hash-table::val (lambda () ,',val)))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',accessor-of-remover-same
                               (implies ,(if ',key-fixer
                                             `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                             `(equal ,',key ,',%key))
                                        (equal (,',accessor ,',key (,',remover ,',%key ,',hash-table))
                                               ,default-val))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-accessor-of-contents-remover-same)
                                 :use ((:instance ,',contents-accessor-of-contents-remover-same
                                                  (,',contents (cdr ,',hash-table)))))))))

                    ,(let ((thm `(defthm ,',contents-accessor-of-contents-remover-diff
                                   (implies ,(if ',key-fixer
                                                 `(not (equal (,',key-fixer ,',key) (,',key-fixer ,',%key)))
                                                 `(not (equal ,',key ,',%key)))
                                            (equal (,',contents-accessor ,',key (,',contents-remover ,',%key ,',contents))
                                                   (,',contents-accessor ,',key ,',contents)))
                                   :hints
                                   (("Goal"
                                     :use ((:functional-instance
                                            define-hash-table::accessor-of-remover-diff
                                            (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::key-fixer ,(or ',key-fixer
                                                                               'identity))
                                            (define-hash-table::key-default (lambda () ,default-key))
                                            (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::val-fixer ,(or val-fixer
                                                                               'identity))
                                            (define-hash-table::val-default (lambda () ,default-val))
                                            (define-hash-table::recognizer ,',contents-recognizer)
                                            (define-hash-table::creator ,',contents-creator)
                                            (define-hash-table::fixer ,',contents-fixer)
                                            (define-hash-table::accessor ,',contents-accessor)
                                            (define-hash-table::updater ,',contents-updater)
                                            (define-hash-table::boundp ,',contents-boundp)
                                            (define-hash-table::remover ,',contents-remover)
                                            (define-hash-table::count ,',contents-count)
                                            (define-hash-table::hash-table (lambda () ,',contents))
                                            (define-hash-table::key (lambda () ,',key))
                                            (define-hash-table::%key (lambda () ,',%key))
                                            (define-hash-table::val (lambda () ,',val)))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',accessor-of-remover-diff
                               (implies ,(if ',key-fixer
                                             `(not (equal (,',key-fixer ,',key) (,',key-fixer ,',%key)))
                                             `(not (equal ,',key ,',%key)))
                                        (equal (,',accessor ,',key (,',remover ,',%key ,',hash-table))
                                               (,',accessor ,',key ,',hash-table)))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-accessor-of-contents-remover-diff)
                                 :use ((:instance ,',contents-accessor-of-contents-remover-diff
                                                  (,',contents (cdr ,',hash-table)))))))))

                    (defthmd ,',accessor-of-remover
                      (equal (,',accessor ,',key (,',remover ,',%key ,',hash-table))
                             (if ,(if ',key-fixer
                                      `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                      `(equal ,',key ,',%key))
                                 ,default-val
                                 (,',accessor ,',key ,',hash-table)))
                      :hints
                      (("Goal"
                        :cases (,(if ',key-fixer
                                     `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                     `(equal ,',key ,',%key)))
                        :in-theory (disable ,',contents-accessor
                                            ,',contents-remover))))

                    ,(let ((thm `(defthm ,',contents-updater-of-contents-accessor-when-contents-boundp
                                   (implies (and ,(if ',key-fixer
                                                      `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                                      `(equal ,',key ,',%key))
                                                 (,',contents-boundp ,',key ,',contents))
                                            (equal (,',contents-updater ,',key (,',contents-accessor ,',%key ,',contents) ,',contents)
                                                   (,',contents-fixer ,',contents)))
                                   :hints
                                   (("Goal"
                                     :use ((:functional-instance
                                            define-hash-table::updater-of-accessor-when-boundp
                                            (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::key-fixer ,(or ',key-fixer
                                                                               'identity))
                                            (define-hash-table::key-default (lambda () ,default-key))
                                            (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::val-fixer ,(or val-fixer
                                                                               'identity))
                                            (define-hash-table::val-default (lambda () ,default-val))
                                            (define-hash-table::recognizer ,',contents-recognizer)
                                            (define-hash-table::creator ,',contents-creator)
                                            (define-hash-table::fixer ,',contents-fixer)
                                            (define-hash-table::accessor ,',contents-accessor)
                                            (define-hash-table::updater ,',contents-updater)
                                            (define-hash-table::boundp ,',contents-boundp)
                                            (define-hash-table::remover ,',contents-remover)
                                            (define-hash-table::count ,',contents-count)
                                            (define-hash-table::hash-table (lambda () ,',contents))
                                            (define-hash-table::key (lambda () ,',key))
                                            (define-hash-table::%key (lambda () ,',%key))
                                            (define-hash-table::val (lambda () ,',val)))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',updater-of-accessor-when-boundp
                               (implies (and ,(if ',key-fixer
                                                  `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                                  `(equal ,',key ,',%key))
                                             (,',boundp ,',key ,',hash-table))
                                        (equal (,',updater ,',key (,',accessor ,',%key ,',hash-table) ,',hash-table)
                                               (,',fixer ,',hash-table)))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-updater-of-contents-accessor-when-contents-boundp)
                                 :use ((:instance ,',contents-updater-of-contents-accessor-when-contents-boundp
                                                  (,',contents (cdr ,',hash-table))))
                                 :expand ((,',contents-updater ,',key
                                                               (,',contents-accessor ,',%key (cdr ,',hash-table))
                                                               (cdr ,',hash-table))
                                          (,',contents-updater ,',%key
                                                               (,',contents-accessor ,',%key (cdr ,',hash-table))
                                                               (cdr ,',hash-table))))))))

                    ,(let ((thm `(defthm ,',contents-updater-of-contents-accessor-when-not-contents-boundp
                                   (implies (and ,(if ',key-fixer
                                                      `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                                      `(equal ,',key ,',%key))
                                                 (not (,',contents-boundp ,',key ,',contents)))
                                            (equal (,',contents-updater ,',key (,',contents-accessor ,',%key ,',contents) ,',contents)
                                                   (,',contents-updater ,',key ,default-val ,',contents)))
                                   :hints
                                   (("Goal"
                                     :use ((:functional-instance
                                            define-hash-table::updater-of-accessor-when-not-boundp
                                            (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::key-fixer ,(or ',key-fixer
                                                                               'identity))
                                            (define-hash-table::key-default (lambda () ,default-key))
                                            (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::val-fixer ,(or val-fixer
                                                                               'identity))
                                            (define-hash-table::val-default (lambda () ,default-val))
                                            (define-hash-table::recognizer ,',contents-recognizer)
                                            (define-hash-table::creator ,',contents-creator)
                                            (define-hash-table::fixer ,',contents-fixer)
                                            (define-hash-table::accessor ,',contents-accessor)
                                            (define-hash-table::updater ,',contents-updater)
                                            (define-hash-table::boundp ,',contents-boundp)
                                            (define-hash-table::remover ,',contents-remover)
                                            (define-hash-table::count ,',contents-count)
                                            (define-hash-table::hash-table (lambda () ,',contents))
                                            (define-hash-table::key (lambda () ,',key))
                                            (define-hash-table::%key (lambda () ,',%key))
                                            (define-hash-table::val (lambda () ,',val)))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',updater-of-accessor-when-not-boundp
                               (implies (and ,(if ',key-fixer
                                                  `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                                  `(equal ,',key ,',%key))
                                             (not (,',boundp ,',key ,',hash-table)))
                                        (equal (,',updater ,',key (,',accessor ,',%key ,',hash-table) ,',hash-table)
                                               (,',updater ,',key ,default-val ,',hash-table)))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-updater-of-contents-accessor-when-not-contents-boundp)
                                 :use ((:instance ,',contents-updater-of-contents-accessor-when-not-contents-boundp
                                                  (,',contents (cdr ,',hash-table))))
                                 :expand ((,',contents-updater ,',key
                                                               (,',contents-accessor ,',%key (cdr ,',hash-table))
                                                               (cdr ,',hash-table))
                                          (,',contents-updater ,',%key
                                                               (,',contents-accessor ,',%key (cdr ,',hash-table))
                                                               (cdr ,',hash-table))))))))

                    (defthmd ,',updater-of-accessor
                      (implies ,(if ',key-fixer
                                    `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                    `(equal ,',key ,',%key))
                               (equal (,',updater ,',key (,',accessor ,',%key ,',hash-table) ,',hash-table)
                                      (if (,',boundp ,',key ,',hash-table)
                                          (,',fixer ,',hash-table)
                                          (,',updater ,',key ,default-val ,',hash-table))))
                      :hints
                      (("Goal"
                        :cases ((,',boundp ,',key ,',hash-table))
                        :in-theory (disable ,',accessor
                                            ,',updater
                                            ,',boundp
                                            ,',fixer
                                            ,',updater-of-accessor-when-not-boundp
                                            ,',updater-of-accessor-when-boundp))
                       ("Subgoal 2"
                        :use ((:instance ,',updater-of-accessor-when-not-boundp)))
                       ("Subgoal 1"
                        :use ((:instance ,',updater-of-accessor-when-boundp)))))

                    ,(let ((thm `(defthm ,',contents-updater-of-contents-updater-same
                                   (implies ,(if ',key-fixer
                                                 `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                                 `(equal ,',key ,',%key))
                                            (equal (,',contents-updater ,',key ,',val (,',contents-updater ,',%key ,',%val ,',contents))
                                                   (,',contents-updater ,',key ,',val ,',contents)))
                                   :hints
                                   (("Goal"
                                     :use ((:functional-instance
                                            define-hash-table::updater-of-updater-same
                                            (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::key-fixer ,(or ',key-fixer
                                                                               'identity))
                                            (define-hash-table::key-default (lambda () ,default-key))
                                            (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::val-fixer ,(or val-fixer
                                                                               'identity))
                                            (define-hash-table::val-default (lambda () ,default-val))
                                            (define-hash-table::recognizer ,',contents-recognizer)
                                            (define-hash-table::creator ,',contents-creator)
                                            (define-hash-table::fixer ,',contents-fixer)
                                            (define-hash-table::accessor ,',contents-accessor)
                                            (define-hash-table::updater ,',contents-updater)
                                            (define-hash-table::boundp ,',contents-boundp)
                                            (define-hash-table::remover ,',contents-remover)
                                            (define-hash-table::count ,',contents-count)
                                            (define-hash-table::hash-table (lambda () ,',contents))
                                            (define-hash-table::key (lambda () ,',key))
                                            (define-hash-table::%key (lambda () ,',%key))
                                            (define-hash-table::val (lambda () ,',val))
                                            (define-hash-table::%val (lambda () ,',%val)))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',updater-of-updater-same
                               (implies ,(if ',key-fixer
                                             `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                             `(equal ,',key ,',%key))
                                        (equal (,',updater ,',key ,',val (,',updater ,',%key ,',%val ,',hash-table))
                                               (,',updater ,',key ,',val ,',hash-table)))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-updater))))))

                    ,(let ((thm `(defthm ,',contents-updater-of-contents-updater-diff
                                   (implies ,(if ',key-fixer
                                                 `(not (equal (,',key-fixer ,',key) (,',key-fixer ,',%key)))
                                                 `(not (equal ,',key ,',%key)))
                                            (equal (,',contents-updater ,',key ,',val (,',contents-updater ,',%key ,',%val ,',contents))
                                                   (,',contents-updater ,',%key ,',%val (,',contents-updater ,',key ,',val ,',contents))))
                                   :rule-classes
                                   ((:rewrite :loop-stopper ((,',key ,',%key ,',contents-updater))))
                                   :hints
                                   (("Goal"
                                     :use ((:functional-instance
                                            define-hash-table::updater-of-updater-diff
                                            (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::key-fixer ,(or ',key-fixer
                                                                               'identity))
                                            (define-hash-table::key-default (lambda () ,default-key))
                                            (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::val-fixer ,(or val-fixer
                                                                               'identity))
                                            (define-hash-table::val-default (lambda () ,default-val))
                                            (define-hash-table::recognizer ,',contents-recognizer)
                                            (define-hash-table::creator ,',contents-creator)
                                            (define-hash-table::fixer ,',contents-fixer)
                                            (define-hash-table::accessor ,',contents-accessor)
                                            (define-hash-table::updater ,',contents-updater)
                                            (define-hash-table::boundp ,',contents-boundp)
                                            (define-hash-table::remover ,',contents-remover)
                                            (define-hash-table::count ,',contents-count)
                                            (define-hash-table::hash-table (lambda () ,',contents))
                                            (define-hash-table::key (lambda () ,',key))
                                            (define-hash-table::%key (lambda () ,',%key))
                                            (define-hash-table::val (lambda () ,',val))
                                            (define-hash-table::%val (lambda () ,',%val)))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',updater-of-updater-diff
                               (implies ,(if ',key-fixer
                                             `(not (equal (,',key-fixer ,',key) (,',key-fixer ,',%key)))
                                             `(not (equal ,',key ,',%key)))
                                        (equal (,',updater ,',key ,',val (,',updater ,',%key ,',%val ,',hash-table))
                                               (,',updater ,',%key ,',%val (,',updater ,',key ,',val ,',hash-table))))
                               :rule-classes
                               ((:rewrite :loop-stopper ((,',key ,',%key ,',updater))))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-updater))))))

                    (defthmd ,',updater-of-updater
                      (equal (,',updater ,',key ,',val (,',updater ,',%key ,',%val ,',hash-table))
                             (if ,(if ',key-fixer
                                      `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                      `(equal ,',key ,',%key))
                                 (,',updater ,',key ,',val ,',hash-table)
                                 (,',updater ,',%key ,',%val (,',updater ,',key ,',val ,',hash-table))))
                      :rule-classes
                      ((:rewrite :loop-stopper ((,',key ,',%key ,',updater))))
                      :hints
                      (("Goal"
                        :cases (,(if ',key-fixer
                                     `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                     `(equal ,',key ,',%key)))
                        :in-theory (disable ,',contents-updater))))

                    ,(let ((thm `(defthm ,',contents-updater-of-contents-remover
                                   (implies ,(if ',key-fixer
                                                 `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                                 `(equal ,',key ,',%key))
                                            (equal (,',contents-updater ,',key ,',val (,',contents-remover ,',%key ,',contents))
                                                   (,',contents-updater ,',key ,',val ,',contents)))
                                   :hints
                                   (("Goal"
                                     :use ((:functional-instance
                                            define-hash-table::updater-of-remover
                                            (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::key-fixer ,(or ',key-fixer
                                                                               'identity))
                                            (define-hash-table::key-default (lambda () ,default-key))
                                            (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::val-fixer ,(or val-fixer
                                                                               'identity))
                                            (define-hash-table::val-default (lambda () ,default-val))
                                            (define-hash-table::recognizer ,',contents-recognizer)
                                            (define-hash-table::creator ,',contents-creator)
                                            (define-hash-table::fixer ,',contents-fixer)
                                            (define-hash-table::accessor ,',contents-accessor)
                                            (define-hash-table::updater ,',contents-updater)
                                            (define-hash-table::boundp ,',contents-boundp)
                                            (define-hash-table::remover ,',contents-remover)
                                            (define-hash-table::count ,',contents-count)
                                            (define-hash-table::hash-table (lambda () ,',contents))
                                            (define-hash-table::key (lambda () ,',key))
                                            (define-hash-table::%key (lambda () ,',%key))
                                            (define-hash-table::val (lambda () ,',val))
                                            (define-hash-table::%val (lambda () ,',%val)))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',updater-of-remover
                               (implies ,(if ',key-fixer
                                             `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                             `(equal ,',key ,',%key))
                                        (equal (,',updater ,',key ,',val (,',remover ,',%key ,',hash-table))
                                               (,',updater ,',key ,',val ,',hash-table)))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-updater
                                                     ,',contents-remover))))))

                    ,(let ((thm `(defthm ,',contents-boundp-of-contents-updater-same
                                   (implies ,(if ',key-fixer
                                                 `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                                 `(equal ,',key ,',%key))
                                            (equal (,',contents-boundp ,',key (,',contents-updater ,',%key ,',val ,',contents))
                                                   t))
                                   :hints
                                   (("Goal"
                                     :use ((:functional-instance
                                            define-hash-table::boundp-of-updater-same
                                            (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::key-fixer ,(or ',key-fixer
                                                                               'identity))
                                            (define-hash-table::key-default (lambda () ,default-key))
                                            (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::val-fixer ,(or val-fixer
                                                                               'identity))
                                            (define-hash-table::val-default (lambda () ,default-val))
                                            (define-hash-table::recognizer ,',contents-recognizer)
                                            (define-hash-table::creator ,',contents-creator)
                                            (define-hash-table::fixer ,',contents-fixer)
                                            (define-hash-table::accessor ,',contents-accessor)
                                            (define-hash-table::updater ,',contents-updater)
                                            (define-hash-table::boundp ,',contents-boundp)
                                            (define-hash-table::remover ,',contents-remover)
                                            (define-hash-table::count ,',contents-count)
                                            (define-hash-table::hash-table (lambda () ,',contents))
                                            (define-hash-table::key (lambda () ,',key))
                                            (define-hash-table::%key (lambda () ,',%key))
                                            (define-hash-table::val (lambda () ,',val))
                                            (define-hash-table::%val (lambda () ,',%val)))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',boundp-of-updater-same
                               (implies ,(if ',key-fixer
                                             `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                             `(equal ,',key ,',%key))
                                        (equal (,',boundp ,',key (,',updater ,',%key ,',val ,',hash-table))
                                               t))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-updater
                                                     ,',contents-boundp))))))

                    ,(let ((thm `(defthm ,',contents-boundp-of-contents-updater-diff
                                   (implies ,(if ',key-fixer
                                                 `(not (equal (,',key-fixer ,',key) (,',key-fixer ,',%key)))
                                                 `(not (equal ,',key ,',%key)))
                                            (equal (,',contents-boundp ,',key (,',contents-updater ,',%key ,',val ,',contents))
                                                   (,',contents-boundp ,',key ,',contents)))
                                   :hints
                                   (("Goal"
                                     :use ((:functional-instance
                                            define-hash-table::boundp-of-updater-diff
                                            (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::key-fixer ,(or ',key-fixer
                                                                               'identity))
                                            (define-hash-table::key-default (lambda () ,default-key))
                                            (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::val-fixer ,(or val-fixer
                                                                               'identity))
                                            (define-hash-table::val-default (lambda () ,default-val))
                                            (define-hash-table::recognizer ,',contents-recognizer)
                                            (define-hash-table::creator ,',contents-creator)
                                            (define-hash-table::fixer ,',contents-fixer)
                                            (define-hash-table::accessor ,',contents-accessor)
                                            (define-hash-table::updater ,',contents-updater)
                                            (define-hash-table::boundp ,',contents-boundp)
                                            (define-hash-table::remover ,',contents-remover)
                                            (define-hash-table::count ,',contents-count)
                                            (define-hash-table::hash-table (lambda () ,',contents))
                                            (define-hash-table::key (lambda () ,',key))
                                            (define-hash-table::%key (lambda () ,',%key))
                                            (define-hash-table::val (lambda () ,',val))
                                            (define-hash-table::%val (lambda () ,',%val)))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',boundp-of-updater-diff
                               (implies ,(if ',key-fixer
                                             `(not (equal (,',key-fixer ,',key) (,',key-fixer ,',%key)))
                                             `(not (equal ,',key ,',%key)))
                                        (equal (,',boundp ,',key (,',updater ,',%key ,',val ,',hash-table))
                                               (,',boundp ,',key ,',hash-table)))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-updater
                                                     ,',contents-boundp))))))

                    (defthmd ,',boundp-of-updater
                      (equal (,',boundp ,',key (,',updater ,',%key ,',val ,',hash-table))
                             (or ,(if ',key-fixer
                                      `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                      `(equal ,',key ,',%key))
                                 (,',boundp ,',key ,',hash-table)))
                      :hints
                      (("Goal"
                        :cases (,(if ',key-fixer
                                     `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                     `(equal ,',key ,',%key)))
                        :in-theory (disable ,',contents-updater
                                            ,',contents-boundp))))

                    ,(let ((thm `(defthm ,',contents-boundp-of-contents-remover-same
                                   (implies ,(if ',key-fixer
                                                 `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                                 `(equal ,',key ,',%key))
                                            (not (,',contents-boundp ,',key (,',contents-remover ,',%key ,',contents))))
                                   :hints
                                   (("Goal"
                                     :use ((:functional-instance
                                            define-hash-table::boundp-of-remover-same
                                            (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::key-fixer ,(or ',key-fixer
                                                                               'identity))
                                            (define-hash-table::key-default (lambda () ,default-key))
                                            (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::val-fixer ,(or val-fixer
                                                                               'identity))
                                            (define-hash-table::val-default (lambda () ,default-val))
                                            (define-hash-table::recognizer ,',contents-recognizer)
                                            (define-hash-table::creator ,',contents-creator)
                                            (define-hash-table::fixer ,',contents-fixer)
                                            (define-hash-table::accessor ,',contents-accessor)
                                            (define-hash-table::updater ,',contents-updater)
                                            (define-hash-table::boundp ,',contents-boundp)
                                            (define-hash-table::remover ,',contents-remover)
                                            (define-hash-table::count ,',contents-count)
                                            (define-hash-table::hash-table (lambda () ,',contents))
                                            (define-hash-table::key (lambda () ,',key))
                                            (define-hash-table::%key (lambda () ,',%key))
                                            (define-hash-table::val (lambda () ,',val))
                                            (define-hash-table::%val (lambda () ,',%val)))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',boundp-of-remover-same
                               (implies ,(if ',key-fixer
                                             `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                             `(equal ,',key ,',%key))
                                        (not (,',boundp ,',key (,',remover ,',%key ,',hash-table))))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-boundp
                                                     ,',contents-remover))))))

                    ,(let ((thm `(defthm ,',contents-boundp-of-contents-remover-diff
                                   (implies ,(if ',key-fixer
                                                 `(not (equal (,',key-fixer ,',key) (,',key-fixer ,',%key)))
                                                 `(not (equal ,',key ,',%key)))
                                            (equal (,',contents-boundp ,',key (,',contents-remover ,',%key ,',contents))
                                                   (,',contents-boundp ,',key ,',contents)))
                                   :hints
                                   (("Goal"
                                     :use ((:functional-instance
                                            define-hash-table::boundp-of-remover-diff
                                            (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::key-fixer ,(or ',key-fixer
                                                                               'identity))
                                            (define-hash-table::key-default (lambda () ,default-key))
                                            (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::val-fixer ,(or val-fixer
                                                                               'identity))
                                            (define-hash-table::val-default (lambda () ,default-val))
                                            (define-hash-table::recognizer ,',contents-recognizer)
                                            (define-hash-table::creator ,',contents-creator)
                                            (define-hash-table::fixer ,',contents-fixer)
                                            (define-hash-table::accessor ,',contents-accessor)
                                            (define-hash-table::updater ,',contents-updater)
                                            (define-hash-table::boundp ,',contents-boundp)
                                            (define-hash-table::remover ,',contents-remover)
                                            (define-hash-table::count ,',contents-count)
                                            (define-hash-table::hash-table (lambda () ,',contents))
                                            (define-hash-table::key (lambda () ,',key))
                                            (define-hash-table::%key (lambda () ,',%key))
                                            (define-hash-table::val (lambda () ,',val))
                                            (define-hash-table::%val (lambda () ,',%val)))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',boundp-of-remover-diff
                               (implies ,(if ',key-fixer
                                             `(not (equal (,',key-fixer ,',key) (,',key-fixer ,',%key)))
                                             `(not (equal ,',key ,',%key)))
                                        (equal (,',boundp ,',key (,',remover ,',%key ,',hash-table))
                                               (,',boundp ,',key ,',hash-table)))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-boundp
                                                     ,',contents-remover))))))

                    (defthmd ,',boundp-of-remover
                      (equal (,',boundp ,',key (,',remover ,',%key ,',hash-table))
                             (and (not ,(if ',key-fixer
                                            `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                            `(equal ,',key ,',%key)))
                                  (,',boundp ,',key ,',hash-table)))
                      :hints
                      (("Goal"
                        :cases (,(if ',key-fixer
                                     `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                     `(equal ,',key ,',%key)))
                        :in-theory (disable ,',contents-boundp
                                            ,',contents-remover))))

                    ,(let ((thm `(defthmd ,',contents-boundp-when-zp-contents-count
                                   (implies (zp (,',contents-count ,',contents))
                                            (not (,',contents-boundp ,',key ,',contents)))
                                   :hints
                                   (("Goal"
                                     :use ((:functional-instance
                                            define-hash-table::boundp-when-zp-count
                                            (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::key-fixer ,(or ',key-fixer
                                                                               'identity))
                                            (define-hash-table::key-default (lambda () ,default-key))
                                            (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::val-fixer ,(or val-fixer
                                                                               'identity))
                                            (define-hash-table::val-default (lambda () ,default-val))
                                            (define-hash-table::recognizer ,',contents-recognizer)
                                            (define-hash-table::creator ,',contents-creator)
                                            (define-hash-table::fixer ,',contents-fixer)
                                            (define-hash-table::accessor ,',contents-accessor)
                                            (define-hash-table::updater ,',contents-updater)
                                            (define-hash-table::boundp ,',contents-boundp)
                                            (define-hash-table::remover ,',contents-remover)
                                            (define-hash-table::count ,',contents-count)
                                            (define-hash-table::hash-table (lambda () ,',contents))
                                            (define-hash-table::key (lambda () ,',key))
                                            (define-hash-table::%key (lambda () ,',%key))
                                            (define-hash-table::val (lambda () ,',val))
                                            (define-hash-table::%val (lambda () ,',%val)))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthmd ,',boundp-when-zp-count
                               (implies (zp (,',count ,',hash-table))
                                        (not (,',boundp ,',key ,',hash-table)))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-count
                                                     ,',contents-boundp
                                                     ,',fixer)
                                 :use ((:instance ,',contents-boundp-when-zp-contents-count
                                                  (,',contents (cdr (,',fixer ,',hash-table))))))))))

                    ,(let ((thm `(defthm ,',contents-remover-of-contents-updater-same
                                   (implies ,(if ',key-fixer
                                                 `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                                 `(equal ,',key ,',%key))
                                            (equal (,',contents-remover ,',key (,',contents-updater ,',%key ,',val ,',contents))
                                                   (,',contents-remover ,',key ,',contents)))
                                   :hints
                                   (("Goal"
                                     :use ((:functional-instance
                                            define-hash-table::remover-of-updater-same
                                            (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::key-fixer ,(or ',key-fixer
                                                                               'identity))
                                            (define-hash-table::key-default (lambda () ,default-key))
                                            (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::val-fixer ,(or val-fixer
                                                                               'identity))
                                            (define-hash-table::val-default (lambda () ,default-val))
                                            (define-hash-table::recognizer ,',contents-recognizer)
                                            (define-hash-table::creator ,',contents-creator)
                                            (define-hash-table::fixer ,',contents-fixer)
                                            (define-hash-table::accessor ,',contents-accessor)
                                            (define-hash-table::updater ,',contents-updater)
                                            (define-hash-table::boundp ,',contents-boundp)
                                            (define-hash-table::remover ,',contents-remover)
                                            (define-hash-table::count ,',contents-count)
                                            (define-hash-table::hash-table (lambda () ,',contents))
                                            (define-hash-table::key (lambda () ,',key))
                                            (define-hash-table::%key (lambda () ,',%key))
                                            (define-hash-table::val (lambda () ,',val))
                                            (define-hash-table::%val (lambda () ,',%val)))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',remover-of-updater-same
                               (implies ,(if ',key-fixer
                                             `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                             `(equal ,',key ,',%key))
                                        (equal (,',remover ,',key (,',updater ,',%key ,',val ,',hash-table))
                                               (,',remover ,',key ,',hash-table)))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-updater
                                                     ,',contents-remover))))))

                    ,(let ((thm `(defthm ,',contents-remover-of-contents-updater-diff
                                   (implies ,(if ',key-fixer
                                                 `(not (equal (,',key-fixer ,',key) (,',key-fixer ,',%key)))
                                                 `(not (equal ,',key ,',%key)))
                                            (equal (,',contents-remover ,',key (,',contents-updater ,',%key ,',val ,',contents))
                                                   (,',contents-updater ,',%key ,',val (,',contents-remover ,',key ,',contents))))
                                   :hints
                                   (("Goal"
                                     :use ((:functional-instance
                                            define-hash-table::remover-of-updater-diff
                                            (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::key-fixer ,(or ',key-fixer
                                                                               'identity))
                                            (define-hash-table::key-default (lambda () ,default-key))
                                            (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::val-fixer ,(or val-fixer
                                                                               'identity))
                                            (define-hash-table::val-default (lambda () ,default-val))
                                            (define-hash-table::recognizer ,',contents-recognizer)
                                            (define-hash-table::creator ,',contents-creator)
                                            (define-hash-table::fixer ,',contents-fixer)
                                            (define-hash-table::accessor ,',contents-accessor)
                                            (define-hash-table::updater ,',contents-updater)
                                            (define-hash-table::boundp ,',contents-boundp)
                                            (define-hash-table::remover ,',contents-remover)
                                            (define-hash-table::count ,',contents-count)
                                            (define-hash-table::hash-table (lambda () ,',contents))
                                            (define-hash-table::key (lambda () ,',key))
                                            (define-hash-table::%key (lambda () ,',%key))
                                            (define-hash-table::val (lambda () ,',val))
                                            (define-hash-table::%val (lambda () ,',%val)))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',remover-of-updater-diff
                               (implies ,(if ',key-fixer
                                             `(not (equal (,',key-fixer ,',key) (,',key-fixer ,',%key)))
                                             `(not (equal ,',key ,',%key)))
                                        (equal (,',remover ,',key (,',updater ,',%key ,',val ,',hash-table))
                                               (,',updater ,',%key ,',val (,',remover ,',key ,',hash-table))))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-updater
                                                     ,',contents-remover))))))

                    (defthmd ,',remover-of-updater
                      (equal (,',remover ,',key (,',updater ,',%key ,',val ,',hash-table))
                             (if ,(if ',key-fixer
                                      `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                      `(equal ,',key ,',%key))
                                 (,',remover ,',key ,',hash-table)
                                 (,',updater ,',%key ,',val (,',remover ,',key ,',hash-table))))
                      :hints
                      (("Goal"
                        :cases (,(if ',key-fixer
                                     `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                     `(equal ,',key ,',%key)))
                        :in-theory (disable ,',contents-updater
                                            ,',contents-remover))))

                    ,(let ((thm `(defthmd ,',contents-remover-when-not-contents-boundp
                                   (implies (not (,',contents-boundp ,',key ,',contents))
                                            (equal (,',contents-remover ,',key ,',contents)
                                                   (,',contents-fixer ,',contents)))
                                   :hints
                                   (("Goal"
                                     :by (:functional-instance
                                          define-hash-table::remover-when-not-boundp
                                          (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::key-fixer ,(or ',key-fixer
                                                                             'identity))
                                          (define-hash-table::key-default (lambda () ,default-key))
                                          (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::val-fixer ,(or val-fixer
                                                                             'identity))
                                          (define-hash-table::val-default (lambda () ,default-val))
                                          (define-hash-table::recognizer ,',contents-recognizer)
                                          (define-hash-table::creator ,',contents-creator)
                                          (define-hash-table::fixer ,',contents-fixer)
                                          (define-hash-table::accessor ,',contents-accessor)
                                          (define-hash-table::updater ,',contents-updater)
                                          (define-hash-table::boundp ,',contents-boundp)
                                          (define-hash-table::remover ,',contents-remover)
                                          (define-hash-table::count ,',contents-count)
                                          (define-hash-table::hash-table (lambda () ,',contents))
                                          (define-hash-table::key (lambda () ,',key))
                                          (define-hash-table::%key (lambda () ,',%key))
                                          (define-hash-table::val (lambda () ,',val))
                                          (define-hash-table::%val (lambda () ,',%val))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthmd ,',remover-when-not-boundp
                               (implies (not (,',boundp ,',key ,',hash-table))
                                        (equal (,',remover ,',key ,',hash-table)
                                               (,',fixer ,',hash-table)))
                               :hints
                               (("Goal"
                                 :in-theory (e/d (,',contents-remover-when-not-contents-boundp)
                                                 (,',contents-boundp
                                                  ,',contents-remover)))))))

                    ,(let ((thm `(defthm ,',contents-remover-of-contents-remover-same
                                   (implies ,(if ',key-fixer
                                                 `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                                 `(equal ,',key ,',%key))
                                            (equal (,',contents-remover ,',key (,',contents-remover ,',%key ,',contents))
                                                   (,',contents-remover ,',key ,',contents)))
                                   :hints
                                   (("Goal"
                                     :use ((:functional-instance
                                            define-hash-table::remover-of-remover-same
                                            (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::key-fixer ,(or ',key-fixer
                                                                               'identity))
                                            (define-hash-table::key-default (lambda () ,default-key))
                                            (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::val-fixer ,(or val-fixer
                                                                               'identity))
                                            (define-hash-table::val-default (lambda () ,default-val))
                                            (define-hash-table::recognizer ,',contents-recognizer)
                                            (define-hash-table::creator ,',contents-creator)
                                            (define-hash-table::fixer ,',contents-fixer)
                                            (define-hash-table::accessor ,',contents-accessor)
                                            (define-hash-table::updater ,',contents-updater)
                                            (define-hash-table::boundp ,',contents-boundp)
                                            (define-hash-table::remover ,',contents-remover)
                                            (define-hash-table::count ,',contents-count)
                                            (define-hash-table::hash-table (lambda () ,',contents))
                                            (define-hash-table::key (lambda () ,',key))
                                            (define-hash-table::%key (lambda () ,',%key))
                                            (define-hash-table::val (lambda () ,',val))
                                            (define-hash-table::%val (lambda () ,',%val)))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',remover-of-remover-same
                               (implies ,(if ',key-fixer
                                             `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                             `(equal ,',key ,',%key))
                                        (equal (,',remover ,',key (,',remover ,',%key ,',hash-table))
                                               (,',remover ,',key ,',hash-table)))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-remover))))))

                    ,(let ((thm `(defthm ,',contents-remover-of-contents-remover-diff
                                   (implies ,(if ',key-fixer
                                                 `(not (equal (,',key-fixer ,',key) (,',key-fixer ,',%key)))
                                                 `(not (equal ,',key ,',%key)))
                                            (equal (,',contents-remover ,',key (,',contents-remover ,',%key ,',contents))
                                                   (,',contents-remover ,',%key (,',contents-remover ,',key ,',contents))))
                                   :rule-classes
                                   ((:rewrite :loop-stopper ((,',key ,',%key ,',contents-remover))))
                                   :hints
                                   (("Goal"
                                     :use ((:functional-instance
                                            define-hash-table::remover-of-remover-diff
                                            (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::key-fixer ,(or ',key-fixer
                                                                               'identity))
                                            (define-hash-table::key-default (lambda () ,default-key))
                                            (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                    '(lambda (x) t)))
                                            (define-hash-table::val-fixer ,(or val-fixer
                                                                               'identity))
                                            (define-hash-table::val-default (lambda () ,default-val))
                                            (define-hash-table::recognizer ,',contents-recognizer)
                                            (define-hash-table::creator ,',contents-creator)
                                            (define-hash-table::fixer ,',contents-fixer)
                                            (define-hash-table::accessor ,',contents-accessor)
                                            (define-hash-table::updater ,',contents-updater)
                                            (define-hash-table::boundp ,',contents-boundp)
                                            (define-hash-table::remover ,',contents-remover)
                                            (define-hash-table::count ,',contents-count)
                                            (define-hash-table::hash-table (lambda () ,',contents))
                                            (define-hash-table::key (lambda () ,',key))
                                            (define-hash-table::%key (lambda () ,',%key))
                                            (define-hash-table::val (lambda () ,',val))
                                            (define-hash-table::%val (lambda () ,',%val)))))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',remover-of-remover-diff
                               (implies ,(if ',key-fixer
                                             `(not (equal (,',key-fixer ,',key) (,',key-fixer ,',%key)))
                                             `(not (equal ,',key ,',%key)))
                                        (equal (,',remover ,',key (,',remover ,',%key ,',hash-table))
                                               (,',remover ,',%key (,',remover ,',key ,',hash-table))))
                               :rule-classes
                               ((:rewrite :loop-stopper ((,',key ,',%key ,',remover))))
                               :hints
                               (("Goal"
                                 :in-theory (disable ,',contents-remover))))))

                    (defthmd ,',remover-of-remover
                      (equal (,',remover ,',key (,',remover ,',%key ,',hash-table))
                             (if ,(if ',key-fixer
                                      `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                      `(equal ,',key ,',%key))
                                 (,',remover ,',key ,',hash-table)
                                 (,',remover ,',%key (,',remover ,',key ,',hash-table))))
                      :rule-classes
                      ((:rewrite :loop-stopper ((,',key ,',%key ,',remover))))
                      :hints
                      (("Goal"
                        :cases (,(if ',key-fixer
                                     `(equal (,',key-fixer ,',key) (,',key-fixer ,',%key))
                                     `(equal ,',key ,',%key)))
                        :in-theory (disable ,',contents-remover))))

                    (defun-sk ,',contents-keys-equal (,',%contents ,',contents)
                      (declare (xargs :guard (and (,',contents-recognizer ,',%contents)
                                                  (,',contents-recognizer ,',contents))
                                      :verify-guards nil))
                      (forall ,',key
                        ,(if ',key-recognizer
                             `(implies (,',key-recognizer ,',key)
                                       (equal (,',contents-boundp ,',key ,',%contents)
                                              (,',contents-boundp ,',key ,',contents)))
                             `(equal (,',contents-boundp ,',key ,',%contents)
                                     (,',contents-boundp ,',key ,',contents))))
                      :rewrite :direct)

                    (local
                      ,(let ((witness `(,',contents-keys-equal-witness ,',%contents
                                                                       ,',contents)))
                         `(defthm ,',contents-keys-equal-lemma-0
                            (implies ,(if ',key-recognizer
                                          `(and (,',key-recognizer ,witness)
                                                (equal (,',contents-boundp ,witness ,',%contents)
                                                       (,',contents-boundp ,witness ,',contents)))
                                          `(equal (,',contents-boundp ,witness ,',%contents)
                                                  (,',contents-boundp ,witness ,',contents)))
                                     (,',contents-keys-equal ,',%contents ,',contents)))))

                    ,@(and ',key-recognizer
                           (let ((witness `(,',contents-keys-equal-witness ,',%contents
                                                                           ,',contents)))
                             `((local
                                 (defthm ,',contents-keys-equal-lemma-1
                                   (implies (not (,',key-recognizer ,witness))
                                            (,',contents-keys-equal ,',%contents ,',contents)))))))

                    ,@(and ',copyable
                           `((defun-sk ,',keys-equal (,',%hash-table ,',hash-table)
                               (declare (xargs :guard (and (,',recognizer ,',%hash-table)
                                                           (,',recognizer ,',hash-table))
                                               :verify-guards nil))
                               (forall ,',key
                                 ,(if ',key-recognizer
                                      `(implies (,',key-recognizer ,',key)
                                                (equal (,',boundp ,',key ,',%hash-table)
                                                       (,',boundp ,',key ,',hash-table)))
                                      `(equal (,',boundp ,',key ,',%hash-table)
                                              (,',boundp ,',key ,',hash-table))))
                               :rewrite :direct)

                             (local
                               (defthm ,',keys-equal-implies-contents-keys-equal
                                 (implies (and (set::setp (car ,',hash-table))
                                               (set::setp (car ,',%hash-table)))
                                          (implies (,',keys-equal ,',%hash-table ,',hash-table)
                                                   (,',contents-keys-equal (cdr ,',%hash-table) (cdr ,',hash-table))))
                                 :hints
                                 (("Goal"
                                   :do-not-induct t
                                   :cases ((,',recognizer ,',%hash-table)
                                           (,',recognizer ,',hash-table))
                                   :in-theory (disable ,',keys-equal
                                                       ,',keys-equal-necc))
                                  ("Subgoal 2"
                                   :use ((:instance ,',keys-equal-necc
                                                    (,',key (,',contents-keys-equal-witness
                                                             (cdr ,',%hash-table)
                                                             (cdr ,',hash-table))))))
                                  ("Subgoal 1"
                                   :use ((:instance ,',keys-equal-necc
                                                    (,',key (,',contents-keys-equal-witness
                                                             (cdr ,',%hash-table)
                                                             (cdr ,',hash-table)))))))))))

                    (defun-sk ,',contents-vals-equal (,',%contents ,',contents)
                      (declare (xargs :guard (and (,',contents-recognizer ,',%contents)
                                                  (,',contents-recognizer ,',contents))
                                      :verify-guards nil))
                      (forall ,',key
                        ,(if ',key-recognizer
                             `(implies (,',key-recognizer ,',key)
                                       (equal (,',contents-accessor ,',key ,',%contents)
                                              (,',contents-accessor ,',key ,',contents)))
                             `(equal (,',contents-accessor ,',key ,',%contents)
                                     (,',contents-accessor ,',key ,',contents))))
                      :rewrite :direct)

                    ,@(and ',copyable
                           `((defun-sk ,',vals-equal (,',%hash-table ,',hash-table)
                               (declare (xargs :guard (and (,',recognizer ,',%hash-table)
                                                           (,',recognizer ,',hash-table))
                                               :verify-guards nil))
                               (forall ,',key
                                 ,(if ',key-recognizer
                                      `(implies (,',key-recognizer ,',key)
                                                (equal (,',accessor ,',key ,',%hash-table)
                                                       (,',accessor ,',key ,',hash-table)))
                                      `(equal (,',accessor ,',key ,',%hash-table)
                                              (,',accessor ,',key ,',hash-table))))
                               :rewrite :direct)

                             (local
                               (defthm ,',vals-equal-implies-contents-vals-equal
                                 (implies (and (set::setp (car ,',hash-table))
                                               (set::setp (car ,',%hash-table)))
                                          (implies (,',vals-equal ,',%hash-table ,',hash-table)
                                                   (,',contents-vals-equal (cdr ,',%hash-table) (cdr ,',hash-table))))
                                 :hints
                                 (("Goal"
                                   :do-not-induct t
                                   :cases ((,',recognizer ,',%hash-table)
                                           (,',recognizer ,',hash-table))
                                   :in-theory (disable ,',vals-equal
                                                       ,',vals-equal-necc))
                                  ("Subgoal 2"
                                   :use ((:instance ,',vals-equal-necc
                                                    (,',key (,',contents-vals-equal-witness
                                                             (cdr ,',%hash-table)
                                                             (cdr ,',hash-table))))))
                                  ("Subgoal 1"
                                   :use ((:instance ,',vals-equal-necc
                                                    (,',key (,',contents-vals-equal-witness
                                                             (cdr ,',%hash-table)
                                                             (cdr ,',hash-table)))))))))))

                    (local
                      ,(let ((witness `(,',contents-vals-equal-witness ,',%contents
                                                                       ,',contents)))
                         `(defthm ,',contents-vals-equal-lemma-0
                            (implies ,(if ',key-recognizer
                                          `(and (,',key-recognizer ,witness)
                                                (equal (,',contents-accessor ,witness ,',%contents)
                                                       (,',contents-accessor ,witness ,',contents)))
                                          `(equal (,',contents-accessor ,witness ,',%contents)
                                                  (,',contents-accessor ,witness ,',contents)))
                                     (,',contents-vals-equal ,',%contents ,',contents)))))

                    ,@(and ',key-recognizer
                           (let ((witness `(,',contents-vals-equal-witness ,',%contents
                                                                           ,',contents)))
                             `((local
                                 (defthm ,',contents-vals-equal-lemma-1
                                   (implies (not (,',key-recognizer ,witness))
                                            (,',contents-vals-equal ,',%contents ,',contents)))))))

                    (defun-nx ,',contents-equal (,',%contents ,',contents)
                      (declare (xargs :guard t
                                      :verify-guards nil))
                      (and (,',contents-recognizer ,',%contents)
                           (,',contents-recognizer ,',contents)
                           (= (,',contents-count ,',%contents)
                              (,',contents-count ,',contents))
                           (,',contents-keys-equal ,',%contents ,',contents)
                           (,',contents-vals-equal ,',%contents ,',contents)))

                    ,@(and ',copyable
                           `((defun-nx ,',hash-table-equal (,',%hash-table ,',hash-table)
                               (declare (xargs :guard t
                                               :verify-guards nil))
                               (and (,',recognizer ,',%hash-table)
                                    (,',recognizer ,',hash-table)
                                    (equal (,',keys ,',%hash-table) (,',keys ,',hash-table))
                                    (= (,',count ,',%hash-table) (,',count ,',hash-table))
                                    (,',keys-equal ,',%hash-table ,',hash-table)
                                    (,',vals-equal ,',%hash-table ,',hash-table)))))

                    ,(let ((thm `(defthm ,',contents-equal{forward-chaining}
                                   (implies (,',contents-equal ,',%contents ,',contents)
                                            (equal ,',%contents ,',contents))
                                   :rule-classes
                                   ((:forward-chaining :trigger-terms
                                                       ((,',contents-equal ,',%contents ,',contents))
                                                       :corollary
                                                       (implies t
                                                                (implies (,',contents-equal ,',%contents ,',contents)
                                                                         (equal ,',%contents ,',contents)))))
                                   :hints
                                   (("Goal"
                                     :in-theory (disable ,',contents-keys-equal
                                                         ,',contents-vals-equal)
                                     :by (:functional-instance
                                          define-hash-table::hash-table-equal{forward-chaining}
                                          (define-hash-table::key-recognizer ,(or ',key-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::key-fixer ,(or ',key-fixer
                                                                             'identity))
                                          (define-hash-table::key-default (lambda () ,default-key))
                                          (define-hash-table::val-recognizer ,(or val-recognizer
                                                                                  '(lambda (x) t)))
                                          (define-hash-table::val-fixer ,(or val-fixer
                                                                             'identity))
                                          (define-hash-table::val-default (lambda () ,default-val))
                                          (define-hash-table::recognizer ,',contents-recognizer)
                                          (define-hash-table::creator ,',contents-creator)
                                          (define-hash-table::fixer ,',contents-fixer)
                                          (define-hash-table::accessor ,',contents-accessor)
                                          (define-hash-table::updater ,',contents-updater)
                                          (define-hash-table::boundp ,',contents-boundp)
                                          (define-hash-table::remover ,',contents-remover)
                                          (define-hash-table::count ,',contents-count)
                                          (define-hash-table::hash-table (lambda () ,',contents))
                                          (define-hash-table::%hash-table (lambda () ,',%contents))
                                          (define-hash-table::key (lambda () ,',key))
                                          (define-hash-table::%key (lambda () ,',%key))
                                          (define-hash-table::val (lambda () ,',val))
                                          (define-hash-table::%val (lambda () ,',%val))
                                          (define-hash-table::hash-table-keys-equal ,',contents-keys-equal)
                                          (define-hash-table::hash-table-keys-equal-witness ,',contents-keys-equal-witness)
                                          (define-hash-table::hash-table-vals-equal ,',contents-vals-equal)
                                          (define-hash-table::hash-table-vals-equal-witness ,',contents-vals-equal-witness)
                                          (define-hash-table::hash-table-equal ,',contents-equal)))))))
                       (if ',copyable
                           `(local ,thm)
                           thm))

                    ,@(and ',copyable
                           `((defthm ,',hash-table-equal{forward-chaining}
                               (implies (,',hash-table-equal ,',%hash-table ,',hash-table)
                                        (equal ,',%hash-table ,',hash-table))
                               :rule-classes
                               ((:forward-chaining :trigger-terms
                                                   ((,',hash-table-equal ,',%hash-table ,',hash-table))
                                                   :corollary
                                                   (implies t
                                                            (implies (,',hash-table-equal ,',%hash-table ,',hash-table)
                                                                     (equal ,',%hash-table ,',hash-table)))))
                               :hints
                               (("Goal"
                                 :do-not-induct t
                                 :in-theory (disable ,',contents-keys-equal
                                                     ,',contents-vals-equal
                                                     ,',contents-equal
                                                     ,',keys-equal
                                                     ,',vals-equal)
                                 :use ((:instance ,',contents-equal
                                                  (,',%contents (cdr ,',%hash-table))
                                                  (,',contents (cdr ,',hash-table)))))))))))

                (stobj$a-property `(stobj$a-property (,',recognizer
                                                      ,',creator
                                                      ,',fixer
                                                      ,',hash-table-equal)
                                                     ((,',key-recognizer
                                                       ,',key-fixer
                                                       ,',key
                                                       ,',default-key-name)
                                                      (,',val-recognizer
                                                       ,',val-fixer
                                                       ,',val
                                                       ,(and (not val-type-is-stobj)
                                                             ',default-val-name))
                                                      (,',test
                                                       ,',copyable)
                                                      (,',accessor
                                                       ,',updater
                                                       ,',boundp
                                                       ,',getp
                                                       ,',remover
                                                       ,',count
                                                       ,',clear
                                                       ,',init
                                                       ,(and ',copyable
                                                             ',keys)
                                                       ,(and ',copyable
                                                             ',keys-set))))))

           `(progn
              ,@prologue

              ,body

              ,@epilogue

              (table stobj$a
                     'stobj$a-property-alist
                     (putprop ',',hash-table
                              'stobj$a
                              ',stobj$a-property
                              (stobj$a-property-alist world)))))))))
