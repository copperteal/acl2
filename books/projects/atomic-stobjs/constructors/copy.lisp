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

(include-book "std/osets/top" :dir :system) ; TODO: remove?

(include-book "../utilities/top")

(deflabel stobj-copy-begin)


;;;; `DEFINE-STOBJ-COPIER'
(make-event
  `(progn
     (table stobj-copier nil nil :guard (and (member key '(stobj-copier-alist
                                                           stobj-coupled-alist))
                                             (plist-worldp val)))
     (table stobj-copier 'stobj-copier-alist '())
     (table stobj-copier 'stobj-coupled-alist '())))

(defun stobj-copier-alist (world)
  (declare (xargs :guard (plist-worldp world)
                  :verify-guards nil))
  (cdr (assoc-eq 'stobj-copier-alist
                 (table-alist 'stobj-copier world))))

(defmacro stobj-copier (stobj)
  (declare (xargs :guard t))
  `(getprop ,stobj
            'copier
            nil
            'current-acl2-world
            (stobj-copier-alist (w state))))

(defmacro stobj-copier{rewrite} (stobj)
  (declare (xargs :guard t))
  `(getprop ,stobj
            'copier{rewrite}
            nil
            'current-acl2-world
            (stobj-copier-alist (w state))))

(defun stobj-coupled-alist (world)
  (declare (xargs :guard (plist-worldp world)
                  :verify-guards nil))
  (cdr (assoc-eq 'stobj-coupled-alist
                 (table-alist 'stobj-copier world))))

(defmacro stobj-coupled (stobj)
  (declare (xargs :guard t))
  `(getprop ,stobj
            'coupled
            nil
            'current-acl2-world
            (stobj-coupled-alist (w state))))

(defun make-vector-copy-events (stobj$a %stobj stobj state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp stobj$a)
                              (symbolp %stobj)
                              (symbolp stobj))
                  :verify-guards nil))
  (let* ((copier (symbolicate stobj stobj '-copy))
         (copier{rewrite} (symbolicate stobj copier '{rewrite}))
         (copier-rec (symbolicate stobj copier '-rec))

         (coupled (symbolicate stobj stobj '-coupled))
         (witness (symbolicate stobj coupled '-witness))

         (recognizer (stobj-recognizer stobj))
         (exports (stobj$abs-exports stobj))
         (fixer (car (first exports)))
         (length (car (second exports)))
         (resizer (car (third exports)))
         (accessor (car (fourth exports)))
         (%accessor (symbolicate stobj '% accessor))
         (updater (car (fifth exports)))
         (%updater (symbolicate stobj '% updater))

         (stobj$a-aggressive (symbolicate stobj stobj$a '-aggressive))
         (%stobj$a (symbolicate stobj '% stobj$a))
         (recognizer$a (stobj$a-recognizer stobj$a))
         (creator$a (stobj$a-creator stobj$a))
         (fixer$a (stobj$a-fixer stobj$a))
         (stobj$a-equal (stobj$a-equal stobj$a))
         (length$a (stobj$a-vector-length stobj$a))
         (accessor$a (stobj$a-vector-accessor stobj$a))
         (updater$a (stobj$a-vector-updater stobj$a))
         (resizer$a (stobj$a-vector-resizer stobj$a))
         (resizablep (stobj$a-vector-resizablep stobj$a))

         (element-recognizer (stobj$a-vector-element-recognizer stobj$a))
         (element-fixer (stobj$a-vector-element-fixer stobj$a))
         (element (stobj$a-vector-element stobj$a))
         (element-copier (stobj-copier element))
         (element-copier{rewrite} (stobj-copier{rewrite} element))
         (%element (car (getpropc element-copier 'formals)))
         (element-coupled (and (stobj-p element)
                               (stobj-coupled element)))
         (element$a (stobj$a-lookup element))
         (element$a-recognizer (stobj$a-recognizer element$a))
         (element$a-fixer (stobj$a-fixer element$a))

         (coupled-when-not-recognizer$a (symbolicate stobj coupled '-when-not- recognizer$a))
         (coupled-of-creator$a (symbolicate stobj coupled '-of- creator$a))
         (coupled-of-fixer$a (symbolicate stobj coupled '-of- fixer$a))
         (element-coupled-of-accessor$a (symbolicate stobj element-coupled '-of- accessor$a))
         (coupled-of-updater$a (symbolicate stobj coupled '-of- updater$a))
         (coupled-of-resizer$a (symbolicate stobj coupled '-of- resizer$a))

         (recognizer$a-of-copier (symbolicate stobj recognizer$a '-of- copier))
         (length$a-of-copier (symbolicate stobj length$a '-of- copier))
         (accessor$a-of-copier (symbolicate stobj accessor$a '-of- copier))
         (recognizer$a-of-copier-rec (symbolicate stobj recognizer$a '-of- copier-rec))
         (length$a-of-copier-rec (symbolicate stobj length$a '-of- copier-rec))
         (accessor$a-of-copier-rec (symbolicate stobj accessor$a '-of- copier-rec)))

    `(encapsulate ()
       ,@(and (or element-recognizer
                  element-fixer
                  element-copier
                  element-coupled)
              `((local
                  (in-theory
                    (disable ,@(and element-recognizer
                                    (list (if element$a
                                              element$a-recognizer
                                              element-recognizer)))
                             ,@(and element-fixer
                                    (list (if element$a
                                              element$a-fixer
                                              element-fixer)))
                             ,@(and element-copier
                                    (list element-copier))
                             ,@(and element-coupled
                                    (list element-coupled)))))))

       ,@(and element-coupled
              `((defun-sk ,coupled (,stobj)
                  (declare (xargs :guard (,recognizer ,stobj)
                                  :verify-guards nil))
                  (forall i
                    (,element-coupled (,accessor$a i ,stobj)))
                  :rewrite :direct)

                (table stobj-copier
                       'stobj-coupled-alist
                       (putprop ',stobj
                                'coupled
                                ',coupled
                                (stobj-coupled-alist world)))

                (defthm ,coupled-when-not-recognizer$a
                  (implies (not (,recognizer$a ,stobj))
                           (,coupled ,stobj))
                  :hints
                  (("Goal"
                    :in-theory (enable ,stobj$a-aggressive))))

                (defthm ,coupled-of-creator$a
                  (,coupled (,creator$a)))

                (defthm ,coupled-of-fixer$a
                  (equal (,coupled (,fixer$a ,stobj))
                         (or (not (,recognizer$a ,stobj))
                             (,coupled ,stobj)))
                  :hints
                  (("Goal"
                    :cases ((,recognizer$a ,stobj))
                    :in-theory (disable ,coupled))))

                (in-theory
                  (disable ,coupled))

                (defthm ,element-coupled-of-accessor$a
                  (implies (coupled ,stobj)
                           (,element-coupled (,accessor$a i ,stobj)))
                  :hints
                  (("Goal"
                    :in-theory (enable ,stobj$a-aggressive))))

                (defthm ,coupled-of-updater$a
                  (implies (coupled ,element ,stobj)
                           (,coupled (,updater$a i ,element ,stobj)))
                  :hints
                  (("Goal"
                    :cases ((< (nfix (,witness (,updater$a i ,element ,stobj)))
                               (,length$a ,stobj)))
                    :in-theory (e/d (,stobj$a-aggressive)
                                    (,element-coupled-of-accessor$a
                                     nfix
                                     (:e force)))
                    :expand ((,coupled (,updater$a i ,element ,stobj))))))

                ,@(and resizablep
                       `((defthm ,coupled-of-resizer$a
                           (implies (coupled ,stobj)
                                    (,coupled (,resizer$a l ,stobj)))
                           :hints
                           (("Goal"
                             :cases ((< (nfix (,witness (,resizer$a l ,stobj)))
                                        (nfix l)))
                             :in-theory (e/d (,stobj$a-aggressive)
                                             (,element-coupled-of-accessor$a
                                              nfix
                                              (:e force)))
                             :expand ((,coupled (,resizer$a l ,stobj))))))))))

       (defun ,copier-rec (l ,%stobj ,stobj)
         (declare (xargs :stobjs (,%stobj ,stobj)
                         :guard (and (= (,length ,%stobj) (,length ,stobj))
                                     (natp l)
                                     (<= l (,length ,stobj)))))
         (if (zp l)
             (,fixer ,%stobj)
             ,(if element-copier
                  `(let ((l (1- l)))
                     (stobj-let ((,element (,accessor l ,stobj) ,updater))
                                (,%stobj)
;;; TODO: `CONCRETE-ACCESSOR' gives error:
;;; ```
;;; HARD ACL2 ERROR in ASSERT$:  Assertion failed:
;;; (ASSERT$ ACCESSOR$C (CONCRETE-ACCESSOR ACCESSOR$C (CDR TUPLES-LST)))
;;; '''
;;; when ACCESSOR is used instead of %ACCESSOR here (respectively UPDATER vs %UPDATER).
;;; Is this a bug?
                                (stobj-let ((,%element (,%accessor l ,%stobj) ,%updater))
                                           (,%element)
                                           (,element-copier ,%element ,element)
                                  ,%stobj)
                       (,copier-rec l ,%stobj ,stobj)))
                  `(let* ((l (1- l))
                          (,element (,accessor l ,stobj))
                          (,%stobj (,updater l ,element ,%stobj)))
                     (,copier-rec l ,%stobj ,stobj)))))

       (local
         (defthm ,recognizer$a-of-copier-rec
           (,recognizer$a (,copier-rec l ,%stobj ,stobj))
           ,@(and element-coupled
                  `(:hints
                    (("Goal"
                      :in-theory (disable ,element-coupled-of-accessor$a
                                          ,element-copier{rewrite})))))))

       (local
         (defthm ,length$a-of-copier-rec
           (equal (,length$a (,copier-rec l ,%stobj ,stobj))
                  (,length$a ,%stobj))
           ,@(and element-coupled
                  `(:hints
                    (("Goal"
                      :in-theory (disable ,element-coupled-of-accessor$a
                                          ,element-copier{rewrite})))))))

       (local
         (defthm ,accessor$a-of-copier-rec
           ,(if element-coupled
                `(implies (and (coupled ,stobj)
                               (force (< (nfix i) (,length$a ,%stobj))))
                          (equal (,accessor$a i (,copier-rec l ,%stobj ,stobj))
                                 (if (< (nfix i) (nfix l))
                                     (,accessor$a i ,stobj)
                                     (,accessor$a i ,%stobj))))
                `(implies (force (< (nfix i) (,length$a ,%stobj)))
                          (equal (,accessor$a i (,copier-rec l ,%stobj ,stobj))
                                 (if (< (nfix i) (nfix l))
                                     (,accessor$a i ,stobj)
                                     (,accessor$a i ,%stobj)))))
           :hints
           (("Goal"
             :in-theory (enable ,stobj$a-aggressive)))))

       (defun ,copier (,%stobj ,stobj)
         (declare (xargs :stobjs (,%stobj ,stobj)))
         (let* ((l (,length ,stobj))
                (,%stobj (if (= (,length ,%stobj) l)
                             ,%stobj
                             (,resizer l ,%stobj))))
           (,copier-rec l ,%stobj ,stobj)))

       (table stobj-copier
              'stobj-copier-alist
              (putprop ',stobj
                       'copier
                       ',copier
                       (stobj-copier-alist world)))

       (defthm ,recognizer$a-of-copier
         (,recognizer$a (,copier ,%stobj ,stobj)))

       (defthm ,length$a-of-copier
         (equal (,length$a (,copier ,%stobj ,stobj))
                (,length$a ,stobj)))

       (local
         (defthm ,accessor$a-of-copier
           (implies ,(if element-coupled
                         `(and (coupled ,stobj)
                               (force (< (nfix i) (,length$a ,stobj))))
                         `(force (< (nfix i) (,length$a ,stobj))))
                    (equal (,accessor$a i (,copier ,%stobj ,stobj))
                           (,accessor$a i ,stobj)))))

       (in-theory
         (disable ,copier-rec
                  ,copier))

       (defthm ,copier{rewrite}
         ,(if element-coupled
              `(implies (coupled ,stobj)
                        (equal (,copier ,%stobj ,stobj)
                               (,fixer ,stobj)))
              `(equal (,copier ,%stobj ,stobj)
                      (,fixer ,stobj)))
         :hints
         (("Goal"
           :use ((:instance ,stobj$a-equal
                            (,%stobj$a (,copier ,%stobj ,stobj))
                            (,stobj$a (,fixer ,stobj)))))))

       (table stobj-copier
              'stobj-copier-alist
              (putprop ',stobj
                       'copier{rewrite}
                       ',copier{rewrite}
                       (stobj-copier-alist world))))))

(defun make-hash-table-copy-events (stobj$a %stobj stobj state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp stobj$a)
                              (symbolp %stobj)
                              (symbolp stobj))
                  :verify-guards nil))
  (let* ((copier (symbolicate stobj stobj '-copy))
         (copier{rewrite} (symbolicate stobj copier '{rewrite}))
         (copier-rec (symbolicate stobj copier '-rec))

         (coupled (symbolicate stobj stobj '-coupled))
         (coupled-keys (symbolicate stobj coupled '-keys))
         (coupled-keys-witness (symbolicate stobj coupled-keys '-witness))
         (coupled-keys-necc (symbolicate stobj coupled-keys '-necc))
         (coupled-vals (symbolicate stobj coupled '-vals))
         (coupled-vals-witness (symbolicate stobj coupled-vals '-witness))
         (coupled-vals-necc (symbolicate stobj coupled-vals '-necc))

         (recognizer (stobj-recognizer stobj))
         (exports (stobj$abs-exports stobj))
         (fixer (car (first exports)))
         (accessor (car (second exports)))
         (%accessor (symbolicate stobj '% accessor))
         (updater (car (third exports)))
         (%updater (symbolicate stobj '% updater))
         (count (car (seventh exports)))
         (init (car (ninth exports)))
         (keys (car (tenth exports)))
         (keys-set (car (nth 10 exports)))

         (stobj$a-aggressive (symbolicate stobj stobj$a '-aggressive))
         (%stobj$a (symbolicate stobj '% stobj$a))
         (recognizer$a (stobj$a-recognizer stobj$a))
         (creator$a (stobj$a-creator stobj$a))
         (fixer$a (stobj$a-fixer stobj$a))
         (stobj$a-equal (stobj$a-equal stobj$a))
         (accessor$a (stobj$a-hash-table-accessor stobj$a))
         (updater$a (stobj$a-hash-table-updater stobj$a))
         (boundp$a (stobj$a-hash-table-boundp stobj$a))
         (count$a (stobj$a-hash-table-count stobj$a))
         (keys$a (stobj$a-hash-table-keys stobj$a))
         (keys-set$a (stobj$a-hash-table-keys-set stobj$a))

         (key-recognizer (stobj$a-hash-table-key-recognizer stobj$a))
         (key-fixer (stobj$a-hash-table-key-fixer stobj$a))
         (key (stobj$a-hash-table-key stobj$a))
         ;; (default-key (stobj$a-hash-table-default-key stobj$a))

         (val-recognizer (stobj$a-hash-table-val-recognizer stobj$a))
         (val-fixer (stobj$a-hash-table-val-fixer stobj$a))
         (val (stobj$a-hash-table-val stobj$a))
         (val-copier (stobj-copier val))
         (val-copier{rewrite} (stobj-copier{rewrite} val))
         (%val (car (getpropc val-copier 'formals)))
         (val-coupled (stobj-coupled val))
         (val$a (stobj$a-lookup val))
         (val$a-recognizer (stobj$a-recognizer val$a))
         (val$a-creator (stobj$a-creator val$a))
         (val$a-fixer (stobj$a-fixer val$a))

         (coupled-keys-when-not-recognizer$a (symbolicate stobj coupled-keys '-when-not- recognizer$a))
         (coupled-keys-of-creator$a (symbolicate stobj coupled-keys '-of- creator$a))
         (coupled-keys-of-fixer$a (symbolicate stobj coupled-keys '-of- fixer$a))
         (coupled-keys-of-updater$a-when-boundp$a (symbolicate stobj coupled-keys '-of- updater$a '-when- boundp$a))
         (coupled-keys-of-updater$a-when-not-boundp$a (symbolicate stobj coupled-keys '-of- updater$a '-when-not- boundp$a))
         (coupled-keys-of-updater$a-when-not-boundp$a-lemma
          (symbolicate stobj coupled-keys-of-updater$a-when-not-boundp$a '-lemma))

         (coupled-vals-when-not-recognizer$a (symbolicate stobj coupled-vals '-when-not- recognizer$a))
         (coupled-vals-of-creator$a (symbolicate stobj coupled-vals '-of- creator$a))
         (coupled-vals-of-fixer$a (symbolicate stobj coupled-vals '-of- fixer$a))
         (coupled-vals-of-updater$a (symbolicate stobj coupled-vals '-of- updater$a))
         (coupled-vals-of-updater$a-lemma (symbolicate stobj coupled-vals-of-updater$a '-lemma))
         (coupled-vals-of-keys-set$a (symbolicate stobj coupled-vals '-of- keys-set$a))

         (coupled-when-not-recognizer$a (symbolicate stobj coupled '-when-not- recognizer$a))
         (coupled-of-creator$a (symbolicate stobj coupled '-of- creator$a))
         (coupled-of-fixer$a (symbolicate stobj coupled '-of- fixer$a))
         (coupled-of-updater$a (symbolicate stobj coupled '-of- updater$a))
         (coupled-of-updater$a-lemma-0 (symbolicate stobj coupled-of-updater$a '-lemma-0))
         (coupled-of-updater$a-lemma-1 (symbolicate stobj coupled-of-updater$a '-lemma-1))
         (cardinality-of-keys$a (symbolicate stobj 'cardinality-of- keys$a))
         (in-of-keys$a (symbolicate stobj 'in-of- keys$a))
         (val-coupled-of-accessor$a (symbolicate stobj val-coupled '-of- accessor$a))
         (emptyp-of-keys$a (symbolicate stobj 'emptyp-of- keys$a))
         (key-recognizer-of-head-when-coupled (symbolicate stobj key-recognizer '-of-head-when- coupled))

         (recognizer$a-of-copier (symbolicate stobj recognizer$a '-of- copier))
         (coupled-of-copier (symbolicate stobj coupled '-of- copier))
         (coupled-of-copier/lemma-0 (symbolicate stobj coupled-of-copier '/lemma-0))
         (coupled-of-copier/lemma-1 (symbolicate stobj coupled-of-copier '/lemma-1))
         (keys$a-of-copier (symbolicate stobj keys$a '-of- copier))
         (count$a-of-copier (symbolicate stobj count$a '-of- copier))
         (boundp$a-of-copier (symbolicate stobj boundp$a '-of- copier))
         (accessor$a-of-copier (symbolicate stobj accessor$a '-of- copier))
         (recognizer$a-of-copier-rec (symbolicate stobj recognizer$a '-of- copier-rec))
         (keys$a-of-copier-rec (symbolicate stobj keys$a '-of- copier-rec))
         (copier-rec-of-updater$a (symbolicate stobj copier-rec '-of- updater$a))
         (count$a-of-copier-rec (symbolicate stobj count$a '-of- copier-rec))
         (boundp$a-of-copier-rec (symbolicate stobj boundp$a '-of- copier-rec))
         (accessor$a-of-copier-rec (symbolicate stobj accessor$a '-of- copier-rec)))

    `(encapsulate ()
       ,@(and (or key-recognizer
                  key-fixer
                  val-recognizer
                  val-fixer
                  val-copier
                  val-coupled)
              `((local
                  (in-theory
                    (disable ,@(and key-recognizer
                                    (list key-recognizer))
                             ,@(and key-fixer
                                    (list key-fixer))
                             ,@(and val-recognizer
                                    (list (if val$a
                                              val$a-recognizer
                                              val-recognizer)))
                             ,@(and val-fixer
                                    (list (if val$a
                                              val$a-fixer
                                              val-fixer)))
                             ,@(and val-copier
                                    (list val-copier))
                             ,@(and val-coupled
                                    (list val-coupled)))))))

       (local
         (in-theory
           (acl2::enable* set::expensive-rules)))

       (defun-sk ,coupled-keys (,stobj)
         (declare (xargs :guard (,recognizer ,stobj)
                         :verify-guards nil))
         (forall ,key
           (equal (set::in ,key (,keys$a ,stobj))
                  ,(if key-recognizer
                       `(and (,key-recognizer ,key)
                             (,boundp$a ,key ,stobj))
                       `(,boundp$a ,key ,stobj))))
         :rewrite :direct)

       (defthm ,coupled-keys-when-not-recognizer$a
         (implies (not (,recognizer$a ,stobj))
                  (,coupled-keys ,stobj))
         :hints
         (("Goal"
           :in-theory (enable ,stobj$a-aggressive))))

       (defthm ,coupled-keys-of-creator$a
         (,coupled-keys (,creator$a)))

       (defthm ,coupled-keys-of-fixer$a
         (equal (,coupled-keys (,fixer$a ,stobj))
                (or (not (,recognizer$a ,stobj))
                    (,coupled-keys ,stobj))))

       (encapsulate ()
         (local
           (in-theory (enable ,stobj$a-aggressive)))

         (defthm ,coupled-keys-of-updater$a-when-boundp$a
           (implies (and (,boundp$a ,key ,stobj)
                         (,coupled-keys ,stobj))
                    (,coupled-keys (,updater$a ,key ,val ,stobj))))

         (local
           (defthm ,coupled-keys-of-updater$a-when-not-boundp$a-lemma
             (implies (let* ((,keys$a (,keys$a ,stobj))
                             (trimmed (set::delete ,key ,keys$a)))
                        (and ,@(and key-recognizer
                                    `((,key-recognizer ,key)))
                             (not (,boundp$a ,key ,stobj))
                             (set::in ,key ,keys$a)
                             (,coupled-keys (,keys-set$a trimmed ,stobj))))
                      (,coupled-keys (,updater$a ,key ,val ,stobj)))
             :hints
             (("Goal"
               :in-theory (disable ,coupled-keys
                                   ,coupled-keys-necc)
               :use ((:instance ,coupled-keys-necc
                                (,key (,coupled-keys-witness (,updater$a ,key ,val ,stobj)))
                                (,stobj (let* ((,keys$a (,keys$a ,stobj))
                                               (trimmed (set::delete ,key ,keys$a)))
                                          (,keys-set$a trimmed ,stobj)))))
               :expand (,coupled-keys (,updater$a ,key ,val ,stobj))))))

         (defthm ,coupled-keys-of-updater$a-when-not-boundp$a
           (implies (let* ((,keys$a (,keys$a ,stobj))
                           (trimmed (set::delete ,(if key-fixer
                                                      `(,key-fixer ,key)
                                                      key)
                                                 ,keys$a)))
                      (and (not (,boundp$a ,key ,stobj))
                           (set::in ,(if key-fixer
                                         `(,key-fixer ,key)
                                         key)
                                    ,keys$a)
                           (,coupled-keys (,keys-set$a trimmed ,stobj))))
                    (,coupled-keys (,updater$a ,key ,val ,stobj)))
           :hints
           (("Goal"
             ,@(and key-recognizer
                    `(:cases ((,key-recognizer ,key))))
             :in-theory (disable ,coupled-keys)))))

       (in-theory
         (disable ,coupled-keys))

       ,@(and val-coupled
              `((defun-sk ,coupled-vals (,stobj)
                  (declare (xargs :guard (,recognizer ,stobj)
                                  :verify-guards nil))
                  (forall ,key
                    (,val-coupled (,accessor$a ,key ,stobj)))
                  :rewrite :direct)

                (defthm ,coupled-vals-when-not-recognizer$a
                  (implies (not (,recognizer$a ,stobj))
                           (,coupled-vals ,stobj))
                  :hints
                  (("Goal"
                    :in-theory (enable ,stobj$a-aggressive))))

                (defthm ,coupled-vals-of-creator$a
                  (,coupled-vals (,creator$a)))

                (defthm ,coupled-vals-of-fixer$a
                  (equal (,coupled-vals (,fixer$a ,stobj))
                         (or (not (,recognizer$a ,stobj))
                             (,coupled-vals ,stobj))))

                (encapsulate ()
                  (local
                    (in-theory (enable ,stobj$a-aggressive)))

                  (local
                    (defthm ,coupled-vals-of-updater$a-lemma
                      (implies ,(if key-recognizer
                                    `(and (,coupled-vals ,stobj)
                                          (,key-recognizer ,key))
                                    `(,coupled-vals ,stobj))
                               (equal (,coupled-vals (,updater$a ,key ,val ,stobj))
                                      (,val-coupled ,val)))
                      :hints
                      (("Goal"
                        :in-theory (disable ,coupled-vals
                                            ,coupled-vals-necc)
                        :use ((:instance ,coupled-vals-necc
                                         (,stobj (,updater$a ,key ,val ,stobj))))
                        :expand ((,coupled-vals (,updater$a ,key ,val ,stobj))
                                 (,coupled-vals (,updater$a ,key (,val$a-creator) ,stobj)))))))

                  (defthm ,coupled-vals-of-updater$a
                    (implies (,coupled-vals ,stobj)
                             (equal (,coupled-vals (,updater$a ,key ,val ,stobj))
                                    (,val-coupled ,val)))
                    :hints
                    (("Goal"
                      ,@(and key-recognizer
                             `(:cases ((,key-recognizer ,key))))
                      :in-theory (disable ,coupled-vals))))

                  (defthm ,coupled-vals-of-keys-set$a
                    (iff (,coupled-vals (,keys-set$a ,keys$a ,stobj))
                         (,coupled-vals ,stobj))
                    :hints
                    (("Goal"
                      :in-theory (disable ,coupled-vals
                                          ,coupled-vals-necc))
                     ("Subgoal 2"
                      :use ((:instance ,coupled-vals-necc
                                       (,key (,coupled-vals-witness (,keys-set$a ,keys$a ,stobj)))))
                      :expand (,coupled-vals (,keys-set$a ,keys$a ,stobj)))
                     ("Subgoal 1"
                      :use ((:instance ,coupled-vals-necc
                                       (,key (,coupled-vals-witness ,stobj))
                                       (,stobj (,keys-set$a ,keys$a ,stobj))))
                      :expand (,coupled-vals ,stobj)))))

                (in-theory
                  (disable ,coupled-vals))))

       (defun-nx ,coupled (,stobj)
         (declare (xargs :guard (,recognizer ,stobj)
                         :verify-guards nil))
         (and (= (set::cardinality (,keys$a ,stobj))
                 (,count$a ,stobj))
              (,coupled-keys ,stobj)
              ,@(and val-coupled
                     `((,coupled-vals ,stobj)))))

       (table stobj-copier
              'stobj-coupled-alist
              (putprop ',stobj
                       'coupled
                       ',coupled
                       (stobj-coupled-alist world)))

       (defthm ,coupled-when-not-recognizer$a
         (implies (not (,recognizer$a ,stobj))
                  (,coupled ,stobj))
         :hints
         (("Goal"
           :in-theory (enable ,stobj$a-aggressive))))

       (defthm ,coupled-of-creator$a
         (,coupled (,creator$a)))

       (defthm ,coupled-of-fixer$a
         (equal (,coupled (,fixer$a ,stobj))
                (or (not (,recognizer$a ,stobj))
                    (,coupled ,stobj)))
         :hints
         (("Goal"
           :cases ((,recognizer$a ,stobj))
           :in-theory (disable ,coupled))))

       (encapsulate ()
         (local
           (in-theory
             (enable ,stobj$a-aggressive)))

         (local
           (defthm ,coupled-of-updater$a-lemma-0
             (implies (and (,boundp$a ,key ,stobj)
                           (,coupled ,stobj))
                      ,(if val-coupled
                           `(equal (,coupled (,updater$a ,key ,val ,stobj))
                                   (,val-coupled ,val))
                           `(,coupled (,updater$a ,key ,val ,stobj))))))

         (local
           (defthm ,coupled-of-updater$a-lemma-1
             (implies (and (not (,boundp$a ,key ,stobj))
                           (let* ((keys (,keys$a ,stobj))
                                  (trimmed (set::delete ,(if key-fixer
                                                             `(,key-fixer ,key)
                                                             key)
                                                        keys)))
                             (and (set::in ,(if key-fixer
                                                `(,key-fixer ,key)
                                                key)
                                           keys)
                                  (,coupled (,keys-set$a trimmed ,stobj)))))
                      ,(if val-coupled
                           `(equal (,coupled (,updater$a ,key ,val ,stobj))
                                   (,val-coupled ,val))
                           `(,coupled (,updater$a ,key ,val ,stobj))))))

         (defthm ,coupled-of-updater$a
           (implies (force (if (,boundp$a ,key ,stobj)
                               (,coupled ,stobj)
                               (let* ((keys (,keys$a ,stobj))
                                      (trimmed (set::delete ,(if key-fixer
                                                                 `(,key-fixer ,key)
                                                                 key)
                                                            keys)))
                                 (and (set::in ,(if key-fixer
                                                    `(,key-fixer ,key)
                                                    key)
                                               keys)
                                      (,coupled (,keys-set$a trimmed ,stobj))))))
                    ,(if val-coupled
                         `(equal (,coupled (,updater$a ,key ,val ,stobj))
                                 (,val-coupled ,val))
                         `(,coupled (,updater$a ,key ,val ,stobj))))
           :hints
           (("Goal"
             :in-theory (disable ,coupled)))))

       (defthm ,cardinality-of-keys$a
         (implies (coupled ,stobj)
                  (equal (set::cardinality (,keys$a ,stobj))
                         (,count$a ,stobj))))

       (defthm ,in-of-keys$a
         (implies (,coupled ,stobj)
                  (equal (set::in ,key (,keys$a ,stobj))
                         ,(if key-recognizer
                              `(and (,key-recognizer ,key)
                                    (,boundp$a ,key ,stobj))
                              `(,boundp$a ,key ,stobj))))
         :hints
         (("Goal"
           :in-theory (disable ,coupled-keys-necc)
           :use ((:instance ,coupled-keys-necc)))))

       ,@(and val-coupled
              `((defthm ,val-coupled-of-accessor$a
                  (implies (coupled ,stobj)
                           (,val-coupled (,accessor$a ,key ,stobj))))))

       (in-theory
         (disable ,coupled))

       (defthm ,emptyp-of-keys$a
         (implies (coupled ,stobj)
                  (equal (set::emptyp (,keys$a ,stobj))
                         (= (,count$a ,stobj) 0)))
         :hints
         (("Goal"
           :in-theory (disable ,cardinality-of-keys$a)
           :use ((:instance ,cardinality-of-keys$a)))))

       ,@(and key-recognizer
              `((defthm ,key-recognizer-of-head-when-coupled
                  (implies (and (not (set::emptyp set))
                                (,coupled ,stobj)
                                (set::subset set (,keys$a ,stobj)))
                           (,key-recognizer (set::head set)))
                  :rule-classes
                  ((:forward-chaining :trigger-terms
                                      ((set::subset set (,keys$a ,stobj)))))
                  :hints
                  (("Goal"
                    :expand (set::subset set (,keys$a ,stobj)))))))

       (defun ,copier-rec (set ,%stobj ,stobj)
         (declare (xargs :stobjs (,%stobj ,stobj)
                         :guard (and (set::setp set)
                                     (set::subset set (,keys ,stobj)))))
         (if (set::emptyp set)
             (,fixer ,%stobj)
             ,(if val-copier
                  `(let ((key ,(if key-fixer
                                   `(,key-fixer (set::head set))
                                   '(set::head set))))
                     (stobj-let ((,val (,accessor key ,stobj) ,updater))
                                (,%stobj)
                                (stobj-let ((,%val (,%accessor key ,%stobj) ,%updater))
                                           (,%val)
                                           (,val-copier ,%val ,val)
                                  ,%stobj)
                       (,copier-rec (set::tail set) ,%stobj ,stobj)))
                  `(let* ((key ,(if key-fixer
                                    `(,key-fixer (set::head set))
                                    '(set::head set)))
                          (,val (,accessor key ,stobj))
                          (,%stobj (,updater key ,val ,%stobj)))
                     (,copier-rec (set::tail set) ,%stobj ,stobj)))))

       (local
         (defthm ,recognizer$a-of-copier-rec
           (,recognizer$a (,copier-rec set ,%stobj ,stobj))
           ,@(and val-coupled
                  `(:hints
                    (("Goal"
                      :in-theory (disable ,val-coupled-of-accessor$a
                                          ,val-copier{rewrite})))))))

       (local
         (defthm ,keys$a-of-copier-rec
           (equal (,keys$a (,copier-rec set ,%stobj ,stobj))
                  (,keys$a ,%stobj))
           ,@(and val-coupled
                  `(:hints
                    (("Goal"
                      :in-theory (disable ,val-coupled-of-accessor$a
                                          ,val-copier{rewrite})))))))

       (local
         (defthm ,copier-rec-of-updater$a
           (implies (and (coupled ,stobj)
                         (set::subset set (,keys$a ,stobj)))
                    (equal (,copier-rec set (,updater$a ,key ,val ,%stobj) ,stobj)
                           (if (set::in ,(if key-fixer
                                             `(,key-fixer ,key)
                                             key)
                                        set)
                               (,copier-rec set ,%stobj ,stobj)
                               (,updater$a ,key ,val (,copier-rec set ,%stobj ,stobj)))))
           :hints
           (("Goal"
             :induct (,copier-rec set ,%stobj ,stobj)
             :in-theory (enable ,stobj$a-aggressive)
             :expand ((,copier-rec set (,updater$a ,key ,val ,%stobj) ,stobj))))))

       (local
         (defthm ,boundp$a-of-copier-rec
           (implies (and (coupled ,stobj)
                         (set::subset set (,keys$a ,stobj)))
                    (equal (,boundp$a ,key (,copier-rec set ,%stobj ,stobj))
                           (or (,boundp$a ,key ,%stobj)
                               (set::in ,(if key-fixer
                                             `(,key-fixer ,key)
                                             key)
                                        set))))
           :hints
           (("Goal"
             :induct (,copier-rec set ,%stobj ,stobj)
             :in-theory (enable ,stobj$a-aggressive))
            ("Subgoal *1/2"
             :cases ((set::in ,(if key-fixer
                                   `(,key-fixer ,key)
                                   key)
                              set))))))

       (local
         (defthm ,accessor$a-of-copier-rec
           (implies (and (coupled ,stobj)
                         (set::subset set (,keys$a ,stobj)))
                    (equal (,accessor$a ,key (,copier-rec set ,%stobj ,stobj))
                           (if (set::in ,(if key-fixer
                                             `(,key-fixer ,key)
                                             key)
                                        set)
                               (,accessor$a ,key ,stobj)
                               (,accessor$a ,key ,%stobj))))
           :hints
           (("Goal"
             :induct (,copier-rec set ,%stobj ,stobj)
             :in-theory (enable ,stobj$a-aggressive)))))

       (local
         (defthm ,count$a-of-copier-rec
           (implies (and (coupled ,stobj)
                         (set::subset set (,keys$a ,stobj)))
                    (equal (,count$a (,copier-rec set ,%stobj ,stobj))
                           (cond
                             ((set::emptyp set)
                              (,count$a ,%stobj))
                             ((,boundp$a (set::head set) ,%stobj)
                              (,count$a (,copier-rec (set::tail set) ,%stobj ,stobj)))
                             (t
                              (1+ (,count$a (,copier-rec (set::tail set) ,%stobj ,stobj)))))))
           :hints
           (("Goal"
             :in-theory (enable ,stobj$a-aggressive))
            ("Subgoal *1/2"
             :use ((:instance set::head-tail-order
                              (x set)))
             :expand (set::subset set (,keys$a ,stobj))))))

       (defun ,copier (,%stobj ,stobj)
         (declare (xargs :stobjs (,%stobj ,stobj)))
         (let* ((keys (,keys ,stobj))
                (count (,count ,stobj))
                (,%stobj (,init count nil nil ,%stobj))
                (,%stobj (,keys-set keys ,%stobj)))
           (,copier-rec keys ,%stobj ,stobj)))

       (table stobj-copier
              'stobj-copier-alist
              (putprop ',stobj
                       'copier
                       ',copier
                       (stobj-copier-alist world)))

       (defthm ,recognizer$a-of-copier
         (,recognizer$a (,copier ,%stobj ,stobj)))

       (local
         (defthm ,coupled-of-copier/lemma-0
           (implies (and (set::setp %set)
                         (coupled ,stobj)
                         (set::subset set (,keys$a ,stobj)))
                    (equal (,count$a (,copier-rec set (,keys-set$a %set (,creator$a)) ,stobj))
                           (,count$a (,copier-rec set (,creator$a) ,stobj))))
           :hints
           (("Goal"
             :induct (set::cardinality set)
             :in-theory (enable (:i set::cardinality))))))

       (local
         (defthm ,coupled-of-copier/lemma-1
           (implies (and (coupled ,stobj)
                         (set::subset set (,keys$a ,stobj)))
                    (equal (,count$a (,copier-rec set (,creator$a) ,stobj))
                           (set::cardinality set)))
           :hints
           (("Goal"
             :induct (set::cardinality set)
             :in-theory (enable (:i set::cardinality)
                                set::cardinality)))))

       (local
         (defthm ,coupled-of-copier
           (implies (coupled ,stobj)
                    (,coupled (,copier ,%stobj ,stobj)))
           :hints
           (("Goal"
             :in-theory (enable ,coupled-keys
                                ,@(and val-coupled
                                       (list coupled-vals)))
             :expand ((,coupled (,copier-rec (,keys$a ,stobj)
                                             (,keys-set$a (,keys$a ,stobj) (,creator$a))
                                             ,stobj)))))))

       (defthm ,keys$a-of-copier
         (equal (,keys$a (,copier ,%stobj ,stobj))
                (,keys$a ,stobj)))

       (local
         (defthm ,count$a-of-copier
           (implies (coupled ,stobj)
                    (equal (,count$a (,copier ,%stobj ,stobj))
                           (,count$a ,stobj)))))

       (local
         (defthm ,boundp$a-of-copier
           (implies (coupled ,stobj)
                    (equal (,boundp$a ,key (,copier ,%stobj ,stobj))
                           (,boundp$a ,key ,stobj)))))

       (local
         (defthm ,accessor$a-of-copier
           (implies (coupled ,stobj)
                    (equal (,accessor$a ,key (,copier ,%stobj ,stobj))
                           (,accessor$a ,key ,stobj)))
           :hints
           (("Goal"
             :in-theory (enable ,stobj$a-aggressive)))))

       (in-theory
         (disable ,copier-rec
                  ,copier))

       (defthm ,copier{rewrite}
         (implies (coupled ,stobj)
                  (equal (,copier ,%stobj ,stobj)
                         (,fixer ,stobj)))
         :hints
         (("goal"
           :do-not-induct t
           :use ((:instance ,stobj$a-equal
                            (,%stobj$a (,copier ,%stobj ,stobj))
                            (,stobj$a (,fixer ,stobj)))))))

       (table stobj-copier
              'stobj-copier-alist
              (putprop ',stobj
                       'copier{rewrite}
                       ',copier{rewrite}
                       (stobj-copier-alist world))))))

(defun make-frame-copy-events (stobj$a %stobj stobj state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp stobj$a)
                              (symbolp %stobj)
                              (symbolp stobj))
                  :verify-guards nil))
  (let* ((world (w state))
         (copier (symbolicate stobj stobj '-copy))
         (copier{rewrite} (symbolicate stobj copier '{rewrite}))

         (coupled (symbolicate stobj stobj '-coupled))

         (recognizer (stobj-recognizer stobj))
         (exports (stobj$abs-exports stobj))
         (fixer (caar exports))
         (exports (cdr exports))
         (2n (len exports))
         (n (floor 2n 2))
         (accessors (loop$ :for i :from 0 :to (1- n)
                          :as export :in exports
                          :collect (car export)))
         (updaters (loop$ :for i :from 0 :to (1- n)
                         :as export :in (nthcdr n exports)
                         :collect (car export)))
         (fields (stobj$a-frame-fields stobj$a))
         (stobjs (stobj$a-frame-stobjs stobj$a))
         (field-recognizers (stobj$a-frame-recognizers stobj$a))
         (field-fixers (stobj$a-frame-fixers stobj$a))
         (stobj-copier-alist (stobj-copier-alist world))
         (field-copiers (loop$ :for stobj :in stobjs
                              :collect (and stobj
                                            (getprop stobj
                                                     'copier
                                                     nil
                                                     'current-acl2-world
                                                     stobj-copier-alist))))
         (copier-body
          (loop$ :with body := %stobj
                :with fields := (reverse fields)
                :with stobjs := (reverse stobjs)
                :with accessors := (reverse accessors)
                :with updaters := (reverse updaters)
                :with field-copiers := (reverse field-copiers)
                :do
                (progn
                  (cond
                    ((atom stobjs)
                     (return body))
                    ((car stobjs)
                     (setq body (let* ((element (car stobjs))
                                       (%element (symbolicate stobj '% element))
                                       (accessor (car accessors))
                                       (updater (car updaters))
                                       (%accessor (symbolicate stobj '% accessor))
                                       (%updater (symbolicate stobj '% updater))
                                       (field-copier (car field-copiers)))
                                  `(stobj-let ((,element (,accessor ,stobj) ,updater))
                                              (,%stobj)
                                              (stobj-let ((,%element (,%accessor ,%stobj) ,%updater))
                                                         (,%element)
                                                         (,field-copier ,%element ,element)
                                                ,%stobj)
                                     ,body))))
                    (t
                     (setq body `(let* ((,(car fields) (,(car accessors) ,stobj))
                                        (,%stobj (,(car updaters) ,(car fields) ,%stobj)))
                                   ,body))))
                  (setq fields (cdr fields))
                  (setq stobjs (cdr stobjs))
                  (setq accessors (cdr accessors))
                  (setq updaters (cdr updaters))
                  (setq field-copiers (cdr field-copiers)))))
         (stobj-coupled-alist (stobj-coupled-alist world))
         (field-couplings (loop$ :for stobj :in stobjs
                                :collect (and stobj
                                              (getprop stobj
                                                       'coupled
                                                       nil
                                                       'current-acl2-world
                                                       stobj-coupled-alist))))

         (stobj$a-lookup-alist (stobj$a-lookup-alist world))
         (stobjs$a (loop$ :for stobj :in stobjs
                         :collect (getprop stobj 'stobj$a
                                           nil 'current-acl2-world
                                           stobj$a-lookup-alist)))
         (stobj$a-property-alist (stobj$a-property-alist world))
         (stobj$a-properties (loop$ :for stobj$a :in stobjs$a
                                   :collect (getprop stobj$a 'stobj$a
                                                     nil 'current-acl2-world
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
         (stobj$a-aggressive (symbolicate stobj stobj$a '-aggressive))
         (%stobj$a (symbolicate stobj '% stobj$a))
         (recognizer$a (stobj$a-recognizer stobj$a))
         (creator$a (stobj$a-creator stobj$a))
         (fixer$a (stobj$a-fixer stobj$a))
         (view$a (stobj$a-frame-view stobj$a))
         (accessors$a (stobj$a-frame-accessors stobj$a))
         (stobj$a-equal (symbolicate stobj stobj$a '-equal))

         (coupled-when-not-recognizer$a (symbolicate stobj coupled '-when-not- recognizer$a))
         (coupled-of-creator$a (symbolicate stobj coupled '-of- creator$a))
         (coupled-of-fixer$a (symbolicate stobj coupled '-of- fixer$a))
         (coupled-of-view$a (symbolicate stobj coupled '-of- view$a))

         (recognizer$a-of-copier (symbolicate stobj recognizer$a '-of- copier)))

    `(encapsulate ()
       ,@(let ((field-recognizers$a (remove nil field-recognizers$a))
               (field-fixers$a (remove nil field-fixers$a))
               (field-copiers (remove nil field-copiers))
               (field-couplings (remove nil field-couplings)))
           (and (or field-recognizers$a
                    field-fixers$a
                    field-copiers
                    field-couplings)
                `((local
                    (in-theory
                      (disable ,@field-recognizers$a
                               ,@field-fixers$a
                               ,@field-copiers
                               ,@field-couplings))))))

       ,@(and (remove nil field-couplings)
              `((defun-nx ,coupled (,stobj)
                  (declare (xargs :guard (,recognizer ,stobj)
                                  :verify-guards nil))
                  ,(let ((body (loop$ :for coupling :in field-couplings
                                     :as accessor$a :in accessors$a
                                     :when coupling
                                     :collect `(,coupling (,accessor$a ,stobj)))))
                     (if (consp (cdr body))
                         (cons 'and body)
                         (car body))))

                (table stobj-copier
                       'stobj-coupled-alist
                       (putprop ',stobj
                                'coupled
                                ',coupled
                                (stobj-coupled-alist world)))

                (defthm ,coupled-when-not-recognizer$a
                  (implies (not (,recognizer$a ,stobj))
                           (,coupled ,stobj))
                  :hints
                  (("Goal"
                    :in-theory (enable ,stobj$a-aggressive))))

                (defthm ,coupled-of-creator$a
                  (,coupled (,creator$a)))

                (defthm ,coupled-of-fixer$a
                  (equal (,coupled (,fixer$a ,stobj))
                         (or (not (,recognizer$a ,stobj))
                             (,coupled ,stobj)))
                  :hints
                  (("Goal"
                    :cases ((,recognizer$a ,stobj))
                    :in-theory (disable ,coupled))))

                (defthm ,coupled-of-view$a
                  (equal (,coupled (,view$a ,@fields ,stobj))
                         ,(let ((constraints (loop$ :for coupling :in field-couplings
                                                   :as field :in fields
                                                   :when coupling
                                                   :collect `(,coupling ,field))))
                            (if (consp (cdr constraints))
                                (cons 'and constraints)
                                (car constraints)))))

                ,@(loop$ :for accessor$a :in accessors$a
                        :as coupling :in field-couplings
                        :when coupling
                        :collect `(defthm ,(symbolicate stobj coupling '-of- accessor$a)
                                    (implies (coupled ,stobj)
                                             (,coupling (,accessor$a ,stobj)))))

                (in-theory
                  (disable ,coupled))))

       (defun ,copier (,%stobj ,stobj)
         (declare (xargs :stobjs (,%stobj ,stobj)))
         ,copier-body)

       (table stobj-copier
              'stobj-copier-alist
              (putprop ',stobj
                       'copier
                       ',copier
                       (stobj-copier-alist world)))

       (defthm ,recognizer$a-of-copier
         (,recognizer$a (,copier ,%stobj ,stobj))
         ,@(and (remove nil field-couplings)
                `(:hints
                  (("Goal"
                    :in-theory (disable (:e force)))))))

       ,@(loop$ :for accessor$a :in accessors$a
               :collect `(local
                           (defthm ,(symbolicate stobj accessor$a '-of- copier)
                             ,(if (remove nil field-couplings)
                                  `(implies (coupled ,stobj)
                                            (equal (,accessor$a (,copier ,%stobj ,stobj))
                                                   (,accessor$a ,stobj)))
                                  `(equal (,accessor$a (,copier ,%stobj ,stobj))
                                          (,accessor$a ,stobj))))))

       (in-theory
         (disable ,copier))

       (defthm ,copier{rewrite}
         ,(if (remove nil field-couplings)
              `(implies (coupled ,stobj)
                        (equal (,copier ,%stobj ,stobj)
                               (,fixer ,stobj)))
              `(equal (,copier ,%stobj ,stobj)
                      (,fixer ,stobj)))
         :hints
         (("Goal"
           :do-not-induct t
           :use ((:instance ,stobj$a-equal
                            (,%stobj$a (,copier ,%stobj ,stobj))
                            (,stobj$a (,fixer ,stobj)))))))

       (table stobj-copier
              'stobj-copier-alist
              (putprop ',stobj
                       'copier{rewrite}
                       ',copier{rewrite}
                       (stobj-copier-alist world))))))

(defun make-copier-events (%stobj stobj state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp %stobj)
                              (symbolp stobj))
                  :verify-guards nil))
  (let* ((stobj$a (stobj$a-lookup stobj))
         (stobj$a-type (cond
                         ((stobj$a-vector-p stobj$a)
                          'vector)
                         ((stobj$a-hash-table-p stobj$a)
                          'hash-table)
                         ((stobj$a-frame-p stobj$a)
                          'frame))))
    (case stobj$a-type
      (vector
       (make-vector-copy-events stobj$a %stobj stobj state))
      (hash-table
       (make-hash-table-copy-events stobj$a %stobj stobj state))
      (frame
       (make-frame-copy-events stobj$a %stobj stobj state)))))

(defmacro define-stobj-copier (stobj &key (debug 'nil))
  (declare (xargs :guard (and (symbolp stobj)
                              (booleanp debug))))
  `(with-output
     ,@(and (not debug)
            '#!acl2(:off (warning! observation prove event history proof-tree)
                         :summary-off (rules)
                         :gag-mode t))

     (make-event
       (let* ((stobj ',stobj)

              (stobj$a (stobj$a-lookup stobj))
              (stobj$a-definitions (symbolicate stobj stobj$a '-definitions))
              (%stobj (symbolicate stobj '% stobj))
              (foundation (stobj$abs-foundation stobj))
              (recognizers (stobj$abs-recognizers stobj))
              (recognizer (car recognizers))
              (%recognizer (symbolicate stobj '% recognizer))
              (creators (stobj$abs-creators stobj))
              (creator (car creators))
              (%creator (symbolicate stobj '% creator))
              (exports (stobj$abs-exports stobj))
              (interface (loop$ :for triple :in exports
                               :collect (car triple)))
              (%interface (loop$ :for sym :in interface
                                :collect (symbolicate stobj '% sym)))
              (interface-alist (loop$ :for sym :in interface
                                     :as %sym :in %interface
                                     :collect (cons sym %sym)))
              (%updaters (loop$ :for triple :in exports
                               :collect (let ((key (cdddr triple)))
                                          (and key
                                               (let ((pair (assoc key interface-alist)))
                                                 (and (consp pair)
                                                      (cdr pair)))))))
              (%protect (loop$ :for triple :in exports
                              :collect (let* ((fn$c (third triple))
                                              (revname (reverse (symbol-name fn$c)))
                                              (length (length revname)))
                                         (and (or (and (<= 5 length)
                                                       (equal (subseq revname 0 5) "TINI-"))
                                                  (and (<= 6 length)
                                                       (equal (subseq revname 0 6) "RAELC-")))
                                              t))))

              (%stobj{rewrite} (symbolicate stobj %stobj '{rewrite}))
              (world (w state))
              (formals (loop$ :with interface := interface
                             :with formals := nil
                             :do (if (consp interface)
                                     (progn (setq formals (cons (getprop (car interface)
                                                                         'formals
                                                                         nil 'current-acl2-world
                                                                         world)
                                                                formals))
                                            (setq interface (cdr interface)))
                                     (return (reverse formals)))))

              (copier-events (make-copier-events %stobj stobj state)))
         `(encapsulate ()
            (local
              (in-theory
                (disable ,stobj$a-definitions)))

            (defabsstobj ,%stobj
              :foundation ,foundation
              :recognizer (,%recognizer :logic ,(second recognizers)
                                        :exec ,(third recognizers))
              :creator (,%creator :logic ,(second creators)
                                  :exec ,(third creators))
              :congruent-to ,stobj
              :non-executable t
              :exports ,(loop$ :for triple :in exports
                              :as %sym :in %interface
                              :as u :in %updaters
                              :as p :in %protect
                              :collect (append (list %sym
                                                     :logic (second triple)
                                                     :exec (third triple))
                                               (and u (list :updater u))
                                               (and p (list :protect t)))))

            (defthm ,%stobj{rewrite}
              (and (equal (,%recognizer ,stobj) (,recognizer ,stobj))
                   (equal (,%creator) (,creator))
                   ,@(loop$ :for %sym :in %interface
                           :as %args :in formals
                           :as sym :in interface
                           :as args :in formals
                           :collect (list 'equal
                                          (cons %sym %args)
                                          (cons sym args)))))

            (in-theory
              (disable ,%recognizer
                       ,%creator
                       ,@%interface))

            ,copier-events)))))
