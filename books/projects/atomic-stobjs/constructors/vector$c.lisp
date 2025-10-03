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
;;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS”
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
; (include-book "../lemmas/vector$c")
(include-book "../utilities/symbolicate")
(include-book "../utilities/with-books")
(include-book "../utilities/macros")
(include-book "../type-spec")


;;;; `ARRAY' Guard Predicates
(defun valid-array-dimensions-p (dimensions)
  ;; TODO: refactor into separate file
  (declare (xargs :guard t))
  (or (and (consp dimensions)
           (natp (car dimensions))
           (null (cdr dimensions)))
      (natp dimensions)))

(defthm valid-array-dimensions-p{compound-recognizer}
  ;; Q: Is this theorem useful?
  (implies (valid-array-dimensions-p dimensions)
           (or (natp dimensions)
               (and (consp dimensions)
                    (true-listp dimensions))))
  :rule-classes :compound-recognizer)


;;;; `DEFINE-ARRAY$C'
(defmacro define-array$c
    (array dimensions
     &key
       (element-type 't)
       (specialize-element-type 'nil)
       (initial-element 'nil)
       (resizable 'nil)

       (inline 'nil)
       (memoizable 'nil)
       (executable 'nil)

       (contents 'nil)
       (contents-recognizer 'nil)
       (recognizer 'nil)
       (creator 'nil)
       (fixer 'nil)
       (length 'nil)
       (resizer 'nil)
       (accessor 'nil)
       (updater 'nil)

       (debug 'nil))

  (declare (xargs :guard (and (symbolp array)
                              (valid-array-dimensions-p dimensions)
                              (if (acl2-type-spec-p element-type)
                                  (typep$ initial-element element-type)
                                  ;; Q: What's the best macro-guard for a value
                                  ;; that is expected to be a stobj name?  We
                                  ;; cannot actually check if it is a stobj name
                                  ;; until we are within an event's scope.
                                  ;; However, it is desirable to reject the
                                  ;; value eagerly if possible.
                                  (symbolp element-type))
                              (boolean-listp (list specialize-element-type
                                                   resizable
                                                   inline
                                                   memoizable
                                                   executable))
                              (symbol-listp (list contents
                                                  contents-recognizer
                                                  recognizer
                                                  creator
                                                  fixer
                                                  length
                                                  resizer
                                                  accessor
                                                  updater))
                              (booleanp debug))))

  (let* (;; TODO: allow defined constant default length
         (dimensions (if (consp dimensions)
                         dimensions
                         (list dimensions)))
         ;; TODO: check if element type is stobj via stobjp
         (element-type-is-stobj (not (acl2-type-spec-p element-type)))

         (contents (or contents
                       (symbolicate array array '-contents)))
         (contents-recognizer-stobj-default (symbolicate array contents 'p))
         (contents-recognizer (or contents-recognizer
                                  (symbolicate array contents (make-predicate-suffix contents))))
         (recognizer-stobj-default (symbolicate array array 'p))
         (recognizer (or recognizer
                         (symbolicate array array (make-predicate-suffix array))))
         (creator-stobj-default (symbolicate array 'create- array))
         (creator (or creator
                      (symbolicate array 'create- array)))
         (fixer (or fixer
                    (symbolicate array array '-fix)))
         (length-stobj-default (symbolicate array contents '-length))
         (length (or length
                     (symbolicate array array '-length)))
         (resizer-stobj-default (symbolicate array 'resize- contents))
         (resizer (or resizer
                      (symbolicate array array '-resize)))
         (accessor-stobj-default (symbolicate array contents 'i))
         (accessor (or accessor
                       (symbolicate array array '-ref)))
         (updater-stobj-default (symbolicate array 'update- contents 'i))
         (updater (or updater
                      (symbolicate array array '-set)))

         (doublets (append (and (not (eq contents-recognizer contents-recognizer-stobj-default))
                                `((,contents-recognizer-stobj-default ,contents-recognizer)))
                           (and (not (eq recognizer recognizer-stobj-default))
                                `((,recognizer-stobj-default ,recognizer)))
                           (and (not (eq creator creator-stobj-default))
                                `((,creator-stobj-default ,creator)))
                           (and (not (eq length length-stobj-default))
                                `((,length-stobj-default ,length)))
                           (and (not (eq resizer resizer-stobj-default))
                                `((,resizer-stobj-default ,resizer)))
                           (and (not (eq accessor accessor-stobj-default))
                                `((,accessor-stobj-default ,accessor)))
                           (and (not (eq updater updater-stobj-default))
                                `((,updater-stobj-default ,updater))))))

    `(with-output
       ,@(and (not debug)
              '#!acl2(:off (warning! observation prove event history proof-tree)
                           :summary-off (rules)
                           :gag-mode t))

       (make-event
         (let* ((array ',array)
                (dimensions ',dimensions)
                (default-length (car dimensions))
                (default-length-name
                 (symbolicate array '* array '-default-length*))
                (zp-default-length (zp default-length))

                (element-type ',element-type)
                (element-type-is-stobj (and ',element-type-is-stobj
                                            (stobj-p ',element-type)))
                (element-type-is-t (eq element-type t))
                (specialize-element-type ',specialize-element-type)
                (initial-element ',initial-element)
                (initial-element-name
                 (symbolicate array '* array '-initial-element*))
                (initial-element-is-nil (and (not element-type-is-stobj)
                                             (not initial-element)))
                (resizable ',resizable)

                (inline ',inline)
                (memoizable ',memoizable)
                (executable ',executable)

                (contents ',contents)
                (contents-recognizer ',contents-recognizer)
                (recognizer ',recognizer)
                (creator ',creator)
                (fixer ',fixer)
                (length ',length)
                (resizer ',resizer)
                (accessor ',accessor)
                (updater ',updater)

                (array-begin (symbolicate array array '-begin))
                (array-end (symbolicate array array '-end))

                (prologue
                 `((deflabel ,array-begin)

                   (defconst ,default-length-name ',default-length)

                   ,@(and (not element-type-is-stobj)
                          `((defconst ,initial-element-name ',initial-element)))

                   (defstobj ,array
                     (,contents :type (array ,element-type ,dimensions)
                                ,@(and (not element-type-is-stobj)
                                       `(:element-type
                                         ,(if specialize-element-type
                                              element-type
                                              t)
                                         :initially ,initial-element))
                                :resizable ,resizable)
                     :renaming ,',doublets
                     :inline ,inline
                     :non-memoizable ,(not memoizable)
                     :non-executable ,(not executable))))

                (array-theorems (symbolicate array array '-theorems))
                (epilogue
                 `((deflabel ,array-end)

                   (deftheory-static ,array-theorems
                     (set-difference-theories
                      (set-difference-theories
                       (current-theory ',array-end)
                       (current-theory ',array-begin))
                      (function-theory ',array-end)))

                   (in-theory
                     (union-theories (current-theory ',array-begin)
                                     (theory ',array-theorems)))))

                (contents-recognizer{compound-recognizer}
                 (symbolicate array contents-recognizer '{compound-recognizer}))
                (contents-recognizer-of-make-list-ac
                 (symbolicate array contents-recognizer '-of-make-list-ac))
                (contents-recognizer-of-resize-list
                 (symbolicate array contents-recognizer '-of-resize-list))
                (typep$-of-accessor (symbolicate array 'typep$-of- accessor))
                (typep$-of-accessor/lemma
                 (symbolicate array typep$-of-accessor '/lemma))
                (contents-recognizer-of-update-nth
                 (symbolicate array contents-recognizer '-of-update-nth))

                (recognizer{compound-recognizer}
                 (symbolicate array recognizer '{compound-recognizer}))
                (recognizer-of-creator
                 (symbolicate array recognizer '-of- creator))
                (recognizer-of-resizer
                 (symbolicate array recognizer '-of- resizer))
                (recognizer-of-updater
                 (symbolicate array recognizer '-of- updater))

                (recognizer-of-fixer (symbolicate array recognizer '-of- fixer))
                (fixer-when-recognizer
                 (symbolicate array fixer '-when- recognizer))
                (fixer-when-not-recognizer
                 (symbolicate array fixer '-when-not- recognizer))

                (length-of-creator (symbolicate array length '-of- creator))
                (length-of-resizer (symbolicate array length '-of- resizer))
                (length-of-updater (symbolicate array length '-of- updater))
                (length{rewrite} (symbolicate array length '{rewrite}))

                (resizer-of-creator (symbolicate array resizer '-of-creator))
                (resizer-of-length (symbolicate array resizer '-of- length))
                (resizer-of-length-free
                 (symbolicate array resizer-of-length '-free))
                (resizer-of-resizer (symbolicate array resizer '-of- resizer))
                (resizer-of-updater-keep
                 (symbolicate array resizer '-of- updater '-keep))
                (resizer-of-updater-drop
                 (symbolicate array resizer '-of- updater '-drop))
                (resizer{rewrite} (symbolicate array resizer '{rewrite}))

                (accessor-of-creator (symbolicate array accessor '-of- creator))
                (accessor-of-resizer-inner
                 (symbolicate array accessor '-of- resizer '-inner))
                (accessor-of-resizer-outer
                 (symbolicate array accessor '-of- resizer '-outer))
                (accessor-of-updater-same
                 (symbolicate array accessor '-of- updater '-same))
                (accessor-of-updater-diff
                 (symbolicate array accessor '-of- updater '-diff))
                (accessor{rewrite} (symbolicate array accessor '{rewrite}))

                (updater-of-creator (symbolicate array updater '-of- creator))
                (updater-of-resizer (symbolicate array updater '-of- resizer))
                (updater-of-accessor (symbolicate array updater '-of- accessor))
                (updater-of-accessor-free
                 (symbolicate array updater-of-accessor '-free))
                (updater-of-updater (symbolicate array updater '-of- updater))
                (updater-of-updater-same
                 (symbolicate array updater-of-updater '-same))
                (updater-of-updater-diff
                 (symbolicate array updater-of-updater '-diff))

                (body
                 `(with-books (("projects/atomic-stobjs/lemmas/std" :dir :system))

                    (local
                      (in-theory
                        (e/d (max)
                             (natp))))

                    ;; `CONTENTS-RECOGNIZER'
                    (defthm ,contents-recognizer{compound-recognizer}
                      (implies (,contents-recognizer ,contents)
                               (true-listp ,contents))
                      :rule-classes :compound-recognizer
                      :hints
                      (("Goal"
                        :induct (,contents-recognizer ,contents))))

                    (lprogn
                     (defthm ,contents-recognizer-of-make-list-ac
                       (equal (,contents-recognizer (make-list-ac n val ac))
                              ,(if element-type-is-t
                                   `(,contents-recognizer ac)
                                   `(and (or (zp n)
                                             ,(if element-type-is-stobj
                                                  `(,(stobj-recognizer ',element-type) val)
                                                  (typep$transform 'val ',element-type)))
                                         (,contents-recognizer ac)))))

                     ,@(and ',resizable
                            `((defthm ,contents-recognizer-of-resize-list
                                (implies (,contents-recognizer lst)
                                         ,(if element-type-is-t
                                              `(,contents-recognizer (resize-list lst n default-value))
                                              `(equal (,contents-recognizer (resize-list lst n default-value))
                                                      (or (<= (nfix n) (len lst))
                                                          ,(if element-type-is-stobj
                                                               `(,(stobj-recognizer ',element-type) default-value)
                                                               (typep$transform 'default-value ',element-type)))))))))

                     ,@(and (or resizable
                                (not zp-default-length))
                            (not element-type-is-t)
                            `((defthmd ,typep$-of-accessor/lemma
                                (implies (and (,contents-recognizer ,contents)
                                              (natp i)
                                              (< i (len ,contents)))
                                         ,(if element-type-is-stobj
                                              `(,(stobj-recognizer ',element-type)
                                                 (nth i ,contents))
                                              (typep$transform/member-fix `(nth i ,contents) ',element-type)))
                                :hints
                                (("Goal"
                                  :induct (nth i ,contents))))))

                     ,@(and (or resizable
                                (not zp-default-length))
                            `((defthm ,contents-recognizer-of-update-nth
                                ,(if element-type-is-t
                                     `(implies (,contents-recognizer l)
                                               (,contents-recognizer (update-nth key val l)))
                                     `(implies (and (,contents-recognizer l)
                                                    ,(if element-type-is-stobj
                                                         `(,(stobj-recognizer ',element-type) val)
                                                         (typep$transform/member-fix 'val ',element-type))
                                                    (<= key (len l)))
                                               (,contents-recognizer (update-nth key val l))))))))

                    ;; `RECOGNIZER'
                    (defthm ,recognizer{compound-recognizer}
                      (implies (,recognizer ,array)
                               (and (consp ,array)
                                    (true-listp ,array)))
                      :rule-classes :compound-recognizer)

                    (defthm ,recognizer-of-creator
                      (,recognizer (,creator)))

                    (defun-inline ,fixer (,array)
                      (declare (xargs :stobjs ,array))
                      (mbe :logic (if (,recognizer ,array)
                                      ,array
                                      (,creator))
                           :exec ,array))

                    (defthm ,recognizer-of-fixer
                      (,recognizer (,fixer ,array)))

                    (defthm ,fixer-when-recognizer
                      (implies (,recognizer ,array)
                               (equal (,fixer ,array) ,array)))

                    (defthm ,fixer-when-not-recognizer
                      (implies (not (,recognizer ,array))
                               (equal (,fixer ,array) (,creator))))

                    ,@(and ',resizable
                           `((defthm ,recognizer-of-resizer
                               (implies (,recognizer ,array)
                                        (,recognizer (,resizer l ,array))))))

                    ,@(and (or resizable
                               (not zp-default-length))
                           (not element-type-is-t)
                           `((defthm ,typep$-of-accessor
                               (implies (and (,recognizer ,array)
                                             (natp i)
                                             (< i ,(if ',resizable
                                                       `(,length ,array)
                                                       default-length-name)))
                                        ,(if element-type-is-stobj
                                             `(,(stobj-recognizer ',element-type)
                                                (,accessor i ,array))
                                             ;; TODO: in case of a `MEMBER'
                                             ;; form, you need to extract the
                                             ;; list, replace it with the symbol
                                             ;; `LIST' and add the (first)
                                             ;; hypothesis (setequiv list [the
                                             ;; list]). in case of
                                             ;; signed/unsigned-byte, do
                                             ;; something similar.  also, check
                                             ;; for similar cases among other
                                             ;; types.
                                             (typep$transform/member-fix `(,accessor i ,array) ',element-type)))
                               :hints
                               (("Goal"
                                 :use ((:instance ,typep$-of-accessor/lemma
                                                  (,contents (car ,array)))))))))

                    (defthm ,recognizer-of-updater
                      ,(if (and (not resizable)
                                zp-default-length)
                           `(not (,recognizer (,updater i v ,array)))
                           `(implies (and (,recognizer ,array)
                                          ,@(and (not element-type-is-t)
                                                 (if element-type-is-stobj
                                                     `((,(stobj-recognizer ',element-type) v))
                                                     `(,(typep$transform/member-fix 'v ',element-type))))
                                          (natp i)
                                          (< i ,(if ',resizable
                                                    `(,length ,array)
                                                    default-length-name)))
                                     (,recognizer (,updater i v ,array)))))

                    ;; `LENGTH'
                    ,@(if ',resizable
                          `((defthm ,length-of-creator
                              (equal (,length (,creator))
                                     ,default-length-name))

                            (with-books (("std/lists/resize-list" :dir :system))
                              (defthm ,length-of-resizer
                                (implies (natp l)
                                         (equal (,length (,resizer l ,array))
                                                l))))

                            (defthm ,length-of-updater
                              (implies (and (natp i)
                                            (< i (,length ,array)))
                                       (equal (,length (,updater i v ,array))
                                              (,length ,array)))))

                          `((defthm ,length{rewrite}
                              (equal (,length ,array)
                                     ,default-length-name))))

                    ;; `RESIZER'
                    ,@(if ',resizable
                          `((with-books (("std/lists/resize-list" :dir :system)
                                         ("std/lists/list-fix" :dir :system))
                              (defthm ,resizer-of-creator
                                (implies (equal l ,default-length-name)
                                         (equal (,resizer l (,creator))
                                                (,creator))))

                              (defthmd ,resizer-of-length-free
                                (implies (and (,recognizer ,array)
                                              (equal l (,length ,array)))
                                         (equal (,resizer l ,array)
                                                ,array)))

                              (defthm ,resizer-of-length
                                (implies (,recognizer ,array)
                                         (equal (,resizer (,length ,array) ,array)
                                                ,array))
                                :hints
                                (("Goal"
                                  :in-theory (e/d (,resizer-of-length-free)
                                                  (,recognizer
                                                   ,length
                                                   ,resizer)))))

                              (defthm ,resizer-of-resizer
                                (implies (and (,recognizer ,array)
                                              (natp l)
                                              (natp m)
                                              (or (<= l m)
                                                  (<= (,length ,array) m)))
                                         (equal (,resizer l (,resizer m ,array))
                                                (,resizer l ,array)))
                                :hints
                                (("Goal"
                                  :in-theory (disable acl2::resize-list-of-resize-list
                                                      resize-list)
                                  :use ((:instance acl2::resize-list-of-resize-list
                                                   (lst (car ,array))
                                                   (n m)
                                                   (d ,(if element-type-is-stobj
                                                           `(,(stobj-creator ',element-type))
                                                           initial-element-name))
                                                   (m l)
                                                   (e ,(if element-type-is-stobj
                                                           `(,(stobj-creator ',element-type))
                                                           initial-element-name)))))))

                              (defthm ,resizer-of-updater-keep
                                (implies (and (natp i)
                                              (natp l)
                                              (< i l)
                                              (< i (,length ,array)))
                                         (equal (,resizer l (,updater i v ,array))
                                                (,updater i v (,resizer l ,array))))
                                :hints
                                (("Goal"
                                  :in-theory (disable acl2::resize-list-of-update-nth-keep)
                                  :use ((:instance acl2::resize-list-of-update-nth-keep
                                                   (key i)
                                                   (val v)
                                                   (l (car ,array))
                                                   (n l)
                                                   (default-value ,(if element-type-is-stobj
                                                                       `(,(stobj-creator ',element-type))
                                                                       initial-element-name))))
                                  :expand ((acl2::repeat l ,(if element-type-is-stobj
                                                                `(,(stobj-creator ',element-type))
                                                                initial-element-name))))))

                              (defthm ,resizer-of-updater-drop
                                (implies (and (natp i)
                                              (natp l)
                                              (<= l i)
                                              (< i (,length ,array)))
                                         (equal (,resizer l (,updater i v ,array))
                                                (,resizer l ,array)))
                                :hints
                                (("Goal"
                                  :in-theory (disable acl2::resize-list-of-update-nth-drop)
                                  :use ((:instance acl2::resize-list-of-update-nth-drop
                                                   (key i)
                                                   (val v)
                                                   (l (car ,array))
                                                   (n l)
                                                   (default-value ,(if element-type-is-stobj
                                                                       `(,(stobj-creator ',element-type))
                                                                       initial-element-name))))
                                  :expand ((acl2::repeat l ,(if element-type-is-stobj
                                                                `(,(stobj-creator ',element-type))
                                                                initial-element-name))))))))

                          `((defthm ,resizer{rewrite}
                              (equal (,resizer l ,array)
                                     ,array))))

                    ;; `ACCESSOR'
                    ,@(if (or resizable
                              (not zp-default-length))
                          `((with-books (("std/lists/nth" :dir :system))
                              (defthm ,accessor-of-creator
                                ,(if (or zp-default-length
                                         initial-element-is-nil)
                                     `(not (,accessor i (,creator)))
                                     `(implies (and (natp i)
                                                    (< i ,default-length-name))
                                               (equal (,accessor i (,creator))
                                                      ,(if element-type-is-stobj
                                                           `(,(stobj-creator ',element-type))
                                                           initial-element-name))))
                                :hints
                                (("Goal"
                                  :in-theory (disable nth)))))

                            ,@(and ',resizable
                                   `((with-books (("std/lists/resize-list" :dir :system))
                                       (defthm ,accessor-of-resizer-inner
                                         (implies (and (natp i)
                                                       (natp l)
                                                       (< i l)
                                                       (< i (,length ,array)))
                                                  (equal (,accessor i (,resizer l ,array))
                                                         (,accessor i ,array)))
                                         :hints
                                         (("Goal"
                                           :in-theory (disable ,@(and element-type-is-stobj
                                                                      `(,(stobj-creator ',element-type)))))))

                                       (with-books (("std/lists/nth" :dir :system))
                                         (defthm ,accessor-of-resizer-outer
                                           (implies (and (natp i)
                                                         (natp l)
                                                         (< i l)
                                                         (<= (,length ,array) i))
                                                    (equal (,accessor i (,resizer l ,array))
                                                           ,(if element-type-is-stobj
                                                                `(,(stobj-creator ',element-type))
                                                                initial-element-name)))
                                           :hints
                                           (("Goal"
                                             :in-theory (disable ,@(and element-type-is-stobj
                                                                        `(,(stobj-creator ',element-type)))))))))))

                            (defthm ,accessor-of-updater-same
                              (implies (equal i j)
                                       (equal (,accessor i (,updater j v ,array))
                                              v)))

                            (defthm ,accessor-of-updater-diff
                              (implies (and (not (equal i j))
                                            (natp i)
                                            (natp j))
                                       (equal (,accessor i (,updater j v ,array))
                                              (,accessor i ,array)))))

                          `((with-books (("std/lists/len" :dir :system))
                              (defthm ,accessor{rewrite}
                                (implies (,recognizer ,array)
                                         (not (,accessor i ,array)))))))

                    ;; `UPDATER'
                    ,@(and (or resizable
                               (not zp-default-length))
                           `((with-books (("std/lists/update-nth" :dir :system)
                                          ("std/lists/repeat" :dir :system))
                               ,@(and (not zp-default-length)
                                      `((defthm ,updater-of-creator
                                          (implies (and (equal v ,(if element-type-is-stobj
                                                                      `(,(stobj-creator ',element-type))
                                                                      initial-element-name))
                                                        (natp i)
                                                        (< i ,default-length-name))
                                                   (equal (,updater i v (,creator))
                                                          (,creator)))
                                          :hints
                                          (("Goal"
                                            :in-theory (disable ,@(and element-type-is-stobj
                                                                       `(,(stobj-creator ',element-type)))))))))

                               ,@(and ',resizable
                                      `((defthm ,updater-of-resizer
                                          (implies (and (natp i)
                                                        (natp l)
                                                        (< i l)
                                                        (equal v (if (< i (,length ,array))
                                                                     (,accessor i ,array)
                                                                     ,(if element-type-is-stobj
                                                                          `(,(stobj-creator ',element-type))
                                                                          initial-element-name))))
                                                   (equal (,updater i v (,resizer l ,array))
                                                          (,resizer l ,array)))
                                          :hints
                                          (("Goal"
                                            :in-theory (disable ,@(and element-type-is-stobj
                                                                       `(,(stobj-creator ',element-type)))))))))

                               (defthmd ,updater-of-accessor-free
                                 (implies (and (,recognizer ,array)
                                               (natp i)
                                               (< i ,(if ',resizable
                                                         `(,length ,array)
                                                         default-length-name))
                                               (equal v (,accessor i ,array)))
                                          (equal (,updater i v ,array)
                                                 ,array))
                                 :hints
                                 (("Goal"
                                   :in-theory (disable acl2::update-nth-of-nth-free)
                                   :use ((:instance acl2::update-nth-of-nth-free
                                                    (n i)
                                                    (x (car ,array))
                                                    (free (,accessor i ,array)))))))

                               (defthm ,updater-of-accessor
                                 (implies (and (equal i j)
                                               (,recognizer ,array)
                                               (natp i)
                                               (< i ,(if ',resizable
                                                         `(,length ,array)
                                                         default-length-name)))
                                          (equal (,updater i (,accessor j ,array) ,array)
                                                 ,array))
                                 :hints
                                 (("Goal"
                                   :in-theory (disable ,recognizer
                                                       ,length
                                                       ,accessor
                                                       ,updater)
                                   :use ((:instance ,updater-of-accessor-free
                                                    (v (,accessor j ,array)))))))

                               (defthm ,updater-of-updater-same
                                 (implies (equal i j)
                                          (equal (,updater i v (,updater j w ,array))
                                                 (,updater i v ,array)))
                                 :hints
                                 (("Goal"
                                   :in-theory (disable acl2::update-nth-of-update-nth-same)
                                   :use ((:instance acl2::update-nth-of-update-nth-same
                                                    (n i)
                                                    (v1 v)
                                                    (v2 w)
                                                    (x (car ,array)))))))

                               (defthm ,updater-of-updater-diff
                                 (implies (and (not (equal i j))
                                               (natp i)
                                               (natp j))
                                          (equal (,updater i v (,updater j w ,array))
                                                 (,updater j w (,updater i v ,array))))
                                 :rule-classes
                                 ((:rewrite :loop-stopper ((i j ,updater))))
                                 :hints
                                 (("Goal"
                                   :in-theory (disable acl2::update-nth-of-update-nth-diff)
                                   :use ((:instance acl2::update-nth-of-update-nth-diff
                                                    (n1 i)
                                                    (n2 j)
                                                    (v1 v)
                                                    (v2 w)
                                                    (x (car ,array)))))))))))))
           `(progn
              ,@prologue

              ,body

              ,@epilogue))))))
