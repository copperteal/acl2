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


;;;; Prologue
(in-package "ATOMIC-STOBJS")

;;; cert.pl
#||
(include-book "std/top" :dir :system)
(include-book "../lemmas/top")
||#

(include-book "../type-spec")
(include-book "../utilities/symbolicate")
(include-book "../utilities/with-books")
(include-book "../utilities/macros")
(include-book "../accessors/top")

(deflabel define-array-begin)


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
(include-book "vector$c")


;;;; `DEFINE-ARRAY$A'
(defmacro define-array$a
    (array dimensions
     &key
       (element-recognizer 'nil)
       (element-fixer 'nil)
       (element 'x)
       (initial-element 'nil)
       (resizable 'nil)

       (recognizer 'nil)
       (creator 'nil)
       (fixer 'nil)
       (length 'nil)
       (resizer 'nil)
       (accessor 'nil)
       (updater 'nil)

       (testp 'nil)
       (debug 'nil))

  (declare (xargs :guard (and (symbolp array)
                              (valid-array-dimensions-p dimensions)
                              (symbol-listp (list element-recognizer
                                                  element-fixer
                                                  element))
                              (or (and (not element-recognizer)
                                       (not element-fixer))
                                  (and element-recognizer
                                       element-fixer))
                              (booleanp resizable)
                              (symbol-listp (list recognizer
                                                  fixer
                                                  creator
                                                  length
                                                  resizer
                                                  accessor
                                                  updater))
                              (booleanp testp)
                              (booleanp debug))))

  (let* ((array-begin (symbolicate array array '-begin))
         (array-end (symbolicate array array '-end))
         (array-theorems (symbolicate array array '-theorems))
         (array-definitions (symbolicate array array '-definitions))
         (array-aggressive (symbolicate array array '-aggressive))

         (default-length (if (consp dimensions)
                             (car dimensions)
                             dimensions))
         (default-length-name (symbolicate array '* array '-default-length*))
         (zp-default-length (zp default-length))

         (array-element-guard (symbolicate array array '-element-guard))
         (initial-element-name (symbolicate array '* array '-initial-element*))

         (recognizer (or recognizer
                         (symbolicate array array (make-predicate-suffix array))))
         (fixer (or fixer
                    (symbolicate array array '-fix)))
         (creator (or creator
                      (symbolicate array 'create- array)))
         (length (or length
                     (symbolicate array array '-length)))
         (resizer (or resizer
                      (symbolicate array array '-resize)))
         (accessor (or accessor
                       (symbolicate array array '-ref)))
         (updater (or updater
                      (symbolicate array array '-set)))

         (recognizer-aux (symbolicate array array '-aux-p))
         (recognizer-aux{compound-recognizer}
          (symbolicate array recognizer-aux '{compound-recognizer}))
         (recognizer-aux-of-resize-list (symbolicate array recognizer-aux '-of-resize-list))
         (recognizer-aux-of-make-list-ac (symbolicate array recognizer-aux '-of-make-list-ac))
         (recognizer-aux-of-repeat (symbolicate array recognizer-aux '-of-repeat))
         (recognizer-aux-of-update-nth (symbolicate array recognizer-aux '-of-update-nth))

         (recognizer{compound-recognizer} (symbolicate array recognizer '{compound-recognizer}))
         (recognizer-of-resize-list (symbolicate array recognizer '-of-resize-list))
         (recognizer-of-make-list-ac (symbolicate array recognizer '-of-make-list-ac))
         (recognizer-of-repeat (symbolicate array recognizer '-of-repeat))
         (recognizer-of-update-nth (symbolicate array recognizer '-of-update-nth))
         (recognizer-of-creator (symbolicate array recognizer '-of- creator))
         (recognizer-of-fixer (symbolicate array recognizer '-of- fixer))
         (recognizer-of-resizer (symbolicate array recognizer '-of- resizer))
         (recognizer-of-updater (symbolicate array recognizer '-of- updater))

         (fixer-when-recognizer (symbolicate array fixer '-when- recognizer))
         (fixer-when-not-recognizer (symbolicate array fixer '-when-not-recognizer))

         (length-when-not-recognizer (symbolicate array length '-when-not- recognizer))
         (length-of-creator (symbolicate array length '-of- creator))
         (length-of-fixer (symbolicate array length '-of- fixer))
         (length-of-resizer (symbolicate array length '-of- resizer))
         (length-of-updater (symbolicate array length '-of- updater))
         (length{rewrite} (symbolicate array length '{rewrite}))

         (resizer-when-not-recognizer (symbolicate array resizer '-when-not- recognizer))
         (resizer-of-nfix (symbolicate array resizer '-of-nfix))
         (resizer-when-zp (symbolicate array resizer '-when-zp))
         (resizer-of-creator (symbolicate array resizer '-of- creator))
         (resizer-of-fixer (symbolicate array resizer '-of-fixer))
         (resizer-of-length (symbolicate array resizer '-of- length))
         (resizer-of-length-free (symbolicate array resizer-of-length '-free))
         (resizer-of-resizer (symbolicate array resizer '-of- resizer))
         (resizer-of-resizer{forced} (symbolicate array resizer-of-resizer '{forced}))
         (resizer-of-updater (symbolicate array resizer '-of- updater))
         (resizer-of-updater-keep (symbolicate array resizer-of-updater '-keep))
         (resizer-of-updater-drop (symbolicate array resizer-of-updater '-drop))
         (resizer{rewrite} (symbolicate array resizer '{rewrite}))

         (accessor-when-not-recognizer (symbolicate array accessor '-when-not- recognizer))
         (accessor-of-nfix (symbolicate array accessor '-of-nfix))
         (accessor-when-zp (symbolicate array accessor '-when-zp))
         (accessor-of-creator (symbolicate array accessor '-of- creator))
         (accessor-of-fixer (symbolicate array accessor '-of- fixer))
         (accessor-of-resizer (symbolicate array accessor '-of- resizer))
         (accessor-of-updater (symbolicate array accessor '-of- updater))
         (accessor-of-updater-same (symbolicate array accessor-of-updater '-same))
         (accessor-of-updater-diff (symbolicate array accessor-of-updater '-diff))
         (accessor-when-large (symbolicate array accessor '-when-large))
         (accessor{rewrite} (symbolicate array accessor '{rewrite}))

         (updater-when-not-recognizer (symbolicate array updater '-when-not- recognizer))
         (updater-of-nfix (symbolicate array updater '-of-nfix))
         (updater-when-zp (symbolicate array updater '-when-zp))
         (updater-when-not-element-recognizer (symbolicate array updater '-when-not- element-recognizer))
         (updater-of-creator (symbolicate array updater '-of- creator))
         (updater-of-fixer (symbolicate array updater '-of- fixer))
         (updater-of-resizer (symbolicate array updater '-of- resizer))
         (updater-of-accessor (symbolicate array updater '-of- accessor))
         (updater-of-accessor-free (symbolicate array updater-of-accessor '-free))
         (updater-of-updater (symbolicate array updater '-of- updater))
         (updater-of-updater-same (symbolicate array updater-of-updater '-same))
         (updater-of-updater-diff (symbolicate array updater-of-updater '-diff))
         (updater-when-large (symbolicate array updater '-when-large))
         (updater{rewrite} (symbolicate array updater '{rewrite}))

         (%array (symbolicate array '% array))
         (array-contents-equal (symbolicate array array '-contents-equal))
         (array-contents-equal-necc (symbolicate array array-contents-equal '-necc))
         (array-equal (symbolicate array array '-equal))
         (array-equal{forward-chaining} (symbolicate array array-equal '{forward-chaining}))
         (array-equal{forward-chaining}-lemma-1 (symbolicate array array-equal{forward-chaining} '-lemma-1))
         (array-equal{forward-chaining}-lemma-2 (symbolicate array array-equal{forward-chaining} '-lemma-2)))

    `(with-output
       ,@(and (not debug)
              '#!acl2(:off (warning! observation prove event history proof-tree)
                           :summary-off (rules)
                           :gag-mode t))

       (make-event
         (let* ((element-type-is-stobj (stobj-p ',element))
                (element$a (stobj$a-lookup ',element))
                (element-recognizer (if element$a
                                        (stobj$a-recognizer element$a)
                                        ',element-recognizer))
                (element-fixer (if element$a
                                   (stobj$a-fixer element$a)
                                   ',element-fixer))
                (element-recognizer-of-nth-when-recognizer-aux
                 (symbolicate ',array element-recognizer '-of-nth-when- ',recognizer-aux))
                (element-recognizer-of-nth-when-recognizer
                 (symbolicate ',array element-recognizer '-of-nth-when- ',recognizer))
                (element-recognizer-of-accessor (symbolicate ',array element-recognizer '-of- ',accessor))
                (updater-of-element-fixer (symbolicate ',array ',updater '-of- element-fixer))
                (updater-of-element-fixer (if (eq updater-of-element-fixer ',updater-of-nfix)
                                              (symbolicate ',array ',updater-of-nfix "-1")
                                              updater-of-element-fixer))
                (updater-of-nfix (if (eq updater-of-element-fixer ',updater-of-nfix)
                                     (symbolicate ',array ',updater-of-nfix "-0")
                                     ',updater-of-nfix))
                (prologue
                 `((deflabel ,',array-begin)

                   (defconst ,',default-length-name ',',default-length)

                   ,@(and (not element-type-is-stobj)
                          `((defconst ,',initial-element-name ',',initial-element)))))
                (epilogue
                 '((deflabel ,array-end)

                   (deftheory-static ,array-theorems
                     (set-difference-theories
                      (set-difference-theories
                       (current-theory ',array-end)
                       (current-theory ',array-begin))
                      (union-theories (function-theory ',array-end)
                                      '(,@(and element-recognizer
                                               (or resizable
                                                   (not zp-default-length))
                                               `((:i ,(if resizable
                                                          recognizer
                                                          recognizer-aux))))))))

                   (deftheory-static ,array-definitions
                     (set-difference-theories
                      (set-difference-theories
                       (set-difference-theories
                        (current-theory ',array-end)
                        (current-theory ',array-begin))
                       (theory ',array-theorems))
                      '(,array-contents-equal)))

                   (deftheory-static ,array-aggressive
                     ',(append (and resizable
                                    (list length-when-not-recognizer
                                          resizer-when-not-recognizer
                                          resizer-when-zp
                                          resizer-of-length-free
                                          resizer-of-resizer{forced}
                                          resizer-of-updater))
                               (and (or resizable
                                        (not zp-default-length))
                                    (list accessor-when-not-recognizer
                                          accessor-when-zp
                                          accessor-when-large
                                          accessor-of-updater
                                          updater-when-not-recognizer
                                          updater-when-zp
                                          updater-when-large
                                          updater-of-accessor-free
                                          updater-of-updater))
                               (and (or resizable
                                        (not zp-default-length))
                                    element-recognizer
                                    (list updater-when-not-element-recognizer))))

                   (in-theory
                     (union-theories (current-theory ',array-begin)
                                     (theory ',array-theorems)))
                   (in-theory
                     (enable ,array-contents-equal))))
                (initial-element (cond
                                   (',testp
                                    ',initial-element)
                                   (element-type-is-stobj
                                    `(,(stobj-creator ',element)))
                                   (t
                                    ',initial-element-name)))
                (body
                 `(with-books (("std/basic/nfix" :dir :system)
                               ("projects/atomic-stobjs/lemmas/std" :dir :system)
                               ("projects/atomic-stobjs/lemmas/define-array-lemmas" :dir :system))

                    ,@(and (or (and element-recognizer
                                    element-fixer)
                               element-type-is-stobj)
                           `((local
                               (defthm ,',array-element-guard
                                 (and ,@(and (and element-recognizer
                                                  element-fixer)
                                             `((booleanp (,element-recognizer ,',element))
                                               (,element-recognizer ,initial-element)
                                               (,element-recognizer (,element-fixer ,',element))
                                               (implies (,element-recognizer ,',element)
                                                        (equal (,element-fixer ,',element) ,',element))
                                               (implies (not (,element-recognizer ,',element))
                                                        (equal (,element-fixer ,',element) ,initial-element))))
                                      ,@(and element-type-is-stobj
                                             `((equal ,',initial-element ,initial-element))))
                                 :rule-classes
                                 (,@(and ',(and element-recognizer
                                                element-fixer)
                                         `((:rewrite :corollary
                                                     (booleanp (,element-recognizer ,',element)))
                                           (:rewrite :corollary
                                                     (,element-recognizer (,element-fixer ,',element)))
                                           (:rewrite :corollary
                                                     (implies (,element-recognizer ,',element)
                                                              (equal (,element-fixer ,',element) ,',element)))
                                           (:rewrite :corollary
                                                     (implies (not (,element-recognizer ,',element))
                                                              (equal (,element-fixer ,',element) ,initial-element))))))
                                 :hints
                                 (("Goal"
                                   ,@(and (and ',(not testp)
                                               element-recognizer
                                               element-fixer)
                                          `(:in-theory (disable ,element-recognizer
                                                                ,element-fixer)))))))))

                    (local
                      (in-theory
                        (e/d (max)
                             (nfix
                              len
                              ,@(and (and ',(not testp)
                                          element-recognizer
                                          element-fixer)
                                     `((:d ,element-recognizer)
                                       (:d ,element-fixer)
                                       (:e ,element-fixer)))))))

                    ,@(and ',(not resizable)
                           ',(not zp-default-length)
                           element-recognizer
                           `((defun ,',recognizer-aux (,',array)
                               (declare (xargs :guard t))
                               (if (consp ,',array)
                                   (and (,element-recognizer (car ,',array))
                                        (,',recognizer-aux (cdr ,',array)))
                                   (null ,',array)))

                             (lprogn
                               (defthm ,',recognizer-aux{compound-recognizer}
                                 (implies (,',recognizer-aux ,',array)
                                          (true-listp ,',array))
                                 :rule-classes :compound-recognizer)

                               (defthm ,',recognizer-aux-of-resize-list
                                 (implies (,',recognizer-aux lst)
                                          (equal (,',recognizer-aux (resize-list lst n default-value))
                                                 (or (<= (nfix n) (len lst))
                                                     (,element-recognizer default-value))))
                                 :hints
                                 (("Goal"
                                   :use ((:functional-instance define-array::recognizer-of-resize-list
                                                               (define-array::recognizer ,',recognizer-aux)
                                                               (define-array::element-recognizer ,element-recognizer))))))

                               (defthm ,',recognizer-aux-of-make-list-ac
                                 (equal (,',recognizer-aux (make-list-ac n val ac))
                                        (and (or (zp n)
                                                 (,element-recognizer val))
                                             (,',recognizer-aux ac))))

                               (with-books (("std/lists/repeat" :dir :system))
                                 (defthm ,',recognizer-aux-of-repeat
                                   (equal (,',recognizer-aux (acl2::repeat n x))
                                          (or (zp n)
                                              (,element-recognizer x)))
                                   :hints
                                   (("Goal"
                                     :in-theory (disable ,',recognizer-aux-of-make-list-ac)
                                     :use ((:instance ,',recognizer-aux-of-make-list-ac
                                                      (val x)
                                                      (ac ())))))))

                               (defthm ,element-recognizer-of-nth-when-recognizer-aux
                                 (implies (and (,',recognizer-aux l)
                                               (< (nfix n) (len l)))
                                          (,element-recognizer (nth n l)))
                                 :hints
                                 (("Goal"
                                   :use ((:functional-instance define-array::element-recognizer-of-nth-when-recognizer
                                                               (define-array::recognizer ,',recognizer-aux)
                                                               (define-array::element-recognizer ,element-recognizer))))))

                               (defthm ,',recognizer-aux-of-update-nth
                                 (implies (and (,',recognizer-aux l)
                                               (,element-recognizer val)
                                               (<= key (len l)))
                                          (,',recognizer-aux (update-nth key val l)))
                                 :hints
                                 (("Goal"
                                   :use ((:functional-instance define-array::recognizer-of-update-nth
                                                               (define-array::recognizer ,',recognizer-aux)
                                                               (define-array::element-recognizer ,element-recognizer)))))))))

                    (defun ,',recognizer (,',array)
                      (declare (xargs :guard t))
                      ,(cond
                         (',resizable
                          (if element-recognizer
                              `(if (consp ,',array)
                                   (and (,element-recognizer (car ,',array))
                                        (,',recognizer (cdr ,',array)))
                                   (null ,',array))
                              `(true-listp ,',array)))
                         (',zp-default-length
                          `(null ,',array))
                         (t
                          `(and (= (len ,',array) ,',default-length-name)
                                ,(if element-recognizer
                                     `(,',recognizer-aux ,',array)
                                     `(true-listp ,',array))))))

                    (defthm ,',recognizer{compound-recognizer}
                      (implies (,',recognizer ,',array)
                               ,(cond
                                  (',resizable
                                   `(true-listp ,',array))
                                  (',zp-default-length
                                   `(null ,',array))
                                  (t
                                   `(and (consp ,',array)
                                         (true-listp ,',array)))))
                      :rule-classes :compound-recognizer)

                    (defun ,',creator ()
                      (declare (xargs :guard t))
                      ,(if ',zp-default-length
                           '()
                           `(make-list ,',default-length-name
                                       :initial-element ,(if element-type-is-stobj
                                                             ',initial-element
                                                             initial-element))))

                    (in-theory
                      (disable (:e ,',creator)))

                    (defun ,',fixer (,',array)
                      (declare (xargs :guard (,',recognizer ,',array)))
                      (if (,',recognizer ,',array)
                          ,',array
                          (,',creator)))

                    (defun ,',length (,',array)
                      (declare (xargs :guard (,',recognizer ,',array))
                               ,@(and ',(not resizable)
                                      `((ignore ,',array))))
                      ,(if ',resizable
                           `(len (,',fixer ,',array))
                           ',default-length-name))

                    (defun ,',resizer (l ,',array)
                      (declare (xargs :guard (and (natp l)
                                                  (,',recognizer ,',array)))
                               ,@(and ',(not resizable)
                                      '((ignore l))))
                      ,(if ',resizable
                           `(let ((,',array (,',fixer ,',array))
                                  (l (mbe :logic (nfix l)
                                          :exec l)))
                              (resize-list ,',array l ,(if element-type-is-stobj
                                                           ',initial-element
                                                           initial-element)))
                           `(,',fixer ,',array)))

                    (with-books (("std/lists/len" :dir :system))
                      (defun ,',accessor (i ,',array)
                        (declare (xargs :guard (and (natp i)
                                                    (,',recognizer ,',array)
                                                    (< i (,',length ,',array))))
                                 ,@(and ',(not resizable)
                                        ',zp-default-length
                                        `((ignore i ,',array))))
                        ,(if ',(and (not resizable)
                                    zp-default-length)
                             (if element-type-is-stobj
                                 ',initial-element
                                 initial-element)
                             `(let ((i (mbe :logic (nfix i)
                                            :exec i))
                                    (,',array (,',fixer ,',array)))
                                (if (< i (,',length ,',array))
                                    ,(if element-fixer
                                         `(,element-fixer (nth i ,',array))
                                         `(nth i ,',array))
                                    ,(if element-type-is-stobj
                                         ',initial-element
                                         initial-element))))))

                    (defun ,',updater (i ,',element ,',array)
                      (declare (xargs :guard (and (natp i)
                                                  ,@(and element-recognizer
                                                         `((,',element-recognizer ,',element)))
                                                  (,',recognizer ,',array)
                                                  (< i (,',length ,',array))))
                               ,@(and ',(not resizable)
                                      ',zp-default-length
                                      `((ignore i ,',element ,',array))))
                      ,(if ',(and (not resizable)
                                  zp-default-length)
                           `(,',creator)
                           `(let ((i (mbe :logic (nfix i)
                                          :exec i))
                                  ,@(and element-fixer
                                         `((,',element (,element-fixer ,',element))))
                                  (,',array (,',fixer ,',array)))
                              (if (< i (,',length ,',array))
                                  (update-nth i ,',element ,',array)
                                  ,',array))))

                    ,@(and element-recognizer
                           `((local
                               (defthm ,element-recognizer-of-nth-when-recognizer
                                 (implies (and (,',recognizer l)
                                               (< (nfix n) (,',length l)))
                                          (,element-recognizer (nth n l)))
                                 :hints
                                 (("Goal"
                                   :use ((:functional-instance define-array::element-recognizer-of-nth-when-recognizer
                                                               (define-array::recognizer ,',recognizer)
                                                               (define-array::element-recognizer ,element-recognizer)))))))))

                    ;; `RECOGNIZER'
                    ,@(and ',resizable
                           element-recognizer
                           `((lprogn
                               (defthm ,',recognizer-of-resize-list
                                 (implies (,',recognizer lst)
                                          (equal (,',recognizer (resize-list lst n default-value))
                                                 (or (<= (nfix n) (len lst))
                                                     (,element-recognizer default-value))))
                                 :hints
                                 (("Goal"
                                   :use ((:functional-instance define-array::recognizer-of-resize-list
                                                               (define-array::recognizer ,',recognizer)
                                                               (define-array::element-recognizer ,element-recognizer))))))

                               (defthm ,',recognizer-of-make-list-ac
                                 (equal (,',recognizer (make-list-ac n val ac))
                                        (and (or (zp n)
                                                 (,element-recognizer val))
                                             (,',recognizer ac))))

                               (with-books (("std/lists/repeat" :dir :system))
                                 (defthm ,',recognizer-of-repeat
                                   (equal (,',recognizer (acl2::repeat n x))
                                          (or (zp n)
                                              (,element-recognizer x)))
                                   :hints
                                   (("Goal"
                                     :in-theory (disable ,',recognizer-of-make-list-ac)
                                     :use ((:instance ,',recognizer-of-make-list-ac
                                                      (val x)
                                                      (ac ())))))))

                               (defthm ,',recognizer-of-update-nth
                                 (implies (and (,',recognizer l)
                                               (,element-recognizer val)
                                               (<= key (len l)))
                                          (,',recognizer (update-nth key val l)))
                                 :hints
                                 (("Goal"
                                   :use ((:functional-instance define-array::recognizer-of-update-nth
                                                               (define-array::recognizer ,',recognizer)
                                                               (define-array::element-recognizer ,element-recognizer)))))))))

                    (defthm ,',recognizer-of-creator
                      (,',recognizer (,',creator)))

                    (defthm ,',recognizer-of-fixer
                      (,',recognizer (,',fixer ,',array)))

                    ,@(and ',resizable
                           `((defthm ,',recognizer-of-resizer
                               (,',recognizer (,',resizer l ,',array)))))

                    ,@(and element-recognizer
                           `((defthm ,element-recognizer-of-accessor
                               (,element-recognizer (,',accessor i ,',array)))))

                    ,@(and ',(or resizable
                                 (not zp-default-length))
                           `((defthm ,',recognizer-of-updater
                               (,',recognizer (,',updater i ,',element ,',array)))))

                    ;; `FIXER'
                    (defthm ,',fixer-when-recognizer
                      (implies (,',recognizer ,',array)
                               (equal (,',fixer ,',array) ,',array)))

                    (defthm ,',fixer-when-not-recognizer
                      (implies (not (,',recognizer ,',array))
                               (equal (,',fixer ,',array) (,',creator))))

                    ;; `LENGTH'
                    ,@(if ',resizable
                          `((defthmd ,',length-when-not-recognizer
                              (implies (not (,',recognizer ,',array))
                                       (equal (,',length ,',array)
                                              ,',default-length-name)))

                            (defthm ,',length-of-creator
                              (equal (,',length (,',creator))
                                     ,',default-length-name))

                            (defthm ,',length-of-fixer
                              (equal (,',length (,',fixer ,',array))
                                     (,',length ,',array)))

                            (with-books (("std/lists/resize-list" :dir :system)
                                         ("std/lists/repeat" :dir :system))
                              (defthm ,',length-of-resizer
                                (equal (,',length (,',resizer l ,',array))
                                       (nfix l))))

                            (defthm ,',length-of-updater
                              (equal (,',length (,',updater i ,',element ,',array))
                                     (,',length ,',array))
                              :hints
                              (("Goal"
                                :in-theory (disable update-nth)))))

                          `((defthm ,',length{rewrite}
                              (equal (,',length ,',array)
                                     ,',default-length-name))))

                    ;; `RESIZER'
                    ,@(if ',resizable
                          `((with-books (("std/lists/resize-list" :dir :system)
                                         ("std/lists/list-fix" :dir :system))
                              (defthmd ,',resizer-when-not-recognizer
                                (implies (not (,',recognizer ,',array))
                                         (equal (,',resizer l ,',array)
                                                (,',resizer l (,',creator)))))

                              (defthm ,',resizer-of-nfix
                                (equal (,',resizer (nfix l) ,',array)
                                       (,',resizer l ,',array)))

                              (defthmd ,',resizer-when-zp
                                (implies (and (syntaxp (not (quotep l)))
                                              (zp l))
                                         (equal (,',resizer l ,',array)
                                                (,',resizer 0 ,',array))))

                              (defthm ,',resizer-of-creator
                                (implies (equal (nfix l) ,',default-length-name)
                                         (equal (,',resizer l (,',creator))
                                                (,',creator))))

                              (defthm ,',resizer-of-fixer
                                (equal (,',resizer l (,',fixer ,',array))
                                       (,',resizer l ,',array)))

                              (defthmd ,',resizer-of-length-free
                                (implies (equal (nfix l) (,',length ,',array))
                                         (equal (,',resizer l ,',array)
                                                (,',fixer ,',array))))

                              (defthm ,',resizer-of-length
                                (equal (,',resizer (,',length ,',array) ,',array)
                                       (,',fixer ,',array))
                                :hints
                                (("Goal"
                                  :in-theory (e/d (,',resizer-of-length-free)
                                                  (,',fixer
                                                   ,',length
                                                   ,',resizer)))))

                              (defthm ,',resizer-of-resizer
                                (implies (or (<= (nfix l) (nfix m))
                                             (<= (,',length ,',array) (nfix m)))
                                         (equal (,',resizer l (,',resizer m ,',array))
                                                (,',resizer l ,',array)))
                                :hints
                                (("Goal"
                                  :in-theory (disable acl2::resize-list-of-resize-list)
                                  :use ((:instance acl2::resize-list-of-resize-list
                                                   (lst (,',fixer ,',array))
                                                   (m (nfix l))
                                                   (n (nfix m))
                                                   (d ,initial-element)
                                                   (e ,initial-element))))))

                              (defthmd ,',resizer-of-resizer{forced}
                                ;; NOTE: The only way this forcing fails is if
                                ;; you shrink an array below its default length
                                ;; and then grow it again.
                                (implies (force (or (<= (nfix l) (nfix m))
                                                    (<= (,',length ,',array) (nfix m))))
                                         (equal (,',resizer l (,',resizer m ,',array))
                                                (,',resizer l ,',array)))
                                :hints
                                (("Goal"
                                  :in-theory (disable ,',length
                                                      ,',resizer))))

                              (defthm ,',resizer-of-updater-keep
                                (implies (and (force (< (nfix i) (,',length ,',array)))
                                              (< (nfix i) (nfix l)))
                                         (equal (,',resizer l (,',updater i ,',element ,',array))
                                                (,',updater i ,',element (,',resizer l ,',array))))
                                :hints
                                (("Goal"
                                  :in-theory (disable acl2::resize-list-of-update-nth-keep
                                                      update-nth)
                                  :use ((:instance acl2::resize-list-of-update-nth-keep
                                                   (key (nfix i))
                                                   (val ,(if element-fixer
                                                             `(,element-fixer ,',element)
                                                             ',element))
                                                   (l (,',fixer ,',array))
                                                   (n (nfix l))
                                                   (default-value ,initial-element))))))

                              (defthm ,',resizer-of-updater-drop
                                (implies (and (force (< (nfix i) (,',length ,',array)))
                                              (<= (nfix l) (nfix i)))
                                         (equal (,',resizer l (,',updater i ,',element ,',array))
                                                (,',resizer l ,',array)))
                                :hints
                                (("Goal"
                                  :in-theory (disable acl2::resize-list-of-update-nth-drop
                                                      update-nth)
                                  :use ((:instance acl2::resize-list-of-update-nth-drop
                                                   (key (nfix i))
                                                   (val ,(if element-fixer
                                                             `(,element-fixer ,',element)
                                                             ',element))
                                                   (l (,',fixer ,',array))
                                                   (n (nfix l))
                                                   (default-value ,initial-element))))))

                              (defthmd ,',resizer-of-updater
                                (implies (force (< (nfix i) (,',length ,',array)))
                                         (equal (,',resizer l (,',updater i ,',element ,',array))
                                                (if (< (nfix i) (nfix l))
                                                    (,',updater i ,',element (,',resizer l ,',array))
                                                    (,',resizer l ,',array))))
                                :hints
                                (("Goal"
                                  :in-theory (disable ,',length
                                                      ,',resizer
                                                      ,',updater))))))

                          `((defthm ,',resizer{rewrite}
                              (equal (,',resizer l ,',array)
                                     (,',fixer ,',array)))))

                    ;; `ACCESSOR'
                    ,@(if ',(or resizable
                                (not zp-default-length))
                          `((with-books (("std/lists/nth" :dir :system))
                              (defthmd ,',accessor-when-not-recognizer
                                (implies (not (,',recognizer ,',array))
                                         (equal (,',accessor i ,',array)
                                                ,initial-element)))

                              (defthm ,',accessor-of-nfix
                                (equal (,',accessor (nfix i) ,',array)
                                       (,',accessor i ,',array)))

                              (defthmd ,',accessor-when-zp
                                (implies (and (syntaxp (not (quotep i)))
                                              (zp i))
                                         (equal (,',accessor i ,',array)
                                                (,',accessor 0 ,',array)))
                                :hints
                                (("Goal"
                                  :in-theory (enable zp
                                                     nfix))))

                              (defthm ,',accessor-of-creator
                                (equal (,',accessor i (,',creator))
                                       ,initial-element))

                              (defthm ,',accessor-of-fixer
                                (equal (,',accessor i (,',fixer ,',array))
                                       (,',accessor i ,',array)))

                              ,@(and ',resizable
                                     `((with-books (("std/lists/resize-list" :dir :system))
                                         (defthm ,',accessor-of-resizer
                                           (implies (force (< (nfix i) (nfix l)))
                                                    (equal (,',accessor i (,',resizer l ,',array))
                                                           (,',accessor i ,',array)))))))

                              (defthm ,',accessor-of-updater-same
                                (implies (and (force (< (nfix i) (,',length ,',array)))
                                              (equal (nfix i) (nfix j)))
                                         (equal (,',accessor i (,',updater j ,',element ,',array))
                                                ,(if element-fixer
                                                     `(,element-fixer ,',element)
                                                     ',element)))
                                :hints
                                (("Goal"
                                  :in-theory (disable update-nth))))

                              (defthm ,',accessor-of-updater-diff
                                (implies (and (force (< (nfix i) (,',length ,',array)))
                                              (not (equal (nfix i) (nfix j))))
                                         (equal (,',accessor i (,',updater j ,',element ,',array))
                                                (,',accessor i ,',array)))
                                :hints
                                (("Goal"
                                  :in-theory (disable update-nth))))

                              (defthmd ,',accessor-of-updater
                                (implies (force (< (nfix i) (,',length ,',array)))
                                         (equal (,',accessor i (,',updater j ,',element ,',array))
                                                (if (equal (nfix i) (nfix j))
                                                    ,(if element-fixer
                                                         `(,element-fixer ,',element)
                                                         ',element)
                                                    (,',accessor i ,',array))))
                                :hints
                                (("Goal"
                                  :in-theory (disable ,',length
                                                      ,',accessor
                                                      ,',updater)))))

                            (defthmd ,',accessor-when-large
                              (implies (<= (,',length ,',array) (nfix i))
                                       (equal (,',accessor i ,',array)
                                              ,initial-element))))

                          `((defthm ,',accessor{rewrite}
                              (equal (,',accessor i ,',array)
                                     ,initial-element))))

                    ;; `UPDATER'
                    ,@(if ',(or resizable
                                (not zp-default-length))
                          `((with-books (("std/lists/update-nth" :dir :system))
                              (defthmd ,',updater-when-not-recognizer
                                (implies (not (,',recognizer ,',array))
                                         (equal (,',updater i ,',element ,',array)
                                                (,',updater i ,',element (,',creator)))))

                              (defthm ,updater-of-nfix
                                (equal (,',updater (nfix i) ,',element ,',array)
                                       (,',updater i ,',element ,',array)))

                              (defthmd ,',updater-when-zp
                                (implies (and (syntaxp (not (quotep i)))
                                              (zp i))
                                         (equal (,',updater i ,',element ,',array)
                                                (,',updater 0 ,',element ,',array)))
                                :hints
                                (("Goal"
                                  :in-theory (enable zp
                                                     nfix))))

                              ,@(and element-recognizer
                                     `((defthmd ,',updater-when-not-element-recognizer
                                         (implies (and (syntaxp (not (quotep ,',element)))
                                                       (not (,',element-recognizer ,',element)))
                                                  (equal (,',updater i ,',element ,',array)
                                                         (,',updater i ,initial-element ,',array))))))

                              ,@(and element-fixer
                                     `((defthm ,updater-of-element-fixer
                                         (equal (,',updater i (,element-fixer ,',element) ,',array)
                                                (,',updater i ,',element ,',array)))))

                              (defthm ,',updater-of-creator
                                (implies (and (force (< (nfix i) ,',default-length-name))
                                              (equal ,(if element-fixer
                                                          `(,element-fixer ,',element)
                                                          ',element)
                                                     ,(if element-type-is-stobj
                                                          `(,(stobj-creator ',element))
                                                          initial-element)))
                                         (equal (,',updater i ,',element (,',creator))
                                                (,',creator)))
                                :hints
                                (("Goal"
                                  :in-theory (disable ,@(and element-type-is-stobj
                                                             (not element$a)
                                                             `(,(stobj-creator ',element)))))))

                              (defthm ,',updater-of-fixer
                                (equal (,',updater i ,',element (,',fixer ,',array))
                                       (,',updater i ,',element ,',array)))

                              (with-books (("std/lists/nth" :dir :system))
                                ,@(and ',resizable
                                       `((defthm ,',updater-of-resizer
                                           (implies (and (force (< (nfix i) (nfix l)))
                                                         (equal ,(if element-fixer
                                                                     `(,element-fixer ,',element)
                                                                     ',element)
                                                                (,',accessor i ,',array)))
                                                    (equal (,',updater i ,',element (,',resizer l ,',array))
                                                           (,',resizer l ,',array))))))

                                (defthmd ,',updater-of-accessor-free
                                  (implies (equal ,(if element-fixer
                                                       `(,element-fixer ,',element)
                                                       ',element)
                                                  (,',accessor i ,',array))
                                           (equal (,',updater i ,',element ,',array)
                                                  (,',fixer ,',array)))))

                              (defthm ,',updater-of-accessor
                                (implies (equal (nfix i) (nfix j))
                                         (equal (,',updater i (,',accessor j ,',array) ,',array)
                                                (,',fixer ,',array)))
                                :hints
                                (("Goal"
                                  :in-theory (disable ,',fixer
                                                      ,',accessor
                                                      ,',updater
                                                      ,',accessor-of-nfix)
                                  :use ((:instance ,',updater-of-accessor-free
                                                   (,',element (,',accessor j ,',array)))
                                        (:instance ,',accessor-of-nfix)
                                        (:instance ,',accessor-of-nfix
                                                   (i j))))))

                              (defthm ,',updater-of-updater-same
                                (implies (equal (nfix i) (nfix j))
                                         (equal (,',updater i v (,',updater j w ,',array))
                                                (,',updater i v ,',array))))

                              (defthm ,',updater-of-updater-diff
                                (implies (not (equal (nfix i) (nfix j)))
                                         (equal (,',updater i v (,',updater j w ,',array))
                                                (,',updater j w (,',updater i v ,',array))))
                                :rule-classes
                                ((:rewrite :loop-stopper ((i j ,',updater))))
                                :hints
                                (("Goal"
                                  :in-theory (disable acl2::update-nth-of-update-nth-diff)
                                  :use ((:instance acl2::update-nth-of-update-nth-diff
                                                   (n1 (nfix i))
                                                   (n2 (nfix j))
                                                   (v1 ,(if element-fixer
                                                            `(,element-fixer v)
                                                            'v))
                                                   (v2 ,(if element-fixer
                                                            `(,element-fixer w)
                                                            'w))
                                                   (x (,',fixer ,',array)))))))

                              (defthmd ,',updater-of-updater
                                (equal (,',updater i v (,',updater j w ,',array))
                                       (if (equal (nfix i) (nfix j))
                                           (,',updater i v ,',array)
                                           (,',updater j w (,',updater i v ,',array))))
                                :rule-classes
                                ((:rewrite :loop-stopper ((i j ,',updater))))
                                :hints
                                (("Goal"
                                  :in-theory (disable ,',updater)))))

                            (defthmd ,',updater-when-large
                              (implies (<= (,',length ,',array) (nfix i))
                                       (equal (,',updater i ,',element ,',array)
                                              (,',fixer ,',array)))))

                          `((defthm ,',updater{rewrite}
                              (equal (,',updater i ,',element ,',array)
                                     (,',creator)))))

                    (defun-sk ,',array-contents-equal (,',%array ,',array)
                      (declare (xargs :guard (and (,',recognizer ,',%array)
                                                  (,',recognizer ,',array))
                                      :verify-guards nil))
                      (forall i
                        (implies (and (natp i)
                                      (< i (,',length ,',%array))
                                      (< i (,',length ,',array)))
                                 (equal (,',accessor i ,',%array) (,',accessor i ,',array))))
                      :rewrite :direct)

                    (defun-nx ,',array-equal (,',%array ,',array)
                      (declare (xargs :guard t
                                      :verify-guards nil))
                      (and (,',recognizer ,',%array)
                           (,',recognizer ,',array)
                           (= (,',length ,',%array) (,',length ,',array))
                           (,',array-contents-equal ,',%array ,',array)))

                    (with-books (("std/lists/nth" :dir :system))
                      (local
                        (defthmd ,',array-equal{forward-chaining}-lemma-2
                          (implies (and (,',recognizer ,',%array)
                                        (,',recognizer ,',array))
                                   (iff (equal (len ,',%array) (len ,',array))
                                        (equal (,',length ,',%array)
                                               (,',length ,',array))))))

                      (local
                        (defthmd ,',array-equal{forward-chaining}-lemma-1
                          (implies (and (,',recognizer ,',%array)
                                        (,',recognizer ,',array)
                                        (equal (,',length ,',%array)
                                               (,',length ,',array))
                                        (,',array-contents-equal ,',%array ,',array)
                                        (natp n)
                                        (< n (len ,',%array)))
                                   (equal (nth n ,',%array) (nth n ,',array)))
                          :rule-classes
                          ((:rewrite :match-free :all))
                          :hints
                          (("Goal"
                            :use ((:instance ,',array-contents-equal-necc
                                             (i n)))))))

                      (local
                        (in-theory
                          (disable ,',recognizer
                                   ,',creator
                                   ,',fixer
                                   ,',length
                                   ,',resizer
                                   ,',accessor
                                   ,',updater
                                   ,',array-contents-equal)))

                      (defthm ,',array-equal{forward-chaining}
                        (implies (,',array-equal ,',%array ,',array)
                                 (equal ,',%array ,',array))
                        :rule-classes
                        ((:forward-chaining :trigger-terms
                                            ((,',array-equal ,',%array ,',array))
                                            :corollary
                                            (implies t
                                                     (implies (,',array-equal ,',%array ,',array)
                                                              (equal ,',%array ,',array)))))
                        :hints
                        ((acl2::equal-by-nths-hint)
                         ("Goal"
                          :do-not-induct t)
                         ("Subgoal 2"
                          :use ((:instance ,',array-equal{forward-chaining}-lemma-2)))
                         ("Subgoal 1"
                          :use ((:instance ,',array-equal{forward-chaining}-lemma-1))))))))
                (stobj$a-property `(stobj$a-property (,',recognizer
                                                      ,',creator
                                                      ,',fixer
                                                      ,',array-equal)
                                                     ((,',element-recognizer
                                                       ,',element-fixer
                                                       ,',element
                                                       ,(and (not element-type-is-stobj)
                                                             ',initial-element-name))
                                                      (,',resizable
                                                       ,',default-length-name)
                                                      (,',length
                                                       ,',resizer
                                                       ,',accessor
                                                       ,',updater)))))

           `(progn
              ,@prologue

              ,body

              ,@epilogue

              (table stobj$a
                     'stobj$a-property-alist
                     (putprop ',',array
                              'stobj$a
                              ',stobj$a-property
                              (stobj$a-property-alist world)))))))))


;;;; `DEFINE-ARRAY$CORR'
(defmacro define-array$corr (array
                             &key
                               (logic 'nil)
                               (exec 'nil)

                               (debug 'nil))
  (declare (xargs :guard (and (symbolp array)
                              (symbolp logic)
                              (symbolp exec)
                              (booleanp debug))))
  (let* ((array$a (or logic
                      (symbolicate array array '$a)))
         (array$c (or exec
                      (symbolicate array array '$c)))
         (array$corr (symbolicate array array '$corr))
         (array$corr-contents (symbolicate array array$corr '-contents)))

    `(with-output
       ,@(and (not debug)
              '#!acl2(:off (warning! observation prove event history proof-tree)
                           :summary-off (rules)
                           :gag-mode t))

       (make-event
         (let* ((recognizer$c (stobj-recognizer ',array$c))
                (recognizer$a (stobj$a-recognizer ',array$a))
                (length$c (stobj$c-array-length ',array$c))
                (length$a (stobj$a-array-length ',array$a))
                (accessor$c (stobj$c-array-accessor ',array$c))
                (accessor$a (stobj$a-array-accessor ',array$a)))

           `(progn
              (defun-sk ,',array$corr-contents (,',array$c ,',array$a)
                (declare (xargs :stobjs ,',array$c
                                :guard t
                                :verify-guards nil))
                (forall i
                  (implies (and (natp i)
                                (< i (,length$c ,',array$c)))
                           (equal (,accessor$c i ,',array$c)
                                  (,accessor$a i ,',array$a))))
                :rewrite :direct)

              (defun-nx ,',array$corr (,',array$c ,',array$a)
                (declare (xargs :stobjs ,',array$c
                                :guard (,recognizer$a ,',array$a)
                                :verify-guards nil))
                (and (,recognizer$c ,',array$c)
                     (,recognizer$a ,',array$a)
                     (= (,length$c ,',array$c)
                        (,length$a ,',array$a))
                     (,',array$corr-contents ,',array$c
                                             ,',array$a)))))))))


;;;; `DEFINE-ARRAY$ABS'
(defmacro define-array$abs
    (array
     &key
       (logic 'nil)
       (exec 'nil)

       (recognizer 'nil)
       (creator 'nil)
       (fixer 'nil)
       (length 'nil)
       (resizer 'nil)
       (accessor 'nil)
       (updater 'nil)

       (executable 'nil)

       (debug 'nil))

  (declare (xargs :guard (and (symbolp array)
                              (symbolp logic)
                              (symbolp exec)
                              (symbol-listp (list recognizer
                                                  creator
                                                  fixer
                                                  length
                                                  resizer
                                                  accessor
                                                  updater))
                              (booleanp executable)
                              (booleanp debug))))

  (let* ((array$a (or logic
                      (symbolicate array array '$a)))
         (array$c (or exec
                      (symbolicate array array '$c)))

         (recognizer (or recognizer
                         (symbolicate array array (make-predicate-suffix array))))
         (creator (or creator
                      (symbolicate array 'create- array)))
         (fixer (or fixer
                    (symbolicate array array '-fix)))
         (length (or length
                     (symbolicate array array '-length)))
         (resizer (or resizer
                      (symbolicate array array '-resize)))
         (accessor (or accessor
                       (symbolicate array array '-ref)))
         (updater (or updater
                      (symbolicate array array '-set)))

         (array$corr (symbolicate array array '$corr))
         (array$corr-contents (symbolicate array array$corr '-contents))
         (array$corr-contents-witness (symbolicate array array$corr-contents '-witness))
         (array-element-guard (symbolicate array array '-element-guard))

         (creator{correspondence} (symbolicate array creator '{correspondence}))
         (creator{preserved} (symbolicate array creator '{preserved}))
         (fixer{correspondence} (symbolicate array fixer '{correspondence}))
         (fixer{preserved} (symbolicate array fixer '{preserved}))
         (length{correspondence} (symbolicate array length '{correspondence}))
         (resizer{correspondence} (symbolicate array resizer '{correspondence}))
         (resizer{preserved} (symbolicate array resizer '{preserved}))
         (accessor{correspondence} (symbolicate array accessor '{correspondence}))
         (accessor{guard-thm} (symbolicate array accessor '{guard-thm}))
         (updater{correspondence} (symbolicate array updater '{correspondence}))
         (updater{guard-thm} (symbolicate array updater '{guard-thm}))
         (updater{preserved} (symbolicate array updater '{preserved})))

    `(with-output
       ,@(and (not debug)
              '#!acl2(:off (warning! observation prove event history proof-tree)
                           :summary-off (rules)
                           :gag-mode t))

       (make-event
         (let* ((recognizer$c (stobj-recognizer ',array$c))
                (recognizer$a (stobj$a-recognizer ',array$a))
                (creator$c (stobj-creator ',array$c))
                (creator$a (stobj$a-creator ',array$a))
                (fixer$c (symbolicate ',array$c ',array$c '-fix))
                (fixer$c$inline (symbolicate ',array$c fixer$c '$inline))
                (fixer$a (stobj$a-fixer ',array$a))
                (length$c (stobj$c-array-length ',array$c))
                (length$a (stobj$a-array-length ',array$a))
                (resizer$c (stobj$c-array-resizer ',array$c))
                (resizer$a (stobj$a-array-resizer ',array$a))
                (accessor$c (stobj$c-array-accessor ',array$c))
                (accessor$a (stobj$a-array-accessor ',array$a))
                (updater$c (stobj$c-array-updater ',array$c))
                (updater$a (stobj$a-array-updater ',array$a))
                (element-recognizer (stobj$a-array-element-recognizer ',array$a))
                (element-fixer (stobj$a-array-element-fixer ',array$a))
                (element (stobj$a-array-element ',array$a))
                (element-type-is-stobj (stobj-p element))
                (element-stobj$a (stobj$a-lookup element))
                (element-recognizer$a (if element-stobj$a
                                          (stobj$a-recognizer element-stobj$a)
                                          element-recognizer))
                (element-fixer$a (if element-stobj$a
                                     (stobj$a-fixer element-stobj$a)
                                     element-fixer))

                (exports `((,',fixer :logic ,fixer$a
                                     :exec ,fixer$c$inline)
                           (,',length :logic ,length$a
                                      :exec ,length$c)
                           (,',resizer :logic ,resizer$a
                                       :exec ,resizer$c)
                           (,',accessor :logic ,accessor$a
                                        :exec ,accessor$c
                                        ,@(and element-type-is-stobj
                                               `(:updater ,',updater)))
                           (,',updater :logic ,updater$a
                                       :exec ,updater$c)))

                (updater$c-guard
                 (cdr (untranslate (getpropc updater$c 'guard)
                                   nil
                                   (w state))))
                (updater$c-guard (if element-type-is-stobj
                                     (cddr updater$c-guard)
                                     (cdr updater$c-guard)))

                (aggressive$a (symbolicate ',array$a ',array$a '-aggressive)))

           `(encapsulate ()
              ,@(and (or element-recognizer$a
                         element-fixer$a)
                     `((local
                         (in-theory
                           (disable ,element-recognizer$a
                                    ,element-fixer$a)))))

              (local
                (defthm ,',array-element-guard
                  (equal (,length$c (,creator$c)) (,length$a (,creator$a)))
                  :rule-classes nil))

              ;; Proof Obligations
              (lprogn
                (defthm ,',creator{correspondence}
                  (,',array$corr (,creator$c) (,creator$a))
                  :rule-classes nil)

                (defthm ,',creator{preserved}
                  (,recognizer$a (,creator$a))
                  :rule-classes nil)

                (defthm ,',fixer{correspondence}
                  (implies (and (,',array$corr ,',array$c ,',array)
                                (,recognizer$a ,',array))
                           (,',array$corr (,fixer$c ,',array$c)
                                          (,fixer$a ,',array)))
                  :rule-classes nil)

                (defthm ,',fixer{preserved}
                  (implies (,recognizer$a ,',array)
                           (,recognizer$a (,fixer$a ,',array)))
                  :rule-classes nil)

                (defthm ,',length{correspondence}
                  (implies (and (,',array$corr ,',array$c ,',array)
                                (,recognizer$a ,',array))
                           (equal (,length$c ,',array$c)
                                  (,length$a ,',array)))
                  :rule-classes nil)

                (defthm ,',resizer{correspondence}
                  (implies (and (,',array$corr ,',array$c ,',array)
                                (natp i)
                                (,recognizer$a ,',array))
                           (,',array$corr (,resizer$c i ,',array$c)
                                          (,resizer$a i ,',array)))
                  :rule-classes nil
                  :hints
                  (("Goal"
                    :cases ((< (,',array$corr-contents-witness (,resizer$c i ,',array$c)
                                                               (,resizer$a i ,',array))
                               (,length$a ,',array)))
                    :in-theory (e/d (,aggressive$a)
                                    (,',array$corr-contents))
                    :expand (,',array$corr-contents (,resizer$c i ,',array$c)
                                                    (,resizer$a i ,',array)))))

                (defthm ,',resizer{preserved}
                  (implies (and (natp i)
                                (,recognizer$a ,',array))
                           (,recognizer$a (,resizer$a i ,',array)))
                  :rule-classes nil)

                (defthm ,',accessor{correspondence}
                  (implies (and (,',array$corr ,',array$c ,',array)
                                (natp i)
                                (,recognizer$a ,',array)
                                (< i (,length$a ,',array)))
                           (equal (,accessor$c i ,',array$c)
                                  (,accessor$a i ,',array)))
                  :rule-classes nil
                  :hints
                  (("Goal"
                    :in-theory (disable ,',array$corr-contents))))

                (defthm ,',accessor{guard-thm}
                  (implies (and (,',array$corr ,',array$c ,',array)
                                (natp i)
                                (,recognizer$a ,',array)
                                (< i (,length$a ,',array)))
                           (and (integerp i)
                                (<= 0 i)
                                (< i (,length$c ,',array$c))))
                  :rule-classes nil)

                (defthm ,',updater{correspondence}
                  (implies (and (,',array$corr ,',array$c ,',array)
                                (natp i)
                                ,@(and element-recognizer
                                       `((,element-recognizer v)))
                                (,recognizer$a ,',array)
                                (< i (,length$a ,',array)))
                           (,',array$corr (,updater$c i v ,',array$c)
                                          (,updater$a i v ,',array)))
                  :rule-classes nil
                  :hints
                  (("Goal"
                    :cases ((equal i (,',array$corr-contents-witness (,updater$c i v ,',array$c)
                                                                     (,updater$a i v ,',array))))
                    :in-theory (disable ,',array$corr-contents)
                    :expand (,',array$corr-contents (,updater$c i v ,',array$c)
                                                    (,updater$a i v ,',array)))))

                (defthm ,',updater{guard-thm}
                  (implies (and (,',array$corr ,',array$c ,',array)
                                (natp i)
                                ,@(and element-recognizer
                                       `((,element-recognizer v)))
                                (,recognizer$a ,',array)
                                (< i (,length$a ,',array)))
                           (and ,@updater$c-guard))
                  :rule-classes nil)

                (defthm ,',updater{preserved}
                  (implies (and (natp i)
                                ,@(and element-recognizer
                                       `((,element-recognizer v)))
                                (,recognizer$a ,',array)
                                (< i (,length$a ,',array)))
                           (,recognizer$a (,updater$a i v ,',array)))
                  :rule-classes nil))

              (defabsstobj ,',array
                :foundation ,',array$c
                :recognizer (,',recognizer :logic ,recognizer$a
                                           :exec ,recognizer$c)
                :creator (,',creator :logic ,creator$a
                                     :exec ,creator$c)
                :corr-fn ,',array$corr
                :non-executable ,',(not executable)
                :exports ,exports)

              (table stobj$a
                     'stobj$a-lookup-alist
                     (putprop ',',array
                              'stobj$a
                              ',',array$a
                              (stobj$a-lookup-alist world)))))))))


;;;; `DEFINE-ARRAY'
(defmacro define-array
    (array dimensions
     &key
       (element-type 't)
       (specialize-element-type 'nil)
       (element-recognizer 'nil)
       (element-fixer 'nil)
       (element 'x)
       (initial-element 'nil)
       (resizable 'nil)

       (inline 'nil)
       (memoizable 'nil)
       (executable 'nil)

       (recognizer 'nil)
       (creator 'nil)
       (length 'nil)
       (resizer 'nil)
       (accessor 'nil)
       (updater 'nil)

       (logic 'nil)
       (exec 'nil)

       (debug 'nil))

  (declare (xargs :guard (and (symbolp array)
                              (valid-array-dimensions-p dimensions)
                              (if (acl2-type-spec-p element-type)
                                  (typep$ initial-element element-type)
                                  (symbolp element-type))
                              (booleanp specialize-element-type)
                              (symbolp element-recognizer)
                              (symbolp element-fixer)
                              (symbolp element)
                              (booleanp resizable)
                              (booleanp inline)
                              (booleanp memoizable)
                              (booleanp executable)
                              (symbol-listp (list recognizer
                                                  creator
                                                  length
                                                  resizer
                                                  accessor
                                                  updater))
                              (symbolp logic)
                              (symbolp exec)
                              (booleanp debug))))

  (let* ((array$a (or logic
                      (symbolicate array array '$a)))
         (array$c (or exec
                      (symbolicate array array '$c)))
         (recognizer (or recognizer
                         (symbolicate array array (make-predicate-suffix array))))
         (creator (or creator
                      (symbolicate array 'create- array)))
         (length (or length
                     (symbolicate array array '-length)))
         (resizer (or resizer
                      (symbolicate array array '-resize)))
         (accessor (or accessor
                       (symbolicate array array '-ref)))
         (updater (or updater
                      (symbolicate array array '-set))))

    `(with-output
       ,@(and (not debug)
              '#!acl2(:off (warning! observation prove event history proof-tree)
                           :summary-off (rules)
                           :gag-mode t))

       (make-event
         `(progn
            (define-array$c ,',array$c ,',dimensions
              :element-type ,',element-type
              :specialize-element-type ,',specialize-element-type
              :initial-element ,',initial-element
              :resizable ,',resizable
              :inline ,',inline
              :memoizable ,',memoizable
              :executable ,',executable
              :debug ,',debug)

            (define-array$a ,',array$a ,',dimensions
              :element-recognizer ,',element-recognizer
              :element-fixer ,',element-fixer
              :element ,',element
              :initial-element ,',initial-element
              :resizable ,',resizable
              :debug ,',debug)

            (define-array$corr ,',array
              :logic ,',array$a
              :exec ,',array$c
              :debug ,',debug)

            (define-array$abs ,',array
              :logic ,',array$a
              :exec ,',array$c
              :recognizer ,',recognizer
              :creator ,',creator
              :length ,',length
              :resizer ,',resizer
              :accessor ,',accessor
              :updater ,',updater
              :executable ,',executable
              :debug ,',debug)

            (in-theory
              (disable ,',(symbolicate array$c array$c '-theorems))))))))


;;;; `DEFINE-ARRAY-THEOREMS'
(deflabel define-array-end)

(deftheory-static define-array-theorems
  (set-difference-theories
   (set-difference-theories
    (current-theory 'define-array-end)
    (current-theory 'define-array-begin))
   (function-theory 'define-array-end)))


;;;; Epilogue
(in-theory
  (union-theories (current-theory 'define-array-begin)
                  (theory 'define-array-theorems)))
