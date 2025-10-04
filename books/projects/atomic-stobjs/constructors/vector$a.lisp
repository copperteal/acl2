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
#||
(include-book "../lemmas/vector$a")
||#
(include-book "../utilities/symbolicate")
(include-book "../utilities/with-books")
(include-book "../utilities/macros")
(include-book "../accessors/top")


;;;; `VECTOR' Guard Predicates
(defun valid-vector-dimensions-p (dimensions)
  ;; TODO: refactor into separate file
  (declare (xargs :guard t))
  (or (and (consp dimensions)
           (natp (car dimensions))
           (null (cdr dimensions)))
      (natp dimensions)))

(defthm valid-vector-dimensions-p{compound-recognizer}
  ;; Q: Is this theorem useful?
  (implies (valid-vector-dimensions-p dimensions)
           (or (natp dimensions)
               (and (consp dimensions)
                    (true-listp dimensions))))
  :rule-classes :compound-recognizer)


;;;; `DEFINE-VECTOR$A'
(defmacro define-vector$a
    (vector dimensions
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

       (debug 'nil))

  (declare (xargs :guard (and (symbolp vector)
                              (valid-vector-dimensions-p dimensions)
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
                              (booleanp debug))))

  (let* ((vector-begin (symbolicate vector vector '-begin))
         (vector-end (symbolicate vector vector '-end))
         (vector-theorems (symbolicate vector vector '-theorems))
         (vector-definitions (symbolicate vector vector '-definitions))
         (vector-aggressive (symbolicate vector vector '-aggressive))

         (default-length (if (consp dimensions)
                             (car dimensions)
                             dimensions))
         (default-length-name (symbolicate vector '* vector '-default-length*))
         (zp-default-length (zp default-length))

         (vector-element-guard (symbolicate vector vector '-element-guard))
         (initial-element-name (symbolicate vector '* vector '-initial-element*))

         (recognizer (or recognizer
                         (symbolicate vector vector (make-predicate-suffix vector))))
         (fixer (or fixer
                    (symbolicate vector vector '-fix)))
         (creator (or creator
                      (symbolicate vector 'create- vector)))
         (length (or length
                     (symbolicate vector vector '-length)))
         (resizer (or resizer
                      (symbolicate vector vector '-resize)))
         (accessor (or accessor
                       (symbolicate vector vector '-ref)))
         (updater (or updater
                      (symbolicate vector vector '-set)))

         (recognizer-aux (symbolicate vector vector '-aux-p))
         (recognizer-aux{compound-recognizer}
          (symbolicate vector recognizer-aux '{compound-recognizer}))
         (recognizer-aux-of-resize-list (symbolicate vector recognizer-aux '-of-resize-list))
         (recognizer-aux-of-make-list-ac (symbolicate vector recognizer-aux '-of-make-list-ac))
         (recognizer-aux-of-repeat (symbolicate vector recognizer-aux '-of-repeat))
         (recognizer-aux-of-update-nth (symbolicate vector recognizer-aux '-of-update-nth))

         (recognizer{compound-recognizer} (symbolicate vector recognizer '{compound-recognizer}))
         (recognizer-of-resize-list (symbolicate vector recognizer '-of-resize-list))
         (recognizer-of-make-list-ac (symbolicate vector recognizer '-of-make-list-ac))
         (recognizer-of-repeat (symbolicate vector recognizer '-of-repeat))
         (recognizer-of-update-nth (symbolicate vector recognizer '-of-update-nth))
         (recognizer-of-creator (symbolicate vector recognizer '-of- creator))
         (recognizer-of-fixer (symbolicate vector recognizer '-of- fixer))
         (recognizer-of-resizer (symbolicate vector recognizer '-of- resizer))
         (recognizer-of-updater (symbolicate vector recognizer '-of- updater))

         (fixer-when-recognizer (symbolicate vector fixer '-when- recognizer))
         (fixer-when-not-recognizer (symbolicate vector fixer '-when-not-recognizer))

         (length-when-not-recognizer (symbolicate vector length '-when-not- recognizer))
         (length-of-creator (symbolicate vector length '-of- creator))
         (length-of-fixer (symbolicate vector length '-of- fixer))
         (length-of-resizer (symbolicate vector length '-of- resizer))
         (length-of-updater (symbolicate vector length '-of- updater))
         (length{rewrite} (symbolicate vector length '{rewrite}))

         (resizer-when-not-recognizer (symbolicate vector resizer '-when-not- recognizer))
         (resizer-of-nfix (symbolicate vector resizer '-of-nfix))
         (resizer-when-zp (symbolicate vector resizer '-when-zp))
         (resizer-of-creator (symbolicate vector resizer '-of- creator))
         (resizer-of-fixer (symbolicate vector resizer '-of-fixer))
         (resizer-of-length (symbolicate vector resizer '-of- length))
         (resizer-of-length-free (symbolicate vector resizer-of-length '-free))
         (resizer-of-resizer (symbolicate vector resizer '-of- resizer))
         (resizer-of-resizer{forced} (symbolicate vector resizer-of-resizer '{forced}))
         (resizer-of-updater (symbolicate vector resizer '-of- updater))
         (resizer-of-updater-keep (symbolicate vector resizer-of-updater '-keep))
         (resizer-of-updater-drop (symbolicate vector resizer-of-updater '-drop))
         (resizer{rewrite} (symbolicate vector resizer '{rewrite}))

         (accessor-when-not-recognizer (symbolicate vector accessor '-when-not- recognizer))
         (accessor-of-nfix (symbolicate vector accessor '-of-nfix))
         (accessor-when-zp (symbolicate vector accessor '-when-zp))
         (accessor-of-creator (symbolicate vector accessor '-of- creator))
         (accessor-of-fixer (symbolicate vector accessor '-of- fixer))
         (accessor-of-resizer (symbolicate vector accessor '-of- resizer))
         (accessor-of-updater (symbolicate vector accessor '-of- updater))
         (accessor-of-updater-same (symbolicate vector accessor-of-updater '-same))
         (accessor-of-updater-diff (symbolicate vector accessor-of-updater '-diff))
         (accessor-when-large (symbolicate vector accessor '-when-large))
         (accessor{rewrite} (symbolicate vector accessor '{rewrite}))

         (updater-when-not-recognizer (symbolicate vector updater '-when-not- recognizer))
         (updater-of-nfix (symbolicate vector updater '-of-nfix))
         (updater-when-zp (symbolicate vector updater '-when-zp))
         (updater-when-not-element-recognizer (symbolicate vector updater '-when-not- element-recognizer))
         (updater-of-creator (symbolicate vector updater '-of- creator))
         (updater-of-fixer (symbolicate vector updater '-of- fixer))
         (updater-of-resizer (symbolicate vector updater '-of- resizer))
         (updater-of-accessor (symbolicate vector updater '-of- accessor))
         (updater-of-accessor-free (symbolicate vector updater-of-accessor '-free))
         (updater-of-updater (symbolicate vector updater '-of- updater))
         (updater-of-updater-same (symbolicate vector updater-of-updater '-same))
         (updater-of-updater-diff (symbolicate vector updater-of-updater '-diff))
         (updater-when-large (symbolicate vector updater '-when-large))
         (updater{rewrite} (symbolicate vector updater '{rewrite}))

         (%vector (symbolicate vector '% vector))
         (vector-contents-equal (symbolicate vector vector '-contents-equal))
         (vector-contents-equal-necc (symbolicate vector vector-contents-equal '-necc))
         (vector-equal (symbolicate vector vector '-equal))
         (vector-equal{forward-chaining} (symbolicate vector vector-equal '{forward-chaining}))
         (vector-equal{forward-chaining}-lemma-1 (symbolicate vector vector-equal{forward-chaining} '-lemma-1))
         (vector-equal{forward-chaining}-lemma-2 (symbolicate vector vector-equal{forward-chaining} '-lemma-2)))

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
                 (symbolicate ',vector element-recognizer '-of-nth-when- ',recognizer-aux))
                (element-recognizer-of-nth-when-recognizer
                 (symbolicate ',vector element-recognizer '-of-nth-when- ',recognizer))
                (element-recognizer-of-accessor (symbolicate ',vector element-recognizer '-of- ',accessor))
                (updater-of-element-fixer (symbolicate ',vector ',updater '-of- element-fixer))
                (updater-of-element-fixer (if (eq updater-of-element-fixer ',updater-of-nfix)
                                              (symbolicate ',vector ',updater-of-nfix "-1")
                                              updater-of-element-fixer))
                (updater-of-nfix (if (eq updater-of-element-fixer ',updater-of-nfix)
                                     (symbolicate ',vector ',updater-of-nfix "-0")
                                     ',updater-of-nfix))
                (prologue
                 `((deflabel ,',vector-begin)

                   (defconst ,',default-length-name ',',default-length)

                   ,@(and (not element-type-is-stobj)
                          `((defconst ,',initial-element-name ',',initial-element)))))
                (epilogue
                 '((deflabel ,vector-end)

                   (deftheory-static ,vector-theorems
                     (set-difference-theories
                      (set-difference-theories
                       (current-theory ',vector-end)
                       (current-theory ',vector-begin))
                      (union-theories (function-theory ',vector-end)
                                      '(,@(and element-recognizer
                                               (or resizable
                                                   (not zp-default-length))
                                               `((:i ,(if resizable
                                                          recognizer
                                                          recognizer-aux))))))))

                   (deftheory-static ,vector-definitions
                     (set-difference-theories
                      (set-difference-theories
                       (set-difference-theories
                        (current-theory ',vector-end)
                        (current-theory ',vector-begin))
                       (theory ',vector-theorems))
                      '(,vector-contents-equal)))

                   (deftheory-static ,vector-aggressive
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
                     (union-theories (current-theory ',vector-begin)
                                     (theory ',vector-theorems)))
                   (in-theory
                     (enable ,vector-contents-equal))))
                (initial-element (cond
                                   (element-type-is-stobj
                                    `(,(stobj-creator ',element)))
                                   (t
                                    ',initial-element-name)))
                (body
                 `(with-books (("std/basic/nfix" :dir :system)
                               ("projects/atomic-stobjs/lemmas/std" :dir :system)
                               ("projects/atomic-stobjs/lemmas/define-vector-lemmas" :dir :system))

                    ,@(and (or (and element-recognizer
                                    element-fixer)
                               element-type-is-stobj)
                           `((local
                               (defthm ,',vector-element-guard
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
                                   ,@(and (and element-recognizer
                                               element-fixer)
                                          `(:in-theory (disable ,element-recognizer
                                                                ,element-fixer)))))))))

                    (local
                      (in-theory
                        (e/d (max)
                             (nfix
                              len
                              ,@(and (and element-recognizer
                                          element-fixer)
                                     `((:d ,element-recognizer)
                                       (:d ,element-fixer)
                                       (:e ,element-fixer)))))))

                    ,@(and ',(not resizable)
                           ',(not zp-default-length)
                           element-recognizer
                           `((defun ,',recognizer-aux (,',vector)
                               (declare (xargs :guard t))
                               (if (consp ,',vector)
                                   (and (,element-recognizer (car ,',vector))
                                        (,',recognizer-aux (cdr ,',vector)))
                                   (null ,',vector)))

                             (lprogn
                              (defthm ,',recognizer-aux{compound-recognizer}
                                (implies (,',recognizer-aux ,',vector)
                                         (true-listp ,',vector))
                                :rule-classes :compound-recognizer)

                              (defthm ,',recognizer-aux-of-resize-list
                                (implies (,',recognizer-aux lst)
                                         (equal (,',recognizer-aux (resize-list lst n default-value))
                                                (or (<= (nfix n) (len lst))
                                                    (,element-recognizer default-value))))
                                :hints
                                (("Goal"
                                  :use ((:functional-instance define-vector::recognizer-of-resize-list
                                                              (define-vector::recognizer ,',recognizer-aux)
                                                              (define-vector::element-recognizer ,element-recognizer))))))

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
                                  :use ((:functional-instance define-vector::element-recognizer-of-nth-when-recognizer
                                                              (define-vector::recognizer ,',recognizer-aux)
                                                              (define-vector::element-recognizer ,element-recognizer))))))

                              (defthm ,',recognizer-aux-of-update-nth
                                (implies (and (,',recognizer-aux l)
                                              (,element-recognizer val)
                                              (<= key (len l)))
                                         (,',recognizer-aux (update-nth key val l)))
                                :hints
                                (("Goal"
                                  :use ((:functional-instance define-vector::recognizer-of-update-nth
                                                              (define-vector::recognizer ,',recognizer-aux)
                                                              (define-vector::element-recognizer ,element-recognizer)))))))))

                    (defun ,',recognizer (,',vector)
                      (declare (xargs :guard t))
                      ,(cond
                         (',resizable
                          (if element-recognizer
                              `(if (consp ,',vector)
                                   (and (,element-recognizer (car ,',vector))
                                        (,',recognizer (cdr ,',vector)))
                                   (null ,',vector))
                              `(true-listp ,',vector)))
                         (',zp-default-length
                          `(null ,',vector))
                         (t
                          `(and (= (len ,',vector) ,',default-length-name)
                                ,(if element-recognizer
                                     `(,',recognizer-aux ,',vector)
                                     `(true-listp ,',vector))))))

                    (defthm ,',recognizer{compound-recognizer}
                      (implies (,',recognizer ,',vector)
                               ,(cond
                                  (',resizable
                                   `(true-listp ,',vector))
                                  (',zp-default-length
                                   `(null ,',vector))
                                  (t
                                   `(and (consp ,',vector)
                                         (true-listp ,',vector)))))
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

                    (defun ,',fixer (,',vector)
                      (declare (xargs :guard (,',recognizer ,',vector)))
                      (if (,',recognizer ,',vector)
                          ,',vector
                          (,',creator)))

                    (defun ,',length (,',vector)
                      (declare (xargs :guard (,',recognizer ,',vector))
                               ,@(and ',(not resizable)
                                      `((ignore ,',vector))))
                      ,(if ',resizable
                           `(len (,',fixer ,',vector))
                           ',default-length-name))

                    (defun ,',resizer (l ,',vector)
                      (declare (xargs :guard (and (natp l)
                                                  (,',recognizer ,',vector)))
                               ,@(and ',(not resizable)
                                      '((ignore l))))
                      ,(if ',resizable
                           `(let ((,',vector (,',fixer ,',vector))
                                  (l (mbe :logic (nfix l)
                                          :exec l)))
                              (resize-list ,',vector l ,(if element-type-is-stobj
                                                            ',initial-element
                                                            initial-element)))
                           `(,',fixer ,',vector)))

                    (with-books (("std/lists/len" :dir :system))
                      (defun ,',accessor (i ,',vector)
                        (declare (xargs :guard (and (natp i)
                                                    (,',recognizer ,',vector)
                                                    (< i (,',length ,',vector))))
                                 ,@(and ',(not resizable)
                                        ',zp-default-length
                                        `((ignore i ,',vector))))
                        ,(if ',(and (not resizable)
                                    zp-default-length)
                             (if element-type-is-stobj
                                 ',initial-element
                                 initial-element)
                             `(let ((i (mbe :logic (nfix i)
                                            :exec i))
                                    (,',vector (,',fixer ,',vector)))
                                (if (< i (,',length ,',vector))
                                    ,(if element-fixer
                                         `(,element-fixer (nth i ,',vector))
                                         `(nth i ,',vector))
                                    ,(if element-type-is-stobj
                                         ',initial-element
                                         initial-element))))))

                    (defun ,',updater (i ,',element ,',vector)
                      (declare (xargs :guard (and (natp i)
                                                  ,@(and element-recognizer
                                                         `((,',element-recognizer ,',element)))
                                                  (,',recognizer ,',vector)
                                                  (< i (,',length ,',vector))))
                               ,@(and ',(not resizable)
                                      ',zp-default-length
                                      `((ignore i ,',element ,',vector))))
                      ,(if ',(and (not resizable)
                                  zp-default-length)
                           `(,',creator)
                           `(let ((i (mbe :logic (nfix i)
                                          :exec i))
                                  ,@(and element-fixer
                                         `((,',element (,element-fixer ,',element))))
                                  (,',vector (,',fixer ,',vector)))
                              (if (< i (,',length ,',vector))
                                  (update-nth i ,',element ,',vector)
                                  ,',vector))))

                    ,@(and element-recognizer
                           `((local
                               (defthm ,element-recognizer-of-nth-when-recognizer
                                 (implies (and (,',recognizer l)
                                               (< (nfix n) (,',length l)))
                                          (,element-recognizer (nth n l)))
                                 :hints
                                 (("Goal"
                                   :use ((:functional-instance define-vector::element-recognizer-of-nth-when-recognizer
                                                               (define-vector::recognizer ,',recognizer)
                                                               (define-vector::element-recognizer ,element-recognizer)))))))))

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
                                  :use ((:functional-instance define-vector::recognizer-of-resize-list
                                                              (define-vector::recognizer ,',recognizer)
                                                              (define-vector::element-recognizer ,element-recognizer))))))

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
                                  :use ((:functional-instance define-vector::recognizer-of-update-nth
                                                              (define-vector::recognizer ,',recognizer)
                                                              (define-vector::element-recognizer ,element-recognizer)))))))))

                    (defthm ,',recognizer-of-creator
                      (,',recognizer (,',creator)))

                    (defthm ,',recognizer-of-fixer
                      (,',recognizer (,',fixer ,',vector)))

                    ,@(and ',resizable
                           `((defthm ,',recognizer-of-resizer
                               (,',recognizer (,',resizer l ,',vector)))))

                    ,@(and element-recognizer
                           `((defthm ,element-recognizer-of-accessor
                               (,element-recognizer (,',accessor i ,',vector)))))

                    ,@(and ',(or resizable
                                 (not zp-default-length))
                           `((defthm ,',recognizer-of-updater
                               (,',recognizer (,',updater i ,',element ,',vector)))))

                    ;; `FIXER'
                    (defthm ,',fixer-when-recognizer
                      (implies (,',recognizer ,',vector)
                               (equal (,',fixer ,',vector) ,',vector)))

                    (defthm ,',fixer-when-not-recognizer
                      (implies (not (,',recognizer ,',vector))
                               (equal (,',fixer ,',vector) (,',creator))))

                    ;; `LENGTH'
                    ,@(if ',resizable
                          `((defthmd ,',length-when-not-recognizer
                              (implies (not (,',recognizer ,',vector))
                                       (equal (,',length ,',vector)
                                              ,',default-length-name)))

                            (defthm ,',length-of-creator
                              (equal (,',length (,',creator))
                                     ,',default-length-name))

                            (defthm ,',length-of-fixer
                              (equal (,',length (,',fixer ,',vector))
                                     (,',length ,',vector)))

                            (with-books (("std/lists/resize-list" :dir :system)
                                         ("std/lists/repeat" :dir :system))
                              (defthm ,',length-of-resizer
                                (equal (,',length (,',resizer l ,',vector))
                                       (nfix l))))

                            (defthm ,',length-of-updater
                              (equal (,',length (,',updater i ,',element ,',vector))
                                     (,',length ,',vector))
                              :hints
                              (("Goal"
                                :in-theory (disable update-nth)))))

                          `((defthm ,',length{rewrite}
                              (equal (,',length ,',vector)
                                     ,',default-length-name))))

                    ;; `RESIZER'
                    ,@(if ',resizable
                          `((with-books (("std/lists/resize-list" :dir :system)
                                         ("std/lists/list-fix" :dir :system))
                              (defthmd ,',resizer-when-not-recognizer
                                (implies (not (,',recognizer ,',vector))
                                         (equal (,',resizer l ,',vector)
                                                (,',resizer l (,',creator)))))

                              (defthm ,',resizer-of-nfix
                                (equal (,',resizer (nfix l) ,',vector)
                                       (,',resizer l ,',vector)))

                              (defthmd ,',resizer-when-zp
                                (implies (and (syntaxp (not (quotep l)))
                                              (zp l))
                                         (equal (,',resizer l ,',vector)
                                                (,',resizer 0 ,',vector))))

                              (defthm ,',resizer-of-creator
                                (implies (equal (nfix l) ,',default-length-name)
                                         (equal (,',resizer l (,',creator))
                                                (,',creator))))

                              (defthm ,',resizer-of-fixer
                                (equal (,',resizer l (,',fixer ,',vector))
                                       (,',resizer l ,',vector)))

                              (defthmd ,',resizer-of-length-free
                                (implies (equal (nfix l) (,',length ,',vector))
                                         (equal (,',resizer l ,',vector)
                                                (,',fixer ,',vector))))

                              (defthm ,',resizer-of-length
                                (equal (,',resizer (,',length ,',vector) ,',vector)
                                       (,',fixer ,',vector))
                                :hints
                                (("Goal"
                                  :in-theory (e/d (,',resizer-of-length-free)
                                                  (,',fixer
                                                   ,',length
                                                   ,',resizer)))))

                              (defthm ,',resizer-of-resizer
                                (implies (or (<= (nfix l) (nfix m))
                                             (<= (,',length ,',vector) (nfix m)))
                                         (equal (,',resizer l (,',resizer m ,',vector))
                                                (,',resizer l ,',vector)))
                                :hints
                                (("Goal"
                                  :in-theory (disable acl2::resize-list-of-resize-list)
                                  :use ((:instance acl2::resize-list-of-resize-list
                                                   (lst (,',fixer ,',vector))
                                                   (m (nfix l))
                                                   (n (nfix m))
                                                   (d ,initial-element)
                                                   (e ,initial-element))))))

                              (defthmd ,',resizer-of-resizer{forced}
                                ;; NOTE: The only way this forcing fails is if
                                ;; you shrink an vector below its default length
                                ;; and then grow it again.
                                (implies (force (or (<= (nfix l) (nfix m))
                                                    (<= (,',length ,',vector) (nfix m))))
                                         (equal (,',resizer l (,',resizer m ,',vector))
                                                (,',resizer l ,',vector)))
                                :hints
                                (("Goal"
                                  :in-theory (disable ,',length
                                                      ,',resizer))))

                              (defthm ,',resizer-of-updater-keep
                                (implies (and (force (< (nfix i) (,',length ,',vector)))
                                              (< (nfix i) (nfix l)))
                                         (equal (,',resizer l (,',updater i ,',element ,',vector))
                                                (,',updater i ,',element (,',resizer l ,',vector))))
                                :hints
                                (("Goal"
                                  :in-theory (disable acl2::resize-list-of-update-nth-keep
                                                      update-nth)
                                  :use ((:instance acl2::resize-list-of-update-nth-keep
                                                   (key (nfix i))
                                                   (val ,(if element-fixer
                                                             `(,element-fixer ,',element)
                                                             ',element))
                                                   (l (,',fixer ,',vector))
                                                   (n (nfix l))
                                                   (default-value ,initial-element))))))

                              (defthm ,',resizer-of-updater-drop
                                (implies (and (force (< (nfix i) (,',length ,',vector)))
                                              (<= (nfix l) (nfix i)))
                                         (equal (,',resizer l (,',updater i ,',element ,',vector))
                                                (,',resizer l ,',vector)))
                                :hints
                                (("Goal"
                                  :in-theory (disable acl2::resize-list-of-update-nth-drop
                                                      update-nth)
                                  :use ((:instance acl2::resize-list-of-update-nth-drop
                                                   (key (nfix i))
                                                   (val ,(if element-fixer
                                                             `(,element-fixer ,',element)
                                                             ',element))
                                                   (l (,',fixer ,',vector))
                                                   (n (nfix l))
                                                   (default-value ,initial-element))))))

                              (defthmd ,',resizer-of-updater
                                (implies (force (< (nfix i) (,',length ,',vector)))
                                         (equal (,',resizer l (,',updater i ,',element ,',vector))
                                                (if (< (nfix i) (nfix l))
                                                    (,',updater i ,',element (,',resizer l ,',vector))
                                                    (,',resizer l ,',vector))))
                                :hints
                                (("Goal"
                                  :in-theory (disable ,',length
                                                      ,',resizer
                                                      ,',updater))))))

                          `((defthm ,',resizer{rewrite}
                              (equal (,',resizer l ,',vector)
                                     (,',fixer ,',vector)))))

                    ;; `ACCESSOR'
                    ,@(if ',(or resizable
                                (not zp-default-length))
                          `((with-books (("std/lists/nth" :dir :system))
                              (defthmd ,',accessor-when-not-recognizer
                                (implies (not (,',recognizer ,',vector))
                                         (equal (,',accessor i ,',vector)
                                                ,initial-element)))

                              (defthm ,',accessor-of-nfix
                                (equal (,',accessor (nfix i) ,',vector)
                                       (,',accessor i ,',vector)))

                              (defthmd ,',accessor-when-zp
                                (implies (and (syntaxp (not (quotep i)))
                                              (zp i))
                                         (equal (,',accessor i ,',vector)
                                                (,',accessor 0 ,',vector)))
                                :hints
                                (("Goal"
                                  :in-theory (enable zp
                                                     nfix))))

                              (defthm ,',accessor-of-creator
                                (equal (,',accessor i (,',creator))
                                       ,initial-element))

                              (defthm ,',accessor-of-fixer
                                (equal (,',accessor i (,',fixer ,',vector))
                                       (,',accessor i ,',vector)))

                              ,@(and ',resizable
                                     `((with-books (("std/lists/resize-list" :dir :system))
                                         (defthm ,',accessor-of-resizer
                                           (implies (force (< (nfix i) (nfix l)))
                                                    (equal (,',accessor i (,',resizer l ,',vector))
                                                           (,',accessor i ,',vector)))))))

                              (defthm ,',accessor-of-updater-same
                                (implies (and (force (< (nfix i) (,',length ,',vector)))
                                              (equal (nfix i) (nfix j)))
                                         (equal (,',accessor i (,',updater j ,',element ,',vector))
                                                ,(if element-fixer
                                                     `(,element-fixer ,',element)
                                                     ',element)))
                                :hints
                                (("Goal"
                                  :in-theory (disable update-nth))))

                              (defthm ,',accessor-of-updater-diff
                                (implies (and (force (< (nfix i) (,',length ,',vector)))
                                              (not (equal (nfix i) (nfix j))))
                                         (equal (,',accessor i (,',updater j ,',element ,',vector))
                                                (,',accessor i ,',vector)))
                                :hints
                                (("Goal"
                                  :in-theory (disable update-nth))))

                              (defthmd ,',accessor-of-updater
                                (implies (force (< (nfix i) (,',length ,',vector)))
                                         (equal (,',accessor i (,',updater j ,',element ,',vector))
                                                (if (equal (nfix i) (nfix j))
                                                    ,(if element-fixer
                                                         `(,element-fixer ,',element)
                                                         ',element)
                                                    (,',accessor i ,',vector))))
                                :hints
                                (("Goal"
                                  :in-theory (disable ,',length
                                                      ,',accessor
                                                      ,',updater)))))

                            (defthmd ,',accessor-when-large
                              (implies (<= (,',length ,',vector) (nfix i))
                                       (equal (,',accessor i ,',vector)
                                              ,initial-element))))

                          `((defthm ,',accessor{rewrite}
                              (equal (,',accessor i ,',vector)
                                     ,initial-element))))

                    ;; `UPDATER'
                    ,@(if ',(or resizable
                                (not zp-default-length))
                          `((with-books (("std/lists/update-nth" :dir :system))
                              (defthmd ,',updater-when-not-recognizer
                                (implies (not (,',recognizer ,',vector))
                                         (equal (,',updater i ,',element ,',vector)
                                                (,',updater i ,',element (,',creator)))))

                              (defthm ,updater-of-nfix
                                (equal (,',updater (nfix i) ,',element ,',vector)
                                       (,',updater i ,',element ,',vector)))

                              (defthmd ,',updater-when-zp
                                (implies (and (syntaxp (not (quotep i)))
                                              (zp i))
                                         (equal (,',updater i ,',element ,',vector)
                                                (,',updater 0 ,',element ,',vector)))
                                :hints
                                (("Goal"
                                  :in-theory (enable zp
                                                     nfix))))

                              ,@(and element-recognizer
                                     `((defthmd ,',updater-when-not-element-recognizer
                                         (implies (and (syntaxp (not (quotep ,',element)))
                                                       (not (,',element-recognizer ,',element)))
                                                  (equal (,',updater i ,',element ,',vector)
                                                         (,',updater i ,initial-element ,',vector))))))

                              ,@(and element-fixer
                                     `((defthm ,updater-of-element-fixer
                                         (equal (,',updater i (,element-fixer ,',element) ,',vector)
                                                (,',updater i ,',element ,',vector)))))

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
                                (equal (,',updater i ,',element (,',fixer ,',vector))
                                       (,',updater i ,',element ,',vector)))

                              (with-books (("std/lists/nth" :dir :system))
                                ,@(and ',resizable
                                       `((defthm ,',updater-of-resizer
                                           (implies (and (force (< (nfix i) (nfix l)))
                                                         (equal ,(if element-fixer
                                                                     `(,element-fixer ,',element)
                                                                     ',element)
                                                                (,',accessor i ,',vector)))
                                                    (equal (,',updater i ,',element (,',resizer l ,',vector))
                                                           (,',resizer l ,',vector))))))

                                (defthmd ,',updater-of-accessor-free
                                  (implies (equal ,(if element-fixer
                                                       `(,element-fixer ,',element)
                                                       ',element)
                                                  (,',accessor i ,',vector))
                                           (equal (,',updater i ,',element ,',vector)
                                                  (,',fixer ,',vector)))))

                              (defthm ,',updater-of-accessor
                                (implies (equal (nfix i) (nfix j))
                                         (equal (,',updater i (,',accessor j ,',vector) ,',vector)
                                                (,',fixer ,',vector)))
                                :hints
                                (("Goal"
                                  :in-theory (disable ,',fixer
                                                      ,',accessor
                                                      ,',updater
                                                      ,',accessor-of-nfix)
                                  :use ((:instance ,',updater-of-accessor-free
                                                   (,',element (,',accessor j ,',vector)))
                                        (:instance ,',accessor-of-nfix)
                                        (:instance ,',accessor-of-nfix
                                                   (i j))))))

                              (defthm ,',updater-of-updater-same
                                (implies (equal (nfix i) (nfix j))
                                         (equal (,',updater i v (,',updater j w ,',vector))
                                                (,',updater i v ,',vector))))

                              (defthm ,',updater-of-updater-diff
                                (implies (not (equal (nfix i) (nfix j)))
                                         (equal (,',updater i v (,',updater j w ,',vector))
                                                (,',updater j w (,',updater i v ,',vector))))
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
                                                   (x (,',fixer ,',vector)))))))

                              (defthmd ,',updater-of-updater
                                (equal (,',updater i v (,',updater j w ,',vector))
                                       (if (equal (nfix i) (nfix j))
                                           (,',updater i v ,',vector)
                                           (,',updater j w (,',updater i v ,',vector))))
                                :rule-classes
                                ((:rewrite :loop-stopper ((i j ,',updater))))
                                :hints
                                (("Goal"
                                  :in-theory (disable ,',updater)))))

                            (defthmd ,',updater-when-large
                              (implies (<= (,',length ,',vector) (nfix i))
                                       (equal (,',updater i ,',element ,',vector)
                                              (,',fixer ,',vector)))))

                          `((defthm ,',updater{rewrite}
                              (equal (,',updater i ,',element ,',vector)
                                     (,',creator)))))

                    (defun-sk ,',vector-contents-equal (,',%vector ,',vector)
                      (declare (xargs :guard (and (,',recognizer ,',%vector)
                                                  (,',recognizer ,',vector))
                                      :verify-guards nil))
                      (forall i
                        (implies (and (natp i)
                                      (< i (,',length ,',%vector))
                                      (< i (,',length ,',vector)))
                                 (equal (,',accessor i ,',%vector) (,',accessor i ,',vector))))
                      :rewrite :direct)

                    (defun-nx ,',vector-equal (,',%vector ,',vector)
                      (declare (xargs :guard t
                                      :verify-guards nil))
                      (and (,',recognizer ,',%vector)
                           (,',recognizer ,',vector)
                           (= (,',length ,',%vector) (,',length ,',vector))
                           (,',vector-contents-equal ,',%vector ,',vector)))

                    (with-books (("std/lists/nth" :dir :system))
                      (local
                        (defthmd ,',vector-equal{forward-chaining}-lemma-2
                          (implies (and (,',recognizer ,',%vector)
                                        (,',recognizer ,',vector))
                                   (iff (equal (len ,',%vector) (len ,',vector))
                                        (equal (,',length ,',%vector)
                                               (,',length ,',vector))))))

                      (local
                        (defthmd ,',vector-equal{forward-chaining}-lemma-1
                          (implies (and (,',recognizer ,',%vector)
                                        (,',recognizer ,',vector)
                                        (equal (,',length ,',%vector)
                                               (,',length ,',vector))
                                        (,',vector-contents-equal ,',%vector ,',vector)
                                        (natp n)
                                        (< n (len ,',%vector)))
                                   (equal (nth n ,',%vector) (nth n ,',vector)))
                          :rule-classes
                          ((:rewrite :match-free :all))
                          :hints
                          (("Goal"
                            :use ((:instance ,',vector-contents-equal-necc
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
                                   ,',vector-contents-equal)))

                      (defthm ,',vector-equal{forward-chaining}
                        (implies (,',vector-equal ,',%vector ,',vector)
                                 (equal ,',%vector ,',vector))
                        :rule-classes
                        ((:forward-chaining :trigger-terms
                                            ((,',vector-equal ,',%vector ,',vector))
                                            :corollary
                                            (implies t
                                                     (implies (,',vector-equal ,',%vector ,',vector)
                                                              (equal ,',%vector ,',vector)))))
                        :hints
                        ((acl2::equal-by-nths-hint)
                         ("Goal"
                          :do-not-induct t)
                         ("Subgoal 2"
                          :use ((:instance ,',vector-equal{forward-chaining}-lemma-2)))
                         ("Subgoal 1"
                          :use ((:instance ,',vector-equal{forward-chaining}-lemma-1))))))))
                (stobj$a-property `(stobj$a-property (,',recognizer
                                                      ,',creator
                                                      ,',fixer
                                                      ,',vector-equal)
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
                     (putprop ',',vector
                              'stobj$a
                              ',stobj$a-property
                              (stobj$a-property-alist world)))))))))
