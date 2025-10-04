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
#||
(include-book "../lemmas/vector$c")
||#
(include-book "../utilities/symbolicate")
(include-book "../utilities/with-books")
(include-book "../utilities/macros")
(include-book "../type-spec")
(include-book "../accessors/top")


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

                (element-type ',element-type)
                (element-type-is-stobj (and ',element-type-is-stobj
                                            (stobj-p element-type)))
                (stobj-recognizer (and element-type-is-stobj
                                       (stobj-recognizer element-type)))
                (stobj-creator (and element-type-is-stobj
                                    (stobj-creator element-type)))
                (element-type-is-t (eq element-type t))
                (specialize-element-type ',specialize-element-type)
                (initial-element ',initial-element)
                (initial-element-name
                 (symbolicate array '* array '-initial-element*))
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

                (fi-bindings
                 (list `(lem-vector$c::default-length (lambda () ,default-length))
                       `(lem-vector$c::value-recognizer
                         ,(if element-type-is-stobj
                              stobj-recognizer
                              `(lambda (value) ,(typep$transform 'value element-type))))
                       `(lem-vector$c::initial-element
                         ,(if element-type-is-stobj
                              stobj-creator
                              `(lambda () ,initial-element-name)))
                       `(lem-vector$c::contents-recognizer ,contents-recognizer)
                       (if resizable
                           `(lem-vector$c::recognizer/resizable ,recognizer)
                           `(lem-vector$c::recognizer/fixed ,recognizer))
                       `(lem-vector$c::creator ,creator)
                       (if resizable
                           `(lem-vector$c::length/resizable ,length)
                           `(lem-vector$c::length/fixed ,length))
                       (if resizable
                           `(lem-vector$c::resizer/resizable ,resizer)
                           `(lem-vector$c::resizer/fixed ,resizer))
                       `(lem-vector$c::accessor ,accessor)
                       `(lem-vector$c::updater ,updater)))
                (fi-bindings-with-fixer
                 (cons (if resizable
                           `(lem-vector$c::fixer/resizable ,fixer)
                           `(lem-vector$c::fixer/fixed ,fixer))
                       fi-bindings))

                (contents-recognizer{type-prescription}
                 (symbolicate array contents-recognizer '{type-prescription}))
                (contents-recognizer{compound-recognizer}
                 (symbolicate array contents-recognizer '{compound-recognizer}))

                (recognizer{type-prescription}
                 (symbolicate array recognizer '{type-prescription}))
                (recognizer{compound-recognizer}
                 (symbolicate array recognizer '{compound-recognizer}))
                (recognizer-of-creator
                 (symbolicate array recognizer '-of- creator))
                (recognizer-of-resizer
                 (symbolicate array recognizer '-of- resizer))
                (recognizer-of-updater
                 (symbolicate array recognizer '-of- updater))

                (length{type-prescription}
                 (symbolicate array length '{type-prescription}))
                (length-of-creator (symbolicate array length '-of- creator))
                (length-of-resizer (symbolicate array length '-of- resizer))
                (length-of-updater (symbolicate array length '-of- updater))
                (length{rewrite} (symbolicate array length '{rewrite}))

                (resizer{type-prescription}
                 (symbolicate array resizer '{type-prescription}))
                (resizer-of-creator (symbolicate array resizer '-of-creator))
                (resizer-of-length (symbolicate array resizer '-of- length))
                (resizer-of-length-free
                 (symbolicate array resizer-of-length '-free))
                (resizer-of-resizer (symbolicate array resizer '-of- resizer))
                (resizer-of-updater
                 (symbolicate array resizer '-of- updater))
                (resizer-of-updater-keep
                 (symbolicate array resizer-of-updater '-keep))
                (resizer-of-updater-drop
                 (symbolicate array resizer-of-updater '-drop))
                (resizer{rewrite} (symbolicate array resizer '{rewrite}))

                (typep$-of-accessor (symbolicate array 'typep$-of- accessor))
                (accessor-of-creator (symbolicate array accessor '-of- creator))
                (accessor-of-resizer
                 (symbolicate array accessor '-of- resizer))
                (accessor-of-resizer-inner
                 (symbolicate array accessor-of-resizer '-inner))
                (accessor-of-resizer-outer
                 (symbolicate array accessor-of-resizer '-outer))
                (accessor-of-updater
                 (symbolicate array accessor '-of- updater))
                (accessor-of-updater-same
                 (symbolicate array accessor-of-updater '-same))
                (accessor-of-updater-diff
                 (symbolicate array accessor-of-updater '-diff))

                (updater{type-prescription}
                 (symbolicate array updater '{type-prescription}))
                (updater-of-creator (symbolicate array updater '-of- creator))
                (updater-of-resizer (symbolicate array updater '-of- resizer))
                (updater-of-resizer-inner
                 (symbolicate array updater-of-resizer '-inner))
                (updater-of-resizer-outer
                 (symbolicate array updater-of-resizer '-outer))
                (updater-of-accessor (symbolicate array updater '-of- accessor))
                (updater-of-accessor-free
                 (symbolicate array updater-of-accessor '-free))
                (updater-of-updater (symbolicate array updater '-of- updater))
                (updater-of-updater-same
                 (symbolicate array updater-of-updater '-same))
                (updater-of-updater-diff
                 (symbolicate array updater-of-updater '-diff))

                (fixer{type-prescription} (symbolicate array fixer '{type-prescription}))
                (recognizer-of-fixer (symbolicate array recognizer '-of- fixer))
                (fixer-when-recognizer
                 (symbolicate array fixer '-when- recognizer))
                (fixer-when-not-recognizer
                 (symbolicate array fixer '-when-not- recognizer))

                (body
                 `(with-books (("projects/atomic-stobjs/lemmas/vector$c" :dir :system))
                    ;; `CONTENTS-RECOGNIZER'
                    (defthm ,contents-recognizer{type-prescription}
                      (booleanp (,contents-recognizer ,contents))
                      :rule-classes :type-prescription
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             lem-vector$c::contents-recognizer{type-prescription}
                             ,@fi-bindings))))

                    (defthm ,contents-recognizer{compound-recognizer}
                      (implies (,contents-recognizer ,contents)
                               (true-listp ,contents))
                      :rule-classes :compound-recognizer
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             lem-vector$c::contents-recognizer{compound-recognizer}
                             ,@fi-bindings))))

                    ;; `RECOGNIZER'
                    (defthm ,recognizer{type-prescription}
                      (booleanp (,recognizer ,array))
                      :rule-classes :type-prescription
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$c::recognizer/resizable{type-prescription}
                                  'lem-vector$c::recognizer/fixed{type-prescription})
                             ,@fi-bindings))))

                    (defthm ,recognizer{compound-recognizer}
                      (implies (,recognizer ,array)
                               (and (consp ,array)
                                    (true-listp ,array)))
                      :rule-classes :compound-recognizer
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$c::recognizer/resizable{compound-recognizer}
                                  'lem-vector$c::recognizer/fixed{compound-recognizer})
                             ,@fi-bindings))))

                    (defthm ,recognizer-of-creator
                      (,recognizer (,creator))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$c::recognizer/resizable-of-creator
                                  'lem-vector$c::recognizer/fixed-of-creator)
                             ,@fi-bindings))))

                    ,@(and resizable
                           `((defthm ,recognizer-of-resizer
                               (implies (,recognizer ,array)
                                        (,recognizer (,resizer length ,array)))
                               :hints
                               (("Goal"
                                 :by (:functional-instance
                                      lem-vector$c::recognizer/resizable-of-resizer/resizable
                                      ,@fi-bindings))))))

                    (defthm ,recognizer-of-updater
                      (implies (and (natp index)
                                    (< index ,(if resizable
                                                  `(,length ,array)
                                                  default-length-name))
                                    ,@(and (not element-type-is-t)
                                           (if element-type-is-stobj
                                               `((,stobj-recognizer value))
                                               `(,(typep$transform 'value element-type))))
                                    (,recognizer ,array))
                               (,recognizer (,updater index value ,array)))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$c::recognizer/resizable-of-updater
                                  'lem-vector$c::recognizer/fixed-of-updater)
                             ,@fi-bindings))))

                    ;; `LENGTH'
                    (defthm ,length{type-prescription}
                      (natp (,length ,array))
                      :rule-classes :type-prescription
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$c::length/resizable{type-prescription}
                                  'lem-vector$c::length/fixed{type-prescription})
                             ,@fi-bindings))))

                    ,@(if resizable
                          `((defthm ,length-of-creator
                              (equal (,length (,creator))
                                     ,default-length-name)
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$c::length/resizable-of-creator
                                     ,@fi-bindings))))

                            (defthm ,length-of-resizer
                              (implies (natp length)
                                       (equal (,length (,resizer length ,array))
                                              length))
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$c::length/resizable-of-resizer/resizable
                                     ,@fi-bindings))))

                            (defthm ,length-of-updater
                              (implies (and (natp index)
                                            (< index (,length ,array)))
                                       (equal (,length (,updater index value ,array))
                                              (,length ,array)))
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$c::length/resizable-of-updater
                                     ,@fi-bindings)))))

                          `((defthm ,length{rewrite}
                              (equal (,length ,array)
                                     ,default-length-name))))

                    ;; `RESIZER'
                    (defthm ,resizer{type-prescription}
                      (implies (,recognizer ,array)
                               (and (true-listp (,resizer length ,array))
                                    (consp (,resizer length ,array))))
                      :rule-classes :type-prescription
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$c::resizer/resizable{type-prescription}
                                  'lem-vector$c::resizer/fixed{type-prescription})
                             ,@fi-bindings))))

                    ,@(if resizable
                          `((defthm ,resizer-of-creator
                              (implies (equal length ,default-length-name)
                                       (equal (,resizer length (,creator))
                                              (,creator)))
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$c::resizer/resizable-of-creator
                                     ,@fi-bindings))))

                            (defthmd ,resizer-of-length-free
                              (implies (and (equal length (,length ,array))
                                            (,recognizer ,array))
                                       (equal (,resizer length ,array)
                                              ,array))
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$c::resizer/resizable-of-length/resizable-free
                                     ,@fi-bindings))))

                            (defthm ,resizer-of-length
                              (implies (,recognizer ,array)
                                       (equal (,resizer (,length ,array) ,array)
                                              ,array))
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$c::resizer/resizable-of-length/resizable
                                     ,@fi-bindings))))

                            (defthm ,resizer-of-resizer
                              (implies (and (natp length0)
                                            (natp length1)
                                            (or (<= length0 length1)
                                                (<= (,length ,array) length1))
                                            (,recognizer ,array))
                                       (equal (,resizer length0 (,resizer length1 ,array))
                                              (,resizer length0 ,array)))
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$c::resizer/resizable-of-resizer/resizable
                                     ,@fi-bindings))))

                            (defthmd ,resizer-of-updater
                              (implies (and (natp index)
                                            (natp length)
                                            (< index (,length ,array)))
                                       (equal (,resizer length (,updater index value ,array))
                                              (if (< index length)
                                                  (,updater index value (,resizer length ,array))
                                                  (,resizer length ,array))))
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$c::resizer/resizable-of-updater
                                     ,@fi-bindings))))

                            (defthm ,resizer-of-updater-keep
                              (implies (and (natp index)
                                            (natp length)
                                            (< index length)
                                            (< index (,length ,array)))
                                       (equal (,resizer length (,updater index value ,array))
                                              (,updater index value (,resizer length ,array))))
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$c::resizer/resizable-of-updater-keep
                                     ,@fi-bindings))))

                            (defthm ,resizer-of-updater-drop
                              (implies (and (natp index)
                                            (natp length)
                                            (<= length index)
                                            (< index (,length ,array)))
                                       (equal (,resizer length (,updater index value ,array))
                                              (,resizer length ,array)))
                              :hints
                              (("Goal"
                                :by (:functional-instance
                                     lem-vector$c::resizer/resizable-of-updater-drop
                                     ,@fi-bindings)))))

                          `((defthm ,resizer{rewrite}
                              (equal (,resizer length ,array)
                                     ,array))))

                    ;; `ACCESSOR'
                    ,@(and (not element-type-is-t)
                           `((defthm ,typep$-of-accessor
                               (implies (and (natp index)
                                             (< index ,(if resizable
                                                           `(,length ,array)
                                                           default-length-name))
                                             (,recognizer ,array))
                                        ,(if element-type-is-stobj
                                             `(,stobj-recognizer (,accessor index ,array))
                                             ;; TODO: check if this fails for member,
                                             ;; unsigned-byte, or signed-byte
                                             (typep$transform `(,accessor index ,array) element-type)))
                               :hints
                               (("Goal"
                                 :by (:functional-instance
                                      ,(if resizable
                                           'lem-vector$c::value-recognizer-of-accessor/resizable
                                           'lem-vector$c::value-recognizer-of-accessor/fixed)
                                      ,@fi-bindings))))))

                    (defthm ,accessor-of-creator
                      (implies (and (natp index)
                                    (< index ,default-length-name))
                               (equal (,accessor index (,creator))
                                      ,(if element-type-is-stobj
                                           ;; TODO: refactor "stobj-" stuff
                                           `(,stobj-creator)
                                           initial-element-name)))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             lem-vector$c::accessor-of-creator
                             ,@fi-bindings))))

                    ,@(and resizable
                           `((defthmd ,accessor-of-resizer
                               (implies (and (natp index)
                                             (natp length)
                                             (< index length))
                                        (equal (,accessor index (,resizer length ,array))
                                               (if (< index (,length ,array))
                                                   (,accessor index ,array)
                                                   ,(if element-type-is-stobj
                                                        `(,stobj-creator)
                                                        initial-element-name))))
                               :hints
                               (("Goal"
                                 :by (:functional-instance
                                      lem-vector$c::accessor-of-resizer/resizable
                                      ,@fi-bindings))))

                             (defthm ,accessor-of-resizer-inner
                               (implies (and (natp index)
                                             (natp length)
                                             (< index length)
                                             (< index (,length ,array)))
                                        (equal (,accessor index (,resizer length ,array))
                                               (,accessor index ,array)))
                               :hints
                               (("Goal"
                                 :by (:functional-instance
                                      lem-vector$c::accessor-of-resizer/resizable-inner
                                      ,@fi-bindings))))

                             (defthm ,accessor-of-resizer-outer
                               (implies (and (natp index)
                                             (natp length)
                                             (< index length)
                                             (<= (,length ,array) index))
                                        (equal (,accessor index (,resizer length ,array))
                                               ,(if element-type-is-stobj
                                                    `(,stobj-creator)
                                                    initial-element-name)))
                               :hints
                               (("Goal"
                                 :by (:functional-instance
                                      lem-vector$c::accessor-of-resizer/resizable-outer
                                      ,@fi-bindings))))))

                    (defthmd ,accessor-of-updater
                      (implies (and (natp index0)
                                    (natp index1))
                               (equal (,accessor index0 (,updater index1 value ,array))
                                      (if (equal index0 index1)
                                          value
                                          (,accessor index0 ,array))))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             lem-vector$c::accessor-of-updater
                             ,@fi-bindings))))

                    (defthm ,accessor-of-updater-same
                      (implies (equal index0 index1)
                               (equal (,accessor index0 (,updater index1 value ,array))
                                      value))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             lem-vector$c::accessor-of-updater-same
                             ,@fi-bindings))))

                    (defthm ,accessor-of-updater-diff
                      (implies (and (not (equal index0 index1))
                                    (natp index0)
                                    (natp index1))
                               (equal (,accessor index0 (,updater index1 value ,array))
                                      (,accessor index0 ,array)))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             lem-vector$c::accessor-of-updater-diff
                             ,@fi-bindings))))

                    ;; `UPDATER'
                    (defthm ,updater{type-prescription}
                      (implies (,recognizer ,array)
                               (and (true-listp (,updater index value ,array))
                                    (consp (,updater index value ,array))))
                      :rule-classes :type-prescription
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$c::updater{type-prescription}/resizable
                                  'lem-vector$c::updater{type-prescription}/fixed)
                             ,@fi-bindings))))

                    (defthm ,updater-of-creator
                      (implies (and (equal value ,(if element-type-is-stobj
                                                      `(,stobj-creator)
                                                      initial-element-name))
                                    (natp index)
                                    (< index ,default-length-name))
                               (equal (,updater index value (,creator))
                                      (,creator)))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             lem-vector$c::updater-of-creator
                             ,@fi-bindings))))

                    ,@(and resizable
                           `((defthmd ,updater-of-resizer
                               (implies (and (natp index)
                                             (natp length)
                                             (< index length)
                                             (equal value (if (< index (,length ,array))
                                                              (,accessor index ,array)
                                                              ,(if element-type-is-stobj
                                                                   `(,stobj-creator)
                                                                   initial-element-name))))
                                        (equal (,updater index value (,resizer length ,array))
                                               (,resizer length ,array)))
                               :hints
                               (("Goal"
                                 :by (:functional-instance
                                      lem-vector$c::updater-of-resizer/resizable
                                      ,@fi-bindings))))

                             (defthm ,updater-of-resizer-inner
                               (implies (and (equal value (,accessor index ,array))
                                             (natp index)
                                             (natp length)
                                             (< index length)
                                             (< index (,length ,array)))
                                        (equal (,updater index value (,resizer length ,array))
                                               (,resizer length ,array)))
                               :hints
                               (("Goal"
                                 :by (:functional-instance
                                      lem-vector$c::updater-of-resizer/resizable-inner
                                      ,@fi-bindings))))

                             (defthm ,updater-of-resizer-outer
                               (implies (and (equal value ,(if element-type-is-stobj
                                                               `(,stobj-creator)
                                                               initial-element-name))
                                             (natp index)
                                             (natp length)
                                             (< index length)
                                             (<= (,length ,array) index))
                                        (equal (,updater index value (,resizer length ,array))
                                               (,resizer length ,array)))
                               :hints
                               (("Goal"
                                 :by (:functional-instance
                                      lem-vector$c::updater-of-resizer/resizable-outer
                                      ,@fi-bindings))))))

                    (defthmd ,updater-of-accessor-free
                      (implies (and (equal value (,accessor index ,array))
                                    (natp index)
                                    (< index ,(if resizable
                                                  `(,length ,array)
                                                  default-length-name))
                                    (,recognizer ,array))
                               (equal (,updater index value ,array)
                                      ,array))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$c::updater-of-accessor-free/resizable
                                  'lem-vector$c::updater-of-accessor-free/fixed)
                             ,@fi-bindings))))

                    (defthm ,updater-of-accessor
                      (implies (and (equal index0 index1)
                                    (natp index0)
                                    (< index0 ,(if resizable
                                                   `(,length ,array)
                                                   default-length-name))
                                    (,recognizer ,array))
                               (equal (,updater index0 (,accessor index1 ,array) ,array)
                                      ,array))
                      :hints
                      (("Goal"
                        :in-theory (disable ,updater-of-accessor-free)
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$c::updater-of-accessor/resizable
                                  'lem-vector$c::updater-of-accessor/fixed)
                             ,@fi-bindings))))

                    (defthm ,updater-of-updater-same
                      (implies (equal index0 index1)
                               (equal (,updater index0 value0 (,updater index1 value1 ,array))
                                      (,updater index0 value0 ,array)))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             lem-vector$c::updater-of-updater-same
                             ,@fi-bindings))))

                    (defthm ,updater-of-updater-diff
                      (implies (and (not (equal index0 index1))
                                    (natp index0)
                                    (natp index1))
                               (equal (,updater index0 value0 (,updater index1 value1 ,array))
                                      (,updater index1 value1 (,updater index0 value0 ,array))))
                      :rule-classes
                      ((:rewrite :loop-stopper ((index0 index1 ,updater))))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             lem-vector$c::updater-of-updater-diff
                             ,@fi-bindings))))

                    ;; `FIXER'
                    (defun-inline ,fixer (,array)
                      (declare (xargs :stobjs ,array))
                      (mbe :logic (if (,recognizer ,array)
                                      ,array
                                      (,creator))
                           :exec ,array))

                    (defthm ,fixer{type-prescription}
                      (and (true-listp (,fixer ,array))
                           (consp (,fixer ,array)))
                      :rule-classes :type-prescription
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$c::fixer/resizable{type-prescription}
                                  'lem-vector$c::fixer/fixed{type-prescription})
                             ,@fi-bindings-with-fixer))))

                    (defthm ,recognizer-of-fixer
                      (,recognizer (,fixer ,array))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$c::recognizer/resizable-of-fixer/resizable
                                  'lem-vector$c::recognizer/fixed-of-fixer/fixed)
                             ,@fi-bindings-with-fixer))))

                    (defthm ,fixer-when-recognizer
                      (implies (,recognizer ,array)
                               (equal (,fixer ,array)
                                      ,array))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$c::fixer/resizable-when-recognizer/resizable
                                  'lem-vector$c::fixer/fixed-when-recognizer/fixed)
                             ,@fi-bindings-with-fixer))))

                    (defthm ,fixer-when-not-recognizer
                      (implies (not (,recognizer ,array))
                               (equal (,fixer ,array) (,creator)))
                      :hints
                      (("Goal"
                        :by (:functional-instance
                             ,(if resizable
                                  'lem-vector$c::fixer/resizable-when-not-recognizer/resizable
                                  'lem-vector$c::fixer/fixed-when-not-recognizer/fixed)
                             ,@fi-bindings-with-fixer)))))))
           `(progn
              ,@prologue

              ,body

              ,@epilogue))))))
