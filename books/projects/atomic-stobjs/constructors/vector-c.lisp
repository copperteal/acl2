;;; Copyright 2026 J. David Taylor
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

#|
(include-book "../lemmas/vector-c-fixed-length")
(include-book "../lemmas/vector-c-resizable")
|#

(include-book "../type-spec")
(include-book "../utilities/top")


;;;; `DEFINE-VECTOR$C'
(defmacro define-vector$c
    (vector dimensions
     &key
       (element-type 't)
       (specialize-element-type 'nil)
       (initial-element 'nil)
       (resizable 't)

       (inline 't)
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

       (pkg-witness 'nil pkg-witness-supplied-p)
       (debug 'nil))

  (declare (xargs :guard (and (symbolp vector)
                              (or (and (consp dimensions)
                                       (natp (car dimensions))
                                       (null (cdr dimensions)))
                                  (natp dimensions))
                              (if (acl2-type-spec-p element-type)
                                  (typep$ initial-element element-type)
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
                              ;; (pkg-witness-p pkg-witness)
                              (booleanp debug))))

  `(with-output
     ,@(and (not debug)
            *constructor-output*)

     (make-event
       (let* ((vector ',vector)
              (pkg-witness (pkg-witness-fix (if ',pkg-witness-supplied-p
                                                ',pkg-witness
                                                (current-package state))))
              (dimensions ',dimensions)
              (dimensions (if (consp dimensions)
                              dimensions
                              (list dimensions)))
              (default-length (car dimensions))
              (default-length-name (symbolicate$ pkg-witness "*" vector "-DEFAULT-LENGTH*"))

              (element-type ',element-type)
              (stobj-property (and (symbolp element-type)
                                   (getpropc element-type 'acl2::stobj)))
              (absstobj-info (and stobj-property
                                  (getpropc element-type 'acl2::absstobj-info)))
              (stobj$a-property (and (symbolp element-type)
                                     (stobj$a-property element-type (w state))))
              (stobj-recognizer (cond
                                  (stobj$a-property
                                   (access stobj$a-property stobj$a-property :recognizer))
                                  (stobj-property
                                   (access acl2::stobj-property stobj-property :recognizer))))
              (stobj-creator (cond
                               (stobj$a-property
                                (access stobj$a-property stobj$a-property :creator))
                               (stobj-property
                                (access acl2::stobj-property stobj-property :creator))))
              (specialize-element-type ',specialize-element-type)
              (initial-element ',initial-element)
              (initial-element-name (symbolicate$ pkg-witness "*" vector "-INITIAL-ELEMENT*"))
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

              ;; Interface Symbols
              (contents (or contents
                            (symbolicate$ pkg-witness vector "-CONTENTS")))
              (contents-recognizer-stobj-default (symbolicate$ pkg-witness contents "P"))
              (contents-recognizer (or contents-recognizer
                                       (symbolicate$ pkg-witness contents (make-predicate-suffix contents))))
              (recognizer-stobj-default (symbolicate$ pkg-witness vector "P"))
              (recognizer (or recognizer
                              (symbolicate$ pkg-witness vector (make-predicate-suffix vector))))
              (creator-stobj-default (symbolicate$ pkg-witness "CREATE-" vector))
              (creator (or creator
                           (symbolicate$ pkg-witness "CREATE-" vector)))
              (fixer (or fixer
                         (symbolicate$ pkg-witness vector "-FIX")))
              (length-stobj-default (symbolicate$ pkg-witness contents "-LENGTH"))
              (length (or length
                          (symbolicate$ pkg-witness vector "-LEN")))
              (resizer-stobj-default (symbolicate$ pkg-witness "RESIZE-" contents))
              (resizer (or resizer
                           (symbolicate$ pkg-witness vector "-RSZ")))
              (accessor-stobj-default (symbolicate$ pkg-witness contents "I"))
              (accessor (or accessor
                            (symbolicate$ pkg-witness vector "-REF")))
              (updater-stobj-default (symbolicate$ pkg-witness "UPDATE-" contents "I"))
              (updater (or updater
                           (symbolicate$ pkg-witness vector "-SET")))

              ;; Make Doublets
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
                                     `((,updater-stobj-default ,updater)))))

              ;; Prologue
              (begin-label (symbolicate$ pkg-witness vector "-BEGIN"))
              (end-label (symbolicate$ pkg-witness vector "-END"))
              (fixer-hack (symbolicate$ pkg-witness vector "/FIXER-HACK"))
              (contents/fh (symbolicate$ pkg-witness contents "/FIXER-HACK"))
              (prologue
               `((deflabel ,begin-label)

                 (defconst ,default-length-name ',default-length)

                 ,@(and (not stobj-property)
                        `((defconst ,initial-element-name ',initial-element)))

                 (defstobj ,vector
                   (,contents :type (acl2::array ,element-type ,dimensions)
                              ,@(and (not stobj-property)
                                     `(:element-type
                                       ,(if specialize-element-type
                                            element-type
                                            t)
                                       :initially ,initial-element))
                              :resizable ,resizable)
                   :renaming ,doublets
                   :inline ,inline
                   :non-memoizable ,(not memoizable)
                   :non-executable ,(not executable))

                 (defstobj ,fixer-hack
                   (,contents/fh :type (acl2::array ,element-type ,dimensions)
                                 ,@(and (not stobj-property)
                                        `(:element-type
                                          ,(if specialize-element-type
                                               element-type
                                               t)
                                          :initially ,initial-element))
                                 :resizable ,resizable)
                   :inline ,inline
                   :congruent-to ,vector
                   :non-memoizable ,(not memoizable)
                   :non-executable t)))

              ;; Theorem Names
              (stobj-recognizer-of-stobj-creator (symbolicate$ "ATOMIC-STOBJS" stobj-recognizer "-OF-" stobj-creator))

              (contents-recognizer-tp (symbolicate$ pkg-witness contents-recognizer "-TP"))
              (contents-recognizer-cr (symbolicate$ pkg-witness contents-recognizer "-CR"))

              (recognizer-tp (symbolicate$ pkg-witness recognizer "-TP"))
              (recognizer-cr (symbolicate$ pkg-witness recognizer "-CR"))
              (recognizer-of-creator (symbolicate$ pkg-witness recognizer "-OF-" creator))
              (recognizer-of-resizer (symbolicate$ pkg-witness recognizer "-OF-" resizer))
              (recognizer-of-updater (symbolicate$ pkg-witness recognizer "-OF-" updater))

              (length-tp (symbolicate$ pkg-witness length "-TP"))
              (length-of-creator (symbolicate$ pkg-witness length "-OF-" creator))
              (length-of-resizer (symbolicate$ pkg-witness length "-OF-" resizer))
              (length-of-updater (symbolicate$ pkg-witness length "-OF-" updater))
              (length-rw (symbolicate$ pkg-witness length "-RW"))

              (resizer-tp (symbolicate$ pkg-witness resizer "-TP"))
              (resizer-of-creator (symbolicate$ pkg-witness resizer "-OF-" creator))
              (resizer-of-length (symbolicate$ pkg-witness resizer "-OF-" length))
              (resizer-of-resizer (symbolicate$ pkg-witness resizer "-OF-" resizer))
              (resizer-of-updater (symbolicate$ pkg-witness resizer "-OF-" updater))
              (resizer-of-updater-keep (symbolicate$ pkg-witness resizer-of-updater "-KEEP"))
              (resizer-of-updater-drop (symbolicate$ pkg-witness resizer-of-updater "-DROP"))
              (resizer-rw (symbolicate$ pkg-witness resizer "-RW"))

              (typep$-of-accessor (symbolicate$ pkg-witness (or stobj-recognizer "TYPEP$") "-OF-" accessor))
              (accessor-of-creator (symbolicate$ pkg-witness accessor "-OF-" creator))
              (accessor-of-resizer (symbolicate$ pkg-witness accessor "-OF-" resizer))
              (accessor-of-resizer-inner (symbolicate$ pkg-witness accessor-of-resizer "-INNER"))
              (accessor-of-resizer-outer (symbolicate$ pkg-witness accessor-of-resizer "-OUTER"))
              (accessor-of-updater (symbolicate$ pkg-witness accessor "-OF-" updater))
              (accessor-of-updater-same (symbolicate$ pkg-witness accessor-of-updater "-SAME"))
              (accessor-of-updater-diff (symbolicate$ pkg-witness accessor-of-updater "-DIFF"))

              (updater-tp (symbolicate$ pkg-witness updater "-TP"))
              (updater-of-creator (symbolicate$ pkg-witness updater "-OF-" creator))
              (updater-of-resizer (symbolicate$ pkg-witness updater "-OF-" resizer))
              (updater-of-resizer-inner (symbolicate$ pkg-witness updater-of-resizer "-INNER"))
              (updater-of-resizer-outer (symbolicate$ pkg-witness updater-of-resizer "-OUTER"))
              (updater-of-accessor (symbolicate$ pkg-witness updater "-OF-" accessor))
              (updater-of-updater (symbolicate$ pkg-witness updater "-OF-" updater))
              (updater-of-updater-same (symbolicate$ pkg-witness updater-of-updater "-SAME"))
              (updater-of-updater-diff (symbolicate$ pkg-witness updater-of-updater "-DIFF"))

              (fixer-def (symbolicate$ pkg-witness fixer "-DEF"))
              (fixer-tp (symbolicate$ pkg-witness fixer "-TP"))
              (recognizer-of-fixer (symbolicate$ pkg-witness recognizer "-OF-" fixer))
              (fixer-when-recognizer (symbolicate$ pkg-witness fixer "-WHEN-" recognizer))
              (fixer-when-not-recognizer (symbolicate$ pkg-witness fixer "-WHEN-NOT-" recognizer))

              ;; Epilogue
              (theorems (symbolicate$ pkg-witness vector "-THEOREMS"))
              (epilogue
               `((deflabel ,end-label)

                 (deftheory-static ,theorems
                   (set-difference-theories
                    (set-difference-theories
                     (current-theory ',end-label)
                     (current-theory ',begin-label))
                    ',(list contents-recognizer
                            recognizer
                            creator
                            length
                            resizer
                            accessor
                            updater
                            fixer)))

                 (in-theory
                   (union-theories (current-theory ',begin-label)
                                   (theory ',theorems)))))

              ;; Functional Instantiation
              (fi-bindings
               (list `(lem-vector$c::default-length (lambda ()
                                                      ,default-length))
                     `(lem-vector$c::element-recognizer ,(or stobj-recognizer
                                                             `(lambda (value)
                                                                ,(typep$transform 'value element-type))))
                     `(lem-vector$c::initial-element ,(or stobj-creator
                                                          `(lambda ()
                                                             ,initial-element-name)))
                     `(lem-vector$c::contents-recognizer ,contents-recognizer)
                     `(lem-vector$c::recognizer ,recognizer)
                     `(lem-vector$c::creator ,creator)
                     `(lem-vector$c::length ,length)
                     `(lem-vector$c::resizer ,resizer)
                     `(lem-vector$c::accessor ,accessor)
                     `(lem-vector$c::updater ,updater)))
              (fi-bindings-with-fixer
               (cons `(lem-vector$c::fixer ,fixer)
                     fi-bindings))
              ;; (theorem-statements (define-vector$c/theorems interface fi-bindings))

              (body
               `(encapsulate ()

                  ,@(and stobj-property
                         `((local
                             (defthm ,stobj-recognizer-of-stobj-creator
                               (,stobj-recognizer (,stobj-creator))))))

                  (local
                    (deflabel end-of-prologue))

                  (local
                    ,(if resizable
                         '(include-book "projects/atomic-stobjs/lemmas/vector-c-resizable" :dir :system)
                         '(include-book "projects/atomic-stobjs/lemmas/vector-c-fixed-length" :dir :system)))

                  (local
                    (table acl2::theory-invariant-table nil nil :clear))

                  (local
                    (in-theory
                      (union-theories (current-theory 'acl2::ground-zero)
                                      (set-difference-theories
                                       (universal-theory 'end-of-prologue)
                                       (universal-theory ',begin-label)))))

                  ,@(and absstobj-info
                         `((local
                             (in-theory
                               (enable ,@(strip-cars (cdr absstobj-info)))))))

                  (local
                    (in-theory
                      (enable type-spec-theory)))

                  (local
                    (in-theory
                      (disable make-list-ac
                               (:e make-list-ac))))

                  ;; ,@theorem-statements

                  ;; `CONTENTS-RECOGNIZER'
                  (defthm ,contents-recognizer-tp
                    (booleanp (,contents-recognizer ,contents))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-vector$c::contents-recognizer-tp
                           ,@fi-bindings))))

                  (defthm ,contents-recognizer-cr
                    (implies (,contents-recognizer ,contents)
                             (true-listp ,contents))
                    :rule-classes :compound-recognizer
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-vector$c::contents-recognizer-cr
                           ,@fi-bindings))))

                  ;; `RECOGNIZER'
                  (defthm ,recognizer-tp
                    (booleanp (,recognizer ,vector))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-vector$c::recognizer-tp
                           ,@fi-bindings))))

                  (defthm ,recognizer-cr
                    (implies (,recognizer ,vector)
                             (and (consp ,vector)
                                  (true-listp ,vector)))
                    :rule-classes :compound-recognizer
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-vector$c::recognizer-cr
                           ,@fi-bindings))))

                  (defthm ,recognizer-of-creator
                    (,recognizer (,creator))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-vector$c::recognizer-of-creator
                           ,@fi-bindings))))

                  ,@(and resizable
                         `((defthm ,recognizer-of-resizer
                             (implies (,recognizer ,vector)
                                      (,recognizer (,resizer length ,vector)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-vector$c::recognizer-of-resizer
                                    ,@fi-bindings))))))

                  (defthm ,recognizer-of-updater
                    (implies (and (natp index)
                                  (< index ,(if resizable
                                                `(,length ,vector)
                                                default-length-name))
                                  ,@(and (not (eq element-type t))
                                         (if stobj-recognizer
                                             `((,stobj-recognizer value))
                                             `(,(typep$transform 'value element-type))))
                                  (,recognizer ,vector))
                             (,recognizer (,updater index value ,vector)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-vector$c::recognizer-of-updater
                           ,@fi-bindings))))

                  ;; `LENGTH'
                  (defthm ,length-tp
                    (natp (,length ,vector))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-vector$c::length-tp
                           ,@fi-bindings))))

                  ,@(if resizable
                        `((defthm ,length-of-creator
                            (equal (,length (,creator))
                                   ,default-length-name)
                            :hints
                            (("Goal"
                              :by (:functional-instance
                                   lem-vector$c::length-of-creator
                                   ,@fi-bindings))))

                          (defthm ,length-of-resizer
                            (implies (natp length)
                                     (equal (,length (,resizer length ,vector))
                                            length))
                            :hints
                            (("Goal"
                              :by (:functional-instance
                                   lem-vector$c::length-of-resizer
                                   ,@fi-bindings))))

                          (defthm ,length-of-updater
                            (implies (and (natp index)
                                          (< index (,length ,vector)))
                                     (equal (,length (,updater index value ,vector))
                                            (,length ,vector)))
                            :hints
                            (("Goal"
                              :by (:functional-instance
                                   lem-vector$c::length-of-updater
                                   ,@fi-bindings)))))

                        `((defthm ,length-rw
                            (equal (,length ,vector)
                                   ,default-length-name)
                            :hints
                            (("Goal"
                              :by (:functional-instance
                                   lem-vector$c::length-rw
                                   ,@fi-bindings))))))

                  ;; `RESIZER'
                  (defthm ,resizer-tp
                    (implies (,recognizer ,vector)
                             (and (consp (,resizer length ,vector))
                                  (true-listp (,resizer length ,vector))))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-vector$c::resizer-tp
                           ,@fi-bindings))))

                  ,@(if resizable
                        `((defthm ,resizer-of-creator
                            (implies (equal length ,default-length-name)
                                     (equal (,resizer length (,creator))
                                            (,creator)))
                            :hints
                            (("Goal"
                              :by (:functional-instance
                                   lem-vector$c::resizer-of-creator
                                   ,@fi-bindings))))

                          (defthm ,resizer-of-length
                            (implies (,recognizer ,vector)
                                     (equal (,resizer (,length ,vector) ,vector)
                                            ,vector))
                            :hints
                            (("Goal"
                              :by (:functional-instance
                                   lem-vector$c::resizer-of-length
                                   ,@fi-bindings))))

                          (defthm ,resizer-of-resizer
                            (implies (and (natp %length)
                                          (natp length)
                                          (or (<= %length length)
                                              (<= (,length ,vector) length))
                                          (,recognizer ,vector))
                                     (equal (,resizer %length (,resizer length ,vector))
                                            (,resizer %length ,vector)))
                            :hints
                            (("Goal"
                              :by (:functional-instance
                                   lem-vector$c::resizer-of-resizer
                                   ,@fi-bindings))))

                          (defthm ,resizer-of-updater-keep
                            (implies (and (natp index)
                                          (natp length)
                                          (< index length)
                                          (< index (,length ,vector)))
                                     (equal (,resizer length (,updater index value ,vector))
                                            (,updater index value (,resizer length ,vector))))
                            :hints
                            (("Goal"
                              :by (:functional-instance
                                   lem-vector$c::resizer-of-updater-keep
                                   ,@fi-bindings))))

                          (defthm ,resizer-of-updater-drop
                            (implies (and (natp index)
                                          (natp length)
                                          (<= length index)
                                          (< index (,length ,vector)))
                                     (equal (,resizer length (,updater index value ,vector))
                                            (,resizer length ,vector)))
                            :hints
                            (("Goal"
                              :by (:functional-instance
                                   lem-vector$c::resizer-of-updater-drop
                                   ,@fi-bindings)))))

                        `((defthm ,resizer-rw
                            (equal (,resizer length ,vector)
                                   ,vector)
                            :hints
                            (("Goal"
                              :by (:functional-instance
                                   lem-vector$c::resizer-rw
                                   ,@fi-bindings))))))

                  ;; `ACCESSOR'
                  ,@(and (not (eq element-type t))
                         `((defthm ,typep$-of-accessor
                             (implies (and (natp index)
                                           (< index ,(if resizable
                                                         `(,length ,vector)
                                                         default-length-name))
                                           (,recognizer ,vector))
                                      ,(if stobj-recognizer
                                           `(,stobj-recognizer (,accessor index ,vector))
                                           (typep$transform `(,accessor index ,vector) element-type)))
                             :rule-classes
                             (:rewrite
                              :type-prescription)
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-vector$c::element-recognizer-of-accessor
                                    ,@fi-bindings))))))

                  (defthm ,accessor-of-creator
                    (implies (and (natp index)
                                  (< index ,default-length-name))
                             (equal (,accessor index (,creator))
                                    ,(if stobj-creator
                                         `(,stobj-creator)
                                         initial-element-name)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-vector$c::accessor-of-creator
                           ,@fi-bindings))))

                  ,@(and resizable
                         `((defthm ,accessor-of-resizer-inner
                             (implies (and (natp index)
                                           (natp length)
                                           (< index length)
                                           (< index (,length ,vector)))
                                      (equal (,accessor index (,resizer length ,vector))
                                             (,accessor index ,vector)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-vector$c::accessor-of-resizer-inner
                                    ,@fi-bindings))))

                           (defthm ,accessor-of-resizer-outer
                             (implies (and (natp index)
                                           (natp length)
                                           (< index length)
                                           (<= (,length ,vector) index))
                                      (equal (,accessor index (,resizer length ,vector))
                                             ,(if stobj-creator
                                                  `(,stobj-creator)
                                                  initial-element-name)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-vector$c::accessor-of-resizer-outer
                                    ,@fi-bindings))))))

                  (defthm ,accessor-of-updater-same
                    (implies (equal %index index)
                             (equal (,accessor %index (,updater index value ,vector))
                                    value))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-vector$c::accessor-of-updater-same
                           ,@fi-bindings))))

                  (defthm ,accessor-of-updater-diff
                    (implies (and (not (equal %index index))
                                  (natp %index)
                                  (natp index))
                             (equal (,accessor %index (,updater index value ,vector))
                                    (,accessor %index ,vector)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-vector$c::accessor-of-updater-diff
                           ,@fi-bindings))))

                  ;; `UPDATER'
                  (defthm ,updater-tp
                    (implies (,recognizer ,vector)
                             (and (consp (,updater index value ,vector))
                                  (true-listp (,updater index value ,vector))))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-vector$c::updater-tp
                           ,@fi-bindings))))

                  (defthm ,updater-of-creator
                    (implies (and (equal value ,(if stobj-creator
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
                         `((defthm ,updater-of-resizer-inner
                             (implies (and (equal value (,accessor index ,vector))
                                           (natp index)
                                           (natp length)
                                           (< index length)
                                           (< index (,length ,vector)))
                                      (equal (,updater index value (,resizer length ,vector))
                                             (,resizer length ,vector)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-vector$c::updater-of-resizer-inner
                                    ,@fi-bindings))))

                           (defthm ,updater-of-resizer-outer
                             (implies (and (equal value ,(if stobj-creator
                                                             `(,stobj-creator)
                                                             initial-element-name))
                                           (natp index)
                                           (natp length)
                                           (< index length)
                                           (<= (,length ,vector) index))
                                      (equal (,updater index value (,resizer length ,vector))
                                             (,resizer length ,vector)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-vector$c::updater-of-resizer-outer
                                    ,@fi-bindings))))))

                  (defthm ,updater-of-accessor
                    (implies (and (equal %index index)
                                  (natp %index)
                                  (< %index ,(if resizable
                                                 `(,length ,vector)
                                                 default-length-name))
                                  (,recognizer ,vector))
                             (equal (,updater %index (,accessor index ,vector) ,vector)
                                    ,vector))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-vector$c::updater-of-accessor
                           ,@fi-bindings))))

                  (defthm ,updater-of-updater-same
                    (implies (equal %index index)
                             (equal (,updater %index %value (,updater index value ,vector))
                                    (,updater %index %value ,vector)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-vector$c::updater-of-updater-same
                           ,@fi-bindings))))

                  (defthm ,updater-of-updater-diff
                    (implies (and (not (equal %index index))
                                  (natp %index)
                                  (natp index))
                             (equal (,updater %index %value (,updater index value ,vector))
                                    (,updater index value (,updater %index %value ,vector))))
                    :rule-classes
                    ((:rewrite :loop-stopper ((%index index ,updater))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-vector$c::updater-of-updater-diff
                           ,@fi-bindings))))

                  ;; `FIXER'
                  (defun-inline ,fixer (,vector)
                    (declare (xargs :stobjs ,vector))
                    (mbe :logic (if (,recognizer ,vector)
                                    ,vector
                                    (with-local-stobj ,fixer-hack
                                      (mv-let (,vector ,fixer-hack)
                                              (swap-stobjs ,vector ,fixer-hack)
                                        ,vector)))
                         :exec ,vector))

                  (table fixer ',vector ',fixer)

                  (defthm ,fixer-def
                    (equal (,fixer ,vector)
                           (if (,recognizer ,vector)
                               ,vector
                               (,creator)))
                    :rule-classes :definition)

                  (in-theory
                    (disable ,fixer))

                  (defthm ,fixer-tp
                    (and (consp (,fixer ,vector))
                         (true-listp (,fixer ,vector)))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-vector$c::fixer-tp
                           ,@fi-bindings-with-fixer))))

                  (defthm ,recognizer-of-fixer
                    (,recognizer (,fixer ,vector))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-vector$c::recognizer-of-fixer
                           ,@fi-bindings-with-fixer))))

                  (defthm ,fixer-when-recognizer
                    (implies (,recognizer ,vector)
                             (equal (,fixer ,vector)
                                    ,vector))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-vector$c::fixer-when-recognizer
                           ,@fi-bindings-with-fixer))))

                  (defthm ,fixer-when-not-recognizer
                    (implies (not (,recognizer ,vector))
                             (equal (,fixer ,vector) (,creator)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-vector$c::fixer-when-not-recognizer
                           ,@fi-bindings-with-fixer))))))
              (stobj$c-property (make vector$c-property
                                      :name vector
                                      :recognizer recognizer
                                      :creator creator
                                      :fixer fixer
                                      :length length
                                      :resizer resizer
                                      :accessor accessor
                                      :updater updater
                                      :contents contents
                                      :contents-recognizer contents-recognizer
                                      :element nil ; TODO: element
                                      :element-type element-type
                                      :initial-element initial-element-name
                                      :default-length default-length-name
                                      :resizable resizable
                                      :memoizable memoizable
                                      :theory theorems
                                      :fi-bindings fi-bindings-with-fixer
                                      :fi-theorem nil
                                      :pkg-witness pkg-witness
                                      )))

         `(progn
            ,@prologue

            ,body

            ,@epilogue

            (table stobj$c ',vector ',stobj$c-property)

            (table pkg-witness ',vector ',pkg-witness))))))
