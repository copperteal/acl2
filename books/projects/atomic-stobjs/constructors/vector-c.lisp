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
    (name dimensions
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

       (package-witness 'nil package-witness-supplied-p)
       (debug 'nil))

  (declare (xargs :guard (and (symbolp name)
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
                              (package-witness-p package-witness)
                              (booleanp debug))))

  `(with-output
     ,@(and (not debug)
            *constructor-output*)

     (make-event
       (let* ((name ',name)
              (package-witness (if ',package-witness-supplied-p
                                   ',package-witness
                                   (current-package state)))
              (dimensions ',dimensions)
              (dimensions (if (consp dimensions)
                              dimensions
                              (list dimensions)))
              (default-length (car dimensions))
              (default-length-name (symbolicate package-witness "*" name "-DEFAULT-LENGTH*"))

              (element-type ',element-type)
              (stobj-property (and (symbolp element-type)
                                   (getpropc element-type 'acl2::stobj)))
              (absstobj-info (and stobj-property
                                  (getpropc element-type 'acl2::absstobj-info)))
              (stobj$a-property (and (symbolp element-type)
                                     (cdr (assoc element-type (table-alist 'stobj$a-property (w state))))))
              (stobj-recognizer (cond
                                  (stobj$a-property
                                   (first (second stobj$a-property)))
                                  (stobj-property
                                   (caadr stobj-property))))
              (stobj-creator (cond
                               (stobj$a-property
                                (second (second stobj$a-property)))
                               (stobj-property
                                (cdadr stobj-property))))
              (specialize-element-type ',specialize-element-type)
              (initial-element ',initial-element)
              (initial-element-name (symbolicate package-witness "*" name "-INITIAL-ELEMENT*"))
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
                            (symbolicate package-witness name "-CONTENTS")))
              (contents-recognizer-stobj-default (symbolicate package-witness contents "P"))
              (contents-recognizer (or contents-recognizer
                                       (symbolicate package-witness contents (make-predicate-suffix contents))))
              (recognizer-stobj-default (symbolicate package-witness name "P"))
              (recognizer (or recognizer
                              (symbolicate package-witness name (make-predicate-suffix name))))
              (creator-stobj-default (symbolicate package-witness "CREATE-" name))
              (creator (or creator
                           (symbolicate package-witness "CREATE-" name)))
              (fixer (or fixer
                         (symbolicate package-witness name "-FIX")))
              (length-stobj-default (symbolicate package-witness contents "-LENGTH"))
              (length (or length
                          (symbolicate package-witness name "-LEN")))
              (resizer-stobj-default (symbolicate package-witness "RESIZE-" contents))
              (resizer (or resizer
                           (symbolicate package-witness name "-RSZ")))
              (accessor-stobj-default (symbolicate package-witness contents "I"))
              (accessor (or accessor
                            (symbolicate package-witness name "-REF")))
              (updater-stobj-default (symbolicate package-witness "UPDATE-" contents "I"))
              (updater (or updater
                           (symbolicate package-witness name "-SET")))

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
              (begin-label (symbolicate package-witness name "-BEGIN"))
              (end-label (symbolicate package-witness name "-END"))
              (fixer-hack (symbolicate package-witness name "/FIXER-HACK"))
              (contents/fh (symbolicate package-witness contents "/FIXER-HACK"))
              (prologue
               `((deflabel ,begin-label)

                 (defconst ,default-length-name ',default-length)

                 ,@(and (not stobj-property)
                        `((defconst ,initial-element-name ',initial-element)))

                 (defstobj ,name
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
                   :congruent-to ,name
                   :non-memoizable ,(not memoizable)
                   :non-executable t)))

              ;; Theorem Names
              (stobj-recognizer-of-stobj-creator (symbolicate "ATOMIC-STOBJS" stobj-recognizer "-OF-" stobj-creator))

              (contents-recognizer-tp (symbolicate package-witness contents-recognizer "-TP"))
              (contents-recognizer-cr (symbolicate package-witness contents-recognizer "-CR"))

              (recognizer-tp (symbolicate package-witness recognizer "-TP"))
              (recognizer-cr (symbolicate package-witness recognizer "-CR"))
              (recognizer-of-creator (symbolicate package-witness recognizer "-OF-" creator))
              (recognizer-of-resizer (symbolicate package-witness recognizer "-OF-" resizer))
              (recognizer-of-updater (symbolicate package-witness recognizer "-OF-" updater))

              (length-tp (symbolicate package-witness length "-TP"))
              (length-of-creator (symbolicate package-witness length "-OF-" creator))
              (length-of-resizer (symbolicate package-witness length "-OF-" resizer))
              (length-of-updater (symbolicate package-witness length "-OF-" updater))
              (length-rw (symbolicate package-witness length "-RW"))

              (resizer-tp (symbolicate package-witness resizer "-TP"))
              (resizer-of-creator (symbolicate package-witness resizer "-OF-" creator))
              (resizer-of-length (symbolicate package-witness resizer "-OF-" length))
              (resizer-of-resizer (symbolicate package-witness resizer "-OF-" resizer))
              (resizer-of-updater (symbolicate package-witness resizer "-OF-" updater))
              (resizer-of-updater-keep (symbolicate package-witness resizer-of-updater "-KEEP"))
              (resizer-of-updater-drop (symbolicate package-witness resizer-of-updater "-DROP"))
              (resizer-rw (symbolicate package-witness resizer "-RW"))

              (typep$-of-accessor (symbolicate package-witness (or stobj-recognizer "TYPEP$") "-OF-" accessor))
              (accessor-of-creator (symbolicate package-witness accessor "-OF-" creator))
              (accessor-of-resizer (symbolicate package-witness accessor "-OF-" resizer))
              (accessor-of-resizer-inner (symbolicate package-witness accessor-of-resizer "-INNER"))
              (accessor-of-resizer-outer (symbolicate package-witness accessor-of-resizer "-OUTER"))
              (accessor-of-updater (symbolicate package-witness accessor "-OF-" updater))
              (accessor-of-updater-same (symbolicate package-witness accessor-of-updater "-SAME"))
              (accessor-of-updater-diff (symbolicate package-witness accessor-of-updater "-DIFF"))

              (updater-tp (symbolicate package-witness updater "-TP"))
              (updater-of-creator (symbolicate package-witness updater "-OF-" creator))
              (updater-of-resizer (symbolicate package-witness updater "-OF-" resizer))
              (updater-of-resizer-inner (symbolicate package-witness updater-of-resizer "-INNER"))
              (updater-of-resizer-outer (symbolicate package-witness updater-of-resizer "-OUTER"))
              (updater-of-accessor (symbolicate package-witness updater "-OF-" accessor))
              (updater-of-updater (symbolicate package-witness updater "-OF-" updater))
              (updater-of-updater-same (symbolicate package-witness updater-of-updater "-SAME"))
              (updater-of-updater-diff (symbolicate package-witness updater-of-updater "-DIFF"))

              (fixer-def (symbolicate package-witness fixer "-DEF"))
              (fixer-tp (symbolicate package-witness fixer "-TP"))
              (recognizer-of-fixer (symbolicate package-witness recognizer "-OF-" fixer))
              (fixer-when-recognizer (symbolicate package-witness fixer "-WHEN-" recognizer))
              (fixer-when-not-recognizer (symbolicate package-witness fixer "-WHEN-NOT-" recognizer))

              ;; Epilogue
              (theorems (symbolicate package-witness name "-THEOREMS"))
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
                    (booleanp (,recognizer ,name))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-vector$c::recognizer-tp
                           ,@fi-bindings))))

                  (defthm ,recognizer-cr
                    (implies (,recognizer ,name)
                             (and (consp ,name)
                                  (true-listp ,name)))
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
                             (implies (,recognizer ,name)
                                      (,recognizer (,resizer length ,name)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-vector$c::recognizer-of-resizer
                                    ,@fi-bindings))))))

                  (defthm ,recognizer-of-updater
                    (implies (and (natp index)
                                  (< index ,(if resizable
                                                `(,length ,name)
                                                default-length-name))
                                  ,@(and (not (eq element-type t))
                                         (if stobj-recognizer
                                             `((,stobj-recognizer value))
                                             `(,(typep$transform 'value element-type))))
                                  (,recognizer ,name))
                             (,recognizer (,updater index value ,name)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-vector$c::recognizer-of-updater
                           ,@fi-bindings))))

                  ;; `LENGTH'
                  (defthm ,length-tp
                    (natp (,length ,name))
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
                                     (equal (,length (,resizer length ,name))
                                            length))
                            :hints
                            (("Goal"
                              :by (:functional-instance
                                   lem-vector$c::length-of-resizer
                                   ,@fi-bindings))))

                          (defthm ,length-of-updater
                            (implies (and (natp index)
                                          (< index (,length ,name)))
                                     (equal (,length (,updater index value ,name))
                                            (,length ,name)))
                            :hints
                            (("Goal"
                              :by (:functional-instance
                                   lem-vector$c::length-of-updater
                                   ,@fi-bindings)))))

                        `((defthm ,length-rw
                            (equal (,length ,name)
                                   ,default-length-name)
                            :hints
                            (("Goal"
                              :by (:functional-instance
                                   lem-vector$c::length-rw
                                   ,@fi-bindings))))))

                  ;; `RESIZER'
                  (defthm ,resizer-tp
                    (implies (,recognizer ,name)
                             (and (consp (,resizer length ,name))
                                  (true-listp (,resizer length ,name))))
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
                            (implies (,recognizer ,name)
                                     (equal (,resizer (,length ,name) ,name)
                                            ,name))
                            :hints
                            (("Goal"
                              :by (:functional-instance
                                   lem-vector$c::resizer-of-length
                                   ,@fi-bindings))))

                          (defthm ,resizer-of-resizer
                            (implies (and (natp %length)
                                          (natp length)
                                          (or (<= %length length)
                                              (<= (,length ,name) length))
                                          (,recognizer ,name))
                                     (equal (,resizer %length (,resizer length ,name))
                                            (,resizer %length ,name)))
                            :hints
                            (("Goal"
                              :by (:functional-instance
                                   lem-vector$c::resizer-of-resizer
                                   ,@fi-bindings))))

                          (defthm ,resizer-of-updater-keep
                            (implies (and (natp index)
                                          (natp length)
                                          (< index length)
                                          (< index (,length ,name)))
                                     (equal (,resizer length (,updater index value ,name))
                                            (,updater index value (,resizer length ,name))))
                            :hints
                            (("Goal"
                              :by (:functional-instance
                                   lem-vector$c::resizer-of-updater-keep
                                   ,@fi-bindings))))

                          (defthm ,resizer-of-updater-drop
                            (implies (and (natp index)
                                          (natp length)
                                          (<= length index)
                                          (< index (,length ,name)))
                                     (equal (,resizer length (,updater index value ,name))
                                            (,resizer length ,name)))
                            :hints
                            (("Goal"
                              :by (:functional-instance
                                   lem-vector$c::resizer-of-updater-drop
                                   ,@fi-bindings)))))

                        `((defthm ,resizer-rw
                            (equal (,resizer length ,name)
                                   ,name)
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
                                                         `(,length ,name)
                                                         default-length-name))
                                           (,recognizer ,name))
                                      ,(if stobj-recognizer
                                           `(,stobj-recognizer (,accessor index ,name))
                                           (typep$transform `(,accessor index ,name) element-type)))
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
                                           (< index (,length ,name)))
                                      (equal (,accessor index (,resizer length ,name))
                                             (,accessor index ,name)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-vector$c::accessor-of-resizer-inner
                                    ,@fi-bindings))))

                           (defthm ,accessor-of-resizer-outer
                             (implies (and (natp index)
                                           (natp length)
                                           (< index length)
                                           (<= (,length ,name) index))
                                      (equal (,accessor index (,resizer length ,name))
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
                             (equal (,accessor %index (,updater index value ,name))
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
                             (equal (,accessor %index (,updater index value ,name))
                                    (,accessor %index ,name)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-vector$c::accessor-of-updater-diff
                           ,@fi-bindings))))

                  ;; `UPDATER'
                  (defthm ,updater-tp
                    (implies (,recognizer ,name)
                             (and (consp (,updater index value ,name))
                                  (true-listp (,updater index value ,name))))
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
                             (implies (and (equal value (,accessor index ,name))
                                           (natp index)
                                           (natp length)
                                           (< index length)
                                           (< index (,length ,name)))
                                      (equal (,updater index value (,resizer length ,name))
                                             (,resizer length ,name)))
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
                                           (<= (,length ,name) index))
                                      (equal (,updater index value (,resizer length ,name))
                                             (,resizer length ,name)))
                             :hints
                             (("Goal"
                               :by (:functional-instance
                                    lem-vector$c::updater-of-resizer-outer
                                    ,@fi-bindings))))))

                  (defthm ,updater-of-accessor
                    (implies (and (equal %index index)
                                  (natp %index)
                                  (< %index ,(if resizable
                                                 `(,length ,name)
                                                 default-length-name))
                                  (,recognizer ,name))
                             (equal (,updater %index (,accessor index ,name) ,name)
                                    ,name))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-vector$c::updater-of-accessor
                           ,@fi-bindings))))

                  (defthm ,updater-of-updater-same
                    (implies (equal %index index)
                             (equal (,updater %index %value (,updater index value ,name))
                                    (,updater %index %value ,name)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-vector$c::updater-of-updater-same
                           ,@fi-bindings))))

                  (defthm ,updater-of-updater-diff
                    (implies (and (not (equal %index index))
                                  (natp %index)
                                  (natp index))
                             (equal (,updater %index %value (,updater index value ,name))
                                    (,updater index value (,updater %index %value ,name))))
                    :rule-classes
                    ((:rewrite :loop-stopper ((%index index ,updater))))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-vector$c::updater-of-updater-diff
                           ,@fi-bindings))))

                  ;; `FIXER'
                  (defun-inline ,fixer (,name)
                    (declare (xargs :stobjs ,name))
                    (mbe :logic (if (,recognizer ,name)
                                    ,name
                                    (with-local-stobj ,fixer-hack
                                      (mv-let (,name ,fixer-hack)
                                              (swap-stobjs ,name ,fixer-hack)
                                        ,name)))
                         :exec ,name))

                  (table fixer ',name ',fixer)

                  (defthm ,fixer-def
                    (equal (,fixer ,name)
                           (if (,recognizer ,name)
                               ,name
                               (,creator)))
                    :rule-classes :definition)

                  (in-theory
                    (disable ,fixer))

                  (defthm ,fixer-tp
                    (and (consp (,fixer ,name))
                         (true-listp (,fixer ,name)))
                    :rule-classes :type-prescription
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-vector$c::fixer-tp
                           ,@fi-bindings-with-fixer))))

                  (defthm ,recognizer-of-fixer
                    (,recognizer (,fixer ,name))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-vector$c::recognizer-of-fixer
                           ,@fi-bindings-with-fixer))))

                  (defthm ,fixer-when-recognizer
                    (implies (,recognizer ,name)
                             (equal (,fixer ,name)
                                    ,name))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-vector$c::fixer-when-recognizer
                           ,@fi-bindings-with-fixer))))

                  (defthm ,fixer-when-not-recognizer
                    (implies (not (,recognizer ,name))
                             (equal (,fixer ,name) (,creator)))
                    :hints
                    (("Goal"
                      :by (:functional-instance
                           lem-vector$c::fixer-when-not-recognizer
                           ,@fi-bindings-with-fixer)))))))

         `(progn
            ,@prologue

            ,body

            ,@epilogue

            (table package-witness ',name ',package-witness))))))
