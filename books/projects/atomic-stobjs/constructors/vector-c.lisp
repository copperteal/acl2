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

(include-book "std/util/bstar" :dir :system)

(include-book "../type-spec")
(include-book "../utilities/top")


;;;; `DEFINE-VECTOR$C/PARSE-FORM'
(defun define-vector$c/parse-form (form state)
; This function should be in logic mode because it is non-recursive and
; satisfies its guards or is trivially fixable.  However, guard checking it
; causes a combinatorial explosion in the prover.  If it is ever needed in logic
; mode, we can refactor it into bite-size, disabled pieces.
  (declare (xargs :mode :program
                  :stobjs state
                  :guard (true-listp form)))
  (b* (((list* & name dimensions kvl) form)
       ((unless (legal-variablep name))
        (mv-er 2 hard 'define-vector$c
               "Invalid stobj name: ~x0." name))
       ((unless (keyword-value-listp kvl))
        (mv-er 2 hard 'define-vector$c
               "Invalid form: ~x0." form))

       (pkg-witness (let ((suppliedp (assoc-keyword :pkg-witness kvl)))
                      (pkg-witness-fix (if suppliedp
                                           (cadr suppliedp)
                                           (current-package state)))))

       ((unless (if (atom dimensions)
                    (or (natp dimensions)
                        (and (legal-constantp dimensions)
                             (let ((qval (getpropc dimensions 'acl2::const)))
                               (and (quotep qval)
                                    (natp (cadr qval))))))
                    (and (null (cdr dimensions))
                         (let ((dimensions (car dimensions)))
                           (or (natp dimensions)
                               (and (legal-constantp dimensions)
                                    (let ((qval (getpropc dimensions 'acl2::const)))
                                      (and (quotep qval)
                                           (natp (cadr qval))))))))))
        (mv-er 2 hard 'define-vector$c
               "Invalid stobj array dimensions: ~x0." dimensions))
       ((mv default-length default-length-val)
        (cond
          ((natp dimensions)
           (mv (symbolicate$ pkg-witness "*" name "-DEFAULT-LENGTH*")
               dimensions))
          ((symbolp dimensions)
           (mv dimensions
               (cadr (getpropc dimensions 'acl2::const))))
          ((natp (car dimensions))
           (mv (symbolicate$ pkg-witness "*" name "-DEFAULT-LENGTH*")
               (car dimensions)))
          ((symbolp (car dimensions))
           (mv (car dimensions)
               (cadr (getpropc (car dimensions) 'acl2::const))))
          (t
           (mv-er 2 hard 'define-vector$c
                  "GUARD VIOLATION: ~x0" :dimensions))))

       (contents (let ((contents (assoc-keyword :contents kvl)))
                   (if contents
                       (cadr contents)
                       (symbolicate$ pkg-witness name "-CONTENTS"))))
       ((unless (legal-variablep contents))
        (mv-er 2 hard 'define-vector$c
               "~x0 is not a legal variable name." contents))
       (contents-recognizer (let ((contents-recognizer (assoc-keyword :contents-recognizer kvl)))
                              (if contents-recognizer
                                  (cadr contents-recognizer)
                                  (symbolicate$ pkg-witness contents (make-predicate-suffix contents)))))
       ((unless (legal-variablep contents-recognizer))
        (mv-er 2 hard 'define-vector$c
               "~x0 is not a legal variable name." contents-recognizer))
       (recognizer (let ((recognizer (assoc-keyword :recognizer kvl)))
                     (if recognizer
                         (cadr recognizer)
                         (symbolicate$ pkg-witness name (make-predicate-suffix name)))))
       ((unless (legal-variablep recognizer))
        (mv-er 2 hard 'define-vector$c
               "~x0 is not a legal variable name." recognizer))
       (creator (let ((creator (assoc-keyword :creator kvl)))
                  (if creator
                      (cadr creator)
                      (symbolicate$ pkg-witness "CREATE-" name))))
       ((unless (legal-variablep creator))
        (mv-er 2 hard 'define-vector$c
               "~x0 is not a legal variable name." creator))
       (fixer (let ((fixer (assoc-keyword :fixer kvl)))
                (if fixer
                    (cadr fixer)
                    (symbolicate$ pkg-witness name "-FIX"))))
       ((unless (legal-variablep fixer))
        (mv-er 2 hard 'define-vector$c
               "~x0 is not a legal variable name." fixer))
       (length (let ((length (assoc-keyword :length kvl)))
                 (if length
                     (cadr length)
                     (symbolicate$ pkg-witness name "-LEN"))))
       ((unless (legal-variablep length))
        (mv-er 2 hard 'define-vector$c
               "~x0 is not a legal variable name." length))
       (resizer (let ((resizer (assoc-keyword :resizer kvl)))
                  (if resizer
                      (cadr resizer)
                      (symbolicate$ pkg-witness name "-RSZ"))))
       ((unless (legal-variablep resizer))
        (mv-er 2 hard 'define-vector$c
               "~x0 is not a legal variable name." resizer))
       (accessor (let ((accessor (assoc-keyword :accessor kvl)))
                   (if accessor
                       (cadr accessor)
                       (symbolicate$ pkg-witness name "-REF"))))
       ((unless (legal-variablep accessor))
        (mv-er 2 hard 'define-vector$c
               "~x0 is not a legal variable name." accessor))
       (updater (let ((updater (assoc-keyword :updater kvl)))
                  (if updater
                      (cadr updater)
                      (symbolicate$ pkg-witness name "-SET"))))
       ((unless (legal-variablep updater))
        (mv-er 2 hard 'define-vector$c
               "~x0 is not a legal variable name." updater))

       (debug (let ((debug (assoc-keyword :debug kvl)))
                (and debug
                     (cadr debug))))
       ((unless (booleanp debug))
        (mv-er 2 hard 'define-vector$c
               "If provided, ~x0 must be boolean." :debug))
       (resizable (let ((resizable (assoc-keyword :resizable kvl)))
                    (if resizable
                        (cadr resizable)
                        t)))
       ((unless (booleanp resizable))
        (mv-er 2 hard 'define-vector$c
               "If provided, ~x0 must be boolean." :resizable))
       (specialize-element-type
        (let ((specialize-element-type (assoc-keyword :specialize-element-type kvl)))
          (and specialize-element-type
               (cadr specialize-element-type))))
       ((unless (booleanp specialize-element-type))
        (mv-er 2 hard 'define-vector$c
               "If provided, ~x0 must be boolean." :specialize-element-type))
       (inline (let ((inline (assoc-keyword :inline kvl)))
                 (if inline
                     (cadr inline)
                     t)))
       ((unless (booleanp inline))
        (mv-er 2 hard 'define-vector$c
               "If provided, ~x0 must be boolean." :inline))
       (memoizable (let ((memoizable (assoc-keyword :memoizable kvl)))
                     (and memoizable
                          (cadr memoizable))))
       ((unless (booleanp memoizable))
        (mv-er 2 hard 'define-vector$c
               "If provided, ~x0 must be boolean." :memoizable))
       (executable (let ((executable (assoc-keyword :executable kvl)))
                     (and executable
                          (cadr executable))))
       ((unless (booleanp executable))
        (mv-er 2 hard 'define-vector$c
               "If provided, ~x0 must be boolean." :executable))

       (element-type (let ((element-type (assoc-keyword :element-type kvl)))
                       (if element-type
                           (cadr element-type)
                           't)))
       (element-stobj-property (and (symbolp element-type)
                                    (getpropc element-type 'acl2::stobj)))
       ((unless (or (acl2-type-spec-p element-type)
                    element-stobj-property))
        (mv-er 2 hard 'define-vector$c
               "~x0 must be a stobj name or type-spec: ~x1."
               :element-type element-type))
       (initial-element (let ((initial-element (assoc-keyword :initial-element kvl)))
                          (and initial-element
                               (cadr initial-element))))
       ((unless (if (acl2-type-spec-p element-type)
                    (or (typep$ initial-element element-type)
                        (and (legal-constantp initial-element)
                             (let ((initial-element (symbol-name initial-element)))
                               (and (not (= (acl2::length initial-element) 0))
                                    (eql (char initial-element 0) #\*)
                                    (eql (char initial-element (1- (acl2::length initial-element))) #\*)))
                             (let ((qval (getpropc initial-element 'acl2::const)))
                               (and (quotep qval)
                                    (typep$ (cadr qval) element-type)))))
                    (and element-stobj-property
                         (null initial-element))))
        (mv-er 2 hard 'define-vector$c
               "Bad ~x0: ~x1.  If ~x0 is provided, ~x2 must be a type-spec and ~
               ~x0 must satisfy it.  Here, ~x2 is ~x3."
               :initial-element initial-element
               :element-type element-type))
       ((mv initial-element initial-element-val)
        (if (acl2-type-spec-p element-type)
            (cond

; This ordering precludes defining a vector with the name of a legal constant as
; initial element.  The alternative is only allowing the initial element to be a
; defined constant when the element type excludes symbols.
;
; Cue "You Can't Always Get What You Want" by The Rolling Stones.

              ((and (legal-constantp initial-element)
                    (let ((initial-element (symbol-name initial-element)))
                      (and (not (= (acl2::length initial-element) 0))
                           (eql (char initial-element 0) #\*)
                           (eql (char initial-element (1- (acl2::length initial-element))) #\*))))
               (mv initial-element
                   (cadr (getpropc initial-element 'acl2::const))))
              ((typep$ initial-element element-type)
               (mv (symbolicate$ pkg-witness "*" name "-INITIAL-ELEMENT*")
                   initial-element))
              (t
               (mv-er 2 hard 'define-vector$c
                      "GUARD VIOLATION: ~x0" :initial-element)))
            (mv nil nil)))
       (element (let ((element (assoc-keyword :element kvl)))
                  (if element
                      (if (legal-variablep (cadr element))
                          (cadr element)
                          (er hard 'define-vector$c
                              "~x0 is not a legal variable name." element))
                      (if element-stobj-property
                          element-type
                          (intern-in-package-of-symbol "X" pkg-witness)))))
       (element-absstobj-info (and element-stobj-property
                                   (getpropc element-type 'acl2::absstobj-info)))
       (element-stobj$a-property (and element-stobj-property
                                      (stobj$a-property element-type (w state))))
       (element-recognizer (access stobj$a-property element-stobj$a-property :recognizer))
       (element-creator (access stobj$a-property element-stobj$a-property :creator)))
    (mv (list (cons :default-length-val default-length-val)
              (cons :element-stobj-property element-stobj-property)
              (cons :initial-element-val initial-element-val)
              (cons :specialize-element-type specialize-element-type)
              (cons :element-absstobj-info element-absstobj-info)
              (cons :element-stobj$a-property element-stobj$a-property)
              (cons :element-recognizer element-recognizer)
              (cons :element-creator element-creator)
              (cons :inline inline)
              (cons :executable executable)
              (cons :debug debug)
              (cons :begin-label (symbolicate$ pkg-witness name "-BEGIN"))
              (cons :end-label (symbolicate$ pkg-witness name "-END")))
        (make vector$c-property
              :name name
              :recognizer recognizer
              :creator creator
              :fixer fixer
              :length length
              :resizer resizer
              :accessor accessor
              :updater updater
              :contents contents
              :contents-recognizer contents-recognizer
              :element element
              :element-type element-type
              :initial-element initial-element
              :default-length default-length
              :resizable resizable
              :memoizable memoizable
              :theory (symbolicate$ pkg-witness name "-THEORY")
              :fi-theorems (symbolicate$ pkg-witness "*" name "-FI-THEOREMS*")
              :pkg-witness pkg-witness))))


;;;; `DEFINE-VECTOR$C/MAKE-DEFSTOBJ-DOUBLETS'
(defun define-vector$c/make-defstobj-doublets (property)
  (declare (xargs :mode :program
                  :guard (vector$c-property-p property)))
  (b* ((pkg-witness (access vector$c-property property :pkg-witness))
       (vector (access vector$c-property property :name))
       (doublets ())
       (contents (access vector$c-property property :contents))
       (contents-recognizer (access vector$c-property property :contents-recognizer))
       (contents-recognizer-stobj-default (symbolicate$ pkg-witness contents "P"))
       (doublets (if (eq contents-recognizer-stobj-default contents-recognizer)
                     doublets
                     (cons (list contents-recognizer-stobj-default
                                 contents-recognizer)
                           doublets)))
       (recognizer (access vector$c-property property :recognizer))
       (recognizer-stobj-default (symbolicate$ pkg-witness vector "P"))
       (doublets (if (eq recognizer-stobj-default recognizer)
                     doublets
                     (cons (list recognizer-stobj-default
                                 recognizer)
                           doublets)))
       (creator (access vector$c-property property :creator))
       (creator-stobj-default (symbolicate$ pkg-witness "CREATE-" vector))
       (doublets (if (eq creator-stobj-default creator)
                     doublets
                     (cons (list creator-stobj-default
                                 creator)
                           doublets)))
       (length (access vector$c-property property :length))
       (length-stobj-default (symbolicate$ pkg-witness contents "-LENGTH"))
       (doublets (if (eq length-stobj-default length)
                     doublets
                     (cons (list length-stobj-default
                                 length)
                           doublets)))
       (resizer (access vector$c-property property :resizer))
       (resizer-stobj-default (symbolicate$ pkg-witness "RESIZE-" contents))
       (doublets (if (eq resizer-stobj-default resizer)
                     doublets
                     (cons (list resizer-stobj-default
                                 resizer)
                           doublets)))
       (accessor (access vector$c-property property :accessor))
       (accessor-stobj-default (symbolicate$ pkg-witness contents "I"))
       (doublets (if (eq accessor-stobj-default accessor)
                     doublets
                     (cons (list accessor-stobj-default
                                 accessor)
                           doublets)))
       (updater (access vector$c-property property :updater))
       (updater-stobj-default (symbolicate$ pkg-witness "UPDATE-" contents "I"))
       (doublets (if (eq updater-stobj-default updater)
                     doublets
                     (cons (list updater-stobj-default
                                 updater)
                           doublets))))
    doublets))


;;;; `DEFINE-VECTOR$C/MAKE-DEFSTOBJ-FORM'
(defun define-vector$c/make-defstobj-form (tmp property)
  (declare (xargs :mode :program
                  :guard (and (alistp tmp)
                              (vector$c-property-p property))))
  (let ((contents (access vector$c-property property :contents))
        (element-type (access vector$c-property property :element-type))
        (default-length (access vector$c-property property :default-length))
        (element-stobj-property (cdr (assoc :element-stobj-property tmp)))
        (specialize-element-type (cdr (assoc :specialize-element-type tmp)))
        (initial-element-val (cdr (assoc :initial-element-val tmp)))
        (resizable (access vector$c-property property :resizable))
        (doublets (define-vector$c/make-defstobj-doublets property))
        (inline (cdr (assoc :inline tmp)))
        (memoizable (access vector$c-property property :memoizable))
        (executable (cdr (assoc :executable tmp))))
    `(defstobj ,(access vector$c-property property :name)
       (,contents :type (acl2::array ,element-type (,default-length))
                  ,@(and (not element-stobj-property)
                         `(:element-type
                           ,(if specialize-element-type
                                element-type
                                t)
                           :initially ,initial-element-val))
                  :resizable ,resizable)
       :renaming ,doublets
       :inline ,inline
       :non-memoizable ,(not memoizable)
       :non-executable ,(not executable))))


;;;; `DEFINE-VECTOR$C/APPLY-FIXER-HACK'
(defun define-vector$c/apply-fixer-hack (property form)
  (declare (xargs :mode :program))
  (b* ((pkg-witness (access vector$c-property property :pkg-witness))
       (vector (access vector$c-property property :name))
       (kvl (list* :congruent-to vector
                   :non-executable t
                   (remove-keyword :renaming
                                   (remove-keyword :non-executable
                                                   (cdddr form)))))
       (name (symbolicate$ pkg-witness vector "/FIXER-HACK"))
       (contents (access vector$c-property property :contents))
       (field-spec (cons (symbolicate$ pkg-witness contents "/FIXER-HACK")
                         (cdaddr form))))
    (list* 'defstobj name field-spec kvl)))


;;;; `DEFINE-VECTOR$C/MAKE-FI-BINDINGS'
(defun define-vector$c/make-fi-bindings (tmp property)
  (declare (xargs :mode :program
                  :guard (and (alistp tmp)
                              (vector$c-property-p property))))
  (let ((element-recognizer (cdr (assoc :element-recognizer tmp)))
        (element-creator (cdr (assoc :element-creator tmp)))
        (default-length (access vector$c-property property :default-length))
        (element (access vector$c-property property :element))
        (element-type (access vector$c-property property :element-type))
        (initial-element (access vector$c-property property :initial-element))
        (contents-recognizer (access vector$c-property property :contents-recognizer))
        (recognizer (access vector$c-property property :recognizer))
        (creator (access vector$c-property property :creator))
        (fixer (access vector$c-property property :fixer))
        (length (access vector$c-property property :length))
        (resizer (access vector$c-property property :resizer))
        (accessor (access vector$c-property property :accessor))
        (updater (access vector$c-property property :updater)))
    `((lem-vector$c::default-length (lambda ()
                                      ,default-length))
      (lem-vector$c::element-recognizer ,(or element-recognizer
                                             `(lambda (,element)
                                                ,(typep$transform element element-type))))
      (lem-vector$c::initial-element ,(or element-creator
                                          `(lambda ()
                                             ,initial-element)))
      (lem-vector$c::contents-recognizer ,contents-recognizer)
      (lem-vector$c::recognizer ,recognizer)
      (lem-vector$c::creator ,creator)
      (lem-vector$c::fixer ,fixer)
      (lem-vector$c::length ,length)
      (lem-vector$c::resizer ,resizer)
      (lem-vector$c::accessor ,accessor)
      (lem-vector$c::updater ,updater))))


;;;; `DEFINE-VECTOR$C/MAKE-THEOREMS'
(defun define-vector$c/make-theorems (tmp property)
  (declare (xargs :mode :program
                  :guard (and (alistp tmp)
                              (vector$c-property-p property))))
  (b* ((vector (access vector$c-property property :name))
       (recognizer (access vector$c-property property :recognizer))
       (creator (access vector$c-property property :creator))
       (fixer (access vector$c-property property :fixer))
       (length (access vector$c-property property :length))
       (resizer (access vector$c-property property :resizer))
       (accessor (access vector$c-property property :accessor))
       (updater (access vector$c-property property :updater))
       (contents (access vector$c-property property :contents))
       (contents-recognizer (access vector$c-property property :contents-recognizer))
       ;; TODO: replace `VALUE' with the `ELEMENT' field
       (element-type (access vector$c-property property :element-type))
       (initial-element-name (access vector$c-property property :initial-element))
       (default-length-name (access vector$c-property property :default-length))
       (resizable (access vector$c-property property :resizable))
       (fi-bindings (access vector$c-property property :fi-bindings))
       (fi-theorems (access vector$c-property property :fi-theorems))
       (pkg-witness (access vector$c-property property :pkg-witness))

       (element-recognizer (cdr (assoc :element-recognizer tmp)))
       (element-creator (cdr (assoc :element-creator tmp)))

       ;; Theorem Names
       (fixer-def (symbolicate$ pkg-witness fixer "-DEF"))
       (fixer-tp (symbolicate$ pkg-witness fixer "-TP"))
       (recognizer-of-fixer (symbolicate$ pkg-witness recognizer "-OF-" fixer))
       (fixer-when-recognizer (symbolicate$ pkg-witness fixer "-WHEN-" recognizer))
       (fixer-when-not-recognizer (symbolicate$ pkg-witness fixer "-WHEN-NOT-" recognizer))

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

       (typep$-of-accessor (symbolicate$ pkg-witness (or element-recognizer "TYPEP$") "-OF-" accessor))
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
       (updater-of-updater-diff (symbolicate$ pkg-witness updater-of-updater "-DIFF")))
    `(
      ;; `FIXER'
      (defthm ,fixer-def
        (equal (,fixer ,vector)
               (if (,recognizer ,vector)
                   ,vector
                   (,creator)))
        :rule-classes :definition)

      (make-event
        `(encapsulate ()
           (set-ignore-ok t)

           ,@(loop$ :for name :in ,fi-theorems
                   :as body :in (sublis ',(doublets-to-alist fi-bindings)
                                        lem-vector$c::*constraints*)
                   :collect `(defthm ,name
                               ,body
                               :rule-classes nil))))

      (local
        (in-theory
          (union-theories
           (strip-theory (set-difference-theories
                          (current-theory :here)
                          (current-theory 'working-theory)))
           (current-theory 'working-theory)
           '((:d ,fixer-def)))))

      (defthm-fi ,fixer-tp
        (and (consp (,fixer ,vector))
             (true-listp (,fixer ,vector)))
        :rule-classes :type-prescription
        :theorem lem-vector$c::fixer-tp
        :bindings ,fi-bindings)

      (defthm-fi ,recognizer-of-fixer
        (,recognizer (,fixer ,vector))
        :theorem lem-vector$c::recognizer-of-fixer
        :bindings ,fi-bindings)

      (defthm-fi ,fixer-when-recognizer
        (implies (,recognizer ,vector)
                 (equal (,fixer ,vector)
                        ,vector))
        :theorem lem-vector$c::fixer-when-recognizer
        :bindings ,fi-bindings)

      (defthm-fi ,fixer-when-not-recognizer
        (implies (not (,recognizer ,vector))
                 (equal (,fixer ,vector) (,creator)))
        :theorem lem-vector$c::fixer-when-not-recognizer
        :bindings ,fi-bindings)

      ;; `CONTENTS-RECOGNIZER'
      (defthm-fi ,contents-recognizer-tp
        (booleanp (,contents-recognizer ,contents))
        :rule-classes :type-prescription
        :theorem lem-vector$c::contents-recognizer-tp
        :bindings ,fi-bindings)

      (defthm-fi ,contents-recognizer-cr
        (implies (,contents-recognizer ,contents)
                 (true-listp ,contents))
        :rule-classes :compound-recognizer
        :theorem lem-vector$c::contents-recognizer-cr
        :bindings ,fi-bindings)

      ;; `RECOGNIZER'
      (defthm-fi ,recognizer-tp
        (booleanp (,recognizer ,vector))
        :rule-classes :type-prescription
        :theorem lem-vector$c::recognizer-tp
        :bindings ,fi-bindings)

      (defthm-fi ,recognizer-cr
        (implies (,recognizer ,vector)
                 (and (consp ,vector)
                      (true-listp ,vector)))
        :rule-classes :compound-recognizer
        :theorem lem-vector$c::recognizer-cr
        :bindings ,fi-bindings)

      (defthm-fi ,recognizer-of-creator
        (,recognizer (,creator))
        :theorem lem-vector$c::recognizer-of-creator
        :bindings ,fi-bindings)

      ,@(and resizable
             `((defthm-fi ,recognizer-of-resizer
                 (implies (,recognizer ,vector)
                          (,recognizer (,resizer length ,vector)))
                 :theorem lem-vector$c::recognizer-of-resizer
                 :bindings ,fi-bindings)))

      (defthm-fi ,recognizer-of-updater
        (implies (and (natp index)
                      (< index ,(if resizable
                                    `(,length ,vector)
                                    default-length-name))
                      ,@(and (not (eq element-type t))
                             (if element-recognizer
                                 `((,element-recognizer value))
                                 `(,(typep$transform 'value element-type))))
                      (,recognizer ,vector))
                 (,recognizer (,updater index value ,vector)))
        :theorem lem-vector$c::recognizer-of-updater
        :bindings ,fi-bindings)

      ;; `LENGTH'
      (defthm-fi ,length-tp
        (natp (,length ,vector))
        :rule-classes :type-prescription
        :theorem lem-vector$c::length-tp
        :bindings ,fi-bindings)

      ,@(if resizable
            `((defthm-fi ,length-of-creator
                (equal (,length (,creator))
                       ,default-length-name)
                :theorem lem-vector$c::length-of-creator
                :bindings ,fi-bindings)

              (defthm-fi ,length-of-resizer
                (implies (natp length)
                         (equal (,length (,resizer length ,vector))
                                length))
                :theorem lem-vector$c::length-of-resizer
                :bindings ,fi-bindings)

              (defthm-fi ,length-of-updater
                (implies (and (natp index)
                              (< index (,length ,vector)))
                         (equal (,length (,updater index value ,vector))
                                (,length ,vector)))
                :theorem lem-vector$c::length-of-updater
                :bindings ,fi-bindings))

            `((defthm-fi ,length-rw
                (equal (,length ,vector)
                       ,default-length-name)
                :theorem lem-vector$c::length-rw
                :bindings ,fi-bindings)))

      ;; `RESIZER'
      (defthm-fi ,resizer-tp
        (implies (,recognizer ,vector)
                 (and (consp (,resizer length ,vector))
                      (true-listp (,resizer length ,vector))))
        :rule-classes :type-prescription
        :theorem lem-vector$c::resizer-tp
        :bindings ,fi-bindings)

      ,@(if resizable
            `((defthm-fi ,resizer-of-creator
                (implies (equal length ,default-length-name)
                         (equal (,resizer length (,creator))
                                (,creator)))
                :theorem lem-vector$c::resizer-of-creator
                :bindings ,fi-bindings)

              (defthm-fi ,resizer-of-length
                (implies (,recognizer ,vector)
                         (equal (,resizer (,length ,vector) ,vector)
                                ,vector))
                :theorem lem-vector$c::resizer-of-length
                :bindings ,fi-bindings)

              (defthm-fi ,resizer-of-resizer
                (implies (and (natp %length)
                              (natp length)
                              (or (<= %length length)
                                  (<= (,length ,vector) length))
                              (,recognizer ,vector))
                         (equal (,resizer %length (,resizer length ,vector))
                                (,resizer %length ,vector)))
                :theorem lem-vector$c::resizer-of-resizer
                :bindings ,fi-bindings)

              (defthm-fi ,resizer-of-updater-keep
                (implies (and (natp index)
                              (natp length)
                              (< index length)
                              (< index (,length ,vector)))
                         (equal (,resizer length (,updater index value ,vector))
                                (,updater index value (,resizer length ,vector))))
                :theorem lem-vector$c::resizer-of-updater-keep
                :bindings ,fi-bindings)

              (defthm-fi ,resizer-of-updater-drop
                (implies (and (natp index)
                              (natp length)
                              (<= length index)
                              (< index (,length ,vector)))
                         (equal (,resizer length (,updater index value ,vector))
                                (,resizer length ,vector)))
                :theorem lem-vector$c::resizer-of-updater-drop
                :bindings ,fi-bindings))

            `((defthm-fi ,resizer-rw
                (equal (,resizer length ,vector)
                       ,vector)
                :theorem lem-vector$c::resizer-rw
                :bindings ,fi-bindings)))

      ;; `ACCESSOR'
      ,@(and (not (eq element-type t))
             `((defthm-fi ,typep$-of-accessor
                 (implies (and (natp index)
                               (< index ,(if resizable
                                             `(,length ,vector)
                                             default-length-name))
                               (,recognizer ,vector))
                          ,(if element-recognizer
                               `(,element-recognizer (,accessor index ,vector))
                               (typep$transform `(,accessor index ,vector) element-type)))
                 :rule-classes
                 (:rewrite
                  :type-prescription)
                 :theorem lem-vector$c::element-recognizer-of-accessor
                 :bindings ,fi-bindings)))

      (defthm-fi ,accessor-of-creator
        (implies (and (natp index)
                      (< index ,default-length-name))
                 (equal (,accessor index (,creator))
                        ,(if element-creator
                             `(,element-creator)
                             initial-element-name)))
        :theorem lem-vector$c::accessor-of-creator
        :bindings ,fi-bindings)

      ,@(and resizable
             `((defthm-fi ,accessor-of-resizer-inner
                 (implies (and (natp index)
                               (natp length)
                               (< index length)
                               (< index (,length ,vector)))
                          (equal (,accessor index (,resizer length ,vector))
                                 (,accessor index ,vector)))
                 :theorem lem-vector$c::accessor-of-resizer-inner
                 :bindings ,fi-bindings)

               (defthm-fi ,accessor-of-resizer-outer
                 (implies (and (natp index)
                               (natp length)
                               (< index length)
                               (<= (,length ,vector) index))
                          (equal (,accessor index (,resizer length ,vector))
                                 ,(if element-creator
                                      `(,element-creator)
                                      initial-element-name)))
                 :theorem lem-vector$c::accessor-of-resizer-outer
                 :bindings ,fi-bindings)))

      (defthm-fi ,accessor-of-updater-same
        (implies (equal %index index)
                 (equal (,accessor %index (,updater index value ,vector))
                        value))
        :theorem lem-vector$c::accessor-of-updater-same
        :bindings ,fi-bindings)

      (defthm-fi ,accessor-of-updater-diff
        (implies (and (not (equal %index index))
                      (natp %index)
                      (natp index))
                 (equal (,accessor %index (,updater index value ,vector))
                        (,accessor %index ,vector)))
        :theorem lem-vector$c::accessor-of-updater-diff
        :bindings ,fi-bindings)

      ;; `UPDATER'
      (defthm-fi ,updater-tp
        (implies (,recognizer ,vector)
                 (and (consp (,updater index value ,vector))
                      (true-listp (,updater index value ,vector))))
        :rule-classes :type-prescription
        :theorem lem-vector$c::updater-tp
        :bindings ,fi-bindings)

      (defthm-fi ,updater-of-creator
        (implies (and (equal value ,(if element-creator
                                        `(,element-creator)
                                        initial-element-name))
                      (natp index)
                      (< index ,default-length-name))
                 (equal (,updater index value (,creator))
                        (,creator)))
        :theorem lem-vector$c::updater-of-creator
        :bindings ,fi-bindings)

      ,@(and resizable
             `((defthm-fi ,updater-of-resizer-inner
                 (implies (and (equal value (,accessor index ,vector))
                               (natp index)
                               (natp length)
                               (< index length)
                               (< index (,length ,vector)))
                          (equal (,updater index value (,resizer length ,vector))
                                 (,resizer length ,vector)))
                 :theorem lem-vector$c::updater-of-resizer-inner
                 :bindings ,fi-bindings)

               (defthm-fi ,updater-of-resizer-outer
                 (implies (and (equal value ,(if element-creator
                                                 `(,element-creator)
                                                 initial-element-name))
                               (natp index)
                               (natp length)
                               (< index length)
                               (<= (,length ,vector) index))
                          (equal (,updater index value (,resizer length ,vector))
                                 (,resizer length ,vector)))
                 :theorem lem-vector$c::updater-of-resizer-outer
                 :bindings ,fi-bindings)))

      (defthm-fi ,updater-of-accessor
        (implies (and (equal %index index)
                      (natp %index)
                      (< %index ,(if resizable
                                     `(,length ,vector)
                                     default-length-name))
                      (,recognizer ,vector))
                 (equal (,updater %index (,accessor index ,vector) ,vector)
                        ,vector))
        :theorem lem-vector$c::updater-of-accessor
        :bindings ,fi-bindings)

      (defthm-fi ,updater-of-updater-same
        (implies (equal %index index)
                 (equal (,updater %index %value (,updater index value ,vector))
                        (,updater %index %value ,vector)))
        :theorem lem-vector$c::updater-of-updater-same
        :bindings ,fi-bindings)

      (defthm-fi ,updater-of-updater-diff
        (implies (and (not (equal %index index))
                      (natp %index)
                      (natp index))
                 (equal (,updater %index %value (,updater index value ,vector))
                        (,updater index value (,updater %index %value ,vector))))
        :rule-classes
        ;; TODO: rename %index index to index1 index2
        ((:rewrite :loop-stopper ((%index index ,updater))))
        :theorem lem-vector$c::updater-of-updater-diff
        :bindings ,fi-bindings))))


;;;; `DEFINE-VECTOR$C-FN'
(defun define-vector$c-fn (form debug)
  (declare (xargs :mode :program
                  :guard (true-listp form)))
  `(with-output
     ,@(and (not debug)
            ;; TODO: revisit constructor output settings
            *constructor-output*)
     (make-event
       (b* (((mv tmp property) (define-vector$c/parse-form ',form state))
            (fi-bindings (define-vector$c/make-fi-bindings tmp property))
            (property (change vector$c-property property
                              :fi-bindings fi-bindings))

            (vector (access vector$c-property property :name))
            (recognizer (access vector$c-property property :recognizer))
            (fixer (access vector$c-property property :fixer))
            (element-stobj-property (cdr (assoc :element-stobj-property tmp)))
            (pkg-witness (access vector$c-property property :pkg-witness))

            (begin-label (cdr (assoc :begin-label tmp)))
            (end-label (cdr (assoc :end-label tmp)))
            (theory (access vector$c-property property :theory))

            (defstobj-form (define-vector$c/make-defstobj-form tmp property))
            (fixer-hack-form (define-vector$c/apply-fixer-hack property defstobj-form))
            (fixer-hack (second fixer-hack-form)))

         `(progn
            (deflabel ,begin-label)

            ,@(let ((default-length-name (access vector$c-property
                                                 property
                                                 :default-length))
                    (default-length (cdr (assoc :default-length-val tmp))))
                (and (not (getpropc default-length-name 'acl2::const))
                     `((defconst ,default-length-name ',default-length))))

            ,@(let ((initial-element-name (access vector$c-property
                                                  property
                                                  :initial-element))
                    (initial-element (cdr (assoc :initial-element-val tmp))))
                (and (not element-stobj-property)
                     (not (getpropc initial-element-name 'acl2::const))
                     `((defconst ,initial-element-name ',initial-element))))

            ,defstobj-form

            ,fixer-hack-form

            (encapsulate ()

              ,@(and element-stobj-property
                     (let ((element-recognizer (cdr (assoc :element-recognizer tmp)))
                           (element-creator (cdr (assoc :element-creator tmp))))
                       `((local
                           (defthm element-constraints
                             (,element-recognizer (,element-creator)))))))

              (local
                (deflabel end-of-prologue))

              (local
                (include-book ,(if (access vector$c-property property :resizable)
                                   "projects/atomic-stobjs/lemmas/vector-c-resizable"
                                   "projects/atomic-stobjs/lemmas/vector-c-fixed-length")
                              :dir :system))

              (local
                (table acl2::theory-invariant-table nil nil :clear))

              (local
                (in-theory
                  (union-theories (current-theory 'acl2::ground-zero)
                                  (set-difference-theories
                                   (universal-theory 'end-of-prologue)
                                   (universal-theory ',begin-label)))))

              ,@(let ((element-absstobj-info (cdr (assoc :element-absstobj-info tmp))))
                  (and element-absstobj-info
                       `((local
                           (in-theory
                             (enable ,@(strip-cars (cdr element-absstobj-info))))))))

              (local
                (in-theory
                  (e/d (type-spec-theory)
                       (make-list-ac
                        (:e make-list-ac)))))

              (local
                (deflabel working-theory))

              (make-event

; The `FI-THEOREMS' constant must be defined inside the local context where
; `LEM-VECTOR$C::*CONSTRAINTS*' is a defined constant.

                (list 'defconst ',(access vector$c-property
                                          property
                                          :fi-theorems)
                      (list 'quote
                            (loop$ :for n
                                  :from 0
                                  :to (1- (len lem-vector$c::*constraints*))
                                  :collect (symbolicate$ ',pkg-witness ',vector "-FI-" n)))))

              (defun-inline ,fixer (,vector)
                (declare (xargs :stobjs ,vector))
                (mbe :logic (if (,recognizer ,vector)
                                ,vector
                                (with-local-stobj ,fixer-hack
                                  (mv-let (,vector ,fixer-hack)
                                          (swap-stobjs ,vector ,fixer-hack)
                                    ,vector)))
                     :exec ,vector))

              ,@(define-vector$c/make-theorems tmp property))

            (deflabel ,end-label)

            (deftheory-static ,theory
              (union-theories
               (strip-theory
                (set-difference-theories
                 (current-theory ',end-label)
                 (current-theory ',begin-label)))
               '((:d ,(symbolicate$ pkg-witness fixer "-DEF")))))

            (in-theory
              (union-theories (current-theory ',begin-label)
                              (theory ',theory)))

            (table stobj$c ',vector ',property))))))


;;;; `DEFINE-VECTOR$C'
(defmacro define-vector$c
    (&whole form
       vector dimensions
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

       (pkg-witness 'nil)
       (debug 'nil))
  (declare (xargs :guard t)
           (ignore vector dimensions
                   element-type specialize-element-type
                   initial-element resizable

                   inline memoizable executable

                   contents
                   contents-recognizer
                   recognizer
                   creator
                   fixer
                   length
                   resizer
                   accessor
                   updater

                   pkg-witness))
  (define-vector$c-fn form debug))
