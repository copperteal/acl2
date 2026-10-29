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

#|
(include-book "../lemmas/hash-table-c")
|#

(include-book "std/util/bstar" :dir :system)

(include-book "../type-spec")
(include-book "../utilities/top")


;;;; `DEFINE-HASH-TABLE$C/PARSE-FORM'
(defun define-hash-table$c/parse-form (form state)
; See comment at top of `DEFINE-HASH-TABLE$C/PARSE-FORM'
  (declare (xargs :mode :program
                  :stobjs state
                  :guard (true-listp form)))
  (b* (((list* & name test kvl) form)
       ((unless (legal-variablep name))
        (mv-er 2 hard 'define-hash-table$c
               "Invalid stobj name: ~x0." name))
       ((unless (keyword-value-listp kvl))
        (mv-er 2 hard 'define-hash-table$c
               "Invalid form: ~x0." form))

       (pkg-witness (let ((suppliedp (assoc-keyword :pkg-witness kvl)))
                      (pkg-witness-fix (if suppliedp
                                           (cadr suppliedp)
                                           (current-package state)))))

       ((unless (member test '(eq eql equal hons-equal) :test 'eq))
        (mv-er 2 hard 'define-hash-table$c
               "Invalid stobj hash-table test: ~x0." test))

       (contents (let ((contents (assoc-keyword :contents kvl)))
                   (if contents
                       (cadr contents)
                       (symbolicate$ pkg-witness name "-CONTENTS"))))
       ((unless (legal-variablep contents))
        (mv-er 2 hard 'define-hash-table$c
               "~x0 is not a legal variable name." contents))
       (contents-recognizer (let ((contents-recognizer (assoc-keyword :contents-recognizer kvl)))
                              (if contents-recognizer
                                  (cadr contents-recognizer)
                                  (symbolicate$ pkg-witness contents (make-predicate-suffix contents)))))
       ((unless (legal-variablep contents-recognizer))
        (mv-er 2 hard 'define-hash-table$c
               "~x0 is not a legal variable name." contents-recognizer))
       (recognizer (let ((recognizer (assoc-keyword :recognizer kvl)))
                     (if recognizer
                         (cadr recognizer)
                         (symbolicate$ pkg-witness name (make-predicate-suffix name)))))
       ((unless (legal-variablep recognizer))
        (mv-er 2 hard 'define-hash-table$c
               "~x0 is not a legal variable name." recognizer))
       (creator (let ((creator (assoc-keyword :creator kvl)))
                  (if creator
                      (cadr creator)
                      (symbolicate$ pkg-witness "CREATE-" name))))
       ((unless (legal-variablep creator))
        (mv-er 2 hard 'define-hash-table$c
               "~x0 is not a legal variable name." creator))
       (fixer (let ((fixer (assoc-keyword :fixer kvl)))
                (if fixer
                    (cadr fixer)
                    (symbolicate$ pkg-witness name "-FIX"))))
       ((unless (legal-variablep fixer))
        (mv-er 2 hard 'define-hash-table$c
               "~x0 is not a legal variable name." fixer))
       (accessor (let ((accessor (assoc-keyword :accessor kvl)))
                   (if accessor
                       (cadr accessor)
                       (symbolicate$ pkg-witness name "-GET"))))
       ((unless (legal-variablep accessor))
        (mv-er 2 hard 'define-hash-table$c
               "~x0 is not a legal variable name." accessor))
       (updater (let ((updater (assoc-keyword :updater kvl)))
                  (if updater
                      (cadr updater)
                      (symbolicate$ pkg-witness name "-PUT"))))
       ((unless (legal-variablep updater))
        (mv-er 2 hard 'define-hash-table$c
               "~x0 is not a legal variable name." updater))
       (boundp (let ((boundp (assoc-keyword :boundp kvl)))
                 (if boundp
                     (cadr boundp)
                     (symbolicate$ pkg-witness name "-BNDP"))))
       ((unless (legal-variablep boundp))
        (mv-er 2 hard 'define-hash-table$c
               "~x0 is not a legal variable name." boundp))
       (getp (let ((getp (assoc-keyword :getp kvl)))
               (if getp
                   (cadr getp)
                   (symbolicate$ pkg-witness name "-GETP"))))
       ((unless (legal-variablep getp))
        (mv-er 2 hard 'define-hash-table$c
               "~x0 is not a legal variable name." getp))
       (remover (let ((remover (assoc-keyword :remover kvl)))
                  (if remover
                      (cadr remover)
                      (symbolicate$ pkg-witness name "-REM"))))
       ((unless (legal-variablep remover))
        (mv-er 2 hard 'define-hash-table$c
               "~x0 is not a legal variable name." remover))
       (count (let ((count (assoc-keyword :count kvl)))
                (if count
                    (cadr count)
                    (symbolicate$ pkg-witness name "-CNT"))))
       ((unless (legal-variablep count))
        (mv-er 2 hard 'define-hash-table$c
               "~x0 is not a legal variable name." count))
       (clear (let ((clear (assoc-keyword :clear kvl)))
                (if clear
                    (cadr clear)
                    (symbolicate$ pkg-witness name "-CLR"))))
       ((unless (legal-variablep clear))
        (mv-er 2 hard 'define-hash-table$c
               "~x0 is not a legal variable name." clear))
       (init (let ((init (assoc-keyword :init kvl)))
               (if init
                   (cadr init)
                   (symbolicate$ pkg-witness name "-INIT"))))
       ((unless (legal-variablep init))
        (mv-er 2 hard 'define-hash-table$c
               "~x0 is not a legal variable name." init))
       (keys (let ((keys (assoc-keyword :keys kvl)))
               (if keys
                   (cadr keys)
                   (symbolicate$ pkg-witness name "-KEYS"))))
       ((unless (legal-variablep keys))
        (mv-er 2 hard 'define-hash-table$c
               "~x0 is not a legal variable name." keys))
       (keys-set (let ((keys-set (assoc-keyword :keys-set kvl)))
                   (if keys-set
                       (cadr keys-set)
                       (symbolicate$ pkg-witness keys "-SET"))))
       ((unless (legal-variablep keys-set))
        (mv-er 2 hard 'define-hash-table$c
               "~x0 is not a legal variable name." keys-set))

       (debug (let ((debug (assoc-keyword :debug kvl)))
                (and debug
                     (cadr debug))))
       ((unless (booleanp debug))
        (mv-er 2 hard 'define-hash-table$c
               "If provided, ~x0 must be boolean." :debug))
       (copyable (let ((copyable (assoc-keyword :copyable kvl)))
                   (if copyable
                       (cadr copyable)
                       t)))
       ((unless (booleanp copyable))
        (mv-er 2 hard 'define-hash-table$c
               "If provided, ~x0 must be boolean." :copyable))
       (size (let ((size (assoc-keyword :size kvl)))
               (and size
                    (cadr size))))
       ((unless (or (null size)
                    (natp size)))
        (mv-er 2 hard 'define-hash-table$c
               "If provided, ~x0 must be NIL or satisfy NATP." :size))
       (inline (let ((inline (assoc-keyword :inline kvl)))
                 (if inline
                     (cadr inline)
                     t)))
       ((unless (booleanp inline))
        (mv-er 2 hard 'define-hash-table$c
               "If provided, ~x0 must be boolean." :inline))
       (memoizable (let ((memoizable (assoc-keyword :memoizable kvl)))
                     (and memoizable
                          (cadr memoizable))))
       ((unless (booleanp memoizable))
        (mv-er 2 hard 'define-hash-table$c
               "If provided, ~x0 must be boolean." :memoizable))
       (executable (let ((executable (assoc-keyword :executable kvl)))
                     (and executable
                          (cadr executable))))
       ((unless (booleanp executable))
        (mv-er 2 hard 'define-hash-table$c
               "If provided, ~x0 must be boolean." :executable))

       (element-type (let ((element-type (assoc-keyword :element-type kvl)))
                       (if element-type
                           (cadr element-type)
                           't)))
       (element-stobj-property (and (symbolp element-type)
                                    (getpropc element-type 'acl2::stobj)))
       ((unless (or (acl2-type-spec-p element-type)
                    element-stobj-property))
        (mv-er 2 hard 'define-hash-table$c
               "~x0 must be a stobj name or type-spec: ~x1."
               :element-type element-type))
       (default-value (let ((default-value (assoc-keyword :default-value kvl)))
                        (and default-value
                             (cadr default-value))))
       ((unless (if (acl2-type-spec-p element-type)
                    (or (typep$ default-value element-type)
                        (and (legal-constantp default-value)
                             (let ((default-value (symbol-name default-value)))
                               (and (not (= (acl2::length default-value) 0))
                                    (eql (char default-value 0) #\*)
                                    (eql (char default-value (1- (acl2::length default-value))) #\*)))
                             (let ((qval (getpropc default-value 'acl2::const)))
                               (and (quotep qval)
                                    (typep$ (cadr qval) element-type)))))
                    (and element-stobj-property
                         (null default-value))))
        (mv-er 2 hard 'define-hash-table$c
               "Bad ~x0: ~x1.  If ~x0 is provided, ~x2 must be a type-spec and ~
               ~x0 must satisfy it.  Here, ~x2 is ~x3."
               :default-value default-value
               :element-type element-type))
       ((mv default-value default-value-val)
        (if (acl2-type-spec-p element-type)
            (cond ; See comment in `DEFINE-VECTOR$C/PARSE-FORM'
              ((and (legal-constantp default-value)
                    (let ((default-value (symbol-name default-value)))
                      (and (not (= (acl2::length default-value) 0))
                           (eql (char default-value 0) #\*)
                           (eql (char default-value (1- (acl2::length default-value))) #\*))))
               (mv default-value
                   (cadr (getpropc default-value 'acl2::const))))
              ((typep$ default-value element-type)
               (mv (symbolicate$ pkg-witness "*" name "-DEFAULT-VALUE*")
                   default-value))
              (t
               (mv-er 2 hard 'define-hash-table$c
                      "GUARD VIOLATION: ~x0" :default-value)))
            (mv nil nil)))
       (element-absstobj-info (and element-stobj-property
                                   (getpropc element-type 'acl2::absstobj-info)))
       (element-stobj$a-property (and element-stobj-property
                                      (stobj$a-property element-type (w state))))
       (element-recognizer (access stobj$a-property element-stobj$a-property :recognizer))
       (element-creator (access stobj$a-property element-stobj$a-property :creator)))

    (mv (list (cons :size size)
              (cons :element-stobj-property element-stobj-property)
              (cons :default-value-val default-value-val)
              (cons :element-absstobj-info element-absstobj-info)
              (cons :element-stobj$a-property element-stobj$a-property)
              (cons :element-recognizer element-recognizer)
              (cons :element-creator element-creator)
              (cons :inline inline)
              (cons :executable executable)
              (cons :debug debug)
              (cons :begin-label (symbolicate$ pkg-witness name "-BEGIN"))
              (cons :end-label (symbolicate$ pkg-witness name "-END")))
        (make hash-table$c-property
              :name name
              :recognizer recognizer
              :creator creator
              :fixer fixer
              :accessor accessor
              :updater updater
              :boundp boundp
              :getp getp
              :remover remover
              :count count
              :clear clear
              :init init
              :keys keys
              :keys-set keys-set
              :contents contents
              :contents-recognizer contents-recognizer
              :element-type element-type
              :default-value default-value
              :copyable copyable
              :test test
              :memoizable memoizable
              :theory (symbolicate$ pkg-witness name "-THEORY")
              :fi-theorems (symbolicate$ pkg-witness "*" name "-FI-THEOREMS*")
              :pkg-witness pkg-witness))))


;;;; `DEFINE-HASH-TABLE$C'
(defmacro define-hash-table$c
    (&whole form
       hash-table test
     &key
       (size 'nil)
       (element-type 't)
       (default-value 'nil)
       (copyable 't)

       (inline 't)
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

       (pkg-witness 'nil)
       (debug 'nil))

  (declare (xargs :guard t)
           (ignore hash-table test
                   size element-type
                   default-value copyable

                   inline memoizable executable

                   contents
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
                   keys-set

                   pkg-witness))

  `(with-output
     ,@(and (not debug)
            *constructor-output*)

     (make-event
       (b* (((mv tmp property) (define-hash-table$c/parse-form ',form state))
            (hash-table (access hash-table$c-property property :name))
            (pkg-witness (access hash-table$c-property property :pkg-witness))
            (test (access hash-table$c-property property :test))
            (size (cdr (assoc :size tmp)))

            (element-type (access hash-table$c-property property :element-type))
            (stobj-property (cdr (assoc :element-stobj-property tmp)))
            (absstobj-info (cdr (assoc :element-absstobj-info tmp)))
            (element-recognizer (cdr (assoc :element-recognizer tmp)))
            (element-creator (cdr (assoc :element-creator tmp)))
            (default-value (cdr (assoc :default-value-val tmp)))
            (default-value-name (access hash-table$c-property property :default-value))
            (copyable (access hash-table$c-property property :copyable))

            (inline (cdr (assoc :inline tmp)))
            (memoizable (access hash-table$c-property property :memoizable))
            (executable (cdr (assoc :executable tmp)))

            (contents (access hash-table$c-property property :contents))
            (contents-recognizer (access hash-table$c-property property :contents-recognizer))
            (recognizer (access hash-table$c-property property :recognizer))
            (creator (access hash-table$c-property property :creator))
            (fixer (access hash-table$c-property property :fixer))
            (accessor (access hash-table$c-property property :accessor))
            (updater (access hash-table$c-property property :updater))
            (boundp (access hash-table$c-property property :boundp))
            (getp (access hash-table$c-property property :getp))
            (remover (access hash-table$c-property property :remover))
            (count (access hash-table$c-property property :count))
            (clear (access hash-table$c-property property :clear))
            (init (access hash-table$c-property property :init))
            (keys (access hash-table$c-property property :keys))
            (keys-set (access hash-table$c-property property :keys-set))

            ;; Interface Symbols
            (contents-recognizer-stobj-default (symbolicate$ pkg-witness contents "P"))
            (recognizer-stobj-default (symbolicate$ pkg-witness hash-table "P"))
            (creator-stobj-default (symbolicate$ pkg-witness "CREATE-" hash-table))
            (accessor-stobj-default (symbolicate$ pkg-witness contents "-GET"))
            (updater-stobj-default (symbolicate$ pkg-witness contents "-PUT"))
            (boundp-stobj-default (symbolicate$ pkg-witness contents "-BOUNDP"))
            (getp-stobj-default (symbolicate$ pkg-witness contents "-GET?"))
            (remover-stobj-default (symbolicate$ pkg-witness contents "-REM"))
            (count-stobj-default (symbolicate$ pkg-witness contents "-COUNT"))
            (clear-stobj-default (symbolicate$ pkg-witness contents "-CLEAR"))
            (%clear (if copyable
                        (symbolicate$ pkg-witness hash-table "-%CLEAR")
                        clear))
            (init-stobj-default (symbolicate$ pkg-witness contents "-INIT"))
            (%init (if copyable
                       (symbolicate$ pkg-witness hash-table "-%INIT")
                       init))
            (keys-set-stobj-default (symbolicate$ pkg-witness "UPDATE-" keys))

            ;; Make Doublets
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
                                   `((,clear-stobj-default ,%clear)))
                              (and (not (eq init init-stobj-default))
                                   `((,init-stobj-default ,%init)))
                              (and copyable
                                   (not (eq keys-set keys-set-stobj-default))
                                   `((,keys-set-stobj-default ,keys-set)))))

            ;; Prologue
            (hash-table-begin (symbolicate$ pkg-witness hash-table "-BEGIN"))
            (hash-table-end (symbolicate$ pkg-witness hash-table "-END"))
            (hash-table/fixer-hack (symbolicate$ pkg-witness hash-table "/FIXER-HACK"))
            (contents/fh (symbolicate$ pkg-witness contents "/FIXER-HACK"))
            (keys/fh (symbolicate$ pkg-witness keys "/FIXER-HACK"))
            (prologue
             `((deflabel ,hash-table-begin)

               ,@(and (not stobj-property)
                      `((defconst ,default-value-name ',default-value)))

               (defstobj ,hash-table
                 (,contents :type (acl2::hash-table ,test ,size ,element-type)
                            ,@(and (not stobj-property)
                                   `(:initially ,default-value)))
                 ,@(and copyable
                        `((,keys)))
                 :renaming ,doublets
                 :inline ,inline
                 :non-memoizable ,(not memoizable)
                 :non-executable ,(not executable))

               (defstobj ,hash-table/fixer-hack
                 (,contents/fh :type (acl2::hash-table ,test ,size ,element-type)
                               ,@(and (not stobj-property)
                                      `(:initially ,default-value)))
                 ,@(and copyable
                        `((,keys/fh)))
                 :inline ,inline
                 :congruent-to ,hash-table
                 :non-memoizable ,(not memoizable)
                 :non-executable t)))

            ;; Theorem Names
            (element-recognizer-of-element-creator (symbolicate$ "ATOMIC-STOBJS" element-recognizer "-OF-" element-creator))

            (contents-recognizer-tp (symbolicate$ pkg-witness contents-recognizer "-TP"))

            (recognizer-tp (symbolicate$ pkg-witness recognizer "-TP"))
            (recognizer-cr (symbolicate$ pkg-witness recognizer "-CR"))
            (recognizer-of-creator (symbolicate$ pkg-witness recognizer "-OF-" creator))
            (recognizer-of-updater (symbolicate$ pkg-witness recognizer "-OF-" updater))
            (recognizer-of-remover (symbolicate$ pkg-witness recognizer "-OF-" remover))
            (recognizer-of-%clear (symbolicate$ pkg-witness recognizer "-OF-" %clear))
            (recognizer-of-%init (symbolicate$ pkg-witness recognizer "-OF-" %init))
            (recognizer-of-keys-set (symbolicate$ pkg-witness recognizer "-OF-" keys-set))

            (typep$-of-accessor (symbolicate$ pkg-witness "TYPEP$-OF-" accessor))
            (accessor-of-creator (symbolicate$ pkg-witness accessor "-OF-" creator))
            (accessor-of-updater (symbolicate$ pkg-witness accessor "-OF-" updater))
            (accessor-of-updater-same (symbolicate$ pkg-witness accessor-of-updater "-SAME"))
            (accessor-of-updater-diff (symbolicate$ pkg-witness accessor-of-updater "-DIFF"))
            (accessor-of-remover (symbolicate$ pkg-witness accessor "-OF-" remover))
            (accessor-of-remover-same (symbolicate$ pkg-witness accessor-of-remover "-SAME"))
            (accessor-of-remover-diff (symbolicate$ pkg-witness accessor-of-remover "-DIFF"))
            (accessor-of-keys-set (symbolicate$ pkg-witness accessor "-OF-" keys-set))

            (updater-tp (symbolicate$ pkg-witness updater "-TP"))

            (boundp-tp (symbolicate$ pkg-witness boundp "-TP"))
            (boundp-of-creator (symbolicate$ pkg-witness boundp "-OF-" creator))
            (boundp-of-updater (symbolicate$ pkg-witness boundp "-OF-" updater))
            (boundp-of-updater-same (symbolicate$ pkg-witness boundp-of-updater "-SAME"))
            (boundp-of-updater-diff (symbolicate$ pkg-witness boundp-of-updater "-DIFF"))
            (boundp-of-remover (symbolicate$ pkg-witness boundp "-OF-" remover))
            (boundp-of-remover-same (symbolicate$ pkg-witness boundp-of-remover "-SAME"))
            (boundp-of-remover-diff (symbolicate$ pkg-witness boundp-of-remover "-DIFF"))
            (boundp-of-keys-set (symbolicate$ pkg-witness boundp "-OF-" keys-set))

            (getp-tp (symbolicate$ pkg-witness getp "-TP"))
            (getp-rw (symbolicate$ pkg-witness getp "-RW"))

            (remover-tp (symbolicate$ pkg-witness remover "-TP"))
            (remover-of-creator (symbolicate$ pkg-witness remover "-OF-" creator))
            (remover-of-updater (symbolicate$ pkg-witness remover "-OF-" updater))
            (remover-of-updater-same (symbolicate$ pkg-witness remover-of-updater "-SAME"))
            (remover-of-updater-diff (symbolicate$ pkg-witness remover-of-updater "-DIFF"))
            (remover-of-remover (symbolicate$ pkg-witness remover "-OF-" remover))
            (remover-of-remover-same (symbolicate$ pkg-witness remover-of-remover "-SAME"))
            (remover-of-remover-diff (symbolicate$ pkg-witness remover-of-remover "-DIFF"))

            (count-tp (symbolicate$ pkg-witness count "-TP"))
            (count-of-creator (symbolicate$ pkg-witness count "-OF-" creator))
            (count-of-updater (symbolicate$ pkg-witness count "-OF-" updater))
            (count-of-updater-when-boundp (symbolicate$ pkg-witness count-of-updater "-WHEN-" boundp))
            (count-of-updater-when-not-boundp (symbolicate$ pkg-witness count-of-updater "-WHEN-NOT-" boundp))
            (count-of-remover (symbolicate$ pkg-witness count "-OF-" remover))
            (count-of-remover-when-boundp (symbolicate$ pkg-witness count-of-remover "-WHEN-" boundp))
            (count-of-remover-when-not-boundp (symbolicate$ pkg-witness count-of-remover "-WHEN-NOT-" boundp))
            (count-of-keys-set (symbolicate$ pkg-witness count "-OF-" keys-set))

            (%clear-tp (symbolicate$ pkg-witness %clear "-TP"))
            (%clear-rw (symbolicate$ pkg-witness %clear "-RW"))

            (%init-tp (symbolicate$ pkg-witness %init "-TP"))
            (%init-rw (symbolicate$ pkg-witness %init "-RW"))

            (keys-of-creator (symbolicate$ pkg-witness keys "-OF-" creator))
            (keys-of-updater (symbolicate$ pkg-witness keys "-OF-" updater))
            (keys-of-remover (symbolicate$ pkg-witness keys "-OF-" remover))
            (keys-of-keys-set (symbolicate$ pkg-witness keys "-OF-" keys-set))

            (keys-set-tp (symbolicate$ pkg-witness keys-set "-TP"))
            (keys-set-of-updater (symbolicate$ pkg-witness keys-set "-OF-" updater))
            (keys-set-of-remover (symbolicate$ pkg-witness keys-set "-OF-" remover))
            (keys-set-of-keys-set (symbolicate$ pkg-witness keys-set "-OF-" keys-set))

            (fixer-def (symbolicate$ pkg-witness fixer "-DEF"))
            (fixer-tp (symbolicate$ pkg-witness fixer "-TP"))
            (recognizer-of-fixer (symbolicate$ pkg-witness recognizer "-OF-" fixer))
            (fixer-when-recognizer (symbolicate$ pkg-witness fixer "-WHEN-" recognizer))
            (fixer-when-not-recognizer (symbolicate$ pkg-witness fixer "-WHEN-NOT-" recognizer))

            (clear-tp (symbolicate$ pkg-witness clear "-TP"))
            (clear-rw (symbolicate$ pkg-witness clear "-RW"))

            (init-tp (symbolicate$ pkg-witness init "-TP"))
            (init-rw (symbolicate$ pkg-witness init "-RW"))

            ;; Epilogue
            (theory (symbolicate$ pkg-witness hash-table "-THEORY"))
            (epilogue
             `((deflabel ,hash-table-end)

               (deftheory-static ,theory
                 (set-difference-theories
                  (set-difference-theories
                   (current-theory ',hash-table-end)
                   (current-theory ',hash-table-begin))
                  ',(append
                     (list contents-recognizer
                           recognizer
                           creator
                           accessor
                           updater
                           boundp
                           getp
                           remover
                           count
                           %clear
                           %init
                           fixer)
                     (and copyable
                          (list keys
                                keys-set
                                clear
                                init)))))

               (in-theory
                 (union-theories (current-theory ',hash-table-begin)
                                 (theory ',theory)))))

            ;; Functional Instantiation
            (fi-bindings
             (append
              (list `(lem-hash-table$c::key-guard ,(case test
                                                     (eq
                                                      'symbolp)
                                                     (eql
                                                      'eqlablep)
                                                     (t
                                                      `(lambda (key)
                                                         t))))
                    `(lem-hash-table$c::element-recognizer ,(or element-recognizer
                                                                `(lambda (value)
                                                                   ,(typep$transform 'value element-type))))
                    `(lem-hash-table$c::default-value ,(or element-creator
                                                           `(lambda ()
                                                              ,default-value-name)))
                    `(lem-hash-table$c::contents-recognizer ,contents-recognizer)
                    (if copyable
                        `(lem-hash-table$c::recognizer/copyable ,recognizer)
                        `(lem-hash-table$c::recognizer/unique ,recognizer))
                    (if copyable
                        `(lem-hash-table$c::creator/copyable ,creator)
                        `(lem-hash-table$c::creator/unique ,creator))
                    `(lem-hash-table$c::accessor ,accessor)
                    `(lem-hash-table$c::updater ,updater)
                    `(lem-hash-table$c::boundp ,boundp)
                    `(lem-hash-table$c::getp ,getp)
                    `(lem-hash-table$c::remover ,remover)
                    `(lem-hash-table$c::count ,count)
                    `(lem-hash-table$c::%clear ,%clear)
                    `(lem-hash-table$c::%init ,%init))
              (and copyable
                   (list `(lem-hash-table$c::keys ,keys)
                         `(lem-hash-table$c::keys-set ,keys-set)))))
            (fi-bindings-with-fixer
             (cons (if copyable
                       `(lem-hash-table$c::fixer/copyable ,fixer)
                       `(lem-hash-table$c::fixer/unique ,fixer))
                   fi-bindings))
            (fi-bindings-with-fixer-and-clear
             (cons `(lem-hash-table$c::clear ,clear)
                   fi-bindings-with-fixer))
            (fi-bindings-with-fixer-and-clear-and-init
             (cons `(lem-hash-table$c::init ,init)
                   fi-bindings-with-fixer-and-clear))

            (body
             `(encapsulate ()

                ,@(and stobj-property
                       `((local
                           (defthm ,element-recognizer-of-element-creator
                             (,element-recognizer (,element-creator))))))

                (local
                  (deflabel end-of-prologue))

                (local
                  (include-book "projects/atomic-stobjs/lemmas/hash-table-c" :dir :system))

                (local
                  (table acl2::theory-invariant-table nil nil :clear))

                (local
                  (in-theory
                    (union-theories (current-theory 'acl2::ground-zero)
                                    (set-difference-theories
                                     (universal-theory 'end-of-prologue)
                                     (universal-theory ',hash-table-begin)))))

                ,@(and absstobj-info
                       `((local
                           (in-theory
                             (enable ,@(strip-cars (cdr absstobj-info)))))))

                (local
                  (in-theory
                    (enable type-spec-theory)))

                ;; `CONTENTS-RECOGNIZER'
                (defthm ,contents-recognizer-tp
                  (booleanp (,contents-recognizer ,contents))
                  :rule-classes :type-prescription
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         lem-hash-table$c::contents-recognizer-tp
                         ,@fi-bindings))))

                ;; `RECOGNIZER'
                (defthm ,recognizer-tp
                  (booleanp (,recognizer ,hash-table))
                  :rule-classes :type-prescription
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         ,(if copyable
                              'lem-hash-table$c::recognizer/copyable-tp
                              'lem-hash-table$c::recognizer/unique-tp)
                         ,@fi-bindings))))

                (defthm ,recognizer-cr
                  (implies (,recognizer ,hash-table)
                           (and (consp ,hash-table)
                                (true-listp ,hash-table)))
                  :rule-classes :compound-recognizer
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         ,(if copyable
                              'lem-hash-table$c::recognizer/copyable-cr
                              'lem-hash-table$c::recognizer/unique-cr)
                         ,@fi-bindings))))

                (defthm ,recognizer-of-creator
                  (,recognizer (,creator))
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         ,(if copyable
                              'lem-hash-table$c::recognizer/copyable-of-creator/copyable
                              'lem-hash-table$c::recognizer/unique-of-creator/unique)
                         ,@fi-bindings))))

                (defthm ,recognizer-of-updater
                  (implies ,(if (eq element-type t)
                                `(,recognizer ,hash-table)
                                `(and (,recognizer ,hash-table)
                                      ,(if element-recognizer
                                           `(,element-recognizer value)
                                           (typep$transform 'value element-type))))
                           (,recognizer (,updater key value ,hash-table)))
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         ,(if copyable
                              'lem-hash-table$c::recognizer/copyable-of-updater
                              'lem-hash-table$c::recognizer/unique-of-updater)
                         ,@fi-bindings))))

                (defthm ,recognizer-of-remover
                  (implies (,recognizer ,hash-table)
                           (,recognizer (,remover key ,hash-table)))
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         ,(if copyable
                              'lem-hash-table$c::recognizer/copyable-of-remover
                              'lem-hash-table$c::recognizer/unique-of-remover)
                         ,@fi-bindings))))

                (defthm ,recognizer-of-%clear
                  (implies (,recognizer ,hash-table)
                           (,recognizer (,%clear ,hash-table)))
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         ,(if copyable
                              'lem-hash-table$c::recognizer/copyable-of-%clear
                              'lem-hash-table$c::recognizer/unique-of-%clear)
                         ,@fi-bindings))))

                (defthm ,recognizer-of-%init
                  (implies (,recognizer ,hash-table)
                           (,recognizer (,%init ht-size rehash-size rehash-threshold ,hash-table)))
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         ,(if copyable
                              'lem-hash-table$c::recognizer/copyable-of-%init
                              'lem-hash-table$c::recognizer/unique-of-%init)
                         ,@fi-bindings))))

                ,@(and copyable
                       `((defthm ,recognizer-of-keys-set
                           (implies (,recognizer ,hash-table)
                                    (,recognizer (,keys-set set ,hash-table)))
                           :hints
                           (("Goal"
                             :by (:functional-instance
                                  lem-hash-table$c::recognizer/copyable-of-keys-set
                                  ,@fi-bindings))))))

                ;; `ACCESSOR'
                ,@(and (not (eq element-type t))
                       `((defthm ,typep$-of-accessor
                           (implies (,recognizer ,hash-table)
                                    ,(if element-recognizer
                                         `(,element-recognizer (,accessor key ,hash-table))
                                         (typep$transform `(,accessor key ,hash-table) element-type)))
                           :rule-classes
                           (:rewrite
                            :type-prescription)
                           :hints
                           (("Goal"
                             :by (:functional-instance
                                  ,(if copyable
                                       'lem-hash-table$c::element-recognizer-of-accessor/copyable
                                       'lem-hash-table$c::element-recognizer-of-accessor/unique)
                                  ,@fi-bindings))))))

                (defthm ,accessor-of-creator
                  (equal (,accessor key (,creator))
                         ,(if element-creator
                              `(,element-creator)
                              default-value-name))
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         ,(if copyable
                              'lem-hash-table$c::accessor-of-creator/copyable
                              'lem-hash-table$c::accessor-of-creator/unique)
                         ,@fi-bindings))))

                (defthm ,accessor-of-updater-same
                  (implies (equal %key key)
                           (equal (,accessor %key (,updater key value ,hash-table))
                                  value))
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         lem-hash-table$c::accessor-of-updater-same
                         ,@fi-bindings))))

                (defthm ,accessor-of-updater-diff
                  (implies (not (equal %key key))
                           (equal (,accessor %key (,updater key value ,hash-table))
                                  (,accessor %key ,hash-table)))
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         lem-hash-table$c::accessor-of-updater-diff
                         ,@fi-bindings))))

                (defthm ,accessor-of-remover-same
                  (implies (equal %key key)
                           (equal (,accessor %key (,remover key ,hash-table))
                                  ,(if element-creator
                                       `(,element-creator)
                                       default-value-name)))
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         lem-hash-table$c::accessor-of-remover-same
                         ,@fi-bindings))))

                (defthm ,accessor-of-remover-diff
                  (implies (not (equal %key key))
                           (equal (,accessor %key (,remover key ,hash-table))
                                  (,accessor %key ,hash-table)))
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         lem-hash-table$c::accessor-of-remover-diff
                         ,@fi-bindings))))

                ,@(and copyable
                       `((defthm ,accessor-of-keys-set
                           (equal (,accessor key (,keys-set set ,hash-table))
                                  (,accessor key ,hash-table))
                           :hints
                           (("Goal"
                             :by (:functional-instance
                                  lem-hash-table$c::accessor-of-keys-set
                                  ,@fi-bindings))))))

                ;; `UPDATER'
                (defthm ,updater-tp
                  (implies (,recognizer ,hash-table)
                           (and (consp (,updater key value ,hash-table))
                                (true-listp (,updater key value ,hash-table))))
                  :rule-classes :type-prescription
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         ,(if copyable
                              'lem-hash-table$c::updater/copyable-tp
                              'lem-hash-table$c::updater/unique-tp)
                         ,@fi-bindings))))

                ;; `BOUNDP'
                (defthm ,boundp-tp
                  (booleanp (,boundp key ,hash-table))
                  :rule-classes :type-prescription
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         lem-hash-table$c::boundp-tp
                         ,@fi-bindings))))

                (defthm ,boundp-of-creator
                  (not (,boundp key (,creator)))
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         ,(if copyable
                              'lem-hash-table$c::boundp-of-creator/copyable
                              'lem-hash-table$c::boundp-of-creator/unique)
                         ,@fi-bindings))))

                (defthm ,boundp-of-updater-same
                  (implies (equal %key key)
                           (equal (,boundp %key (,updater key value ,hash-table))
                                  t))
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         lem-hash-table$c::boundp-of-updater-same
                         ,@fi-bindings))))

                (defthm ,boundp-of-updater-diff
                  (implies (not (equal %key key))
                           (equal (,boundp %key (,updater key value ,hash-table))
                                  (,boundp %key ,hash-table)))
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         lem-hash-table$c::boundp-of-updater-diff
                         ,@fi-bindings))))

                (defthm ,boundp-of-remover-same
                  (implies (equal %key key)
                           (not (,boundp %key (,remover key ,hash-table))))
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         lem-hash-table$c::boundp-of-remover-same
                         ,@fi-bindings))))

                (defthm ,boundp-of-remover-diff
                  (implies (not (equal %key key))
                           (equal (,boundp %key (,remover key ,hash-table))
                                  (,boundp %key ,hash-table)))
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         lem-hash-table$c::boundp-of-remover-diff
                         ,@fi-bindings))))

                ,@(and copyable
                       `((defthm ,boundp-of-keys-set
                           (equal (,boundp key (,keys-set set ,hash-table))
                                  (,boundp key ,hash-table))
                           :hints
                           (("Goal"
                             :by (:functional-instance
                                  lem-hash-table$c::boundp-of-keys-set
                                  ,@fi-bindings))))))

                ;; `GETP'
                (defthm ,getp-tp
                  (and (consp (,getp key ,hash-table))
                       (true-listp (,getp key ,hash-table)))
                  :rule-classes :type-prescription
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         lem-hash-table$c::getp-tp
                         ,@fi-bindings))))

                (defthm ,getp-rw
                  (mv-let (v0 v1)
                          (,getp key ,hash-table)
                    (and (equal v0 (,accessor key ,hash-table))
                         (equal v1 (,boundp key ,hash-table))))
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         lem-hash-table$c::getp-rw
                         ,@fi-bindings))))

                ;; `REMOVER'
                (defthm ,remover-tp
                  (implies (,recognizer ,hash-table)
                           (and (consp (,remover key ,hash-table))
                                (true-listp (,remover key ,hash-table))))
                  :rule-classes :type-prescription
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         ,(if copyable
                              'lem-hash-table$c::remover/copyable-tp
                              'lem-hash-table$c::remover/unique-tp)
                         ,@fi-bindings))))

                (defthm ,remover-of-creator
                  (equal (,remover key (,creator))
                         (,creator))
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         ,(if copyable
                              'lem-hash-table$c::remover-of-creator/copyable
                              'lem-hash-table$c::remover-of-creator/unique)
                         ,@fi-bindings))))

                (defthm ,remover-of-updater-same
                  (implies (equal %key key)
                           (equal (,remover %key (,updater key value ,hash-table))
                                  (,remover %key ,hash-table)))
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         lem-hash-table$c::remover-of-updater-same
                         ,@fi-bindings))))

                (defthm ,remover-of-updater-diff
                  (implies (not (equal %key key))
                           (equal (,remover %key (,updater key value ,hash-table))
                                  (,updater key value (,remover %key ,hash-table))))
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         lem-hash-table$c::remover-of-updater-diff
                         ,@fi-bindings))))

                (defthm ,remover-of-remover-same
                  (implies (equal %key key)
                           (equal (,remover %key (,remover key ,hash-table))
                                  (,remover %key ,hash-table)))
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         lem-hash-table$c::remover-of-remover-same
                         ,@fi-bindings))))

                (defthm ,remover-of-remover-diff
                  (implies (not (equal %key key))
                           (equal (,remover %key (,remover key ,hash-table))
                                  (,remover key (,remover %key ,hash-table))))
                  :rule-classes
                  ((:rewrite :loop-stopper ((%key key ,remover))))
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         lem-hash-table$c::remover-of-remover-diff
                         ,@fi-bindings))))

                ;; `COUNT'
                (defthm ,count-tp
                  (natp (,count ,hash-table))
                  :rule-classes :type-prescription
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         lem-hash-table$c::count-tp
                         ,@fi-bindings))))

                (defthm ,count-of-creator
                  (equal (,count (,creator)) 0)
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         ,(if copyable
                              'lem-hash-table$c::count-of-creator/copyable
                              'lem-hash-table$c::count-of-creator/unique)
                         ,@fi-bindings))))

                (defthm ,count-of-updater-when-boundp
                  (implies (,boundp key ,hash-table)
                           (equal (,count (,updater key value ,hash-table))
                                  (,count ,hash-table)))
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         lem-hash-table$c::count-of-updater-when-boundp
                         ,@fi-bindings))))

                (defthm ,count-of-updater-when-not-boundp
                  (implies (not (,boundp key ,hash-table))
                           (equal (,count (,updater key value ,hash-table))
                                  (1+ (,count ,hash-table))))
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         lem-hash-table$c::count-of-updater-when-not-boundp
                         ,@fi-bindings))))

                (defthm ,count-of-remover-when-boundp
                  (implies (,boundp key ,hash-table)
                           (equal (,count (,remover key ,hash-table))
                                  (1- (,count ,hash-table))))
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         lem-hash-table$c::count-of-remover-when-boundp
                         ,@fi-bindings))))

                (defthm ,count-of-remover-when-not-boundp
                  (implies (not (,boundp key ,hash-table))
                           (equal (,count (,remover key ,hash-table))
                                  (,count ,hash-table)))
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         lem-hash-table$c::count-of-remover-when-not-boundp
                         ,@fi-bindings))))

                ,@(and copyable
                       `((defthm ,count-of-keys-set
                           (equal (,count (,keys-set set ,hash-table))
                                  (,count ,hash-table))
                           :hints
                           (("Goal"
                             :by (:functional-instance
                                  lem-hash-table$c::count-of-keys-set
                                  ,@fi-bindings))))))

                ;; `%CLEAR'
                (defthm ,%clear-tp
                  (implies (,recognizer ,hash-table)
                           (and (consp (,%clear ,hash-table))
                                (true-listp (,%clear ,hash-table))))
                  :rule-classes :type-prescription
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         ,(if copyable
                              'lem-hash-table$c::%clear/copyable-tp
                              'lem-hash-table$c::%clear/unique-tp)
                         ,@fi-bindings))))

                (defthm ,%clear-rw
                  (implies (,recognizer ,hash-table)
                           (equal (,%clear ,hash-table)
                                  ,(if copyable
                                       `(,keys-set (,keys ,hash-table) (,creator))
                                       `(,creator))))
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         ,(if copyable
                              'lem-hash-table$c::%clear/copyable-rw
                              'lem-hash-table$c::%clear/unique-rw)
                         ,@fi-bindings))))

                ;; `%INIT'
                (defthm ,%init-tp
                  (implies (,recognizer ,hash-table)
                           (and (consp (,%init ht-size rehash-size rehash-threshold ,hash-table))
                                (true-listp (,%init ht-size rehash-size rehash-threshold ,hash-table))))
                  :rule-classes :type-prescription
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         ,(if copyable
                              'lem-hash-table$c::%init/copyable-tp
                              'lem-hash-table$c::%init/unique-tp)
                         ,@fi-bindings))))

                (defthm ,%init-rw
                  (implies (,recognizer ,hash-table)
                           (equal (,%init ht-size rehash-size rehash-threshold ,hash-table)
                                  ,(if copyable
                                       `(,keys-set (,keys ,hash-table) (,creator))
                                       `(,creator))))
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         ,(if copyable
                              'lem-hash-table$c::%init/copyable-rw
                              'lem-hash-table$c::%init/unique-rw)
                         ,@fi-bindings))))

                ;; `KEYS'
                ,@(and copyable
                       `((defthm ,keys-of-creator
                           (not (,keys (,creator)))
                           :hints
                           (("Goal"
                             :by (:functional-instance
                                  lem-hash-table$c::keys-of-creator/copyable
                                  ,@fi-bindings))))

                         (defthm ,keys-of-updater
                           (equal (,keys (,updater key value ,hash-table))
                                  (,keys ,hash-table))
                           :hints
                           (("Goal"
                             :by (:functional-instance
                                  lem-hash-table$c::keys-of-updater
                                  ,@fi-bindings))))

                         (defthm ,keys-of-remover
                           (equal (,keys (,remover key ,hash-table))
                                  (,keys ,hash-table))
                           :hints
                           (("Goal"
                             :by (:functional-instance
                                  lem-hash-table$c::keys-of-remover
                                  ,@fi-bindings))))

                         (defthm ,keys-of-keys-set
                           (equal (,keys (,keys-set set ,hash-table))
                                  set)
                           :hints
                           (("Goal"
                             :by (:functional-instance
                                  lem-hash-table$c::keys-of-keys-set
                                  ,@fi-bindings))))))

                ;; `KEYS-SET'
                ,@(and copyable
                       `((defthm ,keys-set-tp
                           (implies (,recognizer ,hash-table)
                                    (and (consp (,keys-set set ,hash-table))
                                         (true-listp (,keys-set set ,hash-table))))
                           :rule-classes :type-prescription
                           :hints
                           (("Goal"
                             :by (:functional-instance
                                  lem-hash-table$c::keys-set-tp
                                  ,@fi-bindings))))

                         (defthm ,keys-set-of-updater
                           (equal (,keys-set set (,updater key value ,hash-table))
                                  (,updater key value (,keys-set set ,hash-table)))
                           :hints
                           (("Goal"
                             :by (:functional-instance
                                  lem-hash-table$c::keys-set-of-updater
                                  ,@fi-bindings))))

                         (defthm ,keys-set-of-remover
                           (equal (,keys-set set (,remover key ,hash-table))
                                  (,remover key (,keys-set set ,hash-table)))
                           :hints
                           (("Goal"
                             :by (:functional-instance
                                  lem-hash-table$c::keys-set-of-remover
                                  ,@fi-bindings))))

                         (defthm ,keys-set-of-keys-set
                           (equal (,keys-set %set (,keys-set set ,hash-table))
                                  (,keys-set %set ,hash-table))
                           :hints
                           (("Goal"
                             :by (:functional-instance
                                  lem-hash-table$c::keys-set-of-keys-set
                                  ,@fi-bindings))))))

                ;; `FIXER'
                (defun-inline ,fixer (,hash-table)
                  (declare (xargs :stobjs ,hash-table))
                  (mbe :logic (if (,recognizer ,hash-table)
                                  ,hash-table
                                  (with-local-stobj ,hash-table/fixer-hack
                                    (mv-let (,hash-table ,hash-table/fixer-hack)
                                            (swap-stobjs ,hash-table ,hash-table/fixer-hack)
                                      ,hash-table)))
                       :exec ,hash-table))

                (defthm ,fixer-def
                  (equal (,fixer ,hash-table)
                         (if (,recognizer ,hash-table)
                             ,hash-table
                             (,creator)))
                  :rule-classes :definition)

                (in-theory
                  (disable ,fixer))

                (defthm ,fixer-tp
                  (and (consp (,fixer ,hash-table))
                       (true-listp (,fixer ,hash-table)))
                  :rule-classes :type-prescription
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         ,(if copyable
                              'lem-hash-table$c::fixer/copyable-tp
                              'lem-hash-table$c::fixer/unique-tp)
                         ,@fi-bindings-with-fixer))))

                (defthm ,recognizer-of-fixer
                  (,recognizer (,fixer ,hash-table))
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         ,(if copyable
                              'lem-hash-table$c::recognizer/copyable-of-fixer/copyable
                              'lem-hash-table$c::recognizer/unique-of-fixer/unique)
                         ,@fi-bindings-with-fixer))))

                (defthm ,fixer-when-recognizer
                  (implies (,recognizer ,hash-table)
                           (equal (,fixer ,hash-table)
                                  ,hash-table))
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         ,(if copyable
                              'lem-hash-table$c::fixer/copyable-when-recognizer/copyable
                              'lem-hash-table$c::fixer/unique-when-recognizer/unique)
                         ,@fi-bindings-with-fixer))))

                (defthm ,fixer-when-not-recognizer
                  (implies (not (,recognizer ,hash-table))
                           (equal (,fixer ,hash-table)
                                  (,creator)))
                  :hints
                  (("Goal"
                    :by (:functional-instance
                         ,(if copyable
                              'lem-hash-table$c::fixer/copyable-when-not-recognizer/copyable
                              'lem-hash-table$c::fixer/unique-when-not-recognizer/unique)
                         ,@fi-bindings-with-fixer))))

                ;; `CLEAR'
                ,@(and copyable
                       `((defun ,clear (,hash-table)
                           (declare (xargs :stobjs ,hash-table))
                           (let* ((,hash-table (,fixer ,hash-table))
                                  (,hash-table (,keys-set '() ,hash-table)))
                             (,%clear ,hash-table)))

                         (defthm ,clear-tp
                           (implies (,recognizer ,hash-table)
                                    (and (consp (,clear ,hash-table))
                                         (true-listp (,clear ,hash-table))))
                           :rule-classes :type-prescription
                           :hints
                           (("Goal"
                             :by (:functional-instance
                                  lem-hash-table$c::clear-tp
                                  ,@fi-bindings-with-fixer-and-clear))))

                         (defthm ,clear-rw
                           (implies (,recognizer ,hash-table)
                                    (equal (,clear ,hash-table)
                                           (,creator)))
                           :hints
                           (("Goal"
                             :by (:functional-instance
                                  lem-hash-table$c::clear-rw
                                  ,@fi-bindings-with-fixer-and-clear))))))

                ;; `INIT'
                ,@(and copyable
                       `((defun ,init (ht-size rehash-size rehash-threshold ,hash-table)
                           (declare (xargs :stobjs ,hash-table
                                           :guard (and (or (natp ht-size)
                                                           (not ht-size))
                                                       (or (and (rationalp rehash-size)
                                                                (<= 1 rehash-size))
                                                           (not rehash-size))
                                                       (or (and (rationalp rehash-threshold)
                                                                (<= 0 rehash-threshold)
                                                                (<= rehash-threshold 1))
                                                           (not rehash-threshold)))))
                           (let* ((,hash-table (,fixer ,hash-table))
                                  (,hash-table (,keys-set '() ,hash-table)))
                             (,%init ht-size rehash-size rehash-threshold ,hash-table)))

                         (defthm ,init-tp
                           (implies (,recognizer ,hash-table)
                                    (and (consp (,init ht-size rehash-size rehash-threshold ,hash-table))
                                         (true-listp (,init ht-size rehash-size rehash-threshold ,hash-table))))
                           :rule-classes :type-prescription
                           :hints
                           (("Goal"
                             :by (:functional-instance
                                  lem-hash-table$c::init-tp
                                  ,@fi-bindings-with-fixer-and-clear-and-init))))

                         (defthm ,init-rw
                           (implies (,recognizer ,hash-table)
                                    (equal (,init ht-size rehash-size rehash-threshold ,hash-table)
                                           (,creator)))
                           :hints
                           (("Goal"
                             :by (:functional-instance
                                  lem-hash-table$c::init-rw
                                  ,@fi-bindings-with-fixer-and-clear-and-init))))))))
            (stobj$c-property (make hash-table$c-property
                                    :name hash-table
                                    :recognizer recognizer
                                    :creator creator
                                    :fixer fixer
                                    :accessor accessor
                                    :updater updater
                                    :boundp boundp
                                    :getp getp
                                    :remover remover
                                    :count count
                                    :clear clear
                                    :init init
                                    :keys keys
                                    :keys-set keys-set
                                    :contents contents
                                    :contents-recognizer contents-recognizer
                                    :element-type element-type
                                    :default-value default-value-name
                                    :copyable copyable
                                    :test test
                                    :memoizable memoizable
                                    :theory theory
                                    :fi-bindings fi-bindings-with-fixer
                                    :fi-theorems nil
                                    :pkg-witness pkg-witness)))

         `(progn
            ,@prologue

            ,body

            ,@epilogue

            (table stobj$c ',hash-table ',stobj$c-property))))))
