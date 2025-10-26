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


;;;; Prologue
(in-package "ATOMIC-STOBJS")
(set-verify-guards-eagerness 2)

(include-book "misc/total-order" :dir :system)
(include-book "std/osets/top" :dir :system) ; TODO: delete?
(include-book "std/omaps/core" :dir :system) ; TODO: delete?

(include-book "../type-spec")
(include-book "../accessors/top")
(include-book "../utilities/top")

(deflabel define-hash-table-begin)


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

(include-book "hash-table$c")
(include-book "hash-table$a")
(include-book "hash-table$abs")


;;;; `DEFINE-HASH-TABLE'
(defmacro define-hash-table
    (hash-table test
     &key
       (size 'nil)
       (element-type 't)
       (key-recognizer 'nil)
       (key-fixer 'nil)
       (key 'key)
       (default-key 'nil)
       (val-recognizer 'nil)
       (val-fixer 'nil)
       (val 'val)
       (default-val 'nil)
       (copyable 't)

       (inline 'nil)
       (memoizable 'nil)
       (executable 'nil)

       (recognizer 'nil)
       (creator 'nil)
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

       (logic 'nil)
       (exec 'nil)

       (debug 'nil))

  (declare (xargs :guard (and (symbolp hash-table)
                              (valid-hash-table-test-p test)
                              (valid-hash-table-size-p size)
                              (if (acl2-type-spec-p element-type)
                                  (typep$ default-val element-type)
                                  (symbolp element-type))
                              (booleanp copyable)
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
                              (booleanp inline)
                              (booleanp memoizable)
                              (booleanp executable)
                              (symbol-listp (list recognizer
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
                              (symbolp logic)
                              (symbolp exec)
                              (booleanp debug))))

  (let* ((hash-table$a (or logic
                           (symbolicate hash-table hash-table '$a)))
         (hash-table$c (or exec
                           (symbolicate hash-table hash-table '$c)))
         (recognizer (or recognizer
                         (symbolicate hash-table hash-table (make-predicate-suffix hash-table))))
         (creator (or creator
                      (symbolicate hash-table 'create- hash-table)))
         (accessor (or accessor
                       (symbolicate hash-table hash-table '-get)))
         (updater (or updater
                      (symbolicate hash-table hash-table '-put)))
         (boundp (or boundp
                     (symbolicate hash-table hash-table '-boundp)))
         (getp (or getp
                   (symbolicate hash-table hash-table '-getp)))
         (remover (or remover
                      (symbolicate hash-table hash-table '-rem)))
         (count (or count
                    (symbolicate hash-table hash-table '-count)))
         (clear (or clear
                    (symbolicate hash-table hash-table '-clear)))
         (init (or init
                   (symbolicate hash-table hash-table '-init)))
         (keys (or keys
                   (symbolicate hash-table hash-table '-keys)))
         (keys-set (or keys-set
                       (symbolicate hash-table hash-table '-keys-set))))

    `(with-output
       ,@(and (not debug)
              '#!acl2(:off (warning! observation prove event history proof-tree)
                           :summary-off (rules)
                           :gag-mode t))

       (make-event
         `(progn
            (define-hash-table$c ,',hash-table$c ,',test
              :size ,',size
              :element-type ,',element-type
              :default-value ,',default-val
              :copyable ,',copyable
              :inline ,',inline
              :memoizable ,',memoizable
              :executable ,',executable
              :debug ,',debug)

            (define-hash-table$a ,',hash-table$a ,',test
              :key-recognizer ,',key-recognizer
              :key-fixer ,',key-fixer
              :key ,',key
              :default-key ,',default-key
              :val-recognizer ,',val-recognizer
              :val-fixer ,',val-fixer
              :val ,',val
              :default-val ,',default-val
              :copyable ,',copyable
              :debug ,',debug)

            (define-hash-table$corr ,',hash-table
              :logic ,',hash-table$a
              :exec ,',hash-table$c
              :copyable ,',copyable
              :debug ,',debug)

            (define-hash-table$abs ,',hash-table ,',test
              :logic ,',hash-table$a
              :exec ,',hash-table$c
              :copyable ,',copyable
              :recognizer ,',recognizer
              :creator ,',creator
              :accessor ,',accessor
              :updater ,',updater
              :boundp ,',boundp
              :getp ,',getp
              :remover ,',remover
              :count ,',count
              :clear ,',clear
              :init ,',init
              ,@(and ',copyable
                     `(:keys ,',keys
                             :keys-set ,',keys-set))
              :executable ,',executable
              :debug ,',debug)

            (in-theory
              (disable ,',(symbolicate hash-table$c hash-table$c '-theorems))))))))


;;;; `HASH-TABLE-THEOREMS'
(deflabel define-hash-table-end)

(deftheory-static define-hash-table-theorems
  (set-difference-theories
   (set-difference-theories
    (current-theory 'define-hash-table-end)
    (current-theory 'define-hash-table-begin))
   (function-theory 'define-hash-table-end)))


;;;; Epilogue
(in-theory
  (union-theories (current-theory 'define-hash-table-begin)
                  (theory 'define-hash-table-theorems)))
