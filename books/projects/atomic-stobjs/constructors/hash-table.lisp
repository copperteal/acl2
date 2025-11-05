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

(include-book "../type-spec")
(include-book "../utilities/top")
(include-book "hash-table$c")
(include-book "hash-table$a")
(include-book "hash-table$abs")


;;;; `DEFINE-HASH-TABLE'
(defmacro define-hash-table
    (hash-table test
     &key
       (size 'nil size-supplied-p)
       (element-type 't element-type-supplied-p)
       (key-recognizer 'nil key-recognizer-supplied-p)
       (key-fixer 'nil key-fixer-supplied-p)
       (key 'key key-supplied-p)
       (default-key 'nil default-key-supplied-p)
       (val-recognizer 'nil val-recognizer-supplied-p)
       (val-fixer 'nil val-fixer-supplied-p)
       (val 'val val-supplied-p)
       (default-val 'nil default-val-supplied-p)
       (copyable 't copyable-supplied-p)

       (inline 'nil inline-supplied-p)
       (memoizable 'nil memoizable-supplied-p)
       (executable 'nil executable-supplied-p)

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
                              (symbolp test)
                              (member test '(eq eql hons-equal equal) :test 'eq)
                              (or (null size)
                                  (natp size))
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
                           (symbolicate hash-table hash-table "$A")))
         (hash-table$c (or exec
                           (symbolicate hash-table hash-table "$C")))
         (recognizer (or recognizer
                         (symbolicate hash-table hash-table (make-predicate-suffix hash-table))))
         (creator (or creator
                      (symbolicate hash-table "CREATE-" hash-table)))
         (accessor (or accessor
                       (symbolicate hash-table hash-table "-GET")))
         (updater (or updater
                      (symbolicate hash-table hash-table "-PUT")))
         (boundp (or boundp
                     (symbolicate hash-table hash-table "-BOUNDP")))
         (getp (or getp
                   (symbolicate hash-table hash-table "-GETP")))
         (remover (or remover
                      (symbolicate hash-table hash-table "-REM")))
         (count (or count
                    (symbolicate hash-table hash-table "-COUNT")))
         (clear (or clear
                    (symbolicate hash-table hash-table "-CLEAR")))
         (init (or init
                   (symbolicate hash-table hash-table "-INIT")))
         (keys (or keys
                   (symbolicate hash-table hash-table "-KEYS")))
         (keys-set (or keys-set
                       (symbolicate hash-table hash-table "-KEYS-SET"))))

    `(with-output
       ,@(and (not debug)
              '#!acl2(:off (warning! observation prove event history proof-tree)
                           :summary-off (rules)
                           :gag-mode t))

       (make-event
         (let* ((hash-table ',hash-table)
                (test ',test)
                (size ',size)
                (element-type ',element-type)
                (key-recognizer ',key-recognizer)
                (key-fixer ',key-fixer)
                (key ',key)
                (default-key ',default-key)
                (val-recognizer ',val-recognizer)
                (val-fixer ',val-fixer)
                (val ',val)
                (default-val ',default-val)
                (copyable ',copyable)

                (inline ',inline)
                (memoizable ',memoizable)
                (executable ',executable)

                (hash-table$a ',hash-table$a)
                (hash-table$c ',hash-table$c)
                (recognizer ',recognizer)
                (creator ',creator)
                (accessor ',accessor)
                (updater ',updater)
                (boundp ',boundp)
                (getp ',getp)
                (remover ',remover)
                (count ',count)
                (clear ',clear)
                (init ',init)
                (keys ',keys)
                (keys-set ',keys-set)

                (debug ',debug))
           `(progn
              (define-hash-table$c ,hash-table$c ,test
                ,@(and ,size-supplied-p
                       `(:size ,size))
                ,@(and ,element-type-supplied-p
                       `(:element-type ,element-type))
                ,@(and ,default-val-supplied-p
                       `(:default-value ,default-val))
                ,@(and ,copyable-supplied-p
                       `(:copyable ,copyable))
                ,@(and ,inline-supplied-p
                       `(:inline ,inline))
                ,@(and ,memoizable-supplied-p
                       `(:memoizable ,memoizable))
                ,@(and ,executable-supplied-p
                       `(:executable ,executable))
                :debug ,debug)

              (define-hash-table$a ,hash-table$a ,test
                ,@(and ,key-recognizer-supplied-p
                       `(:key-recognizer ,key-recognizer))
                ,@(and ,key-fixer-supplied-p
                       `(:key-fixer ,key-fixer))
                ,@(and ,key-supplied-p
                       `(:key ,key))
                ,@(and ,default-key-supplied-p
                       `(:default-key ,default-key))
                ,@(and ,val-recognizer-supplied-p
                       `(:val-recognizer ,val-recognizer))
                ,@(and ,val-fixer-supplied-p
                       `(:val-fixer ,val-fixer))
                ,@(and ,val-supplied-p
                       `(:val ,val))
                ,@(and ,default-val-supplied-p
                       `(:default-val ,default-val))
                ,@(and ,copyable-supplied-p
                       `(:copyable ,copyable))
                :debug ,debug)

              (define-hash-table$corr ,hash-table
                :logic ,hash-table$a
                :exec ,hash-table$c
                ,@(and ,copyable-supplied-p
                       `(:copyable ,copyable))
                :debug ,debug)

              (define-hash-table$abs ,hash-table
                :logic ,hash-table$a
                :exec ,hash-table$c
                :copyable ,copyable
                :recognizer ,recognizer
                :creator ,creator
                :accessor ,accessor
                :updater ,updater
                :boundp ,boundp
                :getp ,getp
                :remover ,remover
                :count ,count
                :clear ,clear
                :init ,init
                ,@(and copyable
                       `(:keys ,keys
                               :keys-set ,keys-set))
                ,@(and ,executable-supplied-p
                       `(:executable ,executable))
                :debug ,debug)))))))
