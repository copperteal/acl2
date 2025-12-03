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
(include-book "hash-table-c")
(include-book "hash-table-a")
(include-book "hash-table-abs")


;;;; `DEFINE-HASH-TABLE'
(defmacro define-hash-table
    (hash-table test
     &key
       (size 'nil size-supplied-p)
       (element-type 't element-type-supplied-p)
       (key-recognizer 'nil key-recognizer-supplied-p)
       (key-fixer 'nil key-fixer-supplied-p)
       (key-equiv 'nil key-equiv-supplied-p)
       (key 'nil key-supplied-p)
       (default-key 'nil default-key-supplied-p)
       (val-recognizer 'nil val-recognizer-supplied-p)
       (val-fixer 'nil val-fixer-supplied-p)
       (val-equiv 'nil val-equiv-supplied-p)
       (val 'nil val-supplied-p)
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

       (package-witness 'nil package-witness-supplied-p)
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
                                                  key-equiv
                                                  key
                                                  val-recognizer
                                                  val-fixer
                                                  val-equiv
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
                              (package-witness-p package-witness)
                              (booleanp debug))))

  `(with-output
     ,@(and (not debug)
            *constructor-output*)

     (make-event
       (let* ((hash-table ',hash-table)
              (logic ',logic)
              (exec ',exec)
              (package-witness (if ',package-witness-supplied-p
                                   ',package-witness
                                   (current-package state)))
              (test ',test)
              (size ',size)
              (element-type ',element-type)
              (stobj-property (and (symbolp element-type)
                                   (getpropc element-type 'acl2::stobj)))
              (key-recognizer ',key-recognizer)
              (key-fixer ',key-fixer)
              (key-equiv ',key-equiv)
              (key ',key)
              (default-key ',default-key)
              (val-recognizer ',val-recognizer)
              (val-fixer ',val-fixer)
              (val-equiv ',val-equiv)
              (val ',val)
              (default-val ',default-val)
              (copyable ',copyable)

              (inline ',inline)
              (memoizable ',memoizable)
              (executable ',executable)

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

              (debug ',debug)

              (hash-table$a (or logic
                                (symbolicate package-witness hash-table "$A")))
              (hash-table$c (or exec
                                (symbolicate package-witness hash-table "$C")))
              (recognizer (or recognizer
                              (symbolicate package-witness hash-table (make-predicate-suffix hash-table))))
              (creator (or creator
                           (symbolicate package-witness "CREATE-" hash-table)))
              (accessor (or accessor
                            (symbolicate package-witness hash-table "-GET")))
              (updater (or updater
                           (symbolicate package-witness hash-table "-PUT")))
              (boundp (or boundp
                          (symbolicate package-witness hash-table "-BOUNDP")))
              (getp (or getp
                        (symbolicate package-witness hash-table "-GETP")))
              (remover (or remover
                           (symbolicate package-witness hash-table "-REM")))
              (count (or count
                         (symbolicate package-witness hash-table "-COUNT")))
              (clear (or clear
                         (symbolicate package-witness hash-table "-CLEAR")))
              (init (or init
                        (symbolicate package-witness hash-table "-INIT")))
              (keys (or keys
                        (symbolicate package-witness hash-table "-KEYS")))
              (keys-set (or keys-set
                            (symbolicate package-witness hash-table "-KEYS-SET"))))

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
              ,@(and ,package-witness-supplied-p
                     `(:package-witness ,package-witness))
              :debug ,debug)

            (define-hash-table$a ,hash-table$a ,test
              ,@(and ,key-recognizer-supplied-p
                     `(:key-recognizer ,key-recognizer))
              ,@(and ,key-fixer-supplied-p
                     `(:key-fixer ,key-fixer))
              ,@(and ,key-equiv-supplied-p
                     `(:key-equiv ,key-equiv))
              ,@(and ,key-supplied-p
                     `(:key ,key))
              ,@(and ,default-key-supplied-p
                     `(:default-key ,default-key))
              ,@(and ,val-recognizer-supplied-p
                     `(:val-recognizer ,val-recognizer))
              ,@(and ,val-fixer-supplied-p
                     `(:val-fixer ,val-fixer))
              ,@(and ,val-equiv-supplied-p
                     `(:val-equiv ,val-equiv))
              ,@(and (or ,val-supplied-p
                         stobj-property)
                     `(:val ,(if stobj-property
                                 element-type
                                 val)))
              ,@(and ,default-val-supplied-p
                     `(:default-val ,default-val))
              ,@(and ,copyable-supplied-p
                     `(:copyable ,copyable))
              ,@(and ,package-witness-supplied-p
                     `(:package-witness ,package-witness))
              :debug ,debug)

            (define-hash-table$corr ,hash-table
              :logic ,hash-table$a
              :exec ,hash-table$c
              ,@(and ,copyable-supplied-p
                     `(:copyable ,copyable))
              ,@(and ,package-witness-supplied-p
                     `(:package-witness ,package-witness))
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
              ,@(and ,package-witness-supplied-p
                     `(:package-witness ,package-witness))
              :debug ,debug))))))
