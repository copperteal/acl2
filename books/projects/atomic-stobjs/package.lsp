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


(in-package "ACL2")

(defpkg "ATOMIC-STOBJS"
  (set-difference-eq
   (union-eq *common-lisp-symbols-from-main-lisp-package*
             *acl2-exports*
             *type-spec-exports*
             '(package-witness-p
               symbolicate
               with-books
               make-predicate-suffix
               coupledp)
             '(<<
               nat-equiv

               b*
               def-b*-binder
               args
               forms
               rest-expr

               inline
               memoizable
               executable
               debug))

   '(
     ;; VECTOR Construction Variables
     vector
     dimensions
     default-length
     specialize-element-type
     initial-element
     resizable
     index
     %index
     element-recognizer
     element-fixer
     element
     %element
     element-type
     default-value

     ;; HASH-TABLE Construction Variables
     hash-table
     test
     size
     copyable
     key-recognizer
     key-fixer
     key
     %key
     default-key
     val-recognizer
     val-fixer
     val
     %val
     default-val
     set
     %set

     contents
     contents-recognizer
     recognizer
     creator
     fixer
     length
     resizer
     accessor
     updater
     boundp
     getp
     remover
     count
     clear
     init
     keysp
     keys
     keys-set

     ;; Table Names
     copy
     corr
     equality
     fixer
     package-witness
     stobj$a-property
     view
     )))
