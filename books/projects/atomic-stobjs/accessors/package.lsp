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


(in-package "ACL2")

(defpkg "ATOMIC-STOBJ-ACCESSORS"
  (union-eq *common-lisp-symbols-from-main-lisp-package*
            *acl2-exports*
            '(stobj)))


;;;; `*EXPORTS*'
(defconst atomic-stobj-accessors::*stobj-exports*
  '#!atomic-stobj-accessors
  (stobj
   stobj-p
   stobj-recognizer
   stobj-creator
   stobj-interface
   stobj-live-constant))

(defconst atomic-stobj-accessors::*stobj$c-exports*
  '#!atomic-stobj-accessors
  (stobj$c-recognizer
   stobj$c-creator
   stobj$c-live-constant
   stobj$c-array-p
   stobj$c-array-contents-recognizer
   stobj$c-array-length
   stobj$c-array-resizer
   stobj$c-array-accessor
   stobj$c-array-updater
   stobj$c-array-accessor-constant
   stobj$c-hash-table-p
   stobj$c-hash-table-contents-recognizer
   stobj$c-hash-table-keys-recognizer
   stobj$c-hash-table-accessor
   stobj$c-hash-table-updater
   stobj$c-hash-table-boundp
   stobj$c-hash-table-getp
   stobj$c-hash-table-remover
   stobj$c-hash-table-count
   stobj$c-hash-table-clear
   stobj$c-hash-table-init
   stobj$c-hash-table-keys
   stobj$c-hash-table-keys-set
   stobj$c-hash-table-accessor-constant
   stobj$c-hash-table-keys-constant
   stobj$c-frame-p
   stobj$c-frame-recognizers
   stobj$c-frame-accessors
   stobj$c-frame-updaters
   stobj$c-frame-accessor-constants))

(defconst atomic-stobj-accessors::*stobj$a-exports*
  (union-eq
   '#!atomic-stobj-accessors
   (stobj$a
    stobj$a-property-alist
    stobj$a-lookup-alist)
   '#!atomic-stobj-accessors
   (stobj$a-property-alist
    stobj$a-property
    stobj$a-p
    stobj$a-recognizer
    stobj$a-creator
    stobj$a-fixer
    stobj$a-equal
    stobj$a-interface
    stobj$a-lookup-alist
    stobj$a-lookup
    stobj$a-array-p
    stobj$a-array-element-recognizer
    stobj$a-array-element-fixer
    stobj$a-array-element
    stobj$a-array-initial-element
    stobj$a-array-resizablep
    stobj$a-array-default-length
    stobj$a-array-length
    stobj$a-array-resizer
    stobj$a-array-accessor
    stobj$a-array-updater
    stobj$a-hash-table-p
    stobj$a-hash-table-key-recognizer
    stobj$a-hash-table-key-fixer
    stobj$a-hash-table-key
    stobj$a-hash-table-default-key
    stobj$a-hash-table-val-recognizer
    stobj$a-hash-table-val-fixer
    stobj$a-hash-table-val
    stobj$a-hash-table-default-val
    stobj$a-hash-table-test
    stobj$a-hash-table-copyable
    stobj$a-hash-table-accessor
    stobj$a-hash-table-updater
    stobj$a-hash-table-boundp
    stobj$a-hash-table-getp
    stobj$a-hash-table-remover
    stobj$a-hash-table-count
    stobj$a-hash-table-clear
    stobj$a-hash-table-init
    stobj$a-hash-table-keys
    stobj$a-hash-table-keys-set
    stobj$a-frame-p
    stobj$a-frame-recognizers
    stobj$a-frame-fixers
    stobj$a-frame-fields
    stobj$a-frame-initial-elements
    stobj$a-frame-stobjs
    stobj$a-frame-accessors
    stobj$a-frame-updaters
    stobj$a-frame-view)))

(defconst atomic-stobj-accessors::*stobj$abs-exports*
  '#!atomic-stobj-accessors
  (stobj$abs-info
   stobj$abs-p
   stobj$abs-foundation
   stobj$abs-recognizers
   stobj$abs-creators
   stobj$abs-exports))

(defconst atomic-stobj-accessors::*exports*
  (union-eq atomic-stobj-accessors::*stobj-exports*
            atomic-stobj-accessors::*stobj$c-exports*
            atomic-stobj-accessors::*stobj$a-exports*
            atomic-stobj-accessors::*stobj$abs-exports*))
