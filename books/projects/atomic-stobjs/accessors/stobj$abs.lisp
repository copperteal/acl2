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

(include-book "portcullis")
(include-book "stobj")


;;;; `STOBJ$ABS'
(defmacro stobj-accessors::stobj$abs-info (stobj$abs)
  (declare (xargs :guard t))
  `(getpropc ,stobj$abs 'absstobj-info))

(defmacro stobj-accessors::stobj$abs-p (stobj$abs)
  (declare (xargs :guard t))
  `(let ((stobj$abs ,stobj$abs))
     (and (symbolp stobj$abs)
          (stobj-p stobj$abs)
          (let* ((absstobj-info (stobj-accessors::stobj$abs-info stobj$abs))
                 (foundation (car absstobj-info))
                 (exports (cdr absstobj-info)))
            (and (symbolp foundation)
                 (symbol-list-listp exports)
                 (<= 2 (len exports)))))))

(defmacro stobj-accessors::stobj$abs-foundation (stobj$abs)
  (declare (xargs :guard t))
  `(first (stobj-accessors::stobj$abs-info ,stobj$abs)))

(defmacro stobj-accessors::stobj$abs-recognizers (stobj$abs)
  (declare (xargs :guard t))
  `(second (stobj-accessors::stobj$abs-info ,stobj$abs)))

(defmacro stobj-accessors::stobj$abs-creators (stobj$abs)
  (declare (xargs :guard t))
  `(third (stobj-accessors::stobj$abs-info ,stobj$abs)))

(defmacro stobj-accessors::stobj$abs-exports (stobj$abs)
  (declare (xargs :guard t))
  `(cdddr (stobj-accessors::stobj$abs-info ,stobj$abs)))


;;;; `*STOBJ$ABS-SYMBOLS*'
(defconst stobj-accessors::*stobj$abs-symbols*
  '#!stobj-accessors
  (stobj$abs-info
   stobj$abs-p
   stobj$abs-foundation
   stobj$abs-recognizers
   stobj$abs-creators
   stobj$abs-exports))
