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


;;;; `STOBJ$C'
(defmacro stobj-accessors::stobj$c-recognizer (stobj$c)
  (declare (xargs :guard t))
  `(stobj-accessors::stobj-recognizer ,stobj$c))

(defmacro stobj-accessors::stobj$c-creator (stobj$c)
  (declare (xargs :guard t))
  `(stobj-accessors::stobj-creator ,stobj$c))

(defmacro stobj-accessors::stobj$c-live-constant (stobj$c)
  (declare (xargs :guard t))
  `(stobj-accessors::stobj-live-constant ,stobj$c))


;;;; `STOBJ$C-ARRAY'
(defmacro stobj-accessors::stobj$c-array-p (stobj$c)
  (declare (xargs :guard t))
  ;; an undesirably brittle characterization
  `(= (len (stobj-accessors::stobj-interface ,stobj$c)) 6))

(defmacro stobj-accessors::stobj$c-array-contents-recognizer (stobj$c)
  (declare (xargs :guard t))
  `(first (stobj-accessors::stobj-interface ,stobj$c)))

(defmacro stobj-accessors::stobj$c-array-length (stobj$c)
  (declare (xargs :guard t))
  `(second (stobj-accessors::stobj-interface ,stobj$c)))

(defmacro stobj-accessors::stobj$c-array-resizer (stobj$c)
  (declare (xargs :guard t))
  `(third (stobj-accessors::stobj-interface ,stobj$c)))

(defmacro stobj-accessors::stobj$c-array-accessor (stobj$c)
  (declare (xargs :guard t))
  `(fourth (stobj-accessors::stobj-interface ,stobj$c)))

(defmacro stobj-accessors::stobj$c-array-updater (stobj$c)
  (declare (xargs :guard t))
  `(fifth (stobj-accessors::stobj-interface ,stobj$c)))

(defmacro stobj-accessors::stobj$c-array-accessor-constant (stobj$c)
  (declare (xargs :guard t))
  `(sixth (stobj-accessors::stobj-interface ,stobj$c)))


;;;; `STOBJ$C-HASH-TABLE'
(defmacro stobj-accessors::stobj$c-hash-table-p (stobj$c copyable)
  (declare (xargs :guard (booleanp copyable)))
  ;; an undesirably brittle characterization
  `(= (len (stobj-accessors::stobj-interface ,stobj$c)) ,(if copyable 14 10)))

(defmacro stobj-accessors::stobj$c-hash-table-contents-recognizer (stobj$c copyable)
  (declare (xargs :guard (booleanp copyable))
           (ignore copyable))
  `(first (stobj-accessors::stobj-interface ,stobj$c)))

(defmacro stobj-accessors::stobj$c-hash-table-keys-recognizer (stobj$c copyable)
  (declare (xargs :guard (booleanp copyable)))
  (and copyable `(second (stobj-accessors::stobj-interface ,stobj$c))))

(defmacro stobj-accessors::stobj$c-hash-table-accessor (stobj$c copyable)
  (declare (xargs :guard (booleanp copyable)))
  `(,(if copyable 'third 'second) (stobj-accessors::stobj-interface ,stobj$c)))

(defmacro stobj-accessors::stobj$c-hash-table-updater (stobj$c copyable)
  (declare (xargs :guard (booleanp copyable)))
  `(,(if copyable 'fourth 'third) (stobj-accessors::stobj-interface ,stobj$c)))

(defmacro stobj-accessors::stobj$c-hash-table-boundp (stobj$c copyable)
  (declare (xargs :guard (booleanp copyable)))
  `(,(if copyable 'fifth 'fourth) (stobj-accessors::stobj-interface ,stobj$c)))

(defmacro stobj-accessors::stobj$c-hash-table-getp (stobj$c copyable)
  (declare (xargs :guard (booleanp copyable)))
  `(,(if copyable 'sixth 'fifth) (stobj-accessors::stobj-interface ,stobj$c)))

(defmacro stobj-accessors::stobj$c-hash-table-remover (stobj$c copyable)
  (declare (xargs :guard (booleanp copyable)))
  `(,(if copyable 'seventh 'sixth) (stobj-accessors::stobj-interface ,stobj$c)))

(defmacro stobj-accessors::stobj$c-hash-table-count (stobj$c copyable)
  (declare (xargs :guard (booleanp copyable)))
  `(,(if copyable 'eighth 'seventh) (stobj-accessors::stobj-interface ,stobj$c)))

(defmacro stobj-accessors::stobj$c-hash-table-clear (stobj$c copyable)
  (declare (xargs :guard (booleanp copyable)))
  `(,(if copyable 'ninth 'eighth) (stobj-accessors::stobj-interface ,stobj$c)))

(defmacro stobj-accessors::stobj$c-hash-table-init (stobj$c copyable)
  (declare (xargs :guard (booleanp copyable)))
  `(,(if copyable 'tenth 'ninth) (stobj-accessors::stobj-interface ,stobj$c)))

(defmacro stobj-accessors::stobj$c-hash-table-keys (stobj$c copyable)
  (declare (xargs :guard (booleanp copyable)))
  (and copyable
       `(nth 10 (stobj-accessors::stobj-interface ,stobj$c))))

(defmacro stobj-accessors::stobj$c-hash-table-keys-set (stobj$c copyable)
  (declare (xargs :guard (booleanp copyable)))
  (and copyable
       `(nth 11 (stobj-accessors::stobj-interface ,stobj$c))))

(defmacro stobj-accessors::stobj$c-hash-table-accessor-constant (stobj$c copyable)
  (declare (xargs :guard (booleanp copyable)))
  (if copyable
      `(nth 12 (stobj-accessors::stobj-interface ,stobj$c))
      `(tenth (stobj-accessors::stobj-interface ,stobj$c))))

(defmacro stobj-accessors::stobj$c-hash-table-keys-constant (stobj$c copyable)
  (declare (xargs :guard (booleanp copyable)))
  (and copyable
       `(nth 13 (stobj-accessors::stobj-interface ,stobj$c))))


;;;; `STOBJ$C-FRAME'
(defmacro stobj-accessors::stobj$c-frame-p (stobj$c)
  (declare (xargs :guard t))
  ;; an undesirably brittle characterization
  `(zp (mod (len (stobj-accessors::stobj-interface ,stobj$c)) 4)))

(defmacro stobj-accessors::stobj$c-frame-recognizers (stobj$c)
  (declare (xargs :guard t))
  `(let* ((interface (stobj-accessors::stobj-interface ,stobj$c))
          (n (floor (len interface) 4)))
     (take n interface)))

(defmacro stobj-accessors::stobj$c-frame-accessors (stobj$c)
  (declare (xargs :guard t))
  `(let* ((interface (stobj-accessors::stobj-interface ,stobj$c))
          (n (floor (len interface) 4)))
     ;; a segment of length 2n starting at n
     (evens (subseq-list interface n (* 3 n)))))

(defmacro stobj-accessors::stobj$c-frame-updaters (stobj$c)
  (declare (xargs :guard t))
  `(let* ((interface (stobj-accessors::stobj-interface ,stobj$c))
          (n (floor (len interface) 4)))
     ;; a segment of length 2n starting at n
     (odds (subseq-list interface n (* 3 n)))))

(defmacro stobj-accessors::stobj$c-frame-accessor-constants (stobj$c)
  (declare (xargs :guard t))
  `(let* ((interface (stobj-accessors::stobj-interface ,stobj$c))
          (n (floor (len interface) 4)))
     (nthcdr (* 3 n) interface)))


;;;; `*STOBJ$C-SYMBOLS*'
(defconst stobj-accessors::*stobj$c-symbols*
  '#!stobj-accessors
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
