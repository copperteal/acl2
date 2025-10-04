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

(include-book "stobj")


;;;; `STOBJ$C'
(defmacro atomic-stobj-accessors::stobj$c-recognizer (stobj$c)
  (declare (xargs :guard t))
  `(atomic-stobj-accessors::stobj-recognizer ,stobj$c))

(defmacro atomic-stobj-accessors::stobj$c-creator (stobj$c)
  (declare (xargs :guard t))
  `(atomic-stobj-accessors::stobj-creator ,stobj$c))

(defmacro atomic-stobj-accessors::stobj$c-live-constant (stobj$c)
  (declare (xargs :guard t))
  `(atomic-stobj-accessors::stobj-live-constant ,stobj$c))


;;;; `STOBJ$C-VECTOR'
(defmacro atomic-stobj-accessors::stobj$c-vector-p (stobj$c)
  (declare (xargs :guard t))
  ;; an undesirably brittle characterization
  `(= (len (atomic-stobj-accessors::stobj-interface ,stobj$c)) 6))

(defmacro atomic-stobj-accessors::stobj$c-vector-contents-recognizer (stobj$c)
  (declare (xargs :guard t))
  `(first (atomic-stobj-accessors::stobj-interface ,stobj$c)))

(defmacro atomic-stobj-accessors::stobj$c-vector-length (stobj$c)
  (declare (xargs :guard t))
  `(second (atomic-stobj-accessors::stobj-interface ,stobj$c)))

(defmacro atomic-stobj-accessors::stobj$c-vector-resizer (stobj$c)
  (declare (xargs :guard t))
  `(third (atomic-stobj-accessors::stobj-interface ,stobj$c)))

(defmacro atomic-stobj-accessors::stobj$c-vector-accessor (stobj$c)
  (declare (xargs :guard t))
  `(fourth (atomic-stobj-accessors::stobj-interface ,stobj$c)))

(defmacro atomic-stobj-accessors::stobj$c-vector-updater (stobj$c)
  (declare (xargs :guard t))
  `(fifth (atomic-stobj-accessors::stobj-interface ,stobj$c)))

(defmacro atomic-stobj-accessors::stobj$c-vector-accessor-constant (stobj$c)
  (declare (xargs :guard t))
  `(sixth (atomic-stobj-accessors::stobj-interface ,stobj$c)))


;;;; `STOBJ$C-HASH-TABLE'
(defmacro atomic-stobj-accessors::stobj$c-hash-table-p (stobj$c copyable)
  (declare (xargs :guard (booleanp copyable)))
  ;; an undesirably brittle characterization
  `(= (len (atomic-stobj-accessors::stobj-interface ,stobj$c)) ,(if copyable 14 10)))

(defmacro atomic-stobj-accessors::stobj$c-hash-table-contents-recognizer (stobj$c copyable)
  (declare (xargs :guard (booleanp copyable))
           (ignore copyable))
  `(first (atomic-stobj-accessors::stobj-interface ,stobj$c)))

(defmacro atomic-stobj-accessors::stobj$c-hash-table-keys-recognizer (stobj$c copyable)
  (declare (xargs :guard (booleanp copyable)))
  (and copyable `(second (atomic-stobj-accessors::stobj-interface ,stobj$c))))

(defmacro atomic-stobj-accessors::stobj$c-hash-table-accessor (stobj$c copyable)
  (declare (xargs :guard (booleanp copyable)))
  `(,(if copyable 'third 'second) (atomic-stobj-accessors::stobj-interface ,stobj$c)))

(defmacro atomic-stobj-accessors::stobj$c-hash-table-updater (stobj$c copyable)
  (declare (xargs :guard (booleanp copyable)))
  `(,(if copyable 'fourth 'third) (atomic-stobj-accessors::stobj-interface ,stobj$c)))

(defmacro atomic-stobj-accessors::stobj$c-hash-table-boundp (stobj$c copyable)
  (declare (xargs :guard (booleanp copyable)))
  `(,(if copyable 'fifth 'fourth) (atomic-stobj-accessors::stobj-interface ,stobj$c)))

(defmacro atomic-stobj-accessors::stobj$c-hash-table-getp (stobj$c copyable)
  (declare (xargs :guard (booleanp copyable)))
  `(,(if copyable 'sixth 'fifth) (atomic-stobj-accessors::stobj-interface ,stobj$c)))

(defmacro atomic-stobj-accessors::stobj$c-hash-table-remover (stobj$c copyable)
  (declare (xargs :guard (booleanp copyable)))
  `(,(if copyable 'seventh 'sixth) (atomic-stobj-accessors::stobj-interface ,stobj$c)))

(defmacro atomic-stobj-accessors::stobj$c-hash-table-count (stobj$c copyable)
  (declare (xargs :guard (booleanp copyable)))
  `(,(if copyable 'eighth 'seventh) (atomic-stobj-accessors::stobj-interface ,stobj$c)))

(defmacro atomic-stobj-accessors::stobj$c-hash-table-clear (stobj$c copyable)
  (declare (xargs :guard (booleanp copyable)))
  `(,(if copyable 'ninth 'eighth) (atomic-stobj-accessors::stobj-interface ,stobj$c)))

(defmacro atomic-stobj-accessors::stobj$c-hash-table-init (stobj$c copyable)
  (declare (xargs :guard (booleanp copyable)))
  `(,(if copyable 'tenth 'ninth) (atomic-stobj-accessors::stobj-interface ,stobj$c)))

(defmacro atomic-stobj-accessors::stobj$c-hash-table-keys (stobj$c copyable)
  (declare (xargs :guard (booleanp copyable)))
  (and copyable
       `(nth 10 (atomic-stobj-accessors::stobj-interface ,stobj$c))))

(defmacro atomic-stobj-accessors::stobj$c-hash-table-keys-set (stobj$c copyable)
  (declare (xargs :guard (booleanp copyable)))
  (and copyable
       `(nth 11 (atomic-stobj-accessors::stobj-interface ,stobj$c))))

(defmacro atomic-stobj-accessors::stobj$c-hash-table-accessor-constant (stobj$c copyable)
  (declare (xargs :guard (booleanp copyable)))
  (if copyable
      `(nth 12 (atomic-stobj-accessors::stobj-interface ,stobj$c))
      `(tenth (atomic-stobj-accessors::stobj-interface ,stobj$c))))

(defmacro atomic-stobj-accessors::stobj$c-hash-table-keys-constant (stobj$c copyable)
  (declare (xargs :guard (booleanp copyable)))
  (and copyable
       `(nth 13 (atomic-stobj-accessors::stobj-interface ,stobj$c))))


;;;; `STOBJ$C-FRAME'
(defmacro atomic-stobj-accessors::stobj$c-frame-p (stobj$c)
  (declare (xargs :guard t))
  ;; an undesirably brittle characterization
  `(zp (mod (len (atomic-stobj-accessors::stobj-interface ,stobj$c)) 4)))

(defmacro atomic-stobj-accessors::stobj$c-frame-recognizers (stobj$c)
  (declare (xargs :guard t))
  `(let* ((interface (atomic-stobj-accessors::stobj-interface ,stobj$c))
          (n (floor (len interface) 4)))
     (take n interface)))

(defmacro atomic-stobj-accessors::stobj$c-frame-accessors (stobj$c)
  (declare (xargs :guard t))
  `(let* ((interface (atomic-stobj-accessors::stobj-interface ,stobj$c))
          (n (floor (len interface) 4)))
     ;; a segment of length 2n starting at n
     (evens (subseq-list interface n (* 3 n)))))

(defmacro atomic-stobj-accessors::stobj$c-frame-updaters (stobj$c)
  (declare (xargs :guard t))
  `(let* ((interface (atomic-stobj-accessors::stobj-interface ,stobj$c))
          (n (floor (len interface) 4)))
     ;; a segment of length 2n starting at n
     (odds (subseq-list interface n (* 3 n)))))

(defmacro atomic-stobj-accessors::stobj$c-frame-accessor-constants (stobj$c)
  (declare (xargs :guard t))
  `(let* ((interface (atomic-stobj-accessors::stobj-interface ,stobj$c))
          (n (floor (len interface) 4)))
     (nthcdr (* 3 n) interface)))
