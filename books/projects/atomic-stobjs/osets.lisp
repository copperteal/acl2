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


(in-package "SET")

(include-book "std/osets/top" :dir :system)

(defsection auxiliary-delete-theorems
  :extension delete

  "<p>The following theorem is available in
@('[books]/projects/atomic-stobjs/osets').</p>"

  (local
    (in-theory
      (enable delete
              insert
              head
              tail
              emptyp
              setp)))

  (defthm delete-of-insert-diff
    (implies (not (equal a b))
             (equal (delete a (insert b x))
                    (insert b (delete a x))))))

(defsection auxiliary-mergesort-theorems
  :extension mergesort

  "<p>The following theorems are available in
@('[books]/projects/atomic-stobjs/osets').</p>"

  (local
    (in-theory
      (enable mergesort)))

  (defthm emptyp-of-mergesort
    (equal (emptyp (mergesort x))
           (atom x)))

  (defthm mergesort-of-cons
    (equal (mergesort (cons x y))
           (insert x (mergesort y))))

  (local
    (defthm cardinality-of-mergesort-lemma
      (implies (setp x)
               (<= (cardinality (insert a x)) (1+ (len x))))
      :rule-classes :linear
      :hints
      (("Goal"
        :induct (len x)
        :in-theory (enable insert-cardinality
                           cardinality
                           tail)))))

  (defthm cardinality-of-mergesort
    (<= (cardinality (mergesort x)) (len x))
    :rule-classes :linear
    :hints
    (("Goal"
      :in-theory (enable insert-cardinality))))

  (defthm mergesort-of-remove
    (equal (mergesort (remove x l))
           (delete x (mergesort l)))))
