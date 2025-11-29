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


(in-package "LEM-VECTOR$C")
(set-verify-guards-eagerness 2)

(local
  (include-book "std/basic/inductions" :dir :system))
(local
  (include-book "std/lists/top" :dir :system))


;;;; STD Lemmas
(local
  (defthm resize-list-of-cons
    (equal (resize-list (cons a l) i d)
           (if (zp i)
               ()
               (cons a (resize-list l (1- i) d))))
    :hints
    (("Goal"
      :expand (resize-list (cons a l) i d)))))

(local
  (defthm resize-list-of-repeat
    ;; TODO: This theorem is a good example of `REPEAT' refusing to expand
    ;; without a hint.
    (implies (equal x d)
             (equal (resize-list (repeat n x) m d)
                    (repeat m d)))
    :hints
    (("Goal"
      :induct (dec-dec-induct n m)
      :expand ((repeat m d)
               (repeat n d))))))

(local
  (defthm resize-list-of-resize-list
    (implies (and (equal d e)
                  (consp lst)
                  (natp n)
                  (natp m)
                  (or (<= m n)
                      (<= (len lst) n)))
             (equal (resize-list (resize-list lst n d) m e)
                    (resize-list lst m e)))
    :hints
    (("Goal"
      :induct (and (nth n lst)
                   (nth m lst))
      :in-theory (enable resize-list)))))

(local
  (defun resize-list-of-update-nth/induction (key l n)
    (declare (xargs :guard (and (natp key)
                                (natp n))))
    (cond
      ((zp n)
       (list key l))
      ((zp key)
       (list l n))
      ((atom l)
       (resize-list-of-update-nth/induction (1- key) l (1- n)))
      (t
       (resize-list-of-update-nth/induction (1- key) (cdr l) (1- n))))))

(local
  (defthm resize-list-of-update-nth-keep
    (implies (and (natp key)
                  (natp n)
                  (< key (len l))
                  (< key n))
             (equal (resize-list (update-nth key val l)
                                 n default-value)
                    (update-nth key val (resize-list l n default-value))))
    :hints
    (("Goal"
      :induct (resize-list-of-update-nth/induction key l n)))))

(local
  (defthm resize-list-of-update-nth-drop
    (implies (and (natp key)
                  (natp n)
                  (< key (len l))
                  (<= n key))
             (equal (resize-list (update-nth key val l)
                                 n default-value)
                    (resize-list l n default-value)))
    :hints
    (("Goal"
      :induct (resize-list-of-update-nth/induction key l n)))))


;;;; Element Constraints
(encapsulate (((default-length) => *)
              ((element-recognizer *) => *)
              ((initial-element) => *))
  (local
    (defun default-length ()
      (declare (xargs :guard t))
      0))

  (defthm natp-of-default-length
    (natp (default-length))
    :rule-classes :type-prescription)

  (local
    (defun element-recognizer (value)
      (declare (xargs :guard t))
      (integerp value)))

  (defthm booleanp-of-element-recognizer
    (booleanp (element-recognizer value))
    :rule-classes :type-prescription)

  (local
    (defun initial-element ()
      (declare (xargs :guard t))
      0))

  (defthm element-recognizer-of-initial-element
    (element-recognizer (initial-element))))


;;;; Resizable Definitions
(defun contents-recognizer (contents)
  (declare (xargs :guard t))
  (if (atom contents)
      (equal contents nil)
      (and (element-recognizer (car contents))
           (contents-recognizer (cdr contents)))))

(defun recognizer/resizable (vector)
  (declare (xargs :guard t))
  (and (true-listp vector)
       (equal (length vector) 1)
       (contents-recognizer (nth 0 vector))
       t))

(defun-nx creator ()
  (declare (xargs :guard t))
  (list (make-list (default-length)
                   :initial-element (initial-element))))

(defun fixer/resizable (vector)
  (declare (xargs :guard (recognizer/resizable vector)))
  (if (recognizer/resizable vector)
      vector
      (creator)))

(defun length/resizable (vector)
  (declare (xargs :guard (recognizer/resizable vector)))
  (len (nth 0 vector)))

(defun resizer/resizable (length vector)
  (declare (xargs :guard (and (natp length)
                              (recognizer/resizable vector))))
  (update-nth 0
              (resize-list (nth 0 vector)
                           length
                           (initial-element))
              vector))

(defun accessor (index vector)
  (declare (xargs :guard (and (recognizer/resizable vector)
                              (natp index)
                              (< index (length/resizable vector)))))
  (nth index (nth 0 vector)))

(defun updater (index value vector)
  (declare (xargs :guard (and (recognizer/resizable vector)
                              (natp index)
                              (< index (length/resizable vector))
                              (element-recognizer value))))
  (update-nth-array 0 index value vector))


;;;; `CONTENTS-RECOGNIZER'
(defthm contents-recognizer-tp
  (booleanp (contents-recognizer contents))
  :rule-classes :type-prescription)

(defthm contents-recognizer-cr
  (implies (contents-recognizer contents)
           (true-listp contents))
  :rule-classes :compound-recognizer)

(local
  (defthm contents-recognizer-of-repeat
    (equal (contents-recognizer (repeat n x))
           (if (zp n)
               t
               (element-recognizer x)))
    :hints
    (("Goal"
      :in-theory (enable repeat)))))

(local
  (defthm contents-recognizer-of-resize-list
    (implies (and (contents-recognizer contents)
                  (element-recognizer value))
             (contents-recognizer (resize-list contents length value)))
    :hints
    (("Goal"
      :in-theory (enable resize-list)))))

(local
  (defthm contents-recognizer-of-update-nth
    (implies (and (natp index)
                  (< index (len contents))
                  (element-recognizer value)
                  (contents-recognizer contents))
             (contents-recognizer (update-nth index value contents)))
    :hints
    (("Goal"
      :in-theory (enable update-nth)))))

(local
  (defthm element-recognizer-of-nth
    (implies (and (natp index)
                  (< index (len contents))
                  (contents-recognizer contents))
             (element-recognizer (nth index contents)))))


;;;; `RECOGNIZER/RESIZABLE'
(defthm recognizer/resizable-tp
  (booleanp (recognizer/resizable vector))
  :rule-classes :type-prescription)

(defthm recognizer/resizable-cr
  (implies (recognizer/resizable vector)
           (and (consp vector)
                (true-listp vector)))
  :rule-classes :compound-recognizer)

(defthm recognizer/resizable-of-creator
  (recognizer/resizable (creator)))

(defthm recognizer/resizable-of-fixer/resizable
  (recognizer/resizable (fixer/resizable vector)))

(defthm recognizer/resizable-of-resizer/resizable
  (implies (recognizer/resizable vector)
           (recognizer/resizable (resizer/resizable length vector))))

(defthm recognizer/resizable-of-updater
  (implies (and (natp index)
                (< index (length/resizable vector))
                (element-recognizer value)
                (recognizer/resizable vector))
           (recognizer/resizable (updater index value vector))))


;;;; `FIXER/RESIZABLE'
(defthm fixer/resizable-tp
  (and (consp (fixer/resizable vector))
       (true-listp (fixer/resizable vector)))
  :rule-classes :type-prescription)

(defthm fixer/resizable-when-recognizer/resizable
  (implies (recognizer/resizable vector)
           (equal (fixer/resizable vector)
                  vector)))

(defthm fixer/resizable-when-not-recognizer/resizable
  (implies (not (recognizer/resizable vector))
           (equal (fixer/resizable vector)
                  (creator))))


;;;; `LENGTH/RESIZABLE'
(defthm length/resizable-tp
  (natp (length/resizable vector))
  :rule-classes :type-prescription)

(defthm length/resizable-of-creator
  (equal (length/resizable (creator))
         (default-length)))

(defthm length/resizable-of-resizer/resizable
  (implies (natp length)
           (equal (length/resizable (resizer/resizable length vector))
                  length)))

(defthm length/resizable-of-updater
  (implies (and (natp index)
                (< index (length/resizable vector)))
           (equal (length/resizable (updater index value vector))
                  (length/resizable vector))))


;;;; `RESIZER/RESIZABLE'
(defthm resizer/resizable-tp
  (implies (recognizer/resizable vector)
           (and (consp (resizer/resizable length vector))
                (true-listp (resizer/resizable length vector))))
  :rule-classes :type-prescription)

(defthm resizer/resizable-of-creator
  (implies (equal length (default-length))
           (equal (resizer/resizable length (creator))
                  (creator))))

(defthm resizer/resizable-of-length/resizable
  (implies (recognizer/resizable vector)
           (equal (resizer/resizable (length/resizable vector) vector)
                  vector)))

(defthm resizer/resizable-of-resizer/resizable
  (implies (and (natp %length)
                (natp length)
                (or (<= %length length)
                    (<= (length/resizable vector) length))
                (recognizer/resizable vector))
           (equal (resizer/resizable %length (resizer/resizable length vector))
                  (resizer/resizable %length vector)))
  :hints
  (("Goal"
    :cases ((atom (car vector))))))

(defthm resizer/resizable-of-updater-keep
  (implies (and (natp index)
                (natp length)
                (< index length)
                (< index (length/resizable vector)))
           (equal (resizer/resizable length (updater index value vector))
                  (updater index value (resizer/resizable length vector)))))

(defthm resizer/resizable-of-updater-drop
  (implies (and (natp index)
                (natp length)
                (<= length index)
                (< index (length/resizable vector)))
           (equal (resizer/resizable length (updater index value vector))
                  (resizer/resizable length vector))))


;;;; `ACCESSOR'
(defthm element-recognizer-of-accessor/resizable
  (implies (and (natp index)
                (< index (length/resizable vector))
                (recognizer/resizable vector))
           (element-recognizer (accessor index vector))))

(defthm accessor-of-creator
  (implies (and (natp index)
                (< index (default-length)))
           (equal (accessor index (creator))
                  (initial-element))))

(defthm accessor-of-resizer/resizable-inner
  (implies (and (natp index)
                (natp length)
                (< index length)
                (< index (length/resizable vector)))
           (equal (accessor index (resizer/resizable length vector))
                  (accessor index vector))))

(defthm accessor-of-resizer/resizable-outer
  (implies (and (natp index)
                (natp length)
                (< index length)
                (<= (length/resizable vector) index))
           (equal (accessor index (resizer/resizable length vector))
                  (initial-element))))

(defthm accessor-of-updater-same
  (implies (equal %index index)
           (equal (accessor %index (updater index value vector))
                  value)))

(defthm accessor-of-updater-diff
  (implies (and (not (equal %index index))
                (natp %index)
                (natp index))
           (equal (accessor %index (updater index value vector))
                  (accessor %index vector))))


;;;; `UPDATER'
(defthm updater-tp/resizable
  (implies (recognizer/resizable vector)
           (and (consp (updater index value vector))
                (true-listp (updater index value vector))))
  :rule-classes :type-prescription)

(defthm updater-of-creator
  (implies (and (equal value (initial-element))
                (natp index)
                (< index (default-length)))
           (equal (updater index value (creator))
                  (creator))))

(defthm updater-of-resizer/resizable-inner
  (implies (and (equal value (accessor index vector))
                (natp index)
                (natp length)
                (< index length)
                (< index (length/resizable vector)))
           (equal (updater index value (resizer/resizable length vector))
                  (resizer/resizable length vector))))

(defthm updater-of-resizer/resizable-outer
  (implies (and (equal value (initial-element))
                (natp index)
                (natp length)
                (< index length)
                (<= (length/resizable vector) index))
           (equal (updater index value (resizer/resizable length vector))
                  (resizer/resizable length vector))))

(defthm updater-of-accessor/resizable
  (implies (and (equal %index index)
                (natp %index)
                (< %index (length/resizable vector))
                (recognizer/resizable vector))
           (equal (updater %index (accessor index vector) vector)
                  vector)))

(defthm updater-of-updater-same
  (implies (equal %index index)
           (equal (updater %index %value (updater index value vector))
                  (updater %index %value vector))))

(defthm updater-of-updater-diff
  (implies (and (not (equal %index index))
                (natp %index)
                (natp index))
           (equal (updater %index %value (updater index value vector))
                  (updater index value (updater %index %value vector))))
  :rule-classes
  ((:rewrite :loop-stopper ((%index index updater)))))


;;;; Fixed-Length Adjustments
(defun recognizer/fixed (vector)
  (declare (xargs :guard t))
  (and (true-listp vector)
       (equal (length vector) 1)
       (contents-recognizer (nth 0 vector))
       (equal (len (nth 0 vector)) (default-length))
       t))

(defun fixer/fixed (vector)
  (declare (xargs :guard (recognizer/fixed vector)))
  (if (recognizer/fixed vector)
      vector
      (creator)))

(defun length/fixed (vector)
  (declare (xargs :guard (recognizer/fixed vector))
           (ignore vector))
  (default-length))

(defun resizer/fixed (length vector)
  (declare (xargs :guard (and (natp length)
                              (recognizer/fixed vector)))
           (ignore length))
  vector)


;;;; `RECOGNIZER/FIXED'
(defthm recognizer/fixed-tp
  (booleanp (recognizer/fixed vector))
  :rule-classes :type-prescription)

(defthm recognizer/fixed-cr
  (implies (recognizer/fixed vector)
           (and (consp vector)
                (true-listp vector)))
  :rule-classes :compound-recognizer)

(defthm recognizer/fixed-of-creator
  (recognizer/fixed (creator)))

(defthm recognizer/fixed-of-fixer/fixed
  (recognizer/fixed (fixer/fixed vector)))

(defthm recognizer/fixed-of-updater
  (implies (and (natp index)
                (< index (default-length))
                (element-recognizer value)
                (recognizer/fixed vector))
           (recognizer/fixed (updater index value vector))))


;;;; `FIXER/FIXED'
(defthm fixer/fixed-tp
  (and (consp (fixer/fixed vector))
       (true-listp (fixer/fixed vector)))
  :rule-classes :type-prescription)

(defthm fixer/fixed-when-recognizer/fixed
  (implies (recognizer/fixed vector)
           (equal (fixer/fixed vector)
                  vector)))

(defthm fixer/fixed-when-not-recognizer/fixed
  (implies (not (recognizer/fixed vector))
           (equal (fixer/fixed vector)
                  (creator))))


;;;; `LENGTH/FIXED'
(defthm length/fixed-tp
  (natp (length/fixed vector))
  :rule-classes :type-prescription)

(defthm length/fixed-rw
  (equal (length/fixed vector)
         (default-length)))


;;;; `RESIZER/FIXED'
(defthm resizer/fixed-tp
  (implies (recognizer/fixed vector)
           (and (consp (resizer/fixed length vector))
                (true-listp (resizer/fixed length vector))))
  :rule-classes :type-prescription)

(defthm resizer/fixed-rw
  (equal (resizer/fixed length vector)
         vector))


;;;; `ACCESSOR' (fixed adjustments)
(defthm element-recognizer-of-accessor/fixed
  (implies (and (natp index)
                (< index (default-length))
                (recognizer/fixed vector))
           (element-recognizer (accessor index vector))))


;;;; `UPDATER' (fixed adjustments)
(defthm updater-tp/fixed
  (implies (recognizer/fixed vector)
           (and (consp (updater index value vector))
                (true-listp (updater index value vector))))
  :rule-classes :type-prescription)

(defthm updater-of-accessor/fixed
  (implies (and (equal %index index)
                (natp %index)
                (< %index (default-length))
                (recognizer/fixed vector))
           (equal (updater %index (accessor index vector) vector)
                  vector)))
