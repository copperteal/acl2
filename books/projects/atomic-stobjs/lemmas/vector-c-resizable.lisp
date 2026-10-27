;;; Copyright 2026 J. David Taylor
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
    :rule-classes
    ((:rewrite :corollary
               (equal (resize-list (cons a l) i d)
                      (if (zp (double-rewrite i))
                          ()
                          (cons a (resize-list l (1- i) d))))))
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
    :rule-classes
    ((:rewrite :corollary
               (implies (and (equal d e)
                             (consp (double-rewrite lst))
                             (natp n)
                             (natp m)
                             (or (<= m n)
                                 (<= (len lst) n)))
                        (equal (resize-list (resize-list lst n d) m e)
                               (resize-list lst m e)))))
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
    (defun element-recognizer (element)
      (declare (xargs :guard t))
      (integerp element)))

  (defthm booleanp-of-element-recognizer
    (booleanp (element-recognizer element))
    :rule-classes :type-prescription)

  (local
    (defun initial-element ()
      (declare (xargs :guard t))
      0))

  (defthm element-recognizer-of-initial-element
    (element-recognizer (initial-element))))


;;;; Definitions
(defun contents-recognizer (contents)
  (declare (xargs :guard t))
  (if (atom contents)
      (equal contents nil)
      (and (element-recognizer (car contents))
           (contents-recognizer (cdr contents)))))

(defun recognizer (vector)
  (declare (xargs :guard t))
  (and (true-listp vector)
       (equal (acl2::length vector) 1)
       (contents-recognizer (nth 0 vector))
       t))

(defun-nx creator ()
  (declare (xargs :guard t))
  (list (make-list (default-length)
                   :initial-element (initial-element))))

(defun fixer (vector)
  (declare (xargs :guard (recognizer vector)))
  (if (recognizer vector)
      vector
      (creator)))

(defun length (vector)
  (declare (xargs :guard (recognizer vector)))
  (len (nth 0 vector)))

(defun resizer (length vector)
  (declare (xargs :guard (and (natp length)
                              (recognizer vector))))
  (update-nth 0
              (resize-list (nth 0 vector)
                           length
                           (initial-element))
              vector))

(defun accessor (index vector)
  (declare (xargs :guard (and (recognizer vector)
                              (natp index)
                              (< index (length vector)))))
  (nth index (nth 0 vector)))

(defun updater (index element vector)
  (declare (xargs :guard (and (recognizer vector)
                              (natp index)
                              (< index (length vector))
                              (element-recognizer element))))
  (update-nth-array 0 index element vector))


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
    :rule-classes
    ((:rewrite :corollary
               (equal (contents-recognizer (repeat n x))
                      (if (zp (double-rewrite n))
                          t
                          (element-recognizer x)))))
    :hints
    (("Goal"
      :in-theory (enable repeat)))))

(local
  (defthm contents-recognizer-of-resize-list
    (implies (and (contents-recognizer contents)
                  (element-recognizer element))
             (contents-recognizer (resize-list contents length element)))
    :hints
    (("Goal"
      :in-theory (enable resize-list)))))

(local
  (defthm contents-recognizer-of-update-nth
    (implies (and (natp index)
                  (< index (len contents))
                  (element-recognizer element)
                  (contents-recognizer contents))
             (contents-recognizer (update-nth index element contents)))
    :rule-classes
    ((:rewrite :corollary
               (implies (and (natp index)
                             (< index (len (double-rewrite contents)))
                             (element-recognizer element)
                             (contents-recognizer contents))
                        (contents-recognizer (update-nth index element contents)))))
    :hints
    (("Goal"
      :in-theory (enable update-nth)))))

(local
  (defthm element-recognizer-of-nth
    (implies (and (natp index)
                  (< index (len contents))
                  (contents-recognizer contents))
             (element-recognizer (nth index contents)))))


;;;; `RECOGNIZER'
(defthm recognizer-tp
  (booleanp (recognizer vector))
  :rule-classes :type-prescription)

(defthm recognizer-cr
  (implies (recognizer vector)
           (and (consp vector)
                (true-listp vector)))
  :rule-classes :compound-recognizer)

(defthm recognizer-of-creator
  (recognizer (creator)))

(defthm recognizer-of-fixer
  (recognizer (fixer vector)))

(defthm recognizer-of-resizer
  (implies (recognizer vector)
           (recognizer (resizer length vector))))

(defthm recognizer-of-updater
  (implies (and (natp index)
                (< index (length vector))
                (element-recognizer element)
                (recognizer vector))
           (recognizer (updater index element vector))))


;;;; `FIXER'
(defthm fixer-tp
  (and (consp (fixer vector))
       (true-listp (fixer vector)))
  :rule-classes :type-prescription)

(defthm fixer-when-recognizer
  (implies (recognizer vector)
           (equal (fixer vector)
                  vector)))

(defthm fixer-when-not-recognizer
  (implies (not (recognizer vector))
           (equal (fixer vector)
                  (creator))))


;;;; `LENGTH'
(defthm length-tp
  (natp (length vector))
  :rule-classes :type-prescription)

(defthm length-of-creator
  (equal (length (creator))
         (default-length)))

(defthm length-of-resizer
  (implies (natp length)
           (equal (length (resizer length vector))
                  length)))

(defthm length-of-updater
  (implies (and (natp index)
                (< index (length vector)))
           (equal (length (updater index element vector))
                  (length vector))))


;;;; `RESIZER'
(defthm resizer-tp
  (implies (recognizer vector)
           (and (consp (resizer length vector))
                (true-listp (resizer length vector))))
  :rule-classes :type-prescription)

(defthm resizer-of-creator
  (implies (equal length (default-length))
           (equal (resizer length (creator))
                  (creator))))

(defthm resizer-of-length
  (implies (recognizer vector)
           (equal (resizer (length vector) vector)
                  vector)))

(defthm resizer-of-resizer
  (implies (and (natp length1)
                (natp length2)
                (or (<= length1 length2)
                    (<= (length vector) length2))
                (recognizer vector))
           (equal (resizer length1 (resizer length2 vector))
                  (resizer length1 vector)))
  :hints
  (("Goal"
    :cases ((atom (car vector))))))

(defthm resizer-of-updater-keep
  (implies (and (natp index)
                (natp length)
                (< index length)
                (< index (length vector)))
           (equal (resizer length (updater index element vector))
                  (updater index element (resizer length vector)))))

(defthm resizer-of-updater-drop
  (implies (and (natp index)
                (natp length)
                (<= length index)
                (< index (length vector)))
           (equal (resizer length (updater index element vector))
                  (resizer length vector))))


;;;; `ACCESSOR'
(defthm element-recognizer-of-accessor
  (implies (and (natp index)
                (< index (length vector))
                (recognizer vector))
           (element-recognizer (accessor index vector))))

(defthm accessor-of-creator
  (implies (and (natp index)
                (< index (default-length)))
           (equal (accessor index (creator))
                  (initial-element))))

(defthm accessor-of-resizer-inner
  (implies (and (natp index)
                (natp length)
                (< index length)
                (< index (length vector)))
           (equal (accessor index (resizer length vector))
                  (accessor index vector))))

(defthm accessor-of-resizer-outer
  (implies (and (natp index)
                (natp length)
                (< index length)
                (<= (length vector) index))
           (equal (accessor index (resizer length vector))
                  (initial-element))))

(defthm accessor-of-updater-same
  (implies (equal index1 index2)
           (equal (accessor index1 (updater index2 element vector))
                  element)))

(defthm accessor-of-updater-diff
  (implies (and (not (equal index1 index2))
                (natp index1)
                (natp index2))
           (equal (accessor index1 (updater index2 element vector))
                  (accessor index1 vector))))


;;;; `UPDATER'
(defthm updater-tp
  (implies (recognizer vector)
           (and (consp (updater index element vector))
                (true-listp (updater index element vector))))
  :rule-classes :type-prescription)

(defthm updater-of-creator
  (implies (and (equal element (initial-element))
                (natp index)
                (< index (default-length)))
           (equal (updater index element (creator))
                  (creator))))

(defthm updater-of-resizer-inner
  (implies (and (equal element (accessor index vector))
                (natp index)
                (natp length)
                (< index length)
                (< index (length vector)))
           (equal (updater index element (resizer length vector))
                  (resizer length vector))))

(defthm updater-of-resizer-outer
  (implies (and (equal element (initial-element))
                (natp index)
                (natp length)
                (< index length)
                (<= (length vector) index))
           (equal (updater index element (resizer length vector))
                  (resizer length vector))))

(defthm updater-of-accessor
  (implies (and (equal index1 index2)
                (natp index1)
                (< index1 (length vector))
                (recognizer vector))
           (equal (updater index1 (accessor index2 vector) vector)
                  vector)))

(defthm updater-of-updater-same
  (implies (equal index1 index2)
           (equal (updater index1 element1 (updater index2 element2 vector))
                  (updater index1 element1 vector))))

(defthm updater-of-updater-diff
  (implies (and (not (equal index1 index2))
                (natp index1)
                (natp index2))
           (equal (updater index1 element1 (updater index2 element2 vector))
                  (updater index2 element2 (updater index1 element1 vector))))
  :rule-classes
  ((:rewrite :loop-stopper ((index1 index2 updater)))))


;;;; Constraints
(defconst *exports* '(default-length
                      element-recognizer
                      initial-element
                      contents-recognizer
                      recognizer
                      creator
                      fixer
                      length
                      resizer
                      accessor
                      updater))

(encapsulate ()
  (local
    (include-book"../utilities/top"))

  (make-event
    `(defconst *constraints*
       ',(collect-constraint-info *exports* (w state)))))
