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
       (equal (len (nth 0 vector)) (default-length))
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
  (declare (xargs :guard (recognizer vector))
           (ignore vector))
  (default-length))

(defun resizer (length vector)
  (declare (xargs :guard (and (natp length)
                              (recognizer vector)))
           (ignore length))
  vector)

(defun accessor (index vector)
  (declare (xargs :guard (and (recognizer vector)
                              (natp index)
                              (< index (default-length)))))
  (nth index (nth 0 vector)))

(defun updater (index value vector)
  (declare (xargs :guard (and (recognizer vector)
                              (natp index)
                              (< index (default-length))
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

(defthm recognizer-of-updater
  (implies (and (natp index)
                (< index (default-length))
                (element-recognizer value)
                (recognizer vector))
           (recognizer (updater index value vector))))


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

(defthm length-rw
  (equal (length vector)
         (default-length)))


;;;; `RESIZER'
(defthm resizer-tp
  (implies (recognizer vector)
           (and (consp (resizer length vector))
                (true-listp (resizer length vector))))
  :rule-classes :type-prescription)

(defthm resizer-rw
  (equal (resizer length vector)
         vector))


;;;; `ACCESSOR'
(defthm element-recognizer-of-accessor
  (implies (and (natp index)
                (< index (default-length))
                (recognizer vector))
           (element-recognizer (accessor index vector))))

(defthm accessor-of-creator
  (implies (and (natp index)
                (< index (default-length)))
           (equal (accessor index (creator))
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
(defthm updater-tp
  (implies (recognizer vector)
           (and (consp (updater index value vector))
                (true-listp (updater index value vector))))
  :rule-classes :type-prescription)

(defthm updater-of-creator
  (implies (and (equal value (initial-element))
                (natp index)
                (< index (default-length)))
           (equal (updater index value (creator))
                  (creator))))

(defthm updater-of-accessor
  (implies (and (equal %index index)
                (natp %index)
                (< %index (default-length))
                (recognizer vector))
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
