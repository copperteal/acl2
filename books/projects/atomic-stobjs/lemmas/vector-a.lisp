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


(in-package "LEM-VECTOR$A")
(set-verify-guards-eagerness 2)

(include-book "std/basic/arith-equiv-defs" :dir :system)

(local
  (include-book "std/basic/inductions" :dir :system))
(local
  (include-book "std/lists/top" :dir :system))


;;;; STD Lemmas
(local
  (defthm resize-list-of-cons
    (equal (resize-list (cons a l) i d)
           (if (zp (double-rewrite i))
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
                  (consp (double-rewrite lst))
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

(local
  (defthm update-nth-of-resize-list
    (implies (and (and (natp key)
                       (natp n)
                       (< key n))
                  (equal val (if (< key (len lst))
                                 (nth key lst)
                                 default-value)))
             (equal (update-nth key val (resize-list lst n default-value))
                    (resize-list lst n default-value)))))


;;;; Element Constraints
(encapsulate (((default-length) => *)
              ((element-recognizer *) => *)
              ((initial-element) => *))
  (local
    (defun default-length ()
      (declare (xargs :guard t))
      0))

  (defthm default-length-tp
    (natp (default-length))
    :rule-classes :type-prescription)

  (local
    (defun element-recognizer (value)
      (declare (xargs :guard t))
      (integerp value)))

  (defthm element-recognizer-tp
    (booleanp (element-recognizer value))
    :rule-classes :type-prescription)

  (local
    (defun initial-element ()
      (declare (xargs :guard t))
      0))

  (defthm element-recognizer-of-initial-element
    (element-recognizer (initial-element))))

(defun element-fixer (value)
  (declare (xargs :guard t))
  (if (element-recognizer value)
      value
      (initial-element)))

(local
  (defthm element-recognizer-of-element-fixer
    (element-recognizer (element-fixer value))))

(local
  (defthm element-fixer-when-element-recognizer
    (implies (element-recognizer value)
             (equal (element-fixer value)
                    value))))

(local
  (defthm element-fixer-when-not-element-recognizer
    (implies (not (element-recognizer value))
             (equal (element-fixer value)
                    (initial-element)))))

(defun element-equiv (%value value)
  (declare (xargs :guard t))
  (equal (element-fixer %value)
         (element-fixer value)))

(defequiv element-equiv)

(local
  (defcong element-equiv equal (element-fixer value) 1))

(local
  (defthm element-fixer-mod-element-equiv
    (element-equiv (element-fixer value) value)))

(local
  (in-theory
    (disable element-fixer)))


;;;; Shared Definitions
(defun recognizer-aux (contents)
  (declare (xargs :guard t))
  (if (consp contents)
      (and (element-recognizer (car contents))
           (recognizer-aux (cdr contents)))
      (null contents)))

(defun-nx creator ()
  (declare (xargs :guard t))
  (make-list (default-length)
             :initial-element (initial-element)))


;;;; Resizable Definitions
(defun recognizer/resizable (vector)
  (declare (xargs :guard t))
  (recognizer-aux vector))

(defun fixer/resizable (vector)
  (declare (xargs :guard (recognizer/resizable vector)))
  (if (recognizer/resizable vector)
      vector
      (creator)))

(defun equiv/resizable (%vector vector)
  (declare (xargs :guard (and (recognizer/resizable %vector)
                              (recognizer/resizable vector))))
  (equal (fixer/resizable %vector)
         (fixer/resizable vector)))

(defun length/resizable (vector)
  (declare (xargs :guard (recognizer/resizable vector)))
  (len (fixer/resizable vector)))

(defun resizer/resizable (length vector)
  (declare (xargs :guard (and (natp length)
                              (recognizer/resizable vector))))
  (let ((length (nfix length))
        (vector (fixer/resizable vector)))
    (resize-list vector length (initial-element))))

(defun accessor/resizable (index vector)
  (declare (xargs :guard (and (natp index)
                              (recognizer/resizable vector)
                              (< index (length/resizable vector)))))
  (let ((index (nfix index))
        (vector (fixer/resizable vector)))
    (if (< index (length/resizable vector))
        (element-fixer (nth index vector))
        (initial-element))))

(defun updater/resizable (index value vector)
  (declare (xargs :guard (and (natp index)
                              (element-recognizer value)
                              (recognizer/resizable vector)
                              (< index (length/resizable vector)))))
  (let ((index (nfix index))
        (value (element-fixer value))
        (vector (fixer/resizable vector)))
    (if (< index (length/resizable vector))
        (update-nth index value vector)
        vector)))


;;;; `RECOGNIZER-AUX'
(defthm recognizer-aux-tp
  (booleanp (recognizer-aux vector))
  :rule-classes :type-prescription)

(defthm recognizer-aux-cr
  (implies (recognizer-aux vector)
           (true-listp vector))
  :rule-classes :compound-recognizer)

(local
  (defthm recognizer-aux-of-repeat
    (equal (recognizer-aux (repeat n x))
           (if (zp (double-rewrite n))
               t
               (element-recognizer x)))
    :hints
    (("Goal"
      :in-theory (enable repeat)))))

(local
  (defthm recognizer-aux-of-resize-list
    (implies (and (recognizer-aux contents)
                  (element-recognizer value))
             (recognizer-aux (resize-list contents length value)))
    :hints
    (("Goal"
      :in-theory (enable resize-list)))))

(local
  (defthm recognizer-aux-of-update-nth
    (implies (and (natp index)
                  (< index (len (double-rewrite contents)))
                  (element-recognizer value)
                  (recognizer-aux contents))
             (recognizer-aux (update-nth index value contents)))
    :hints
    (("Goal"
      :in-theory (enable update-nth)))))

(defthm element-recognizer-of-nth-when-recognizer-aux
  (implies (and (natp index)
                (< index (len contents))
                (recognizer-aux contents))
           (element-recognizer (nth index contents))))


;;;; `RECOGNIZER/RESIZABLE'
(defthm recognizer/resizable-tp
  (booleanp (recognizer/resizable vector))
  :rule-classes :type-prescription)

(defthm recognizer/resizable-cr
  (implies (recognizer/resizable vector)
           (true-listp vector))
  :rule-classes :compound-recognizer)

(defthm recognizer/resizable-of-creator
  (recognizer/resizable (creator)))

(defthm recognizer/resizable-of-fixer/resizable
  (recognizer/resizable (fixer/resizable vector)))

(defthm recognizer/resizable-of-resizer/resizable
  (recognizer/resizable (resizer/resizable length vector)))

(defthm recognizer/resizable-of-updater/resizable
  (recognizer/resizable (updater/resizable index value vector))
  :hints
  (("Goal"
    :in-theory (disable update-nth
                        update-nth-when-zp))))


;;;; `FIXER/RESIZABLE'
(defthm fixer/resizable-tp
  (true-listp (fixer/resizable vector))
  :rule-classes :type-prescription)

(defthm fixer/resizable-when-recognizer/resizable
  (implies (recognizer/resizable vector)
           (equal (fixer/resizable vector)
                  vector)))

(defthm fixer/resizable-when-not-recognizer/resizable
  (implies (not (recognizer/resizable vector))
           (equal (fixer/resizable vector)
                  (creator))))


;;;; `EQUIV/RESIZABLE'
(defthm equiv/resizable-tp
  (booleanp (equiv/resizable %vector vector))
  :rule-classes :type-prescription)

(defequiv equiv/resizable)

(defcong equiv/resizable equal (fixer/resizable vector) 1)

(defthm fixer/resizable-mod-equiv/resizable
  (equiv/resizable (fixer/resizable vector) vector))

(defthm equiv/resizable-when-not-recognizer/resizable
  (implies (not (recognizer/resizable vector))
           (equiv/resizable vector (creator))))


;;;; `LENGTH/RESIZABLE'
(defthm length/resizable-tp
  (natp (length/resizable vector))
  :rule-classes :type-prescription)

(defcong equiv/resizable equal (length/resizable vector) 1)

(defthm length/resizable-when-not-recognizer/resizable
  (implies (not (recognizer/resizable vector))
           (equal (length/resizable vector)
                  (default-length))))

(defthm length/resizable-of-creator
  (equal (length/resizable (creator))
         (default-length)))

(defthm length/resizable-of-resizer/resizable
  (equal (length/resizable (resizer/resizable length vector))
         (nfix length))
  :rule-classes
  ((:rewrite :corollary
             (equal (length/resizable (resizer/resizable length vector))
                    (nfix (double-rewrite length))))))

(defthm length/resizable-of-updater/resizable
  (equal (length/resizable (updater/resizable index value vector))
         (length/resizable vector))
  :rule-classes
  ((:rewrite :corollary
             (equal (length/resizable (updater/resizable index value vector))
                    (length/resizable (double-rewrite vector)))))
  :hints
  (("Goal"
    :in-theory (disable update-nth
                        update-nth-when-zp))))


;;;; `RESIZER/RESIZABLE'
(defthm resizer/resizable-tp
  (true-listp (resizer/resizable length vector))
  :rule-classes :type-prescription)

(defcong nat-equiv equal (resizer/resizable length vector) 1)

(defcong equiv/resizable equal (resizer/resizable length vector) 2)

(defthm resizer/resizable-when-not-natp
  (implies (not (natp length))
           (equal (resizer/resizable length vector)
                  (resizer/resizable 0 vector))))

(defthm resizer/resizable-when-not-recognizer/resizable
  (implies (not (recognizer/resizable vector))
           (equal (resizer/resizable length vector)
                  (resizer/resizable length (creator)))))

(defthm resizer/resizable-of-creator
  (implies (nat-equiv length (default-length))
           (equal (resizer/resizable length (creator))
                  (creator))))

(defthm resizer/resizable-of-length/resizable-free
  (implies (nat-equiv length (length/resizable vector))
           (equal (resizer/resizable length vector)
                  (fixer/resizable vector))))

(defthm resizer/resizable-of-length/resizable
  (implies (equiv/resizable %vector vector)
           (equal (resizer/resizable (length/resizable %vector) vector)
                  (fixer/resizable vector)))
  :hints
  (("Goal"
    :in-theory (disable resizer/resizable-of-length/resizable-free
                        resizer/resizable
                        length/resizable
                        fixer/resizable
                        equiv/resizable)
    :use (:instance resizer/resizable-of-length/resizable-free
                    (length (length/resizable vector))))))

(defthm resizer/resizable-of-resizer/resizable
  (implies (or (<= (nfix %length) (nfix length))
               (<= (length/resizable vector) (nfix length)))
           (equal (resizer/resizable %length (resizer/resizable length vector))
                  (resizer/resizable %length vector)))
  :hints
  (("Goal"
    :in-theory (disable nfix
                        resize-list-of-resize-list)
    :use ((:instance resize-list-of-resize-list
                     (lst vector)
                     (n (nfix length))
                     (d (initial-element))
                     (m (nfix %length))
                     (e (initial-element)))))))

(defthm resizer/resizable-of-updater/resizable-keep
  (implies (and (< (nfix index) (length/resizable vector))
                (< (nfix index) (nfix length)))
           (equal (resizer/resizable length (updater/resizable index value vector))
                  (updater/resizable index value (resizer/resizable length vector))))
  :rule-classes
  ((:rewrite :corollary
             (implies (and (< (nfix (double-rewrite index)) (length/resizable (double-rewrite vector)))
                           (< (nfix (double-rewrite index)) (nfix length)))
                      (equal (resizer/resizable length (updater/resizable index value vector))
                             (updater/resizable index value (resizer/resizable length (double-rewrite vector)))))))
  :hints
  (("Goal"
    :in-theory (disable nfix
                        update-nth
                        resize-list-of-update-nth-keep))
   ("Subgoal 3"
    :use ((:instance resize-list-of-update-nth-keep
                     (key (nfix index))
                     (val (element-fixer value))
                     (l vector)
                     (n (nfix length))
                     (default-value (initial-element)))))
   ("Subgoal 2"
    :use ((:instance resize-list-of-update-nth-keep
                     (key (nfix index))
                     (val (element-fixer value))
                     (l (repeat (default-length)
                                (initial-element)))
                     (n (nfix length))
                     (default-value (initial-element)))))))

(defthm resizer/resizable-of-updater/resizable-drop
  (implies (and (< (nfix index) (length/resizable vector))
                (<= (nfix length) (nfix index)))
           (equal (resizer/resizable length (updater/resizable index value vector))
                  (resizer/resizable length vector)))
  :rule-classes
  ((:rewrite :corollary
             (implies (and (< (nfix (double-rewrite index)) (length/resizable (double-rewrite vector)))
                           (<= (nfix length) (nfix (double-rewrite index))))
                      (equal (resizer/resizable length (updater/resizable index value vector))
                             (resizer/resizable length (double-rewrite vector))))))
  :hints
  (("Goal"
    :in-theory (disable nfix
                        update-nth
                        resize-list-of-update-nth-drop))
   ("Subgoal 3"
    :use ((:instance resize-list-of-update-nth-drop
                     (key (nfix index))
                     (val (element-fixer value))
                     (l vector)
                     (n (nfix length))
                     (default-value (initial-element)))))
   ("Subgoal 2"
    :use ((:instance resize-list-of-update-nth-drop
                     (key (nfix index))
                     (val (element-fixer value))
                     (l (repeat (default-length)
                                (initial-element)))
                     (n (nfix length))
                     (default-value (initial-element)))))))

(encapsulate ()
  (local
    (defthm updater/resizable-when-large
      ;; This theorem is re-proved in the `UPDATER/RESIZABLE' section.
      (implies (<= (length/resizable (double-rewrite vector)) (nfix (double-rewrite index)))
               (equal (updater/resizable index value vector)
                      (fixer/resizable (double-rewrite vector))))))

  (defthm resizer/resizable-of-updater/resizable
    (equal (resizer/resizable length (updater/resizable index value vector))
           (if (and (< (nfix index) (length/resizable vector))
                    (< (nfix index) (nfix length)))
               (updater/resizable index value (resizer/resizable length vector))
               (resizer/resizable length vector)))
    :rule-classes
    ((:rewrite :corollary
               (equal (resizer/resizable length (updater/resizable index value vector))
                      (if (and (< (nfix (double-rewrite index)) (length/resizable (double-rewrite vector)))
                               (< (nfix (double-rewrite index)) (nfix length)))
                          (updater/resizable index value (resizer/resizable length (double-rewrite vector)))
                          (resizer/resizable length (double-rewrite vector))))))
    :hints
    (("Goal"
      :cases ((<= (length/resizable vector) (nfix index)))
      :in-theory (disable nfix
                          resizer/resizable
                          updater/resizable
                          length/resizable)))))


;;;; `ACCESSOR/RESIZABLE'
(defthm element-recognizer-of-accessor/resizable
  (element-recognizer (accessor/resizable index vector)))

(defcong nat-equiv equal (accessor/resizable index vector) 1)

(defcong equiv/resizable equal (accessor/resizable index vector) 2)

(defthm accessor/resizable-when-large
  (implies (<= (length/resizable vector) (nfix index))
           (equal (accessor/resizable index vector)
                  (initial-element))))

(defthm accessor/resizable-when-not-natp
  (implies (not (natp index))
           (equal (accessor/resizable index vector)
                  (accessor/resizable 0 vector))))

(defthm accessor/resizable-when-not-recognizer/resizable
  (implies (not (recognizer/resizable vector))
           (equal (accessor/resizable index vector)
                  (initial-element))))

(defthm accessor/resizable-of-creator
  (equal (accessor/resizable index (creator))
         (initial-element)))

(defthm accessor/resizable-of-resizer/resizable-wh
  (implies (< (nfix index) (nfix length))
           (equal (accessor/resizable index (resizer/resizable length vector))
                  (accessor/resizable index vector))))

(defthm accessor/resizable-of-resizer/resizable
  (equal (accessor/resizable index (resizer/resizable length vector))
         (if (< (nfix index) (nfix length))
             (accessor/resizable index vector)
             (initial-element))))

(defthm accessor/resizable-of-updater/resizable-same
  (implies (and (nat-equiv %index index)
                (< (nfix %index) (length/resizable vector)))
           (equal (accessor/resizable %index (updater/resizable index value vector))
                  (element-fixer value)))
  :rule-classes
  ((:rewrite :corollary
             (implies (and (nat-equiv %index (double-rewrite index))
                           (< (nfix %index) (length/resizable (double-rewrite vector))))
                      (equal (accessor/resizable %index (updater/resizable index value vector))
                             (element-fixer (double-rewrite value))))))
  :hints
  (("Goal"
    :in-theory (disable nfix
                        update-nth
                        update-nth-when-zp))))

(defthm accessor/resizable-of-updater/resizable-diff
  (implies (and (not (nat-equiv %index index))
                (< (nfix %index) (length/resizable vector)))
           (equal (accessor/resizable %index (updater/resizable index value vector))
                  (accessor/resizable %index vector)))
  :rule-classes
  ((:rewrite :corollary
             (implies (and (not (nat-equiv %index (double-rewrite index)))
                           (< (nfix %index) (length/resizable (double-rewrite vector))))
                      (equal (accessor/resizable %index (updater/resizable index value vector))
                             (accessor/resizable %index (double-rewrite vector))))))
  :hints
  (("Goal"
    :in-theory (disable nfix
                        update-nth
                        update-nth-when-zp))))

(defthm accessor/resizable-of-updater/resizable
  (equal (accessor/resizable %index (updater/resizable index value vector))
         (cond
           ((<= (length/resizable vector) (nfix %index))
            (initial-element))
           ((nat-equiv %index index)
            (element-fixer value))
           (t
            (accessor/resizable %index vector))))
  :rule-classes
  ((:rewrite :corollary
             (equal (accessor/resizable %index (updater/resizable index value vector))
                    (cond
                      ((<= (length/resizable (double-rewrite vector)) (nfix %index))
                       (initial-element))
                      ((nat-equiv %index (double-rewrite index))
                       (element-fixer (double-rewrite value)))
                      (t
                       (accessor/resizable %index (double-rewrite vector)))))))
  :hints
  (("Goal"
    :cases ((and (nat-equiv %index index)
                 (< (nfix %index) (length/resizable vector)))
            (and (not (nat-equiv %index index))
                 (< (nfix %index) (length/resizable vector))))
    :in-theory (disable nfix
                        accessor/resizable
                        updater/resizable
                        length/resizable))))


;;;; `UPDATER/RESIZABLE'
(defthm updater/resizable-tp
  (true-listp (updater/resizable index value vector))
  :rule-classes :type-prescription)

(defcong nat-equiv equal (updater/resizable index value vector) 1)

(defcong element-equiv equal (updater/resizable index value vector) 2)

(defcong equiv/resizable equal (updater/resizable index value vector) 3)

(defthm updater/resizable-when-large
  (implies (<= (length/resizable vector) (nfix index))
           (equal (updater/resizable index value vector)
                  (fixer/resizable vector)))
  :rule-classes
  ((:rewrite :corollary
             (implies (<= (length/resizable (double-rewrite vector)) (nfix (double-rewrite index)))
                      (equal (updater/resizable index value vector)
                             (fixer/resizable (double-rewrite vector)))))))

(defthm updater/resizable-when-not-natp
  (implies (not (natp index))
           (equal (updater/resizable index value vector)
                  (updater/resizable 0 value vector))))

(defthm updater/resizable-when-not-element-recognizer
  (implies (not (element-recognizer value))
           (equal (updater/resizable index value vector)
                  (updater/resizable index (initial-element) vector))))

(defthm updater/resizable-when-not-recognizer/resizable
  (implies (not (recognizer/resizable vector))
           (equal (updater/resizable index value vector)
                  (updater/resizable index value (creator)))))

(defthm updater/resizable-of-creator
  (implies (element-equiv value (initial-element))
           (equal (updater/resizable index value (creator))
                  (creator))))

(defthm updater/resizable-of-resizer/resizable
  (implies (element-equiv value (accessor/resizable index vector))
           (equal (updater/resizable index value (resizer/resizable length vector))
                  (resizer/resizable length vector)))
  :hints
  (("Goal"
    :in-theory (disable update-nth
                        update-nth-when-zp))))

(defthm updater/resizable-of-accessor/resizable-free
  (implies (element-equiv value (accessor/resizable index vector))
           (equal (updater/resizable index value vector)
                  (fixer/resizable vector)))
  :hints
  (("Goal"
    :in-theory (disable update-nth
                        update-nth-when-zp))))

(defthm updater/resizable-of-accessor/resizable
  (implies (and (nat-equiv %index index)
                (equiv/resizable %vector vector))
           (equal (updater/resizable %index (accessor/resizable index %vector) vector)
                  (fixer/resizable vector)))
  :hints
  (("Goal"
    :in-theory (disable updater/resizable-of-accessor/resizable-free
                        updater/resizable
                        accessor/resizable
                        fixer/resizable
                        equiv/resizable)
    :use (:instance updater/resizable-of-accessor/resizable-free
                    (index %index)
                    (value (accessor/resizable index vector))))))

(defthm updater/resizable-of-updater/resizable-same
  (implies (nat-equiv %index index)
           (equal (updater/resizable %index %value (updater/resizable index value vector))
                  (updater/resizable %index %value vector)))
  :hints
  (("Goal"
    :in-theory (disable update-nth
                        update-nth-when-zp))))

(defthm updater/resizable-of-updater/resizable-diff
  (implies (not (nat-equiv %index index))
           (equal (updater/resizable %index %value (updater/resizable index value vector))
                  (updater/resizable index value (updater/resizable %index %value vector))))
  :rule-classes
  ((:rewrite :loop-stopper ((%index index updater/resizable))))
  :hints
  (("Goal"
    :in-theory (disable update-nth
                        update-nth-when-zp))))

(defthm updater/resizable-of-updater/resizable
  (equal (updater/resizable %index %value (updater/resizable index value vector))
         (if (nat-equiv %index index)
             (updater/resizable %index %value vector)
             (updater/resizable index value (updater/resizable %index %value vector))))
  :rule-classes
  ((:rewrite :loop-stopper ((%index index updater/resizable))))
  :hints
  (("Goal"
    :in-theory (disable updater/resizable))))

(local
  (in-theory
    (disable recognizer/resizable
             fixer/resizable
             equiv/resizable
             length/resizable
             resizer/resizable
             accessor/resizable
             updater/resizable)))


;;;; Fixed Definitions
(defun recognizer/fixed (vector)
  (declare (xargs :guard t))
  (and (equal (len vector) (default-length))
       (recognizer-aux vector)))

(defun fixer/fixed (vector)
  (declare (xargs :guard (recognizer/fixed vector)))
  (if (recognizer/fixed vector)
      vector
      (creator)))

(defun equiv/fixed (%vector vector)
  (declare (xargs :guard (and (recognizer/fixed %vector)
                              (recognizer/fixed vector))))
  (equal (fixer/fixed %vector)
         (fixer/fixed vector)))

(defun length/fixed (vector)
  (declare (xargs :guard (recognizer/fixed vector))
           (ignore vector))
  (default-length))

(defun resizer/fixed (length vector)
  (declare (xargs :guard (and (natp length)
                              (recognizer/fixed vector)))
           (ignore length))
  (fixer/fixed vector))

(defun accessor/fixed (index vector)
  (declare (xargs :guard (and (natp index)
                              (recognizer/fixed vector)
                              (< index (default-length)))))
  (let ((index (nfix index))
        (vector (fixer/fixed vector)))
    (if (< index (default-length))
        (element-fixer (nth index vector))
        (initial-element))))

(defun updater/fixed (index value vector)
  (declare (xargs :guard (and (natp index)
                              (element-recognizer value)
                              (recognizer/fixed vector)
                              (< index (default-length)))))
  (let ((index (nfix index))
        (value (element-fixer value))
        (vector (fixer/fixed vector)))
    (if (< index (default-length))
        (update-nth index value vector)
        vector)))


;;;; `RECOGNIZER/FIXED'
(defthm recognizer/fixed-tp
  (booleanp (recognizer/fixed vector))
  :rule-classes :type-prescription)

(defthm recognizer/fixed-cr
  (implies (recognizer/fixed vector)
           (true-listp vector))
  :rule-classes :compound-recognizer)

(defthm recognizer/fixed-of-creator
  (recognizer/fixed (creator)))

(defthm recognizer/fixed-of-fixer/fixed
  (recognizer/fixed (fixer/fixed vector)))

(defthm recognizer/fixed-of-updater/fixed
  (recognizer/fixed (updater/fixed index value vector))
  :hints
  (("Goal"
    :in-theory (disable update-nth
                        update-nth-when-zp))))


;;;; `FIXER/FIXED'
(defthm fixer/fixed-tp
  (true-listp (fixer/fixed vector))
  :rule-classes :type-prescription)

(defthm fixer/fixed-when-recognizer/fixed
  (implies (recognizer/fixed vector)
           (equal (fixer/fixed vector)
                  vector)))

(defthm fixer/fixed-when-not-recognizer/fixed
  (implies (not (recognizer/fixed vector))
           (equal (fixer/fixed vector)
                  (creator))))


;;;; `EQUIV/FIXED'
(defthm equiv/fixed-tp
  (booleanp (equiv/fixed %vector vector))
  :rule-classes :type-prescription)

(defequiv equiv/fixed)

(defcong equiv/fixed equal (fixer/fixed vector) 1)

(defthm fixer/fixed-mod-equiv/fixed
  (equiv/fixed (fixer/fixed vector) vector))

(defthm equiv/fixed-when-not-recognizer/fixed
  (implies (not (recognizer/fixed vector))
           (equiv/fixed vector (creator))))


;;;; `LENGTH/FIXED'
(defthm length/fixed-tp
  (natp (length/fixed vector))
  :rule-classes :type-prescription)

(defthm length/fixed-rw
  (equal (length/fixed vector)
         (default-length)))


;;;; `RESIZER/FIXED'
(defthm resizer/fixed-tp
  (true-listp (resizer/fixed length vector))
  :rule-classes :type-prescription)

(defthm resizer/fixed-rw
  (equal (resizer/fixed length vector)
         (fixer/fixed vector))
  :rule-classes
  ((:rewrite :corollary
             (equal (resizer/fixed length vector)
                    (fixer/fixed (double-rewrite vector))))))


;;;; `ACCESSOR/FIXED'
(defthm element-recognizer-of-accessor/fixed
  (element-recognizer (accessor/fixed index vector)))

(defcong nat-equiv equal (accessor/fixed index vector) 1)

(defcong equiv/fixed equal (accessor/fixed index vector) 2)

(defthm accessor/fixed-when-large
  (implies (<= (default-length) (nfix index))
           (equal (accessor/fixed index vector)
                  (initial-element))))

(defthm accessor/fixed-when-not-natp
  (implies (not (natp index))
           (equal (accessor/fixed index vector)
                  (accessor/fixed 0 vector))))

(defthm accessor/fixed-when-not-recognizer/fixed
  (implies (not (recognizer/fixed vector))
           (equal (accessor/fixed index vector)
                  (initial-element))))

(defthm accessor/fixed-of-creator
  (equal (accessor/fixed index (creator))
         (initial-element)))

(defthm accessor/fixed-of-updater/fixed-same
  (implies (and (nat-equiv %index index)
                (< (nfix %index) (default-length)))
           (equal (accessor/fixed %index (updater/fixed index value vector))
                  (element-fixer value)))
  :rule-classes
  ((:rewrite :corollary
             (implies (and (nat-equiv %index (double-rewrite index))
                           (< (nfix %index) (default-length)))
                      (equal (accessor/fixed %index (updater/fixed index value vector))
                             (element-fixer (double-rewrite value))))))
  :hints
  (("Goal"
    :in-theory (disable nth-when-zp
                        update-nth
                        update-nth-when-zp
                        recognizer-aux))))

(defthm accessor/fixed-of-updater/fixed-diff
  (implies (and (not (nat-equiv %index index))
                (< (nfix %index) (default-length)))
           (equal (accessor/fixed %index (updater/fixed index value vector))
                  (accessor/fixed %index vector)))
  :rule-classes
  ((:rewrite :corollary
             (implies (and (not (nat-equiv %index (double-rewrite index)))
                           (< (nfix %index) (default-length)))
                      (equal (accessor/fixed %index (updater/fixed index value vector))
                             (accessor/fixed %index (double-rewrite vector))))))
  :hints
  (("Goal"
    :in-theory (disable nth-when-zp
                        update-nth
                        update-nth-when-zp
                        recognizer-aux))))

(defthm accessor/fixed-of-updater/fixed
  (equal (accessor/fixed %index (updater/fixed index value vector))
         (cond
           ((<= (default-length) (nfix %index))
            (initial-element))
           ((nat-equiv %index index)
            (element-fixer value))
           (t
            (accessor/fixed %index vector))))
  :rule-classes
  ((:rewrite :corollary
             (equal (accessor/fixed %index (updater/fixed index value vector))
                    (cond
                      ((<= (default-length) (nfix %index))
                       (initial-element))
                      ((nat-equiv %index (double-rewrite index))
                       (element-fixer (double-rewrite value)))
                      (t
                       (accessor/fixed %index (double-rewrite vector)))))))
  :hints
  (("Goal"
    :cases ((and (nat-equiv %index index)
                 (< (nfix %index) (default-length)))
            (and (not (nat-equiv %index index))
                 (< (nfix %index) (default-length))))
    :in-theory (disable nfix
                        accessor/fixed
                        updater/fixed))))


;;;; `UPDATER/FIXED'
(defthm updater/fixed-tp
  (true-listp (updater/fixed index value vector))
  :rule-classes :type-prescription)

(defcong nat-equiv equal (updater/fixed index value vector) 1)

(defcong element-equiv equal (updater/fixed index value vector) 2)

(defcong equiv/fixed equal (updater/fixed index value vector) 3)

(defthm updater/fixed-when-large
  (implies (<= (default-length) (nfix index))
           (equal (updater/fixed index value vector)
                  (fixer/fixed vector))))

(defthm updater/fixed-when-not-natp
  (implies (not (natp index))
           (equal (updater/fixed index value vector)
                  (updater/fixed 0 value vector))))

(defthm updater/fixed-when-not-element-recognizer
  (implies (not (element-recognizer value))
           (equal (updater/fixed index value vector)
                  (updater/fixed index (initial-element) vector))))

(defthm updater/fixed-when-not-recognizer/fixed
  (implies (not (recognizer/fixed vector))
           (equal (updater/fixed index value vector)
                  (updater/fixed index value (creator)))))

(defthm updater/fixed-of-creator
  (implies (element-equiv value (initial-element))
           (equal (updater/fixed index value (creator))
                  (creator))))

(defthm updater/fixed-of-accessor/fixed-free
  (implies (element-equiv value (accessor/fixed index vector))
           (equal (updater/fixed index value vector)
                  (fixer/fixed vector)))
  :hints
  (("Goal"
    :in-theory (disable update-nth
                        update-nth-when-zp))))

(defthm updater/fixed-of-accessor/fixed
  (implies (and (nat-equiv %index index)
                (equiv/fixed %vector vector))
           (equal (updater/fixed %index (accessor/fixed index %vector) vector)
                  (fixer/fixed vector)))
  :hints
  (("Goal"
    :in-theory (disable updater/fixed-of-accessor/fixed-free
                        updater/fixed
                        accessor/fixed
                        fixer/fixed
                        equiv/fixed)
    :use (:instance updater/fixed-of-accessor/fixed-free
                    (index %index)
                    (value (accessor/fixed index vector))))))

(defthm updater/fixed-of-updater/fixed-same
  (implies (nat-equiv %index index)
           (equal (updater/fixed %index %value (updater/fixed index value vector))
                  (updater/fixed %index %value vector)))
  :hints
  (("Goal"
    :in-theory (disable nfix
                        update-nth
                        update-nth-when-zp))))

(defthm updater/fixed-of-updater/fixed-diff
  (implies (not (nat-equiv %index index))
           (equal (updater/fixed %index %value (updater/fixed index value vector))
                  (updater/fixed index value (updater/fixed %index %value vector))))
  :rule-classes
  ((:rewrite :loop-stopper ((%index index updater/fixed))))
  :hints
  (("Goal"
    :in-theory (disable update-nth
                        update-nth-when-zp))))

(defthm updater/fixed-of-updater/fixed
  (equal (updater/fixed %index %value (updater/fixed index value vector))
         (if (nat-equiv %index index)
             (updater/fixed %index %value vector)
             (updater/fixed index value (updater/fixed %index %value vector))))
  :rule-classes
  ((:rewrite :loop-stopper ((%index index updater/fixed))))
  :hints
  (("Goal"
    :in-theory (disable updater/fixed))))

(local
  (in-theory
    (disable recognizer/fixed
             fixer/fixed
             equiv/fixed
             length/fixed
             resizer/fixed
             accessor/fixed
             updater/fixed)))

(local
  (in-theory
    (disable creator
             recognizer-aux)))


;;;; `EQUAL/RESIZABLE-FC'
(defun-sk contents-equal/resizable (%vector vector)
  (declare (xargs :guard (and (recognizer/resizable %vector)
                              (recognizer/resizable vector))
                  :verify-guards nil))
  (forall index
    (equal (accessor/resizable index %vector)
           (accessor/resizable index vector)))
  :rewrite :direct)

(defun-nx equal/resizable (%vector vector)
  (declare (xargs :guard (and (recognizer/resizable %vector)
                              (recognizer/resizable vector))
                  :verify-guards nil))
  (and (recognizer/resizable %vector)
       (recognizer/resizable vector)
       (equal (length/resizable %vector)
              (length/resizable vector))
       (contents-equal/resizable %vector vector)))

(encapsulate ()
  (local
    (in-theory
      (disable contents-equal/resizable)))

  (local
    (defthmd equal/resizable-fc-lemma-2
      (implies (and (recognizer/resizable %vector)
                    (recognizer/resizable vector))
               (iff (equal (len %vector) (len vector))
                    (equal (length/resizable (double-rewrite %vector))
                           (length/resizable (double-rewrite vector)))))
      :hints
      (("Goal"
        :in-theory (enable length/resizable)))))

  (local
    (defthmd equal/resizable-fc-lemma-1
      (implies (and (recognizer/resizable %vector)
                    (recognizer/resizable vector)
                    (equal (length/resizable (double-rewrite %vector))
                           (length/resizable (double-rewrite vector)))
                    (contents-equal/resizable %vector vector)
                    (natp n)
                    (< n (len %vector)))
               (equal (nth n %vector)
                      (nth n (double-rewrite vector))))
      :rule-classes
      ((:rewrite :match-free :all))
      :hints
      (("Goal"
        :in-theory (enable length/resizable
                           accessor/resizable
                           element-fixer)
        :use ((:instance contents-equal/resizable-necc
                         (index n)))))))

  (defthm equal/resizable-fc
    (implies (equal/resizable %vector vector)
             (equal %vector vector))
    :rule-classes
    ((:forward-chaining :trigger-terms
                        ((equal/resizable %vector vector))
                        :corollary
                        (implies t
                                 (implies (equal/resizable %vector vector)
                                          (equal %vector vector)))))
    :hints
    ((equal-by-nths-hint)
     ("Goal"
      :do-not-induct t)
     ("Subgoal 2"
      :use equal/resizable-fc-lemma-2)
     ("Subgoal 1"
      :use equal/resizable-fc-lemma-1))))

(local
  (in-theory
    (disable equal/resizable)))


;;;; `EQUAL/FIXED-FC'
(defun-sk contents-equal/fixed (%vector vector)
  (declare (xargs :guard (and (recognizer/fixed %vector)
                              (recognizer/fixed vector))
                  :verify-guards nil))
  (forall index
    (equal (accessor/fixed index %vector)
           (accessor/fixed index vector)))
  :rewrite :direct)

(defun-nx equal/fixed (%vector vector)
  (declare (xargs :guard (and (recognizer/fixed %vector)
                              (recognizer/fixed vector))
                  :verify-guards nil))
  (and (recognizer/fixed %vector)
       (recognizer/fixed vector)
       (contents-equal/fixed %vector vector)))

(encapsulate ()
  (local
    (in-theory
      (disable contents-equal/fixed)))

  (local
    (defthm equal/fixed-fc-lemma-2
      (implies (recognizer/fixed vector)
               (equal (len vector)
                      (default-length)))
      :hints
      (("Goal"
        :expand (recognizer/fixed vector)))))

  (local
    (defthmd equal/fixed-fc-lemma-1
      (implies (and (recognizer/fixed %vector)
                    (recognizer/fixed vector)
                    (contents-equal/fixed %vector vector)
                    (natp n)
                    (< n (len %vector)))
               (equal (nth n %vector)
                      (nth n (double-rewrite vector))))
      :rule-classes
      ((:rewrite :match-free :all))
      :hints
      (("Goal"
        :in-theory (e/d (accessor/fixed
                         recognizer/fixed)
                        (contents-equal/fixed-necc))
        :use ((:instance contents-equal/fixed-necc
                         (index n)))))))

  (defthm equal/fixed-fc
    (implies (equal/fixed %vector vector)
             (equal %vector vector))
    :rule-classes
    ((:forward-chaining :trigger-terms
                        ((equal/fixed %vector vector))
                        :corollary
                        (implies t
                                 (implies (equal/fixed %vector vector)
                                          (equal %vector vector)))))
    :hints
    ((equal-by-nths-hint)
     ("Goal"
      :do-not-induct t)
     ("Subgoal 1"
      :use equal/fixed-fc-lemma-1))))

(local
  (in-theory
    (disable equal/fixed)))


;;;; Element Copy
(encapsulate (((element-coupledp *) => *))
  (local
    (defun element-coupledp (value)
      (declare (xargs :guard t)
               (ignore value))
      t))

  (defthm element-coupledp-tp
    (booleanp (element-coupledp value))
    :rule-classes :type-prescription)

  (defthm element-coupledp-when-not-element-recognizer
    (implies (not (element-recognizer value))
             (element-coupledp value)))

  (defthm element-coupledp-of-initial-element
    (element-coupledp (initial-element))))

(local
  (defcong element-equiv equal (element-coupledp value) 1
    :hints
    (("Goal"
      :in-theory (enable element-fixer)))))

(encapsulate (((element-copy * *) => *))
  (local
    (defun element-copy (%value value)
      (declare (xargs :guard (and (element-recognizer %value)
                                  (element-recognizer value)))
               (ignore %value))
      (if (element-coupledp value)
          (element-fixer value)
          (initial-element))))

  (defthm element-recognizer-of-element-copy
    (element-recognizer (element-copy %value value)))

  (defthm element-coupledp-of-element-copy
    (element-coupledp (element-copy %value value)))

  (defthm element-copy-ignores-1
    (equal (element-copy %value value)
           (element-copy (initial-element) value))
    :rule-classes
    ((:rewrite :corollary
               (implies (syntaxp (not (and (consp %value)
                                           (eq (car %value) 'initial-element))))
                        (equal (element-copy %value value)
                               (element-copy (initial-element) value))))))

  (defthm element-copy-rw
    (implies (element-coupledp value)
             (equal (element-copy %value value)
                    (element-fixer value)))
    :rule-classes
    ((:rewrite :corollary
               (implies (element-coupledp (double-rewrite value))
                        (equal (element-copy %value value)
                               (element-fixer (double-rewrite value))))))))

(local
  (defcong element-equiv equal (element-copy %value value) 2
    :hints
    (("Goal"
      :in-theory (enable element-fixer)))))


;;;; `COUPLEDP/RESIZABLE'
(defun-sk coupledp/resizable (vector)
  (declare (xargs :guard (recognizer/resizable vector)
                  :verify-guards nil))
  (forall index
    (element-coupledp (accessor/resizable index vector)))
  :rewrite :direct)

(defthm coupledp/resizable-tp
  (booleanp (coupledp/resizable vector))
  :rule-classes :type-prescription)

(defthm coupledp/resizable-when-not-recognizer/resizable
  (implies (not (recognizer/resizable vector))
           (coupledp/resizable vector)))

(defthm coupledp/resizable-of-creator
  (coupledp/resizable (creator)))

(local
  (in-theory
    (disable coupledp/resizable)))

(defcong equiv/resizable equal (coupledp/resizable vector) 1
  :hints
  (("Goal"
    :in-theory (enable fixer/resizable
                       equiv/resizable))))

(defthm coupledp/resizable-of-resizer/resizable
  (implies (coupledp/resizable vector)
           (coupledp/resizable (resizer/resizable length vector)))
  :hints
  (("Goal"
    :expand (coupledp/resizable (resizer/resizable length vector)))))

(defthm element-coupledp-of-accessor/resizable
  (implies (coupledp/resizable vector)
           (element-coupledp (accessor/resizable index vector))))

(defthm coupledp/resizable-of-updater/resizable
  (implies (coupledp/resizable vector)
           (equal (coupledp/resizable (updater/resizable index value vector))
                  (if (< (nfix index) (length/resizable vector))
                      (element-coupledp value)
                      t)))
  :hints
  (("Goal"
    :cases ((< (nfix index) (length/resizable vector)))
    :in-theory (disable coupledp/resizable-necc))
   ("Subgoal 1.3"
    :use ((:instance coupledp/resizable-necc
                     (index 0)
                     (vector (updater/resizable 0 value vector))))
    :expand (:free (index)
                   (coupledp/resizable (updater/resizable index value vector))))
   ("Subgoal 1.2"
    :use ((:instance coupledp/resizable-necc
                     (vector (updater/resizable index value vector))))
    :expand (:free (index)
                   (coupledp/resizable (updater/resizable index value vector))))
   ("Subgoal 1.1"
    :use ((:instance coupledp/resizable-necc
                     (index 0)
                     (vector (updater/resizable 0 value vector))))
    :expand (:free (index)
                   (coupledp/resizable (updater/resizable index value vector))))))


;;;; `COPY/RESIZABLE-REC'
(defun copy/resizable-rec (index %vector vector)
  (declare (xargs :guard (and (natp index)
                              (recognizer/resizable %vector)
                              (recognizer/resizable vector)
                              (equal (length/resizable %vector)
                                     (length/resizable vector))
                              (<= index (length/resizable vector)))))
  (if (zp index)
      (fixer/resizable %vector)
      (let* ((index (1- index))
             (value (accessor/resizable index vector))
             (%value (accessor/resizable index %vector))
             (%value (element-copy %value value))
             (%vector (updater/resizable index %value %vector))
             (vector (updater/resizable index value vector)))
        (copy/resizable-rec index %vector vector))))

(local
  (defthm recognizer/resizable-of-copy/resizable-rec
    (recognizer/resizable (copy/resizable-rec index %vector vector))))

(local
  (defcong nat-equiv equal (copy/resizable-rec index %vector vector) 1))

(local
  (defcong equiv/resizable equal (copy/resizable-rec index %vector vector) 2))

(local
  (defcong equiv/resizable equal (copy/resizable-rec index %vector vector) 3))

(local
  (defthm length/resizable-of-copy/resizable-rec
    (equal (length/resizable (copy/resizable-rec index %vector vector))
           (length/resizable %vector))
    :rule-classes
    ((:rewrite :corollary
               (equal (length/resizable (copy/resizable-rec index %vector vector))
                      (length/resizable (double-rewrite %vector)))))))

(local
  (defthm accessor/resizable-of-copy/resizable-rec
    (equal (accessor/resizable %index (copy/resizable-rec index %vector vector))
           (cond
             ((<= (length/resizable %vector) (nfix %index))
              (initial-element))
             ((< (nfix %index) (nfix index))
              (element-copy (accessor/resizable %index %vector)
                            (accessor/resizable %index vector)))
             (t
              (accessor/resizable %index %vector))))
    :rule-classes
    ((:rewrite :corollary
               (equal (accessor/resizable %index (copy/resizable-rec index %vector vector))
                      (cond
                        ((<= (length/resizable (double-rewrite %vector)) (nfix %index))
                         (initial-element))
                        ((< (nfix %index) (nfix index))
                         (element-copy (accessor/resizable %index (double-rewrite %vector))
                                       (accessor/resizable %index (double-rewrite vector))))
                        (t
                         (accessor/resizable %index (double-rewrite %vector)))))))
    :hints
    (("Goal"
      :cases ((<= (length/resizable %vector) (nfix %index))
              (< (nfix %index) (nfix index)))))))

(local
  (in-theory
    (disable copy/resizable-rec)))


;;;; `COPY/RESIZABLE'
(defun copy/resizable (%vector vector)
  (declare (xargs :guard (and (recognizer/resizable %vector)
                              (recognizer/resizable vector))))
  (let* ((length (length/resizable vector))
         (%vector (if (equal (length/resizable %vector) length)
                      %vector
                      (resizer/resizable length %vector))))
    (copy/resizable-rec length %vector vector)))

(defthm recognizer/resizable-of-copy/resizable
  (recognizer/resizable (copy/resizable %vector vector)))

(defthm copy/resizable-ignores-1
  (equal (copy/resizable %vector vector)
         (copy/resizable (creator) vector))
  :rule-classes
  ((:rewrite :corollary
             (implies (syntaxp (not (and (consp %vector)
                                         (eq (car %vector) 'creator))))
                      (equal (copy/resizable %vector vector)
                             (copy/resizable (creator) vector)))))
  :hints
  (("Goal"
    :use ((:instance equal/resizable
                     (%vector (copy/resizable %vector vector))
                     (vector (copy/resizable (creator) vector)))))))

(defcong equiv/resizable equal (copy/resizable %vector vector) 2
  :hints
  (("Goal"
    :use ((:instance equal/resizable
                     (%vector (copy/resizable %vector vector))
                     (vector (copy/resizable %vector vector-equiv)))))))

(defthm coupledp/resizable-of-copy/resizable
  (coupledp/resizable (copy/resizable %vector vector))
  :hints
  (("Subgoal 2"
    :expand (coupledp/resizable (copy/resizable-rec (default-length)
                                                    (creator) vector)))
   ("Subgoal 1"
    :expand (coupledp/resizable (copy/resizable-rec (length/resizable vector)
                                                    (resizer/resizable (length/resizable vector)
                                                                       (creator))
                                                    vector)))))

(defthm length/resizable-of-copy/resizable
  (equal (length/resizable (copy/resizable %vector vector))
         (length/resizable vector)))

(defthm copy/resizable-of-resizer/resizable
  (equal (copy/resizable %vector (resizer/resizable length vector))
         (resizer/resizable length (copy/resizable %vector vector)))
  :hints
  (("Goal"
    :use ((:instance equal/resizable
                     (%vector (copy/resizable %vector (resizer/resizable length vector)))
                     (vector (resizer/resizable length (copy/resizable %vector vector))))))))

(defthm accessor/resizable-of-copy/resizable
  (equal (accessor/resizable index (copy/resizable %vector vector))
         (element-copy (initial-element) (accessor/resizable index vector)))
  :hints
  (("Goal"
    :cases ((< (nfix index) (length/resizable vector))))))

(defthm copy/resizable-of-updater/resizable
  (equal (copy/resizable %vector (updater/resizable index element vector))
         (if (< (nfix index) (length/resizable vector))
             (updater/resizable index
                                (element-copy (initial-element) element)
                                (copy/resizable %vector vector))
             (copy/resizable %vector vector)))
  :hints
  (("Goal"
    :use ((:instance equal/resizable
                     (%vector (copy/resizable %vector (updater/resizable index element vector)))
                     (vector (if (< (nfix index) (length/resizable vector))
                                 (updater/resizable index
                                                    (element-copy (initial-element) element)
                                                    (copy/resizable %vector vector))
                                 (copy/resizable %vector vector))))))))

(local
  (in-theory
    (disable copy/resizable)))

(defthm copy/resizable-rw
  (implies (coupledp/resizable vector)
           (equal (copy/resizable %vector vector)
                  (fixer/resizable vector)))
  :hints
  (("Goal"
    :use ((:instance equal/resizable
                     (%vector (copy/resizable %vector vector))
                     (vector (fixer/resizable vector)))))))


;;;; `COUPLEDP/FIXED'
(defun-sk coupledp/fixed (vector)
  (declare (xargs :guard (recognizer/fixed vector)
                  :verify-guards nil))
  (forall index
    (element-coupledp (accessor/fixed index vector)))
  :rewrite :direct)

(defthm coupledp/fixed-tp
  (booleanp (coupledp/fixed vector))
  :rule-classes :type-prescription)

(defthm coupledp/fixed-when-not-recognizer/fixed
  (implies (not (recognizer/fixed vector))
           (coupledp/fixed vector)))

(defthm coupledp/fixed-of-creator
  (coupledp/fixed (creator)))

(local
  (in-theory
    (disable coupledp/fixed)))

(defcong equiv/fixed equal (coupledp/fixed vector) 1
  :hints
  (("Goal"
    :in-theory (enable fixer/fixed
                       equiv/fixed))))

(defthm element-coupledp-of-accessor/fixed
  (implies (coupledp/fixed vector)
           (element-coupledp (accessor/fixed index vector))))

(defthm coupledp/fixed-of-updater/fixed
  (implies (coupledp/fixed vector)
           (equal (coupledp/fixed (updater/fixed index value vector))
                  (if (< (nfix index) (default-length))
                      (element-coupledp value)
                      t)))
  :hints
  (("Goal"
    :cases ((< (nfix index) (default-length)))
    :in-theory (disable coupledp/fixed-necc))
   ("Subgoal 1.3"
    :use ((:instance coupledp/fixed-necc
                     (index 0)
                     (vector (updater/fixed 0 value vector))))
    :expand (:free (index)
                   (coupledp/fixed (updater/fixed index value vector))))
   ("Subgoal 1.2"
    :use ((:instance coupledp/fixed-necc
                     (vector (updater/fixed index value vector))))
    :expand (:free (index)
                   (coupledp/fixed (updater/fixed index value vector))))
   ("Subgoal 1.1"
    :use ((:instance coupledp/fixed-necc
                     (index 0)
                     (vector (updater/fixed 0 value vector))))
    :expand (:free (index)
                   (coupledp/fixed (updater/fixed index value vector))))))


;;;; `COPY/FIXED-REC'
(defun copy/fixed-rec (index %vector vector)
  (declare (xargs :guard (and (natp index)
                              (recognizer/fixed %vector)
                              (recognizer/fixed vector)
                              (<= index (default-length)))))
  (if (zp index)
      (fixer/fixed %vector)
      (let* ((index (1- index))
             (value (accessor/fixed index vector))
             (%value (accessor/fixed index %vector))
             (%value (element-copy %value value))
             (%vector (updater/fixed index %value %vector))
             (vector (updater/fixed index value vector)))
        (copy/fixed-rec index %vector vector))))

(local
  (defthm recognizer/fixed-of-copy/fixed-rec
    (recognizer/fixed (copy/fixed-rec index %vector vector))))

(local
  (defcong nat-equiv equal (copy/fixed-rec index %vector vector) 1))

(local
  (defcong equiv/fixed equal (copy/fixed-rec index %vector vector) 2))

(local
  (defcong equiv/fixed equal (copy/fixed-rec index %vector vector) 3))

(local
  (defthm accessor/fixed-of-copy/fixed-rec
    (equal (accessor/fixed %index (copy/fixed-rec index %vector vector))
           (cond
             ((<= (default-length) (nfix %index))
              (initial-element))
             ((< (nfix %index) (nfix index))
              (element-copy (accessor/fixed %index %vector)
                            (accessor/fixed %index vector)))
             (t
              (accessor/fixed %index %vector))))
    :rule-classes
    ((:rewrite :corollary
               (equal (accessor/fixed %index (copy/fixed-rec index %vector vector))
                      (cond
                        ((<= (default-length) (nfix %index))
                         (initial-element))
                        ((< (nfix %index) (nfix index))
                         (element-copy (accessor/fixed %index (double-rewrite %vector))
                                       (accessor/fixed %index (double-rewrite vector))))
                        (t
                         (accessor/fixed %index (double-rewrite %vector)))))))
    :hints
    (("Goal"
      :cases ((<= (default-length) (nfix %index))
              (< (nfix %index) (nfix index)))))))

(local
  (in-theory
    (disable copy/fixed-rec)))


;;;; `COPY/FIXED'
(defun copy/fixed (%vector vector)
  (declare (xargs :guard (and (recognizer/fixed %vector)
                              (recognizer/fixed vector))))
  (copy/fixed-rec (default-length) %vector vector))

(defthm recognizer/fixed-of-copy/fixed
  (recognizer/fixed (copy/fixed %vector vector)))

(defthm copy/fixed-ignores-1
  (equal (copy/fixed %vector vector)
         (copy/fixed (creator) vector))
  :rule-classes
  ((:rewrite :corollary
             (implies (syntaxp (not (and (consp %vector)
                                         (eq (car %vector) 'creator))))
                      (equal (copy/fixed %vector vector)
                             (copy/fixed (creator) vector)))))
  :hints
  (("Goal"
    :use ((:instance equal/fixed
                     (%vector (copy/fixed %vector vector))
                     (vector (copy/fixed (creator) vector)))))))

(defcong equiv/fixed equal (copy/fixed %vector vector) 2
  :hints
  (("Goal"
    :use ((:instance equal/fixed
                     (%vector (copy/fixed %vector vector))
                     (vector (copy/fixed %vector vector-equiv)))))))

(defthm coupledp/fixed-of-copy/fixed
  (coupledp/fixed (copy/fixed %vector vector))
  :hints
  (("Goal"
    :expand (coupledp/fixed (copy/fixed-rec (default-length)
                                            %vector vector)))))

(defthm accessor/fixed-of-copy/fixed
  (equal (accessor/fixed index (copy/fixed %vector vector))
         (element-copy (initial-element) (accessor/fixed index vector)))
  :hints
  (("Goal"
    :cases ((< (nfix index) (default-length))))))

(defthm copy/fixed-of-updater/fixed
  (equal (copy/fixed %vector (updater/fixed index element vector))
         (if (< (nfix index) (default-length))
             (updater/fixed index
                            (element-copy (initial-element) element)
                            (copy/fixed %vector vector))
             (copy/fixed %vector vector)))
  :hints
  (("Goal"
    :use ((:instance equal/fixed
                     (%vector (copy/fixed %vector (updater/fixed index element vector)))
                     (vector (if (< (nfix index) (default-length))
                                 (updater/fixed index
                                                (element-copy (initial-element) element)
                                                (copy/fixed %vector vector))
                                 (copy/fixed %vector vector))))))))

(local
  (in-theory
    (disable copy/fixed)))

(defthm copy/fixed-rw
  (implies (coupledp/fixed vector)
           (equal (copy/fixed %vector vector)
                  (fixer/fixed vector)))
  :hints
  (("Goal"
    :use ((:instance equal/fixed
                     (%vector (copy/fixed %vector vector))
                     (vector (fixer/fixed vector)))))))


;;;; Element Export
(encapsulate (((name) => *)
              ((element-export-p *) => *)
              ((element-export *) => *)
              ((element-import * *) => *))
  (local
    (defun name ()
      (declare (xargs :guard t))
      nil))

  (defthm name-tp
    (symbolp (name))
    :rule-classes :type-prescription)

  (local
    (defun element-export-p (export)
      (declare (xargs :guard t))
      (and (element-recognizer export)
           (element-coupledp export))))

  (defthm element-export-p-tp
    (booleanp (element-export-p export))
    :rule-classes :type-prescription)

  (local
    (defun element-export (value)
      (declare (xargs :guard (element-recognizer value)))
      (if (element-coupledp value)
          (element-fixer value)
          (initial-element))))

  (defthm element-export-p-of-element-export
    (element-export-p (element-export value)))

  (defcong element-equiv equal (element-export value) 1
    :hints
    (("Goal"
      :in-theory (disable element-equiv))))

  (local
    (defun element-import (export value)
      (declare (xargs :guard (and (element-export-p export)
                                  (element-recognizer value)))
               (ignore value))
      (if (element-coupledp export)
          (element-fixer export)
          (initial-element))))

  (defthm element-recognizer-of-element-import
    (element-recognizer (element-import export value)))

  (defthm element-coupledp-of-element-import
    (element-coupledp (element-import export value)))

  (defthm element-import-when-not-element-export-p
    (implies (not (element-export-p export))
             (equal (element-import export value)
                    (initial-element))))

  (defthm element-import-ignores-2
    (equal (element-import export value)
           (element-import export (initial-element)))
    :rule-classes
    ((:rewrite :corollary
               (implies (syntaxp (not (and (consp value)
                                           (eq (car value) 'initial-element))))
                        (equal (element-import export value)
                               (element-import export (initial-element)))))))

  (defthm element-export-of-element-import
    (implies (element-export-p export)
             (equal (element-export (element-import export value))
                    export)))

  (defthm element-import-of-element-export
    (implies (element-coupledp %value)
             (equal (element-import (element-export %value) value)
                    (element-fixer %value)))))


;;;; `EXPORTP-REC'
(defun exportp-rec (list)
  (declare (xargs :guard t))
  (if (consp list)
      (and (element-export-p (car list))
           (exportp-rec (cdr list)))
      (null list)))

(local
  (defthm exportp-rec-tp
    (booleanp (exportp-rec list))
    :rule-classes :type-prescription))

(local
  (defthm exportp-rec-cr
    (implies (exportp-rec list)
             (true-listp list))
    :rule-classes :compound-recognizer))

(local
  (defthm element-export-p-of-nth-when-exportp-rec
    (implies (and (exportp-rec list)
                  (natp n)
                  (< n (len list)))
             (element-export-p (nth n list)))))

(local
  (defthm exportp-rec-of-cons
    (equal (exportp-rec (cons value list))
           (and (element-export-p value)
                (exportp-rec list)))))

(local
  (in-theory
    (disable exportp-rec)))


;;;; `EXPORTP/RESIZABLE'
(defun exportp/resizable (export)
  (declare (xargs :guard t))
  (and (consp export)
       (equal (car export) (name))
       (exportp-rec (cdr export))))

(defthm exportp/resizable-tp
  (booleanp (exportp/resizable export))
  :rule-classes :type-prescription)

(defthm exportp/resizable-cr
  (implies (exportp/resizable export)
           (and (consp export)
                (true-listp export)))
  :rule-classes :compound-recognizer)

(local
  (defthm element-export-p-of-nth-when-exportp/resizable
    (implies (and (exportp/resizable export)
                  (posp n)
                  (< n (len export)))
             (element-export-p (nth n export)))))

(local
  (in-theory
    (disable exportp/resizable)))


;;;; `EXPORT-ACC/RESIZABLE'
(defun export-acc/resizable (index acc vector)
  (declare (xargs :guard (and (natp index)
                              (exportp-rec acc)
                              (recognizer/resizable vector)
                              (<= index (length/resizable vector)))))
  (if (zp index)
      (true-list-fix acc)
      (let* ((index (1- index))
             (value (accessor/resizable index vector))
             (export (element-export value)))
        (export-acc/resizable index (cons export acc) vector))))

(local
  (defthm export-acc/resizable-tp
    (true-listp (export-acc/resizable index acc vector))
    :rule-classes :type-prescription))

(local
  (defthm exportp-rec-of-export-acc/resizable
    (equal (exportp-rec (export-acc/resizable index acc vector))
           (exportp-rec (true-list-fix acc)))
    :rule-classes
    ((:rewrite :corollary
               (equal (exportp-rec (export-acc/resizable index acc vector))
                      (exportp-rec (true-list-fix (double-rewrite acc))))))))

(local
  (defcong nat-equiv equal (export-acc/resizable index acc vector) 1))

(local
  (defcong equiv/resizable equal (export-acc/resizable index acc vector) 3))

(local
  (defthm export-acc/resizable-when-not-recognizer/resizable
    (implies (not (recognizer/resizable vector))
             (equal (export-acc/resizable index acc vector)
                    (export-acc/resizable index acc (creator))))
    :rule-classes
    ((:rewrite :corollary
               (implies (and (syntaxp (not (and (consp vector)
                                                (eq (car vector) 'creator))))
                             (not (recognizer/resizable vector)))
                        (equal (export-acc/resizable index acc vector)
                               (export-acc/resizable index acc (creator))))))))

(local
  (defthm len-of-export-acc/resizable
    (equal (len (export-acc/resizable index acc vector))
           (+ (nfix index) (len acc)))
    :rule-classes
    ((:rewrite :corollary
               (equal (len (export-acc/resizable index acc vector))
                      (+ (nfix index) (len (double-rewrite acc))))))))

(local
  (defthm nth-of-export-acc/resizable
    (equal (nth %index (export-acc/resizable index acc vector))
           (if (< (nfix %index) (nfix index))
               (element-export (accessor/resizable %index vector))
               (nth (- (nfix %index) (nfix index)) acc)))
    :rule-classes
    ((:rewrite :corollary
               (equal (nth %index (export-acc/resizable index acc vector))
                      (if (< (nfix (double-rewrite %index)) (nfix index))
                          (element-export (accessor/resizable (double-rewrite %index) vector))
                          (nth (- (nfix (double-rewrite %index)) (nfix index)) (double-rewrite acc))))))))

(local
  (in-theory
    (disable export-acc/resizable)))


;;;; `EXPORT/RESIZABLE'
(defun export/resizable (vector)
  (declare (xargs :guard (recognizer/resizable vector)))
  (cons (name)
        (export-acc/resizable (length/resizable vector) () vector)))

(defthm export/resizable-tp
  (and (consp (export/resizable vector))
       (true-listp (export/resizable vector)))
  :rule-classes :type-prescription)

(defthm exportp/resizable-of-export/resizable
  (exportp/resizable (export/resizable vector))
  :hints
  (("Goal"
    :in-theory (enable exportp/resizable))))

(local
  (defcong equiv/resizable equal (export/resizable vector) 1))

(defthm export/resizable-when-not-recognizer/resizable
  (implies (not (recognizer/resizable vector))
           (equal (export/resizable vector)
                  (export/resizable (creator))))
  :rule-classes
  ((:rewrite :corollary
             (implies (and (syntaxp (not (and (consp vector)
                                              (eq (car vector) 'creator))))
                           (not (recognizer/resizable vector)))
                      (equal (export/resizable vector)
                             (export/resizable (creator)))))))

(local
  (defthm len-of-export/resizable
    (equal (len (export/resizable vector))
           (1+ (length/resizable vector)))))

(local
  (defthm nth-of-export/resizable
    (equal (nth index (export/resizable vector))
           (cond
             ((zp index)
              (name))
             ((<= index (length/resizable vector))
              (element-export (accessor/resizable (1- index) vector)))))
    :rule-classes
    ((:rewrite :corollary
               (equal (nth index (export/resizable vector))
                      (cond
                        ((zp (double-rewrite index))
                         (name))
                        ((<= index (length/resizable vector))
                         (element-export (accessor/resizable (1- index) vector)))))))))

(local
  (in-theory
    (disable export/resizable)))


;;;; `IMPORT-REC/RESIZABLE'
(defun import-rec/resizable (list index vector)
  (declare (xargs :guard (and (exportp-rec list)
                              (natp index)
                              (recognizer/resizable vector)
                              (<= (+ (len list) index) (length/resizable vector)))))
  (if (consp list)
      (let* ((index (nfix index))
             (value (accessor/resizable index vector))
             (value (element-import (car list) value))
             (vector (updater/resizable index value vector)))
        (import-rec/resizable (cdr list) (1+ index) vector))
      (fixer/resizable vector)))

(local
  (defthm import-rec/resizable-tp
    (true-listp (import-rec/resizable list index vector))
    :rule-classes :type-prescription))

(local
  (defthm recognizer/resizable-of-import-rec/resizable
    (recognizer/resizable (import-rec/resizable list index vector))))

(local
  (defthm length/resizable-of-import-rec/resizable
    (equal (length/resizable (import-rec/resizable list index vector))
           (length/resizable vector))
    :rule-classes
    ((:rewrite :corollary
               (equal (length/resizable (import-rec/resizable list index vector))
                      (length/resizable (double-rewrite vector)))))))

(local
  (defthm import-rec/resizable-of-updater/resizable
    (equal (import-rec/resizable list %index (updater/resizable index value vector))
           (if (or (atom list)
                   (< (nfix index) (nfix %index))
                   (<= (+ (len list) (nfix %index)) (nfix index)))
               (updater/resizable index value (import-rec/resizable list %index vector))
               (import-rec/resizable list %index vector)))
    :rule-classes
    ((:rewrite :corollary
               (equal (import-rec/resizable list %index (updater/resizable index value vector))
                      (if (or (atom (double-rewrite list))
                              (< (nfix index) (nfix (double-rewrite %index)))
                              (<= (+ (len (double-rewrite list)) (nfix (double-rewrite %index))) (nfix index)))
                          (updater/resizable index value (import-rec/resizable list %index vector))
                          (import-rec/resizable list %index vector)))))))

(local
  (defthm accessor/resizable-of-import-rec/resizable
    (equal (accessor/resizable %index (import-rec/resizable list index vector))
           (cond
             ((atom list)
              (accessor/resizable %index vector))
             ((<= (length/resizable vector) (nfix %index))
              (initial-element))
             ((or (< (nfix %index) (nfix index))
                  (<= (+ (len list) (nfix index)) (nfix %index)))
              (accessor/resizable %index vector))
             (t
              (element-import (nth (- (nfix %index) (nfix index)) list)
                              (initial-element)))))
    :rule-classes
    ((:rewrite :corollary
               (equal (accessor/resizable %index (import-rec/resizable list index vector))
                      (cond
                        ((atom (double-rewrite list))
                         (accessor/resizable %index (double-rewrite vector)))
                        ((<= (length/resizable (double-rewrite vector)) (nfix %index))
                         (initial-element))
                        ((or (< (nfix %index) (nfix (double-rewrite index)))
                             (<= (+ (len (double-rewrite list)) (nfix (double-rewrite index))) (nfix %index)))
                         (accessor/resizable %index (double-rewrite vector)))
                        (t
                         (element-import (nth (- (nfix %index) (nfix (double-rewrite index))) (double-rewrite list))
                                         (initial-element)))))))))

(local
  (defcong list-equiv equal (import-rec/resizable list index vector) 1
    :hints
    (("Goal"
      :use ((:instance equal/resizable
                       (%vector (import-rec/resizable list index vector))
                       (vector (import-rec/resizable list-equiv index vector))))))))

(local
  (defcong nat-equiv equal (import-rec/resizable list index vector) 2
    :hints
    (("Goal"
      :use ((:instance equal/resizable
                       (%vector (import-rec/resizable list index vector))
                       (vector (import-rec/resizable list index-equiv vector))))))))

(local
  (defcong equiv/resizable equal (import-rec/resizable list index vector) 3
    :hints
    (("Goal"
      :use ((:instance equal/resizable
                       (%vector (import-rec/resizable list index vector))
                       (vector (import-rec/resizable list index vector-equiv))))))))

(local
  (in-theory
    (disable import-rec/resizable)))


;;;; `IMPORT/RESIZABLE'
(defun import/resizable (export vector)
  (declare (xargs :guard (and (exportp/resizable export)
                              (recognizer/resizable vector))
                  :guard-hints
                  (("Goal"
                    :in-theory (enable exportp/resizable)))))
  (if (exportp/resizable export)
      (let* ((list (cdr export))
             (vector (resizer/resizable (len list) vector))
             (vector (import-rec/resizable list 0 vector)))
        vector)
      (creator)))

(defthm import/resizable-tp
  (true-listp (import/resizable export vector))
  :rule-classes :type-prescription)

(defthm recognizer/resizable-of-import/resizable
  (recognizer/resizable (import/resizable export vector)))

(defthm coupledp/resizable-of-import/resizable
  (coupledp/resizable (import/resizable export vector))
  :hints
  (("Goal"
    :in-theory (enable coupledp/resizable
                       exportp/resizable))))

(defthm import/resizable-when-not-exportp/resizable
  (implies (not (exportp/resizable export))
           (equal (import/resizable export vector)
                  (creator))))

(defthm import/resizable-ignores-2
  (equal (import/resizable export vector)
         (import/resizable export (creator)))
  :rule-classes
  ((:rewrite :corollary
             (implies (syntaxp (not (and (consp vector)
                                         (eq (car vector) 'creator))))
                      (equal (import/resizable export vector)
                             (import/resizable export (creator))))))
  :hints
  (("Goal"
    :use ((:instance equal/resizable
                     (%vector (import/resizable export vector))
                     (vector (import/resizable export (creator))))))))

(defthm length/resizable-of-import/resizable
  (equal (length/resizable (import/resizable export vector))
         (if (exportp/resizable export)
             (1- (len export))
             (default-length)))
  :rule-classes
  ((:rewrite :corollary
             (equal (length/resizable (import/resizable export vector))
                    (if (exportp/resizable export)
                        (1- (len (double-rewrite export)))
                        (default-length))))))

(defthm accessor/resizable-of-import/resizable
  (equal (accessor/resizable index (import/resizable export vector))
         (if (and (exportp/resizable export)
                  (< (1+ (nfix index)) (len export)))
             (element-import (nth (1+ (nfix index)) export)
                             (initial-element))
             (initial-element)))
  :rule-classes
  ((:rewrite :corollary
             (equal (accessor/resizable index (import/resizable export vector))
                    (if (and (exportp/resizable export)
                             (< (1+ (nfix index)) (len (double-rewrite export))))
                        (element-import (nth (1+ (nfix index)) (double-rewrite export))
                                        (initial-element))
                        (initial-element))))))

(local
  (in-theory
    (disable import/resizable)))


;;;; `EXPORT/RESIZABLE' and `IMPORT/RESIZABLE' Composition Theorems
(defthm export/resizable-of-import/resizable
  (implies (exportp/resizable export)
           (equal (export/resizable (import/resizable export vector))
                  export))
  :hints
  ((equal-by-nths-hint)
   ("Goal"
    :in-theory (enable exportp/resizable))))

(defthm import/resizable-of-export/resizable
  (implies (coupledp/resizable %vector)
           (equal (import/resizable (export/resizable %vector) vector)
                  (fixer/resizable %vector)))
  :hints
  (("Goal"
    :use ((:instance equal/resizable
                     (%vector (import/resizable (export/resizable %vector) (creator)))
                     (vector (fixer/resizable %vector)))))))


;;;; `EXPORTP/FIXED'
(defun exportp/fixed (export)
  (declare (xargs :guard t))
  (and (consp export)
       (equal (car export) (name))
       (exportp-rec (cdr export))
       (equal (len (cdr export)) (default-length))))

(defthm exportp/fixed-tp
  (booleanp (exportp/fixed export))
  :rule-classes :type-prescription)

(defthm exportp/fixed-cr
  (implies (exportp/fixed export)
           (and (consp export)
                (true-listp export)))
  :rule-classes :compound-recognizer)

(local
  (defthm len-when-exportp/fixed
    (implies (exportp/fixed export)
             (equal (len export)
                    (1+ (default-length))))))

(local
  (defthm element-export-p-of-nth-when-exportp/fixed
    (implies (and (exportp/fixed export)
                  (posp n)
                  (<= n (default-length)))
             (element-export-p (nth n export)))))

(local
  (in-theory
    (disable exportp/fixed)))


;;;; `EXPORT-ACC/FIXED'
(defun export-acc/fixed (index acc vector)
  (declare (xargs :guard (and (natp index)
                              (exportp-rec acc)
                              (recognizer/fixed vector)
                              (<= index (default-length)))))
  (if (zp index)
      (true-list-fix acc)
      (let* ((index (1- index))
             (value (accessor/fixed index vector))
             (export (element-export value)))
        (export-acc/fixed index (cons export acc) vector))))

(local
  (defthm export-acc/fixed-tp
    (true-listp (export-acc/fixed index acc vector))
    :rule-classes :type-prescription))

(local
  (defthm exportp-rec-of-export-acc/fixed
    (equal (exportp-rec (export-acc/fixed index acc vector))
           (exportp-rec (true-list-fix acc)))
    :rule-classes
    ((:rewrite :corollary
               (equal (exportp-rec (export-acc/fixed index acc vector))
                      (exportp-rec (true-list-fix (double-rewrite acc))))))))

(local
  (defcong nat-equiv equal (export-acc/fixed index acc vector) 1))

(local
  (defcong equiv/fixed equal (export-acc/fixed index acc vector) 3))

(local
  (defthm export-acc/fixed-when-not-recognizer/fixed
    (implies (not (recognizer/fixed vector))
             (equal (export-acc/fixed index acc vector)
                    (export-acc/fixed index acc (creator))))
    :rule-classes
    ((:rewrite :corollary
               (implies (and (syntaxp (not (and (consp vector)
                                                (eq (car vector) 'creator))))
                             (not (recognizer/fixed vector)))
                        (equal (export-acc/fixed index acc vector)
                               (export-acc/fixed index acc (creator))))))))

(local
  (defthm len-of-export-acc/fixed
    (equal (len (export-acc/fixed index acc vector))
           (+ (nfix index) (len acc)))
    :rule-classes
    ((:rewrite :corollary
               (equal (len (export-acc/fixed index acc vector))
                      (+ (nfix index) (len (double-rewrite acc))))))))

(local
  (defthm nth-of-export-acc/fixed
    (equal (nth %index (export-acc/fixed index acc vector))
           (if (< (nfix %index) (nfix index))
               (element-export (accessor/fixed %index vector))
               (nth (- (nfix %index) (nfix index)) acc)))
    :rule-classes
    ((:rewrite :corollary
               (equal (nth %index (export-acc/fixed index acc vector))
                      (if (< (nfix (double-rewrite %index)) (nfix index))
                          (element-export (accessor/fixed (double-rewrite %index) vector))
                          (nth (- (nfix (double-rewrite %index)) (nfix index)) (double-rewrite acc))))))))

(local
  (in-theory
    (disable export-acc/fixed)))


;;;; `EXPORT/FIXED'
(defun export/fixed (vector)
  (declare (xargs :guard (recognizer/fixed vector)))
  (cons (name)
        (export-acc/fixed (default-length) () vector)))

(defthm export/fixed-tp
  (and (consp (export/fixed vector))
       (true-listp (export/fixed vector)))
  :rule-classes :type-prescription)

(defthm exportp/fixed-of-export/fixed
  (exportp/fixed (export/fixed vector))
  :hints
  (("Goal"
    :in-theory (enable exportp/fixed))))

(local
  (defcong equiv/fixed equal (export/fixed vector) 1))

(defthm export/fixed-when-not-recognizer/fixed
  (implies (not (recognizer/fixed vector))
           (equal (export/fixed vector)
                  (export/fixed (creator))))
  :rule-classes
  ((:rewrite :corollary
             (implies (and (syntaxp (not (and (consp vector)
                                              (eq (car vector) 'creator))))
                           (not (recognizer/fixed vector)))
                      (equal (export/fixed vector)
                             (export/fixed (creator)))))))

(local
  (defthm len-of-export/fixed
    (equal (len (export/fixed vector))
           (1+ (default-length)))))

(local
  (defthm nth-of-export/fixed
    (equal (nth index (export/fixed vector))
           (cond
             ((zp index)
              (name))
             ((<= index (default-length))
              (element-export (accessor/fixed (1- index) vector)))))
    :rule-classes
    ((:rewrite :corollary
               (equal (nth index (export/fixed vector))
                      (cond
                        ((zp (double-rewrite index))
                         (name))
                        ((<= index (default-length))
                         (element-export (accessor/fixed (1- index) vector)))))))))

(local
  (in-theory
    (disable export/fixed)))


;;;; `IMPORT-REC/FIXED'
(defun import-rec/fixed (list index vector)
  (declare (xargs :guard (and (exportp-rec list)
                              (natp index)
                              (recognizer/fixed vector)
                              (<= (+ (len list) index) (default-length)))))
  (if (consp list)
      (let* ((index (nfix index))
             (value (accessor/fixed index vector))
             (value (element-import (car list) value))
             (vector (updater/fixed index value vector)))
        (import-rec/fixed (cdr list) (1+ index) vector))
      (fixer/fixed vector)))

(local
  (defthm import-rec/fixed-tp
    (true-listp (import-rec/fixed list index vector))
    :rule-classes :type-prescription))

(local
  (defthm recognizer/fixed-of-import-rec/fixed
    (recognizer/fixed (import-rec/fixed list index vector))))

(local
  (defthm import-rec/fixed-of-updater/fixed
    (equal (import-rec/fixed list %index (updater/fixed index value vector))
           (if (or (atom list)
                   (< (nfix index) (nfix %index))
                   (<= (+ (len list) (nfix %index)) (nfix index)))
               (updater/fixed index value (import-rec/fixed list %index vector))
               (import-rec/fixed list %index vector)))
    :rule-classes
    ((:rewrite :corollary
               (equal (import-rec/fixed list %index (updater/fixed index value vector))
                      (if (or (atom (double-rewrite list))
                              (< (nfix index) (nfix (double-rewrite %index)))
                              (<= (+ (len (double-rewrite list)) (nfix (double-rewrite %index))) (nfix index)))
                          (updater/fixed index value (import-rec/fixed list %index vector))
                          (import-rec/fixed list %index vector)))))))

(local
  (defthm accessor/fixed-of-import-rec/fixed
    (equal (accessor/fixed %index (import-rec/fixed list index vector))
           (cond
             ((atom list)
              (accessor/fixed %index vector))
             ((<= (default-length) (nfix %index))
              (initial-element))
             ((or (< (nfix %index) (nfix index))
                  (<= (+ (len list) (nfix index)) (nfix %index)))
              (accessor/fixed %index vector))
             (t
              (element-import (nth (- (nfix %index) (nfix index)) list)
                              (initial-element)))))
    :rule-classes
    ((:rewrite :corollary
               (equal (accessor/fixed %index (import-rec/fixed list index vector))
                      (cond
                        ((atom (double-rewrite list))
                         (accessor/fixed %index (double-rewrite vector)))
                        ((<= (default-length) (nfix %index))
                         (initial-element))
                        ((or (< (nfix %index) (nfix (double-rewrite index)))
                             (<= (+ (len (double-rewrite list)) (nfix (double-rewrite index))) (nfix %index)))
                         (accessor/fixed %index (double-rewrite vector)))
                        (t
                         (element-import (nth (- (nfix %index) (nfix (double-rewrite index))) (double-rewrite list))
                                         (initial-element)))))))))

(local
  (defcong list-equiv equal (import-rec/fixed list index vector) 1
    :hints
    (("Goal"
      :use ((:instance equal/fixed
                       (%vector (import-rec/fixed list index vector))
                       (vector (import-rec/fixed list-equiv index vector))))))))

(local
  (defcong nat-equiv equal (import-rec/fixed list index vector) 2
    :hints
    (("Goal"
      :use ((:instance equal/fixed
                       (%vector (import-rec/fixed list index vector))
                       (vector (import-rec/fixed list index-equiv vector))))))))

(local
  (defcong equiv/fixed equal (import-rec/fixed list index vector) 3
    :hints
    (("Goal"
      :use ((:instance equal/fixed
                       (%vector (import-rec/fixed list index vector))
                       (vector (import-rec/fixed list index vector-equiv))))))))

(local
  (in-theory
    (disable import-rec/fixed)))


;;;; `IMPORT/FIXED'
(defun import/fixed (export vector)
  (declare (xargs :guard (and (exportp/fixed export)
                              (recognizer/fixed vector))
                  :guard-hints
                  (("Goal"
                    :in-theory (enable exportp/fixed)))))
  (if (exportp/fixed export)
      (let* ((list (cdr export))
             (vector (import-rec/fixed list 0 vector)))
        vector)
      (creator)))

(defthm import/fixed-tp
  (true-listp (import/fixed export vector))
  :rule-classes :type-prescription)

(defthm recognizer/fixed-of-import/fixed
  (recognizer/fixed (import/fixed export vector)))

(defthm coupledp/fixed-of-import/fixed
  (coupledp/fixed (import/fixed export vector))
  :hints
  (("Goal"
    :in-theory (enable coupledp/fixed
                       exportp/fixed))))

(defthm import/fixed-when-not-exportp/fixed
  (implies (not (exportp/fixed export))
           (equal (import/fixed export vector)
                  (creator))))

(defthm import/fixed-ignores-2
  (equal (import/fixed export vector)
         (import/fixed export (creator)))
  :rule-classes
  ((:rewrite :corollary
             (implies (syntaxp (not (and (consp vector)
                                         (eq (car vector) 'creator))))
                      (equal (import/fixed export vector)
                             (import/fixed export (creator))))))
  :hints
  (("Goal"
    :in-theory (enable exportp/fixed)
    :use ((:instance equal/fixed
                     (%vector (import/fixed export vector))
                     (vector (import/fixed export (creator))))))))

(defthm accessor/fixed-of-import/fixed
  (equal (accessor/fixed index (import/fixed export vector))
         (if (and (exportp/fixed export)
                  (< (nfix index) (default-length)))
             (element-import (nth (1+ (nfix index)) export)
                             (initial-element))
             (initial-element)))
  :rule-classes
  ((:rewrite :corollary
             (equal (accessor/fixed index (import/fixed export vector))
                    (if (and (exportp/fixed export)
                             (< (nfix index) (default-length)))
                        (element-import (nth (1+ (nfix index)) (double-rewrite export))
                                        (initial-element))
                        (initial-element)))))
  :hints
  (("Goal"
    :in-theory (enable exportp/fixed))))

(local
  (in-theory
    (disable import/fixed)))


;;;; `EXPORT/FIXED' and `IMPORT/FIXED' Composition Theorems
(defthm export/fixed-of-import/fixed
  (implies (exportp/fixed export)
           (equal (export/fixed (import/fixed export vector))
                  export))
  :hints
  ((equal-by-nths-hint)
   ("Goal"
    :in-theory (enable exportp/fixed))))

(defthm import/fixed-of-export/fixed
  (implies (coupledp/fixed %vector)
           (equal (import/fixed (export/fixed %vector) vector)
                  (fixer/fixed %vector)))
  :hints
  (("Goal"
    :use ((:instance equal/fixed
                     (%vector (import/fixed (export/fixed %vector) (creator)))
                     (vector (fixer/fixed %vector)))))))
