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

#||
(include-book "std/lists/top" :dir :system)
||#

(include-book "../utilities/with-books")
(local
  (include-book "std"))

(encapsulate (((default-length) => *)
              ((element-recognizer *) => *)
              ((initial-element) => *)
              ((element-fixer *) => *))
  (local
    (defun default-length ()
      (declare (xargs :guard t))
      0))

  (defthm default-length-constraint
    (natp (default-length))
    :rule-classes :type-prescription)

  (local
    (defun element-recognizer (value)
      (declare (xargs :guard t))
      (integerp value)))

  (defthm element-recognizer-constraint
    (booleanp (element-recognizer value))
    :rule-classes :type-prescription)

  (local
    (defun initial-element ()
      (declare (xargs :guard t))
      0))

  (defthm initial-element-constraint
    (element-recognizer (initial-element)))

  (local
    (defun element-fixer (value)
      (declare (xargs :guard (element-recognizer value)))
      (if (element-recognizer value)
          value
          (initial-element))))

  (defthm element-fixer-constraint
    (equal (element-fixer value)
           (if (element-recognizer value)
               value
               (initial-element)))))

(defun contents-recognizer (contents)
  (declare (xargs :guard t))
  (if (atom contents)
      (null contents)
      (and (element-recognizer (car contents))
           (contents-recognizer (cdr contents)))))

(defun recognizer/resizable (vector)
  (declare (xargs :guard t))
  (contents-recognizer vector))

(defun recognizer/fixed (vector)
  (declare (xargs :guard t))
  (and (equal (len vector) (default-length))
       (contents-recognizer vector)))

(defun creator ()
  (declare (xargs :guard t))
  (make-list (default-length)
             :initial-element (initial-element)))

(defun fixer/resizable (vector)
  (declare (xargs :guard (recognizer/resizable vector)))
  (if (recognizer/resizable vector)
      vector
      (creator)))

(defun fixer/fixed (vector)
  (declare (xargs :guard (recognizer/fixed vector)))
  (if (recognizer/fixed vector)
      vector
      (creator)))

(defun length/resizable (vector)
  (declare (xargs :guard (recognizer/resizable vector)))
  (len (fixer/resizable vector)))

(defun length/fixed (vector)
  (declare (xargs :guard (recognizer/fixed vector))
           (ignore vector))
  (default-length))

(defun resizer/resizable (length vector)
  (declare (xargs :guard (and (natp length)
                              (recognizer/resizable vector))))
  (let ((vector (fixer/resizable vector))
        (length (nfix length)))
    (resize-list vector length (initial-element))))

(defun resizer/fixed (length vector)
  (declare (xargs :guard (and (natp length)
                              (recognizer/fixed vector)))
           (ignore length))
  (fixer/fixed vector))

(defun accessor/resizable (index vector)
  (declare (xargs :guard (and (natp index)
                              (recognizer/resizable vector)
                              (< index (length/resizable vector)))))
  (let ((index (nfix index))
        (vector (fixer/resizable vector)))
    (if (< index (length/resizable vector))
        (element-fixer (nth index vector))
        (initial-element))))

(defun accessor/fixed (index vector)
  (declare (xargs :guard (and (natp index)
                              (recognizer/fixed vector)
                              (< index (default-length)))))
  (let ((index (nfix index))
        (vector (fixer/fixed vector)))
    (if (< index (default-length))
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


;;;; `CONTENTS-RECOGNIZER'
(defthm contents-recognizer-tp
  (booleanp (contents-recognizer vector))
  :rule-classes :type-prescription)

(defthm contents-recognizer-cr
  (implies (contents-recognizer vector)
           (true-listp vector))
  :rule-classes :compound-recognizer)

(local
  (defthm contents-recognizer-of-make-list-ac
    (equal (contents-recognizer (make-list-ac size value acc))
           (and (or (zp size)
                    (element-recognizer value))
                (contents-recognizer acc)))))

(local
  (defthm contents-recognizer-of-repeat
    (equal (contents-recognizer (acl2::repeat n x))
           (or (zp n)
               (element-recognizer x)))))

(local
  (defthm contents-recognizer-of-resize-list
    (implies (contents-recognizer contents)
             (contents-recognizer (resize-list contents length (initial-element))))))

(local
  (defthm contents-recognizer-of-update-nth
    (implies (and (natp index)
                  (< index (len contents))
                  (element-recognizer value)
                  (contents-recognizer contents))
             (contents-recognizer (update-nth index value contents)))))

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
           (true-listp vector))
  :rule-classes :compound-recognizer)

(defthm recognizer/resizable-of-creator
  (recognizer/resizable (creator)))

(defthm recognizer/resizable-of-fixer/resizable
  (recognizer/resizable (fixer/resizable vector)))

(defthm recognizer/resizable-of-resizer/resizable
  (recognizer/resizable (resizer/resizable length vector)))

(with-books (("std/lists/repeat" :dir :system))
  (defthm recognizer/resizable-of-updater/resizable
    (recognizer/resizable (updater/resizable index value vector))
    :hints
    (("Goal"
      :expand (acl2::repeat (default-length) (initial-element))))))


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

(with-books (("std/lists/repeat" :dir :system))
  (defthm recognizer/fixed-of-updater/fixed
    (recognizer/fixed (updater/fixed index value vector))
    :hints
    (("Goal"
      :expand (acl2::repeat (default-length) (initial-element))))))


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


;;;; `LENGTH/RESIZABLE'
(defthm length/resizable-tp
  (natp (length/resizable vector))
  :rule-classes :type-prescription)

(defthm length/resizable-when-not-recognizer/resizable
  (implies (not (recognizer/resizable vector))
           (equal (length/resizable vector)
                  (default-length))))

(defthm length/resizable-of-creator
  (equal (length/resizable (creator))
         (default-length)))

(defthm length/resizable-of-fixer/resizable
  (equal (length/resizable (fixer/resizable vector))
         (length/resizable vector)))

(with-books (("std/lists/resize-list" :dir :system))
  (defthm length/resizable-of-resizer/resizable
    (equal (length/resizable (resizer/resizable length vector))
           (nfix length))))

(with-books (("std/lists/repeat" :dir :system))
  (defthm length/resizable-of-updater/resizable
    (equal (length/resizable (updater/resizable index value vector))
           (length/resizable vector))
    :hints
    (("Goal"
      :expand (acl2::repeat (default-length) (initial-element))))))


;;;; `LENGTH/FIXED'
(defthm length/fixed-tp
  (natp (length/fixed vector))
  :rule-classes :type-prescription)

(defthm length/fixed-rw
  (equal (length/fixed vector)
         (default-length)))


;;;; `RESIZER/RESIZABLE'
(defthm resizer/resizable-tp
  (true-listp (resizer/resizable length vector))
  :rule-classes :type-prescription)

(defthm resizer/resizable-when-not-natp
  (implies (not (natp length))
           (equal (resizer/resizable length vector)
                  (resizer/resizable 0 vector))))

(defthm resizer/resizable-when-not-recognizer/resizable
  (implies (not (recognizer/resizable vector))
           (equal (resizer/resizable length vector)
                  (resizer/resizable length (creator)))))

(with-books (("std/lists/repeat" :dir :system))
  (defthm resizer/resizable-of-creator
    (implies (equal (nfix length) (default-length))
             (equal (resizer/resizable length (creator))
                    (creator)))))

(defthm resizer/resizable-of-nfix
  (equal (resizer/resizable (nfix length) vector)
         (resizer/resizable length vector)))

(defthm resizer/resizable-of-fixer/resizable
  (equal (resizer/resizable length (fixer/resizable vector))
         (resizer/resizable length vector)))

(with-books (("std/lists/resize-list" :dir :system)
             ("std/lists/list-fix" :dir :system))
  (defthm resizer/resizable-of-length/resizable-free
    (implies (equal (nfix length) (length/resizable vector))
             (equal (resizer/resizable length vector)
                    (fixer/resizable vector)))))

(defthm resizer/resizable-of-length/resizable
  (equal (resizer/resizable (length/resizable vector) vector)
         (fixer/resizable vector))
  :hints
  (("Goal"
    :in-theory (disable resizer/resizable-of-length/resizable-free)
    :use (:instance resizer/resizable-of-length/resizable-free
                    (length (length/resizable vector))))))

(with-books (("std/lists/resize-list" :dir :system)
             ("std/lists/list-fix" :dir :system))
  (defthm resizer/resizable-of-resizer/resizable
    (implies (or (<= (nfix %length) (nfix length))
                 (<= (length/resizable vector) (nfix length)))
             (equal (resizer/resizable %length (resizer/resizable length vector))
                    (resizer/resizable %length vector)))
    :hints
    (("Goal"
      :use ((:instance acl2::resize-list-of-resize-list
                       (lst (fixer/resizable vector))
                       (n (nfix length))
                       (d (initial-element))
                       (m (nfix %length))
                       (e (initial-element))))))))

(with-books (("std/lists/resize-list" :dir :system)
             ("std/lists/repeat" :dir :system))
  (defthm resizer/resizable-of-updater/resizable-keep
    (implies (and (< (nfix index) (length/resizable vector))
                  (< (nfix index) (nfix length)))
             (equal (resizer/resizable length (updater/resizable index value vector))
                    (updater/resizable index value (resizer/resizable length vector))))
    :hints
    (("Goal"
      :in-theory (disable acl2::resize-list-of-update-nth-keep
                          acl2::update-nth-of-resize-list)
      :use ((:instance acl2::resize-list-of-update-nth-keep
                       (key (nfix index))
                       (val (element-fixer value))
                       (l (fixer/resizable vector))
                       (n (nfix length))
                       (default-value (initial-element)))
            (:instance acl2::update-nth-of-resize-list
                       (key (nfix index))
                       (val (element-fixer value))
                       (lst (fixer/resizable vector))
                       (n (nfix length))
                       (default-value (initial-element))))
      :expand ((:free (x) (acl2::repeat length x))
               (acl2::repeat (default-length) (initial-element)))))))

(defthm resizer/resizable-of-updater/resizable-drop
  (implies (or (<= (length/resizable vector) (nfix index))
               (<= (nfix length) (nfix index)))
           (equal (resizer/resizable length (updater/resizable index value vector))
                  (resizer/resizable length vector))))

(defthm resizer/resizable-of-updater/resizable
  (equal (resizer/resizable length (updater/resizable index value vector))
         (if (and (< (nfix index) (length/resizable vector))
                  (< (nfix index) (nfix length)))
             (updater/resizable index value (resizer/resizable length vector))
             (resizer/resizable length vector)))
  :hints
  (("Goal"
    :cases ((and (< (nfix index) (length/resizable vector))
                 (< (nfix index) (nfix length)))))
   ("Subgoal 2"
    :use resizer/resizable-of-updater/resizable-drop)
   ("Subgoal 1"
    :use resizer/resizable-of-updater/resizable-keep)))


;;;; `RESIZER/FIXED'
(defthm resizer/fixed-tp
  (true-listp (resizer/fixed length vector))
  :rule-classes :type-prescription)

(defthm resizer/fixed-rw
  (equal (resizer/fixed length vector)
         (fixer/fixed vector)))


;;;; `ACCESSOR/RESIZABLE'
(defthm element-recognizer-of-accessor/resizable
  (element-recognizer (accessor/resizable index vector)))

(defthm accessor/resizable-when-large
  (implies (<= (length/resizable vector) (nfix index))
           (equal (accessor/resizable index vector)
                  (initial-element))))

(defthm accessor/resizable-when-not-natp
  (implies (not (natp index))
           (equal (accessor/resizable index vector)
                  (accessor/resizable 0 vector))))

(with-books (("std/lists/nth" :dir :system))
  (defthm accessor/resizable-when-not-recognizer/resizable
    (implies (not (recognizer/resizable vector))
             (equal (accessor/resizable index vector)
                    (initial-element))))

  (defthm accessor/resizable-of-creator
    (equal (accessor/resizable index (creator))
           (initial-element))))

(defthm accessor/resizable-of-nfix
  (equal (accessor/resizable (nfix index) vector)
         (accessor/resizable index vector)))

(defthm accessor/resizable-of-fixer/resizable
  (equal (accessor/resizable index (fixer/resizable vector))
         (accessor/resizable index vector)))

(with-books (("std/lists/resize-list" :dir :system))
  (defthm accessor/resizable-of-resizer/resizable
    (implies (< (nfix index) (nfix length))
             (equal (accessor/resizable index (resizer/resizable length vector))
                    (accessor/resizable index vector))))

  (defthm accessor/resizable-of-resizer/resizable-split
    (equal (accessor/resizable index (resizer/resizable length vector))
           (if (< (nfix index) (nfix length))
               (accessor/resizable index vector)
               (initial-element)))))

(with-books (("std/lists/repeat" :dir :system))
  (defthm accessor/resizable-of-updater/resizable-same
    (implies (and (< (nfix %index) (length/resizable vector))
                  (equal (nfix %index) (nfix index)))
             (equal (accessor/resizable %index (updater/resizable index value vector))
                    (element-fixer value)))
    :hints
    (("Goal"
      :expand (acl2::repeat (default-length) (initial-element))))))

(defthm accessor/resizable-of-updater/resizable-diff
  (implies (or (<= (length/resizable vector) (nfix %index))
               (not (equal (nfix %index) (nfix index))))
           (equal (accessor/resizable %index (updater/resizable index value vector))
                  (accessor/resizable %index vector)))
  :hints
  (("Goal"
    :in-theory (disable update-nth))))

(with-books (("std/lists/repeat" :dir :system)
             ("std/lists/nth" :dir :system)
             ("std/lists/update-nth" :dir :system))
  (local
    (defthm nth-of-cons
      (equal (nth n (cons a d))
             (if (zp n)
                 a
                 (nth (1- n) d)))))

  (local
    (defthm cdr-of-repeat
      (equal (cdr (acl2::repeat n x))
             (if (zp n)
                 nil
                 (acl2::repeat (1- n) x)))
      :hints
      (("Goal"
        :expand (acl2::repeat n x)))))

  (defthm accessor/resizable-of-updater/resizable
    (equal (accessor/resizable %index (updater/resizable index value vector))
           (cond
             ((<= (length/resizable vector) (nfix %index))
              (initial-element))
             ((equal (nfix %index) (nfix index))
              (element-fixer value))
             (t
              (accessor/resizable %index vector))))
    :hints
    (("Goal"
      :cases ((<= (length/resizable vector) (nfix %index))
              (equal (nfix %index) (nfix index)))
      :in-theory (enable acl2::repeat))
     ("Subgoal 3"
      :use ((:instance accessor/resizable-when-large
                       (index %index)
                       (vector (updater/resizable index value vector))))
      :expand ((nth %index vector))))))


;;;; `ACCESSOR/FIXED'
(defthm element-recognizer-of-accessor/fixed
  (element-recognizer (accessor/fixed index vector)))

(defthm accessor/fixed-when-large
  (implies (<= (default-length) (nfix index))
           (equal (accessor/fixed index vector)
                  (initial-element))))

(defthm accessor/fixed-when-not-natp
  (implies (not (natp index))
           (equal (accessor/fixed index vector)
                  (accessor/fixed 0 vector))))

(with-books (("std/lists/nth" :dir :system))
  (defthm accessor/fixed-when-not-recognizer/fixed
    (implies (not (recognizer/fixed vector))
             (equal (accessor/fixed index vector)
                    (initial-element))))

  (defthm accessor/fixed-of-creator
    (equal (accessor/fixed index (creator))
           (initial-element))))

(defthm accessor/fixed-of-nfix
  (equal (accessor/fixed (nfix index) vector)
         (accessor/fixed index vector)))

(defthm accessor/fixed-of-fixer/fixed
  (equal (accessor/fixed index (fixer/fixed vector))
         (accessor/fixed index vector)))

(with-books (("std/lists/repeat" :dir :system))
  (defthm accessor/fixed-of-updater/fixed-same
    (implies (and (< (nfix %index) (default-length))
                  (equal (nfix %index) (nfix index)))
             (equal (accessor/fixed %index (updater/fixed index value vector))
                    (element-fixer value)))
    :hints
    (("Goal"
      :expand (acl2::repeat (default-length) (initial-element))))))

(defthm accessor/fixed-of-updater/fixed-diff
  (implies (or (<= (default-length) (nfix %index))
               (not (equal (nfix %index) (nfix index))))
           (equal (accessor/fixed %index (updater/fixed index value vector))
                  (accessor/fixed %index vector)))
  :hints
  (("Goal"
    :in-theory (disable update-nth))))

(with-books (("std/lists/repeat" :dir :system)
             ("std/lists/nth" :dir :system)
             ("std/lists/update-nth" :dir :system))
  (local
    (defthm nth-of-cons
      (equal (nth n (cons a d))
             (if (zp n)
                 a
                 (nth (1- n) d)))))

  (local
    (defthm cdr-of-repeat
      (equal (cdr (acl2::repeat n x))
             (if (zp n)
                 nil
                 (acl2::repeat (1- n) x)))
      :hints
      (("Goal"
        :in-theory (enable acl2::repeat)))))

  (defthm accessor/fixed-of-updater/fixed
    (equal (accessor/fixed %index (updater/fixed index value vector))
           (cond
             ((<= (default-length) (nfix %index))
              (initial-element))
             ((equal (nfix %index) (nfix index))
              (element-fixer value))
             (t
              (accessor/fixed %index vector))))
    :hints
    (("Goal"
      :cases ((<= (default-length) (nfix %index))
              (equal (nfix %index) (nfix index)))))))


;;;; `UPDATER/RESIZABLE'
(defthm updater/resizable-tp
  (true-listp (updater/resizable index value vector))
  :rule-classes :type-prescription)

(defthm updater/resizable-when-large
  (implies (<= (length/resizable vector) (nfix index))
           (equal (updater/resizable index value vector)
                  (fixer/resizable vector))))

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
  (implies (equal (element-fixer value) (initial-element))
           (equal (updater/resizable index value (creator))
                  (creator))))

(defthm updater/resizable-of-nfix
  (equal (updater/resizable (nfix index) value vector)
         (updater/resizable index value vector)))

(defthm updater/resizable-of-element-fixer
  (equal (updater/resizable index (element-fixer value) vector)
         (updater/resizable index value vector)))

(defthm updater/resizable-of-fixer/resizable
  (equal (updater/resizable index value (fixer/resizable vector))
         (updater/resizable index value vector)))

(with-books (("std/lists/update-nth" :dir :system)
             ("std/lists/repeat" :dir :system)
             ("std/lists/resize-list" :dir :system)
             ("std/lists/len" :dir :system)
             ("std/lists/nth" :dir :system))
  (local
    (defthm updater/resizable-of-resizer/resizable-lemma
      (implies (and (< (nfix index) (nfix length))
                    (equal (element-fixer value) (accessor/resizable index vector)))
               (equal (updater/resizable index value (resizer/resizable length vector))
                      (resizer/resizable length vector)))
      :hints
      (("Goal"
        :expand ((resize-list vector length (initial-element))
                 (acl2::repeat length (initial-element))
                 (acl2::repeat (default-length) (initial-element)))))))

  (defthm updater/resizable-of-resizer/resizable
    (implies (equal (element-fixer value) (accessor/resizable index vector))
             (equal (updater/resizable index value (resizer/resizable length vector))
                    (resizer/resizable length vector)))
    :hints
    (("Goal"
      :cases ((< (nfix index) (nfix length))))
     ("Subgoal 1"
      :by updater/resizable-of-resizer/resizable-lemma))))

(with-books (("std/lists/update-nth" :dir :system)
             ("std/lists/repeat" :dir :system))
  (defthm updater/resizable-of-accessor/resizable-free
    (implies (equal (element-fixer value) (accessor/resizable index vector))
             (equal (updater/resizable index value vector)
                    (fixer/resizable vector)))
    :hints
    (("Goal"
      :expand (acl2::repeat (default-length) (initial-element))))))

(defthm updater/resizable-of-accessor/resizable
  (implies (equal (nfix %index) (nfix index))
           (equal (updater/resizable %index (accessor/resizable index vector) vector)
                  (fixer/resizable vector)))
  :hints
  (("Goal"
    :in-theory (disable updater/resizable-of-accessor/resizable-free
                        contents-recognizer
                        recognizer/resizable
                        creator
                        fixer/resizable
                        length/resizable
                        accessor/resizable)
    :use (:instance updater/resizable-of-accessor/resizable-free
                    (index %index)
                    (value (accessor/resizable index vector))))))

(with-books (("std/basic/nfix" :dir :system)
             ("std/lists/update-nth" :dir :system))
  (defthm updater/resizable-of-updater/resizable-same
    (implies (equal (nfix %index) (nfix index))
             (equal (updater/resizable %index %value (updater/resizable index value vector))
                    (updater/resizable %index %value vector))))

  (defthm updater/resizable-of-updater/resizable-diff
    (implies (not (equal (nfix %index) (nfix index)))
             (equal (updater/resizable %index %value (updater/resizable index value vector))
                    (updater/resizable index value (updater/resizable %index %value vector))))
    :rule-classes
    ((:rewrite :loop-stopper ((%index index updater/resizable))))
    :hints
    (("Goal"
      :in-theory (disable acl2::update-nth-of-update-nth-diff
                          nfix
                          update-nth
                          nth
                          acl2::update-nth-when-zp)
      :use ((:instance acl2::update-nth-of-update-nth-diff
                       (n1 (nfix %index))
                       (n2 (nfix index))
                       (v1 (element-fixer %value))
                       (v2 (element-fixer value))
                       (x (fixer/resizable vector))))))))

(defthm updater/resizable-of-updater/resizable
  (equal (updater/resizable %index %value (updater/resizable index value vector))
         (if (equal (nfix %index) (nfix index))
             (updater/resizable %index %value vector)
             (updater/resizable index value (updater/resizable %index %value vector))))
  :rule-classes
  ((:rewrite :loop-stopper ((%index index updater/resizable))))
  :hints
  (("Goal"
    :cases ((equal (nfix %index) (nfix index))))
   ("Subgoal 2"
    :by updater/resizable-of-updater/resizable-diff)
   ("Subgoal 1"
    :by updater/resizable-of-updater/resizable-same)))


;;;; `UPDATER/FIXED'
(defthm updater/fixed-tp
  (true-listp (updater/fixed index value vector))
  :rule-classes :type-prescription)

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
  (implies (equal (element-fixer value) (initial-element))
           (equal (updater/fixed index value (creator))
                  (creator))))

(defthm updater/fixed-of-nfix
  (equal (updater/fixed (nfix index) value vector)
         (updater/fixed index value vector)))

(defthm updater/fixed-of-element-fixer
  (equal (updater/fixed index (element-fixer value) vector)
         (updater/fixed index value vector)))

(defthm updater/fixed-of-fixer/fixed
  (equal (updater/fixed index value (fixer/fixed vector))
         (updater/fixed index value vector)))

(with-books (("std/lists/update-nth" :dir :system)
             ("std/lists/repeat" :dir :system))
  (defthm updater/fixed-of-accessor/fixed-free
    (implies (equal (element-fixer value) (accessor/fixed index vector))
             (equal (updater/fixed index value vector)
                    (fixer/fixed vector)))
    :hints
    (("Goal"
      :expand (acl2::repeat (default-length) (initial-element))))))

(defthm updater/fixed-of-accessor/fixed
  (implies (equal (nfix %index) (nfix index))
           (equal (updater/fixed %index (accessor/fixed index vector) vector)
                  (fixer/fixed vector)))
  :hints
  (("Goal"
    :in-theory (disable updater/fixed-of-accessor/fixed-free
                        contents-recognizer
                        recognizer/fixed
                        creator
                        fixer/fixed
                        length/fixed
                        accessor/fixed)
    :use (:instance updater/fixed-of-accessor/fixed-free
                    (index %index)
                    (value (accessor/fixed index vector))))))

(with-books (("std/basic/nfix" :dir :system)
             ("std/lists/update-nth" :dir :system))
  (defthm updater/fixed-of-updater/fixed-same
    (implies (equal (nfix %index) (nfix index))
             (equal (updater/fixed %index %value (updater/fixed index value vector))
                    (updater/fixed %index %value vector))))

  (defthm updater/fixed-of-updater/fixed-diff
    (implies (not (equal (nfix %index) (nfix index)))
             (equal (updater/fixed %index %value (updater/fixed index value vector))
                    (updater/fixed index value (updater/fixed %index %value vector))))
    :rule-classes
    ((:rewrite :loop-stopper ((%index index updater/fixed))))
    :hints
    (("Goal"
      :in-theory (disable acl2::update-nth-of-update-nth-diff
                          nfix
                          update-nth
                          nth
                          acl2::update-nth-when-zp)
      :use ((:instance acl2::update-nth-of-update-nth-diff
                       (n1 (nfix %index))
                       (n2 (nfix index))
                       (v1 (element-fixer %value))
                       (v2 (element-fixer value))
                       (x (fixer/fixed vector))))))))

(defthm updater/fixed-of-updater/fixed
  (equal (updater/fixed %index %value (updater/fixed index value vector))
         (if (equal (nfix %index) (nfix index))
             (updater/fixed %index %value vector)
             (updater/fixed index value (updater/fixed %index %value vector))))
  :rule-classes
  ((:rewrite :loop-stopper ((%index index updater/fixed))))
  :hints
  (("Goal"
    :cases ((equal (nfix %index) (nfix index))))
   ("Subgoal 2"
    :by updater/fixed-of-updater/fixed-diff)
   ("Subgoal 1"
    :by updater/fixed-of-updater/fixed-same)))


;;;; `EQUAL/RESIZABLE-FC'
(defun-sk contents-equal/resizable (%vector vector)
  (declare (xargs :guard (and (recognizer/resizable %vector)
                              (recognizer/resizable vector))
                  :verify-guards nil))
  (forall index
    (implies (and (natp index)
                  (< index (length/resizable %vector))
                  (< index (length/resizable vector)))
             (equal (accessor/resizable index %vector)
                    (accessor/resizable index vector))))
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

(with-books (("std/lists/nth" :dir :system))
  (local
    (defthmd equal/resizable-fc-lemma-2
      (implies (and (recognizer/resizable %vector)
                    (recognizer/resizable vector))
               (iff (equal (len %vector) (len vector))
                    (equal (length/resizable %vector) (length/resizable vector))))))

  (local
    (defthmd equal/resizable-fc-lemma-1
      (implies (and (recognizer/resizable %vector)
                    (recognizer/resizable vector)
                    (equal (length/resizable %vector)
                           (length/resizable vector))
                    (contents-equal/resizable %vector vector)
                    (natp n)
                    (< n (len %vector)))
               (equal (nth n %vector)
                      (nth n vector)))
      :rule-classes
      ((:rewrite :match-free :all))
      :hints
      (("Goal"
        :use ((:instance contents-equal/resizable-necc
                         (index n)))))))

  (local
    (in-theory
      (disable contents-recognizer
               recognizer/resizable
               creator
               fixer/resizable
               length/resizable
               resizer/resizable
               accessor/resizable
               updater/resizable
               contents-equal/resizable)))

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
    ((acl2::equal-by-nths-hint)
     ("Goal"
      :do-not-induct t)
     ("Subgoal 2"
      :use equal/resizable-fc-lemma-2)
     ("Subgoal 1"
      :use (:instance equal/resizable-fc-lemma-1
                      (n acl2::n))))))


;;;; `EQUAL/FIXED-FC'
(defun-sk contents-equal/fixed (%vector vector)
  (declare (xargs :guard (and (recognizer/fixed %vector)
                              (recognizer/fixed vector))
                  :verify-guards nil))
  (forall index
    (implies (and (natp index)
                  (< index (default-length))
                  (< index (default-length)))
             (equal (accessor/fixed index %vector)
                    (accessor/fixed index vector))))
  :rewrite :direct)

(defun-nx equal/fixed (%vector vector)
  (declare (xargs :guard (and (recognizer/fixed %vector)
                              (recognizer/fixed vector))
                  :verify-guards nil))
  (and (recognizer/fixed %vector)
       (recognizer/fixed vector)
       (contents-equal/fixed %vector vector)))

(with-books (("std/lists/nth" :dir :system))
  (local
    (defthmd equal/fixed-fc-lemma-2
      (implies (and (recognizer/fixed %vector)
                    (recognizer/fixed vector))
               (equal (len %vector) (len vector)))))

  (local
    (defthmd equal/fixed-fc-lemma-1
      (implies (and (recognizer/fixed %vector)
                    (recognizer/fixed vector)
                    (contents-equal/fixed %vector vector)
                    (natp n)
                    (< n (len %vector)))
               (equal (nth n %vector)
                      (nth n vector)))
      :rule-classes
      ((:rewrite :match-free :all))
      :hints
      (("Goal"
        :use ((:instance contents-equal/fixed-necc
                         (index n)))))))

  (local
    (in-theory
      (disable contents-recognizer
               recognizer/fixed
               creator
               fixer/fixed
               length/fixed
               resizer/fixed
               accessor/fixed
               updater/fixed
               contents-equal/fixed)))

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
    ((acl2::equal-by-nths-hint)
     ("Goal"
      :do-not-induct t)
     ("Subgoal 2"
      :use equal/fixed-fc-lemma-2)
     ("Subgoal 1"
      :use (:instance equal/fixed-fc-lemma-1
                      (n acl2::n))))))


(local
  (in-theory
    (disable contents-recognizer
             recognizer/resizable
             recognizer/fixed
             creator
             (:e creator)
             fixer/resizable
             fixer/fixed
             length/resizable
             length/fixed
             resizer/resizable
             resizer/fixed
             accessor/resizable
             accessor/fixed
             updater/resizable
             updater/fixed
             equal/resizable
             equal/fixed)))


;;;; Element Copy
(encapsulate (((element-coupled-p *) => *))
  (local
    (defun element-coupled-p (value)
      (declare (xargs :guard t)
               (ignore value))
      t))

  (defthm element-coupled-p-constraint
    (booleanp (element-coupled-p value))
    :rule-classes :type-prescription)

  (defthm element-coupled-p-of-initial-element
    (element-coupled-p (initial-element)))

  (defthm element-coupled-p-when-not-element-recognizer
    (implies (not (element-recognizer value))
             (element-coupled-p value))))

(encapsulate (((element-copy * *) => *))
  (local
    (defun element-copy (%value value)
      (declare (xargs :guard (and (element-recognizer %value)
                                  (element-recognizer value)))
               (ignore %value))
      (element-fixer value)))

  (defthm element-recognizer-of-element-copy
    (element-recognizer (element-copy %value value)))

  (defthm element-copy-ignores-1
    (implies (syntaxp (not (and (consp %value)
                                (eq (car %value) 'initial-element))))
             (equal (element-copy %value value)
                    (element-copy (initial-element) value))))

  (defthm element-copy-rw
    (implies (element-coupled-p value)
             (equal (element-copy %value value)
                    (element-fixer value)))))


;;;; `COUPLEDP/RESIZABLE'
(defun-sk coupledp/resizable (vector)
  (declare (xargs :guard (recognizer/resizable vector)
                  :verify-guards nil))
  (forall index
    (element-coupled-p (accessor/resizable index vector)))
  :rewrite :direct)

(defthm coupledp/resizable-when-not-recognizer/resizable
  (implies (not (recognizer/resizable vector))
           (coupledp/resizable vector)))

(defthm coupledp/resizable-of-creator
  (coupledp/resizable (creator)))

(defthm coupledp/resizable-of-fixer/resizable
  (equal (coupledp/resizable (fixer/resizable vector))
         (coupledp/resizable vector))
  :hints
  (("Goal"
    :in-theory (enable fixer/resizable))))

(defthm coupledp/resizable-of-resizer/resizable
  (implies (coupledp/resizable vector)
           (coupledp/resizable (resizer/resizable length vector)))
  :hints
  (("Goal"
    :cases ((< (nfix (coupledp/resizable-witness vector)) (nfix length))))
   ("Subgoal 2"
    :use ((:instance accessor/resizable-when-large
                     (index (coupledp/resizable-witness (resizer/resizable length vector)))
                     (vector (resizer/resizable length vector)))))
   ("Subgoal 1"
    :cases ((< (nfix (coupledp/resizable-witness (resizer/resizable length vector))) (nfix length))))))

(defthm element-coupled-p-of-accessor/resizable
  (implies (coupledp/resizable vector)
           (element-coupled-p (accessor/resizable index vector))))

(defthm coupledp/resizable-of-updater/resizable
  (implies (coupledp/resizable vector)
           (equal (coupledp/resizable (updater/resizable index value vector))
                  (if (<= (length/resizable vector) (nfix index))
                      t
                      (element-coupled-p value))))
  :hints
  (("Goal"
    :cases ((< (nfix index) (length/resizable vector)))
    :in-theory (disable coupledp/resizable
                        coupledp/resizable-necc))
   ("Subgoal 1.3"
    :use ((:instance coupledp/resizable-necc
                     (index 0)
                     (vector (updater/resizable 0 value vector)))))
   ("Subgoal 1.3.3"
    :use ((:instance accessor/resizable-of-updater/resizable
                     (%index (coupledp/resizable-witness (updater/resizable 0 value vector)))
                     (index 0)))
    :expand (:free (index value)
                   (coupledp/resizable (updater/resizable index value vector))))
   ("Subgoal 1.3.2"
    :use ((:instance accessor/resizable-of-updater/resizable
                     (%index (coupledp/resizable-witness (updater/resizable 0 (initial-element)
                                                                            vector)))
                     (index 0)
                     (value (initial-element))))
    :expand (:free (index value)
                   (coupledp/resizable (updater/resizable index value vector))))
   ("Subgoal 1.3.1"
    :use ((:instance accessor/resizable-of-updater/resizable
                     (%index (coupledp/resizable-witness (updater/resizable 0 value vector)))
                     (index 0)))
    :expand (:free (index value)
                   (coupledp/resizable (updater/resizable index value vector))))
   ("Subgoal 1.2"
    :use ((:instance coupledp/resizable-necc
                     (vector (updater/resizable index value vector)))))
   ("Subgoal 1.2.3"
    :use ((:instance accessor/resizable-of-updater/resizable
                     (%index (coupledp/resizable-witness (updater/resizable index value vector)))
                     (index index)))
    :expand (:free (index value)
                   (coupledp/resizable (updater/resizable index value vector))))
   ("Subgoal 1.2.2"
    :use ((:instance accessor/resizable-of-updater/resizable
                     (%index (coupledp/resizable-witness (updater/resizable index (initial-element) vector)))
                     (index index)))
    :expand (:free (index value)
                   (coupledp/resizable (updater/resizable index value vector))))
   ("Subgoal 1.2.1"
    :use ((:instance accessor/resizable-of-updater/resizable
                     (%index (coupledp/resizable-witness (updater/resizable index value vector)))
                     (index index)))
    :expand (:free (index value)
                   (coupledp/resizable (updater/resizable index value vector))))
   ("Subgoal 1.1"
    :use ((:instance coupledp/resizable-necc
                     (vector (updater/resizable 0 value vector)))))
   ("Subgoal 1.1.3"
    :use ((:instance accessor/resizable-of-updater/resizable
                     (%index (coupledp/resizable-witness (updater/resizable 0 value vector)))
                     (index 0)))
    :expand (:free (index value)
                   (coupledp/resizable (updater/resizable index value vector))))
   ("Subgoal 1.1.2"
    :use ((:instance accessor/resizable-of-updater/resizable
                     (%index (coupledp/resizable-witness (updater/resizable 0 (initial-element) vector)))
                     (index 0)))
    :expand (:free (index value)
                   (coupledp/resizable (updater/resizable index value vector))))
   ("Subgoal 1.1.1"
    :use ((:instance accessor/resizable-of-updater/resizable
                     (%index (coupledp/resizable-witness (updater/resizable 0 value vector)))
                     (index 0)))
    :expand (:free (index value)
                   (coupledp/resizable (updater/resizable index value vector))))))

(local
  (in-theory
    (disable coupledp/resizable)))


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

(defthm recognizer/resizable-of-copy/resizable-rec
  (recognizer/resizable (copy/resizable-rec index %vector vector)))

(defthm copy/resizable-rec-of-fixer/resizable-1
  (equal (copy/resizable-rec index (fixer/resizable %vector) vector)
         (copy/resizable-rec index %vector vector)))

(defthm copy/resizable-rec-of-fixer/resizable-2
  (equal (copy/resizable-rec index %vector (fixer/resizable vector))
         (copy/resizable-rec index %vector vector)))

(defthm length/resizable-of-copy/resizable-rec
  (equal (length/resizable (copy/resizable-rec index %vector vector))
         (length/resizable %vector)))

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
  :hints
  (("Goal"
    :cases ((<= (length/resizable %vector) (nfix %index))
            (< (nfix %index) (nfix index))))))

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

(defthmd copy/resizable-ignores-1
  (equal (copy/resizable %vector vector)
         (copy/resizable (creator) vector))
  :hints
  (("Goal"
    :use ((:instance equal/resizable
                     (%vector (copy/resizable %vector vector))
                     (vector (copy/resizable (creator) vector)))))))

(local
  (defthm copy/resizable-ignores-1-local
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
      :by (:functional-instance copy/resizable-ignores-1)))))

(defthm copy/resizable-of-fixer/resizable-2
  (equal (copy/resizable %vector (fixer/resizable vector))
         (copy/resizable %vector vector)))

(defthm coupledp/resizable-of-copy/resizable
  (implies (coupledp/resizable vector)
           (coupledp/resizable (copy/resizable %vector vector)))
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

(defthm accessor/resizable-of-copy/resizable
  (implies (coupledp/resizable vector)
           (equal (accessor/resizable index (copy/resizable %vector vector))
                  (accessor/resizable index vector)))
  :hints
  (("Goal"
    :cases ((< (nfix index) (length/resizable vector))))))

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
    (element-coupled-p (accessor/fixed index vector)))
  :rewrite :direct)

(defthm coupledp/fixed-when-not-recognizer/fixed
  (implies (not (recognizer/fixed vector))
           (coupledp/fixed vector)))

(defthm coupledp/fixed-of-creator
  (coupledp/fixed (creator)))

(defthm coupledp/fixed-of-fixer/fixed
  (equal (coupledp/fixed (fixer/fixed vector))
         (coupledp/fixed vector))
  :hints
  (("Goal"
    :in-theory (enable fixer/fixed))))

(defthm element-coupled-p-of-accessor/fixed
  (implies (coupledp/fixed vector)
           (element-coupled-p (accessor/fixed index vector))))

(defthm coupledp/fixed-of-updater/fixed
  (implies (coupledp/fixed vector)
           (equal (coupledp/fixed (updater/fixed index value vector))
                  (if (<= (default-length) (nfix index))
                      t
                      (element-coupled-p value))))
  :hints
  (("Goal"
    :cases ((< (nfix index) (default-length)))
    :in-theory (disable coupledp/fixed
                        coupledp/fixed-necc))
   ("Subgoal 1.3"
    :use ((:instance coupledp/fixed-necc
                     (index 0)
                     (vector (updater/fixed 0 value vector)))))
   ("Subgoal 1.3.3"
    :use ((:instance accessor/fixed-of-updater/fixed
                     (%index (coupledp/fixed-witness (updater/fixed 0 value vector)))
                     (index 0)))
    :expand (:free (index value)
                   (coupledp/fixed (updater/fixed index value vector))))
   ("Subgoal 1.3.2"
    :use ((:instance accessor/fixed-of-updater/fixed
                     (%index (coupledp/fixed-witness (updater/fixed 0 (initial-element)
                                                                    vector)))
                     (index 0)
                     (value (initial-element))))
    :expand (:free (index value)
                   (coupledp/fixed (updater/fixed index value vector))))
   ("Subgoal 1.3.1"
    :use ((:instance accessor/fixed-of-updater/fixed
                     (%index (coupledp/fixed-witness (updater/fixed 0 value vector)))
                     (index 0)))
    :expand (:free (index value)
                   (coupledp/fixed (updater/fixed index value vector))))
   ("Subgoal 1.2"
    :use ((:instance coupledp/fixed-necc
                     (vector (updater/fixed index value vector)))))
   ("Subgoal 1.2.3"
    :use ((:instance accessor/fixed-of-updater/fixed
                     (%index (coupledp/fixed-witness (updater/fixed index value vector)))
                     (index index)))
    :expand (:free (index value)
                   (coupledp/fixed (updater/fixed index value vector))))
   ("Subgoal 1.2.2"
    :use ((:instance accessor/fixed-of-updater/fixed
                     (%index (coupledp/fixed-witness (updater/fixed index (initial-element) vector)))
                     (index index)))
    :expand (:free (index value)
                   (coupledp/fixed (updater/fixed index value vector))))
   ("Subgoal 1.2.1"
    :use ((:instance accessor/fixed-of-updater/fixed
                     (%index (coupledp/fixed-witness (updater/fixed index value vector)))
                     (index index)))
    :expand (:free (index value)
                   (coupledp/fixed (updater/fixed index value vector))))
   ("Subgoal 1.1"
    :use ((:instance coupledp/fixed-necc
                     (vector (updater/fixed 0 value vector)))))
   ("Subgoal 1.1.3"
    :use ((:instance accessor/fixed-of-updater/fixed
                     (%index (coupledp/fixed-witness (updater/fixed 0 value vector)))
                     (index 0)))
    :expand (:free (index value)
                   (coupledp/fixed (updater/fixed index value vector))))
   ("Subgoal 1.1.2"
    :use ((:instance accessor/fixed-of-updater/fixed
                     (%index (coupledp/fixed-witness (updater/fixed 0 (initial-element) vector)))
                     (index 0)))
    :expand (:free (index value)
                   (coupledp/fixed (updater/fixed index value vector))))
   ("Subgoal 1.1.1"
    :use ((:instance accessor/fixed-of-updater/fixed
                     (%index (coupledp/fixed-witness (updater/fixed 0 value vector)))
                     (index 0)))
    :expand (:free (index value)
                   (coupledp/fixed (updater/fixed index value vector))))))

(local
  (in-theory
    (disable coupledp/fixed)))


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

(defthm recognizer/fixed-of-copy/fixed-rec
  (recognizer/fixed (copy/fixed-rec index %vector vector)))

(defthm copy/fixed-rec-of-fixer/fixed-1
  (equal (copy/fixed-rec index (fixer/fixed %vector) vector)
         (copy/fixed-rec index %vector vector)))

(defthm copy/fixed-rec-of-fixer/fixed-2
  (equal (copy/fixed-rec index %vector (fixer/fixed vector))
         (copy/fixed-rec index %vector vector)))

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
  :hints
  (("Goal"
    :cases ((<= (default-length) (nfix %index))
            (< (nfix %index) (nfix index))))))

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

(defthmd copy/fixed-ignores-1
  (equal (copy/fixed %vector vector)
         (copy/fixed (creator) vector))
  :hints
  (("Goal"
    :use ((:instance equal/fixed
                     (%vector (copy/fixed %vector vector))
                     (vector (copy/fixed (creator) vector)))))))

(local
  (defthm copy/fixed-ignores-1-local
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
      :by (:functional-instance copy/fixed-ignores-1)))))

(defthm copy/fixed-of-fixer/fixed-2
  (equal (copy/fixed %vector (fixer/fixed vector))
         (copy/fixed %vector vector)))

(defthm coupledp/fixed-of-copy/fixed
  (implies (coupledp/fixed vector)
           (coupledp/fixed (copy/fixed %vector vector)))
  :hints
  (("Goal"
    :expand ((coupledp/fixed (copy/fixed %vector vector))
             (coupledp/fixed (copy/fixed-rec (default-length)
                                             %vector vector))))))

(defthm accessor/fixed-of-copy/fixed
  (implies (coupledp/fixed vector)
           (equal (accessor/fixed index (copy/fixed %vector vector))
                  (accessor/fixed index vector)))
  :hints
  (("Goal"
    :cases ((< (nfix index) (default-length))))))

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

  (defthm name-constraint
    (symbolp (name))
    :rule-classes :type-prescription)

  (local
    (defun element-export-p (export)
      (declare (xargs :guard t))
      (element-recognizer export)))

  (defthm element-export-p-constraint
    (booleanp (element-export-p export))
    :rule-classes :type-prescription)

  (local
    (defun element-export (value)
      (declare (xargs :guard (element-recognizer value)))
      (element-fixer value)))

  (defthm element-export-p-of-element-export
    (element-export-p (element-export value)))

  (local
    (defun element-import (export value)
      (declare (xargs :guard (and (element-export-p export)
                                  (element-recognizer value)))
               (ignore value))
      (element-fixer export)))

  (defthm element-recognizer-of-element-import
    (element-recognizer (element-import export value)))

  (defthm element-import-when-not-element-export-p
    (implies (not (element-export-p export))
             (equal (element-import export value)
                    (initial-element))))

  (defthm element-import-ignores-value
    (implies (syntaxp (not (and (consp value)
                                (eq (car value) 'initial-element))))
             (equal (element-import export value)
                    (element-import export (initial-element)))))

  (defthm element-export-of-element-import
    (implies (element-export-p export)
             (equal (element-export (element-import export value))
                    export)))

  (defthm element-import-of-element-export
    (implies (element-coupled-p %value)
             (equal (element-import (element-export %value) value)
                    (element-fixer %value)))))


;;;; `EXPORTP-REC'
(defun exportp-rec (list)
  (declare (xargs :guard t))
  (if (atom list)
      (null list)
      (and (element-export-p (car list))
           (exportp-rec (cdr list)))))

(defthm exportp-rec-tp
  (booleanp (exportp-rec list))
  :rule-classes :type-prescription)

(defthm exportp-rec-cr
  (implies (exportp-rec list)
           (true-listp list))
  :rule-classes :compound-recognizer)

(defthm element-export-p-of-nth-when-exportp-rec
  (implies (and (exportp-rec list)
                (natp n)
                (< n (len list)))
           (element-export-p (nth n list))))

(defthm exportp-rec-of-cons
  (equal (exportp-rec (cons value list))
         (and (element-export-p value)
              (exportp-rec list))))

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
  (in-theory
    (disable exportp/resizable)))


;;;; `EXPORT-ACC/RESIZABLE'
(defun export-acc/resizable (index acc vector)
  (declare (xargs :guard (and (natp index)
                              (exportp-rec acc)
                              (recognizer/resizable vector)
                              (<= index (length/resizable vector)))))
  (if (zp index)
      acc
      (let* ((index (1- index))
             (value (accessor/resizable index vector))
             (export (element-export value)))
        (export-acc/resizable index (cons export acc) vector))))

(defthm export-acc/resizable-tp
  (implies (true-listp acc)
           (true-listp (export-acc/resizable index acc vector)))
  :rule-classes :type-prescription)

(defthm exportp-rec-of-export-acc/resizable
  (equal (exportp-rec (export-acc/resizable index acc vector))
         (exportp-rec acc)))

(defthm len-of-export-acc/resizable
  (equal (len (export-acc/resizable index acc vector))
         (+ (nfix index) (len acc))))

(defthm nth-of-export-acc/resizable
  (equal (nth %index (export-acc/resizable index acc vector))
         (if (< (nfix %index) (nfix index))
             (element-export (accessor/resizable %index vector))
             (nth (- (nfix %index) (nfix index)) acc))))

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

(defthm len-of-export/resizable
  (equal (len (export/resizable vector))
         (1+ (length/resizable vector))))

(defthm nth-of-export/resizable
  (equal (nth index (export/resizable vector))
         (cond
           ((zp index)
            (name))
           ((<= index (length/resizable vector))
            (element-export (accessor/resizable (1- index) vector))))))

(local
  (in-theory
    (disable export/resizable)))


;;;; `IMPORT-REC/RESIZABLE'
(defun import-rec/resizable (list index vector)
  (declare (xargs :guard (and (exportp-rec list)
                              (natp index)
                              (recognizer/resizable vector)
                              (<= (+ (len list) index) (length/resizable vector)))))
  (if (endp list)
      (fixer/resizable vector)
      (let* ((value (accessor/resizable index vector))
             (value (element-import (car list) value))
             (vector (updater/resizable index value vector)))
        (import-rec/resizable (cdr list) (1+ (nfix index)) vector))))

(defthm import-rec/resizable-tp
  (true-listp (import-rec/resizable list index vector))
  :rule-classes :type-prescription)

(defthm recognizer/resizable-of-import-rec/resizable
  (recognizer/resizable (import-rec/resizable list index vector)))

(defthm length/resizable-of-import-rec/resizable
  (equal (length/resizable (import-rec/resizable list index vector))
         (length/resizable vector)))

(defthm import-rec/resizable-of-updater/resizable
  (equal (import-rec/resizable list %index (updater/resizable index value vector))
         (if (or (atom list)
                 (< (nfix index) (nfix %index))
                 (<= (+ (len list) (nfix %index)) (nfix index)))
             (updater/resizable index value (import-rec/resizable list %index vector))
             (import-rec/resizable list %index vector))))

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
                            (initial-element))))))

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

(defthm import/resizable-when-not-exportp/resizable
  (implies (not (exportp/resizable export))
           (equal (import/resizable export vector)
                  (creator))))

(defthm import/resizable-ignores-vector
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
             (default-length))))

(defthm accessor/resizable-of-import/resizable
  (equal (accessor/resizable index (import/resizable export vector))
         (if (or (not (exportp/resizable export))
                 (<= (len export) (1+ (nfix index))))
             (initial-element)
             (element-import (nth (1+ (nfix index)) export)
                             (initial-element)))))

(local
  (in-theory
    (disable import/resizable)))


;;;; `EXPORT/RESIZABLE' and `IMPORT/RESIZABLE' Composition Theorems
(with-books (("std/lists/nth" :dir :system))
  (defthm export/resizable-of-import/resizable
    (implies (exportp/resizable export)
             (equal (export/resizable (import/resizable export vector))
                    export))
    :hints
    ((acl2::equal-by-nths-hint)
     ("Goal"
      :in-theory (enable exportp/resizable)
      :expand (:free (n a d)
                     (nth n (cons a d)))))))

(defthm import/resizable-of-export/resizable
  (implies (coupledp/resizable %vector)
           (equal (import/resizable (export/resizable %vector) vector)
                  (fixer/resizable %vector)))
  :hints
  (("Goal"
    :use ((:instance equal/resizable
                     (%vector (import/resizable (export/resizable %vector) vector))
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
  (in-theory
    (disable exportp/fixed)))


;;;; `EXPORT-ACC/FIXED'
(defun export-acc/fixed (index acc vector)
  (declare (xargs :guard (and (natp index)
                              (exportp-rec acc)
                              (recognizer/fixed vector)
                              (<= index (default-length)))))
  (if (zp index)
      acc
      (let* ((index (1- index))
             (value (accessor/fixed index vector))
             (export (element-export value)))
        (export-acc/fixed index (cons export acc) vector))))

(defthm export-acc/fixed-tp
  (implies (true-listp acc)
           (true-listp (export-acc/fixed index acc vector)))
  :rule-classes :type-prescription)

(defthm exportp-rec-of-export-acc/fixed
  (equal (exportp-rec (export-acc/fixed index acc vector))
         (exportp-rec acc)))

(defthm len-of-export-acc/fixed
  (equal (len (export-acc/fixed index acc vector))
         (+ (nfix index) (len acc))))

(defthm nth-of-export-acc/fixed
  (equal (nth %index (export-acc/fixed index acc vector))
         (if (< (nfix %index) (nfix index))
             (element-export (accessor/fixed %index vector))
             (nth (- (nfix %index) (nfix index)) acc))))

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

(defthm len-of-export/fixed
  (equal (len (export/fixed vector))
         (1+ (default-length))))

(defthm nth-of-export/fixed
  (equal (nth index (export/fixed vector))
         (cond
           ((zp index)
            (name))
           ((<= index (default-length))
            (element-export (accessor/fixed (1- index) vector))))))

(local
  (in-theory
    (disable export/fixed)))


;;;; `IMPORT-REC/FIXED'
(defun import-rec/fixed (list index vector)
  (declare (xargs :guard (and (exportp-rec list)
                              (natp index)
                              (recognizer/fixed vector)
                              (<= (+ (len list) index) (default-length)))))
  (if (endp list)
      (fixer/fixed vector)
      (let* ((index (nfix index))
             (value (accessor/fixed index vector))
             (value (element-import (car list) value))
             (vector (updater/fixed index value vector)))
        (import-rec/fixed (cdr list) (1+ index) vector))))

(defthm import-rec/fixed-tp
  (true-listp (import-rec/fixed list index vector))
  :rule-classes :type-prescription)

(defthm recognizer/fixed-of-import-rec/fixed
  (recognizer/fixed (import-rec/fixed list index vector)))

(defthm length/fixed-of-import-rec/fixed
  (equal (length/fixed (import-rec/fixed list index vector))
         (default-length)))

(defthm import-rec/fixed-of-updater/fixed
  (equal (import-rec/fixed list %index (updater/fixed index value vector))
         (if (or (atom list)
                 (< (nfix index) (nfix %index))
                 (<= (+ (len list) (nfix %index)) (nfix index)))
             (updater/fixed index value (import-rec/fixed list %index vector))
             (import-rec/fixed list %index vector))))

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
                            (initial-element))))))

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

(defthm import/fixed-when-not-exportp/fixed
  (implies (not (exportp/fixed export))
           (equal (import/fixed export vector)
                  (creator))))

(defthm import/fixed-ignores-vector
  (implies (exportp/fixed export)
           (equal (import/fixed export vector)
                  (import/fixed export (creator))))
  :rule-classes
  ((:rewrite :corollary
             (implies (and (syntaxp (not (and (consp vector)
                                              (eq (car vector) 'creator))))
                           (exportp/fixed export))
                      (equal (import/fixed export vector)
                             (import/fixed export (creator))))))
  :hints
  (("Goal"
    :in-theory (enable exportp/fixed)
    :use ((:instance equal/fixed
                     (%vector (import/fixed export vector))
                     (vector (import/fixed export (creator))))))))

(defthm length/fixed-of-import/fixed
  (equal (length/fixed (import/fixed export vector))
         (default-length)))

(defthm accessor/fixed-of-import/fixed
  (equal (accessor/fixed index (import/fixed export vector))
         (if (or (not (exportp/fixed export))
                 (<= (default-length) (nfix index)))
             (initial-element)
             (element-import (nth (1+ (nfix index)) export)
                             (initial-element))))
  :hints
  (("Goal"
    :in-theory (enable exportp/fixed))))

(local
  (in-theory
    (disable import/fixed)))


;;;; `EXPORT/FIXED' and `IMPORT/FIXED' Composition Theorems
(with-books (("std/lists/nth" :dir :system))
  (defthm export/fixed-of-import/fixed
    (implies (exportp/fixed export)
             (equal (export/fixed (import/fixed export vector))
                    export))
    :hints
    ((acl2::equal-by-nths-hint)
     ("Goal"
      :in-theory (enable exportp/fixed)))))

(defthm import/fixed-of-export/fixed
  (implies (coupledp/fixed %vector)
           (equal (import/fixed (export/fixed %vector) vector)
                  (fixer/fixed %vector)))
  :hints
  (("Goal"
    :use ((:instance equal/fixed
                     (%vector (import/fixed (export/fixed %vector) vector))
                     (vector (fixer/fixed %vector)))))))
