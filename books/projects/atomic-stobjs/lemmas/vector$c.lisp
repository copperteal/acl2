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

#||
(include-book "std/lists/top" :dir :system)
||#

(include-book "../utilities/with-books")
(local
  (include-book "std"))

(encapsulate (((default-length) => *)
              ((element-recognizer *) => *)
              ((initial-element) => *))
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
    (element-recognizer (initial-element))))

(defun contents-recognizer (contents)
  (declare (xargs :guard t))
  (if (atom contents)
      (equal contents nil)
      (and (element-recognizer (car contents))
           (contents-recognizer (cdr contents)))))

(defun recognizer/resizable (vector)
  (declare (xargs :guard t))
  (and (true-listp vector)
       (= (cl:length vector) 1)
       (contents-recognizer (nth 0 vector))
       t))

(defun recognizer/fixed (vector)
  (declare (xargs :guard t))
  (and (true-listp vector)
       (= (cl:length vector) 1)
       (contents-recognizer (nth 0 vector))
       (equal (len (nth 0 vector)) (default-length))
       t))

(defun length/resizable (vector)
  (declare (xargs :guard (recognizer/resizable vector)))
  (len (nth 0 vector)))

(defun length/fixed (vector)
  (declare (xargs :guard (recognizer/fixed vector))
           (ignore vector))
  (default-length))

(defun resizer/resizable (length vector)
  (declare (xargs :guard (and (natp length)
                              (recognizer/resizable vector))))
  (update-nth 0
              (resize-list (nth 0 vector)
                           length
                           (initial-element))
              vector))

(defun resizer/fixed (length vector)
  (declare (xargs :guard (and (natp length)
                              (recognizer/fixed vector)))
           (ignore length))
  vector)

(defun creator ()
  (declare (xargs :guard t))
  (list (make-list (default-length)
                   :initial-element (initial-element))))

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
(defthm contents-recognizer{type-prescription}
  (booleanp (contents-recognizer contents))
  :rule-classes :type-prescription
  :hints
  (("Goal"
    :induct (len contents))))

(defthm contents-recognizer{compound-recognizer}
  (implies (contents-recognizer contents)
           (true-listp contents))
  :rule-classes :compound-recognizer)

(local
  (defthm contents-recognizer-of-make-list-ac
    (equal (contents-recognizer (make-list-ac size element acc))
           (and (or (zp size)
                    (element-recognizer element))
                (contents-recognizer acc)))))

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
  (defthm resize-list-when-contents-recognizer
    (implies (contents-recognizer contents)
             (equal (resize-list contents
                                 (len contents)
                                 (initial-element))
                    contents))))

(local
  (defthm element-recognizer-of-nth
    (implies (and (natp index)
                  (< index (len contents))
                  (contents-recognizer contents))
             (element-recognizer (nth index contents)))))


;;;; `RECOGNIZER/RESIZABLE'
(defthm recognizer/resizable{type-prescription}
  (booleanp (recognizer/resizable vector))
  :rule-classes :type-prescription)

(defthm recognizer/resizable{compound-recognizer}
  (implies (recognizer/resizable vector)
           (and (consp vector)
                (true-listp vector)))
  :rule-classes :compound-recognizer)

(defthm recognizer/resizable-of-creator
  (recognizer/resizable (creator)))

(defthm recognizer/resizable-of-resizer/resizable
  (implies (recognizer/resizable vector)
           (recognizer/resizable (resizer/resizable length vector))))

(defthm recognizer/resizable-of-updater
  (implies (and (natp index)
                (< index (length/resizable vector))
                (element-recognizer value)
                (recognizer/resizable vector))
           (recognizer/resizable (updater index value vector))))


;;;; `RECOGNIZER/FIXED'
(defthm recognizer/fixed{type-prescription}
  (booleanp (recognizer/fixed vector))
  :rule-classes :type-prescription)

(defthm recognizer/fixed{compound-recognizer}
  (implies (recognizer/fixed vector)
           (and (consp vector)
                (true-listp vector)))
  :rule-classes :compound-recognizer)

(defthm recognizer/fixed-of-creator
  (recognizer/fixed (creator)))

(defthm recognizer/fixed-of-updater
  (implies (and (natp index)
                (< index (default-length))
                (element-recognizer value)
                (recognizer/fixed vector))
           (recognizer/fixed (updater index value vector))))


;;;; `LENGTH/RESIZABLE'
(defthm length/resizable{type-prescription}
  (natp (length/resizable vector))
  :rule-classes :type-prescription)

(defthm length/resizable-of-creator
  (equal (length/resizable (creator))
         (default-length)))

(with-books (("std/lists/resize-list" :dir :system))
  (defthm length/resizable-of-resizer/resizable
    (implies (natp length)
             (equal (length/resizable (resizer/resizable length vector))
                    length))))

(defthm length/resizable-of-updater
  (implies (and (natp index)
                (< index (length/resizable vector)))
           (equal (length/resizable (updater index value vector))
                  (length/resizable vector))))


;;;; `LENGTH/FIXED'
(defthm length/fixed{type-prescription}
  (natp (length/fixed vector))
  :rule-classes :type-prescription)

(defthm length/fixed{rewrite}
  (equal (length/fixed vector)
         (default-length)))


;;;; `RESIZER/RESIZABLE'
(defthm resizer/resizable{type-prescription}
  (implies (recognizer/resizable vector)
           (and (true-listp (resizer/resizable length vector))
                (consp (resizer/resizable length vector))))
  :rule-classes :type-prescription)

(with-books (("std/lists/repeat" :dir :system))
  (defthm resizer/resizable-of-creator
    (implies (equal length (default-length))
             (equal (resizer/resizable length (creator))
                    (creator)))))

(defthm resizer/resizable-of-length/resizable-free
  (implies (and (equal length (length/resizable vector))
                (recognizer/resizable vector))
           (equal (resizer/resizable length vector)
                  vector)))

(defthm resizer/resizable-of-length/resizable
  (implies (recognizer/resizable vector)
           (equal (resizer/resizable (length/resizable vector) vector)
                  vector)))

(with-books (("std/lists/resize-list" :dir :system))
  (defthm resizer/resizable-of-resizer/resizable
    (implies (and (natp length0)
                  (natp length1)
                  (or (<= length0 length1)
                      (<= (length/resizable vector) length1))
                  (recognizer/resizable vector))
             (equal (resizer/resizable length0 (resizer/resizable length1 vector))
                    (resizer/resizable length0 vector)))
    :hints
    (("Goal"
      :use ((:instance acl2::resize-list-of-resize-list
                       (lst (car vector))
                       (n length1)
                       (d (initial-element))
                       (m length0)
                       (e (initial-element))))))))

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

(defthm resizer/resizable-of-updater
  (implies (and (natp index)
                (natp length)
                (< index (length/resizable vector)))
           (equal (resizer/resizable length (updater index value vector))
                  (if (< index length)
                      (updater index value (resizer/resizable length vector))
                      (resizer/resizable length vector)))))


;;;; `RESIZER/FIXED'
(defthm resizer/fixed{type-prescription}
  (implies (recognizer/fixed vector)
           (and (true-listp (resizer/fixed length vector))
                (consp (resizer/fixed length vector))))
  :rule-classes :type-prescription)

(defthm resizer/fixed{rewrite}
  (equal (resizer/fixed length vector)
         vector))


;;;; `ACCESSOR'
(defthm element-recognizer-of-accessor/resizable
  (implies (and (natp index)
                (< index (length/resizable vector))
                (recognizer/resizable vector))
           (element-recognizer (accessor index vector))))

(defthm element-recognizer-of-accessor/fixed
  (implies (and (natp index)
                (< index (default-length))
                (recognizer/fixed vector))
           (element-recognizer (accessor index vector))))

(with-books (("std/lists/nth" :dir :system))
  (defthm accessor-of-creator
    (implies (and (natp index)
                  (< index (default-length)))
             (equal (accessor index (creator))
                    (initial-element)))))

(with-books (("std/lists/resize-list" :dir :system))
  (defthm accessor-of-resizer/resizable-inner
    (implies (and (natp index)
                  (natp length)
                  (< index length)
                  (< index (length/resizable vector)))
             (equal (accessor index (resizer/resizable length vector))
                    (accessor index vector)))))

(with-books (("std/lists/resize-list" :dir :system)
             ("std/lists/nth" :dir :system))
  (defthm accessor-of-resizer/resizable-outer
    (implies (and (natp index)
                  (natp length)
                  (< index length)
                  (<= (length/resizable vector) index))
             (equal (accessor index (resizer/resizable length vector))
                    (initial-element)))))

(defthm accessor-of-resizer/resizable
  (implies (and (natp index)
                (natp length)
                (< index length))
           (equal (accessor index (resizer/resizable length vector))
                  (if (< index (length/resizable vector))
                      (accessor index vector)
                      (initial-element))))
  :hints
  (("Goal"
    :cases ((< index (length/resizable vector)))
    :in-theory (disable accessor-of-resizer/resizable-outer
                        accessor-of-resizer/resizable-inner))
   ("Subgoal 2"
    :use (:instance accessor-of-resizer/resizable-outer))
   ("Subgoal 1"
    :use (:instance accessor-of-resizer/resizable-inner))))

(defthm accessor-of-updater-same
  (implies (equal index0 index1)
           (equal (accessor index0 (updater index1 value vector))
                  value)))

(defthm accessor-of-updater-diff
  (implies (and (not (equal index0 index1))
                (natp index0)
                (natp index1))
           (equal (accessor index0 (updater index1 value vector))
                  (accessor index0 vector))))

(defthm accessor-of-updater
  (implies (and (natp index0)
                (natp index1))
           (equal (accessor index0 (updater index1 value vector))
                  (if (equal index0 index1)
                      value
                      (accessor index0 vector)))))


;;;; `UPDATER'
(defthm updater{type-prescription}/resizable
  (implies (recognizer/resizable vector)
           (and (true-listp (updater index value vector))
                (consp (updater index value vector))))
  :rule-classes :type-prescription)

(defthm updater{type-prescription}/fixed
  (implies (recognizer/fixed vector)
           (and (true-listp (updater index value vector))
                (consp (updater index value vector))))
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

(defthm updater-of-resizer/resizable
  (implies (and (natp index)
                (natp length)
                (< index length)
                (equal value (if (< index (length/resizable vector))
                                 (accessor index vector)
                                 (initial-element))))
           (equal (updater index value (resizer/resizable length vector))
                  (resizer/resizable length vector))))

(with-books (("std/lists/update-nth" :dir :system)
             ("std/lists/repeat" :dir :system))
  (defthm updater-of-accessor-free/resizable
    (implies (and (equal value (accessor index vector))
                  (natp index)
                  (< index (length/resizable vector))
                  (recognizer/resizable vector))
             (equal (updater index value vector)
                    vector)))

  (defthm updater-of-accessor-free/fixed
    (implies (and (equal value (accessor index vector))
                  (natp index)
                  (< index (default-length))
                  (recognizer/fixed vector))
             (equal (updater index value vector)
                    vector)))

  (defthm updater-of-accessor/resizable
    (implies (and (equal index0 index1)
                  (natp index0)
                  (< index0 (length/resizable vector))
                  (recognizer/resizable vector))
             (equal (updater index0 (accessor index1 vector) vector)
                    vector)))

  (defthm updater-of-accessor/fixed
    (implies (and (equal index0 index1)
                  (natp index0)
                  (< index0 (default-length))
                  (recognizer/fixed vector))
             (equal (updater index0 (accessor index1 vector) vector)
                    vector)))

  (defthm updater-of-updater-same
    (implies (equal index0 index1)
             (equal (updater index0 value0 (updater index1 value1 vector))
                    (updater index0 value0 vector)))
    :hints
    (("Goal"
      :in-theory (disable acl2::update-nth-of-update-nth-same)
      :use ((:instance acl2::update-nth-of-update-nth-same
                       (n index0)
                       (v1 value0)
                       (v2 value1)
                       (x (car vector)))))))

  (defthm updater-of-updater-diff
    (implies (and (not (equal index0 index1))
                  (natp index0)
                  (natp index1))
             (equal (updater index0 value0 (updater index1 value1 vector))
                    (updater index1 value1 (updater index0 value0 vector))))
    :hints
    (("Goal"
      :in-theory (disable acl2::update-nth-of-update-nth-diff)
      :use ((:instance acl2::update-nth-of-update-nth-diff
                       (n1 index0)
                       (n2 index1)
                       (v1 value0)
                       (v2 value1)
                       (x (car vector))))))))


;;;; `FIXER'
(defun fixer/resizable (vector)
  (declare (xargs :guard (recognizer/resizable vector)))
  (if (recognizer/resizable vector)
      vector
      (creator)))

(defthm fixer/resizable{type-prescription}
  (and (true-listp (fixer/resizable vector))
       (consp (fixer/resizable vector)))
  :rule-classes :type-prescription)

(defun fixer/fixed (vector)
  (declare (xargs :guard (recognizer/fixed vector)))
  (if (recognizer/fixed vector)
      vector
      (creator)))

(defthm fixer/fixed{type-prescription}
  (and (true-listp (fixer/fixed vector))
       (consp (fixer/fixed vector)))
  :rule-classes :type-prescription)

(defthm recognizer/resizable-of-fixer/resizable
  (recognizer/resizable (fixer/resizable vector)))

(defthm recognizer/fixed-of-fixer/fixed
  (recognizer/fixed (fixer/fixed vector)))

(defthm fixer/resizable-when-recognizer/resizable
  (implies (recognizer/resizable vector)
           (equal (fixer/resizable vector)
                  vector)))

(defthm fixer/fixed-when-recognizer/fixed
  (implies (recognizer/fixed vector)
           (equal (fixer/fixed vector)
                  vector)))

(defthm fixer/resizable-when-not-recognizer/resizable
  (implies (not (recognizer/resizable vector))
           (equal (fixer/resizable vector)
                  (creator))))

(defthm fixer/fixed-when-not-recognizer/fixed
  (implies (not (recognizer/fixed vector))
           (equal (fixer/fixed vector)
                  (creator))))
