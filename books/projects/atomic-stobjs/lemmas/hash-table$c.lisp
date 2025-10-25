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


(in-package "LEM-HASH-TABLE$C")
(set-verify-guards-eagerness 2)

#||
(include-book "std/lists/top" :dir :system)
(include-book "std/alists/top" :dir :system)
||#

(include-book "../utilities/with-books")
(local
  (include-book "std"))

(encapsulate (((key-guard *) => *)
              ((element-recognizer *) => *)
              ((default-value) => *))
  (local
    (defun key-guard (key)
      (declare (xargs :guard t))
      (symbolp key)))

  (defthm key-guard-constraint
    (booleanp (key-guard key))
    :rule-classes :type-prescription)

  (local
    (defun element-recognizer (value)
      (declare (xargs :guard t))
      (symbolp value)))

  (defthm element-recognizer-constraint
    (booleanp (element-recognizer value))
    :rule-classes :type-prescription)

  (local
    (defun default-value ()
      (declare (xargs :guard t))
      '||))

  (defthm default-value-constraint
    (element-recognizer (default-value))))

(defun contents-recognizer (contents)
  (declare (xargs :guard t))
  (cond
    ((atom contents)
     t)
    ((consp (car contents))
     (and (element-recognizer (cdar contents))
          (contents-recognizer (cdr contents))))
    (t
     (contents-recognizer (cdr contents)))))

(defun recognizer (hash-table)
  (declare (xargs :guard t))
  (and (true-listp hash-table)
       (>= (cl::length hash-table) 1)
       (contents-recognizer (nth 0 hash-table))
       t))

(defun recognizer/unique (hash-table)
  (declare (xargs :guard t))
  (and (true-listp hash-table)
       (= (cl::length hash-table) 1)
       (contents-recognizer (nth 0 hash-table))
       t))

(defun recognizer/copyable (hash-table)
  (declare (xargs :guard t))
  (and (true-listp hash-table)
       (= (cl::length hash-table) 2)
       (contents-recognizer (nth 0 hash-table))
       t))

(defun creator/unique ()
  (declare (xargs :guard t))
  (list nil))

(defun creator/copyable ()
  (declare (xargs :guard t))
  (list nil nil))

(defun accessor (key hash-table)
  (declare (xargs :guard (and (recognizer hash-table)
                              (key-guard key))))
  (let ((pair (hons-assoc-equal key (nth 0 hash-table))))
    (if pair
        (cdr pair)
        (default-value))))

(defun updater (key value hash-table)
  (declare (xargs :guard (and (recognizer hash-table)
                              (key-guard key)
                              (element-recognizer value))))
  (update-nth 0
              (cons (cons key value)
                    (nth 0 hash-table))
              hash-table))

(defun boundp (key hash-table)
  (declare (xargs :guard (and (recognizer hash-table)
                              (key-guard key))))
  (consp (hons-assoc-equal key (nth 0 hash-table))))

(defun getp (key hash-table)
  (declare (xargs :guard (and (recognizer hash-table)
                              (key-guard key))))
  (mv (accessor key hash-table)
      (boundp key hash-table)))

(defun remover (key hash-table)
  (declare (xargs :guard (and (recognizer hash-table)
                              (key-guard key))))
  (update-nth 0
              (hons-remove-assoc key (nth 0 hash-table))
              hash-table))

(defun count (hash-table)
  (declare (xargs :guard (recognizer hash-table)))
  (count-keys (nth 0 hash-table)))

(defun %clear (hash-table)
  (declare (xargs :guard (recognizer hash-table)))
  (update-nth 0 nil hash-table))

(defun %init (ht-size rehash-size rehash-threshold hash-table)
  (declare (xargs :guard (and (recognizer hash-table)
                              (or (natp ht-size)
                                  (not ht-size))
                              (or (and (rationalp rehash-size)
                                       (<= 1 rehash-size))
                                  (not rehash-size))
                              (or (and (rationalp rehash-threshold)
                                       (<= 0 rehash-threshold)
                                       (<= rehash-threshold 1))
                                  (not rehash-threshold))))
           (ignorable ht-size rehash-size rehash-threshold))
  (update-nth 0 nil hash-table))

(defun keys (hash-table)
  (declare (xargs :guard (recognizer/copyable hash-table)))
  (nth 1 hash-table))

(defun keys-set (set hash-table)
  (declare (xargs :guard (recognizer/copyable hash-table)))
  (update-nth 1 set hash-table))


;;;; `CONTENTS-RECOGNIZER'
(defthm contents-recognizer{type-prescription}
  (booleanp (contents-recognizer contents))
  :rule-classes :type-prescription)

(local
  (defthm contents-recognizer-of-hons-remove-assoc
    (implies (contents-recognizer contents)
             (contents-recognizer (hons-remove-assoc key contents)))))

(local
  (defthm element-recognizer-of-cdr-of-hons-assoc-equal
    (implies (and (contents-recognizer contents)
                  (hons-assoc-equal key contents))
             (element-recognizer (cdr (hons-assoc-equal key contents))))))


;;;; `RECOGNIZER/UNIQUE'
(defthm recognizer/unique{type-prescription}
  (booleanp (recognizer/unique hash-table))
  :rule-classes :type-prescription)

(defthm recognizer/unique{compound-recognizer}
  (implies (recognizer/unique hash-table)
           (and (consp hash-table)
                (true-listp hash-table)))
  :rule-classes :compound-recognizer)

(defthm recognizer/unique-of-creator/unique
  (recognizer/unique (creator/unique)))

(defthm recognizer/unique-of-updater
  (implies (and (recognizer/unique hash-table)
                (element-recognizer value))
           (recognizer/unique (updater key value hash-table))))

(defthm recognizer/unique-of-remover
  (implies (recognizer/unique hash-table)
           (recognizer/unique (remover key hash-table))))

(defthm recognizer/unique-of-%clear
  (implies (recognizer/unique hash-table)
           (recognizer/unique (%clear hash-table))))

(defthm recognizer/unique-of-%init
  (implies (recognizer/unique hash-table)
           (recognizer/unique (%init ht-size rehash-size rehash-threshold hash-table))))


;;;; `RECOGNIZER/COPYABLE'
(defthm recognizer/copyable{type-prescription}
  (booleanp (recognizer/copyable hash-table))
  :rule-classes :type-prescription)

(defthm recognizer/copyable{compound-recognizer}
  (implies (recognizer/copyable hash-table)
           (and (consp hash-table)
                (true-listp hash-table)))
  :rule-classes :compound-recognizer)

(defthm recognizer/copyable-of-creator/copyable
  (recognizer/copyable (creator/copyable)))

(defthm recognizer/copyable-of-updater
  (implies (and (recognizer/copyable hash-table)
                (element-recognizer value))
           (recognizer/copyable (updater key value hash-table))))

(defthm recognizer/copyable-of-remover
  (implies (recognizer/copyable hash-table)
           (recognizer/copyable (remover key hash-table))))

(defthm recognizer/copyable-of-%clear
  (implies (recognizer/copyable hash-table)
           (recognizer/copyable (%clear hash-table))))

(defthm recognizer/copyable-of-%init
  (implies (recognizer/copyable hash-table)
           (recognizer/copyable (%init ht-size rehash-size rehash-threshold hash-table))))

(defthm recognizer/copyable-of-keys-set
  (implies (recognizer/copyable hash-table)
           (recognizer/copyable (keys-set set hash-table))))


;;;; `ACCESSOR'
(defthm element-recognizer-of-accessor/unique
  (implies (recognizer/unique hash-table)
           (element-recognizer (accessor key hash-table))))

(defthm element-recognizer-of-accessor/copyable
  (implies (recognizer/copyable hash-table)
           (element-recognizer (accessor key hash-table))))

(defthm accessor-of-creator/unique
  (equal (accessor key (creator/unique))
         (default-value)))

(defthm accessor-of-creator/copyable
  (equal (accessor key (creator/copyable))
         (default-value)))

(defthm accessor-of-updater-same
  (implies (equal %key key)
           (equal (accessor %key (updater key value hash-table))
                  value)))

(defthm accessor-of-updater-diff
  (implies (not (equal %key key))
           (equal (accessor %key (updater key value hash-table))
                  (accessor %key hash-table))))

(defthm accessor-of-updater
  (equal (accessor %key (updater key value hash-table))
         (if (equal %key key)
             value
             (accessor %key hash-table)))
  :hints
  (("Goal"
    :cases ((equal %key key)))
   ("Subgoal 2"
    :by accessor-of-updater-diff)
   ("Subgoal 1"
    :by accessor-of-updater-same)))

(defthm accessor-when-not-boundp
  (implies (not (boundp key hash-table))
           (equal (accessor key hash-table)
                  (default-value))))

(with-books (("std/alists/hons-remove-assoc" :dir :system))
  (defthm accessor-of-remover-same
    (implies (equal %key key)
             (equal (accessor %key (remover key hash-table))
                    (default-value))))

  (defthm accessor-of-remover-diff
    (implies (not (equal %key key))
             (equal (accessor %key (remover key hash-table))
                    (accessor %key hash-table)))))

(defthm accessor-of-remover
  (equal (accessor %key (remover key hash-table))
         (if (equal %key key)
             (default-value)
             (accessor %key hash-table)))
  :hints
  (("Goal"
    :cases ((equal %key key)))
   ("Subgoal 2"
    :by accessor-of-remover-diff)
   ("Subgoal 1"
    :by accessor-of-remover-same)))

(defthm accessor-of-keys-set
  (equal (accessor key (keys-set set hash-table))
         (accessor key hash-table)))


;;;; `UPDATER'
(defthm updater{type-prescription}/unique
  (implies (recognizer/unique hash-table)
           (and (consp (updater key value hash-table))
                (true-listp (updater key value hash-table))))
  :rule-classes :type-prescription)

(defthm updater{type-prescription}/copyable
  (implies (recognizer/copyable hash-table)
           (and (consp (updater key value hash-table))
                (true-listp (updater key value hash-table))))
  :rule-classes :type-prescription)


;;;; `BOUNDP'
(defthm boundp{type-prescription}
  (booleanp (boundp key hash-table))
  :rule-classes :type-prescription)

(defthm boundp-of-creator/unique
  (not (boundp key (creator/unique))))

(defthm boundp-of-creator/copyable
  (not (boundp key (creator/copyable))))

(defthm boundp-of-updater-same
  (implies (equal %key key)
           (equal (boundp %key (updater key value hash-table))
                  t)))

(defthm boundp-of-updater-diff
  (implies (not (equal %key key))
           (equal (boundp %key (updater key value hash-table))
                  (boundp %key hash-table))))

(defthm boundp-of-updater
  (equal (boundp %key (updater key value hash-table))
         (or (equal %key key)
             (boundp %key hash-table)))
  :hints
  (("Goal"
    :cases ((equal %key key)))
   ("Subgoal 2"
    :by boundp-of-updater-diff)
   ("Subgoal 1"
    :use boundp-of-updater-same)))

(with-books (("std/alists/hons-remove-assoc" :dir :system))
  (defthm boundp-of-remover-same
    (implies (equal %key key)
             (not (boundp %key (remover key hash-table)))))

  (defthm boundp-of-remover-diff
    (implies (not (equal %key key))
             (equal (boundp %key (remover key hash-table))
                    (boundp %key hash-table)))))

(defthm boundp-of-remover
  (equal (boundp %key (remover key hash-table))
         (if (equal %key key)
             nil
             (boundp %key hash-table)))
  :hints
  (("Goal"
    :cases ((equal %key key)))
   ("Subgoal 2"
    :by boundp-of-remover-diff)
   ("Subgoal 1"
    :use boundp-of-remover-same)))

(defthm boundp-of-keys-set
  (equal (boundp key (keys-set set hash-table))
         (boundp key hash-table)))


;;;; `GETP'
(defthm getp{type-prescription}
  (and (consp (getp key hash-table))
       (true-listp (getp key hash-table)))
  :rule-classes :type-prescription)

(defthm getp{rewrite}
  (mv-let (v0 v1)
          (getp key hash-table)
    (and (equal v0 (accessor key hash-table))
         (equal v1 (boundp key hash-table)))))


;;;; `REMOVER'
(defthm remover{type-prescription}/unique
  (implies (recognizer/unique hash-table)
           (and (consp (remover key hash-table))
                (true-listp (remover key hash-table))))
  :rule-classes :type-prescription)

(defthm remover{type-prescription}/copyable
  (implies (recognizer/copyable hash-table)
           (and (consp (remover key hash-table))
                (true-listp (remover key hash-table))))
  :rule-classes :type-prescription)

(defthm remover-of-creator/unique
  (equal (remover key (creator/unique))
         (creator/unique)))

(defthm remover-of-creator/copyable
  (equal (remover key (creator/copyable))
         (creator/copyable)))

(defthm remover-of-updater-same
  (implies (equal %key key)
           (equal (remover %key (updater key value hash-table))
                  (remover %key hash-table))))

(defthm remover-of-updater-diff
  (implies (not (equal %key key))
           (equal (remover %key (updater key value hash-table))
                  (updater key value (remover %key hash-table)))))

(defthm remover-of-updater
  (equal (remover %key (updater key value hash-table))
         (if (equal %key key)
             (remover %key hash-table)
             (updater key value (remover %key hash-table))))
  :hints
  (("Goal"
    :cases ((equal %key key)))
   ("Subgoal 2"
    :by remover-of-updater-diff)
   ("Subgoal 1"
    :by remover-of-updater-same)))

(with-books (("std/alists/hons-remove-assoc" :dir :system))
  (defthm remover-of-remover-same
    (implies (equal %key key)
             (equal (remover %key (remover key hash-table))
                    (remover %key hash-table))))

  (defthm remover-of-remover-diff
    (implies (not (equal %key key))
             (equal (remover %key (remover key hash-table))
                    (remover key (remover %key hash-table))))
    :rule-classes
    ((:rewrite :loop-stopper ((%key key remover))))))


;;;; `COUNT'
(defthm count{type-prescription}
  (natp (count hash-table))
  :rule-classes :type-prescription)

(defthm count-of-creator/unique
  (equal (count (creator/unique)) 0))

(defthm count-of-creator/copyable
  (equal (count (creator/copyable)) 0))

(defthm count-of-updater-when-boundp
  (implies (boundp key hash-table)
           (equal (count (updater key value hash-table))
                  (count hash-table))))

(defthm count-of-updater-when-not-boundp
  (implies (not (boundp key hash-table))
           (equal (count (updater key value hash-table))
                  (1+ (count hash-table)))))

(defthm count-of-updater
  (equal (count (updater key value hash-table))
         (if (boundp key hash-table)
             (count hash-table)
             (1+ (count hash-table))))
  :hints
  (("Goal"
    :cases ((boundp key hash-table)))
   ("Subgoal 2"
    :by count-of-updater-when-not-boundp)
   ("Subgoal 1"
    :by count-of-updater-when-boundp)))

(defthm count-when-boundp
  (implies (boundp key hash-table)
           (posp (count hash-table)))
  :rule-classes :type-prescription)

(defthm count-of-remover-when-boundp
  (implies (boundp key hash-table)
           (equal (count (remover key hash-table))
                  (1- (count hash-table)))))

(defthm count-of-remover-when-not-boundp
  (implies (not (boundp key hash-table))
           (equal (count (remover key hash-table))
                  (count hash-table))))

(defthm count-of-remover
  (equal (count (remover key hash-table))
         (if (boundp key hash-table)
             (1- (count hash-table))
             (count hash-table)))
  :hints
  (("Goal"
    :cases ((boundp key hash-table)))
   ("Subgoal 2"
    :by count-of-remover-when-not-boundp)
   ("Subgoal 1"
    :by count-of-remover-when-boundp)))

(defthm count-of-keys-set
  (equal (count (keys-set set hash-table))
         (count hash-table)))


;;;; `%CLEAR'
(defthm %clear{type-prescription}/unique
  (implies (recognizer/unique hash-table)
           (and (consp (%clear hash-table))
                (true-listp (%clear hash-table))))
  :rule-classes :type-prescription)

(defthm %clear{type-prescription}/copyable
  (implies (recognizer/copyable hash-table)
           (and (consp (%clear hash-table))
                (true-listp (%clear hash-table))))
  :rule-classes :type-prescription)

(with-books (("std/lists/len" :dir :system)
             ("std/lists/nth" :dir :system))
  (defthm %clear{rewrite}/unique
    (implies (recognizer/unique hash-table)
             (equal (%clear hash-table)
                    (creator/unique))))

  (defthm %clear{rewrite}/copyable
    (implies (recognizer/copyable hash-table)
             (equal (%clear hash-table)
                    (keys-set (keys hash-table) (creator/copyable))))
    :hints
    ((acl2::equal-by-nths-hint))))


;;;; `%INIT'
(defthm %init{type-prescription}/unique
  (implies (recognizer/unique hash-table)
           (and (consp (%init ht-size rehash-size rehash-threshold hash-table))
                (true-listp (%init ht-size rehash-size rehash-threshold hash-table))))
  :rule-classes :type-prescription)

(defthm %init{type-prescription}/copyable
  (implies (recognizer/copyable hash-table)
           (and (consp (%init ht-size rehash-size rehash-threshold hash-table))
                (true-listp (%init ht-size rehash-size rehash-threshold hash-table))))
  :rule-classes :type-prescription)

(with-books (("std/lists/len" :dir :system)
             ("std/lists/nth" :dir :system))
  (defthm %init{rewrite}/unique
    (implies (recognizer/unique hash-table)
             (equal (%init ht-size rehash-size rehash-threshold hash-table)
                    (creator/unique))))

  (defthm %init{rewrite}/copyable
    (implies (recognizer/copyable hash-table)
             (equal (%init ht-size rehash-size rehash-threshold hash-table)
                    (keys-set (keys hash-table) (creator/copyable))))
    :hints
    ((acl2::equal-by-nths-hint))))


;;;; `KEYS'
(defthm keys-of-creator/unique
  (not (keys (creator/unique))))

(defthm keys-of-creator/copyable
  (not (keys (creator/copyable))))

(defthm keys-of-updater
  (equal (keys (updater key value hash-table))
         (keys hash-table)))

(defthm keys-of-remover
  (equal (keys (remover key hash-table))
         (keys hash-table)))

(defthm keys-of-keys-set
  (equal (keys (keys-set set hash-table))
         set))


;;;; `KEYS-SET'
(defthm keys-set{type-prescription}
  (implies (recognizer/copyable hash-table)
           (and (consp (keys-set set hash-table))
                (true-listp (keys-set set hash-table))))
  :rule-classes :type-prescription)

(with-books (("std/lists/update-nth" :dir :system))
  (defthm keys-set-of-updater
    (equal (keys-set set (updater key value hash-table))
           (updater key value (keys-set set hash-table))))

  (defthm keys-set-of-remover
    (equal (keys-set set (remover key hash-table))
           (remover key (keys-set set hash-table))))

  (defthm keys-set-of-keys-set
    (equal (keys-set %set (keys-set set hash-table))
           (keys-set %set hash-table))))


;;;; `FIXER/UNIQUE'
(defun fixer/unique (hash-table)
  (declare (xargs :guard (recognizer/unique hash-table)))
  (if (recognizer/unique hash-table)
      hash-table
      (creator/unique)))

(defthm fixer/unique{type-prescription}
  (and (consp (fixer/unique hash-table))
       (true-listp (fixer/unique hash-table)))
  :rule-classes :type-prescription)

(defthm recognizer/unique-of-fixer/unique
  (recognizer/unique (fixer/unique hash-table)))

(defthm fixer/unique-when-recognizer/unique
  (implies (recognizer/unique hash-table)
           (equal (fixer/unique hash-table)
                  hash-table)))

(defthm fixer/unique-when-not-recognizer/unique
  (implies (not (recognizer/unique hash-table))
           (equal (fixer/unique hash-table)
                  (creator/unique))))


;;;; `FIXER/COPYABLE'
(defun fixer/copyable (hash-table)
  (declare (xargs :guard (recognizer/copyable hash-table)))
  (if (recognizer/copyable hash-table)
      hash-table
      (creator/copyable)))

(defthm fixer/copyable{type-prescription}
  (and (consp (fixer/copyable hash-table))
       (true-listp (fixer/copyable hash-table)))
  :rule-classes :type-prescription)

(defthm recognizer/copyable-of-fixer/copyable
  (recognizer/copyable (fixer/copyable hash-table)))

(defthm fixer/copyable-when-recognizer/copyable
  (implies (recognizer/copyable hash-table)
           (equal (fixer/copyable hash-table)
                  hash-table)))

(defthm fixer/copyable-when-not-recognizer/copyable
  (implies (not (recognizer/copyable hash-table))
           (equal (fixer/copyable hash-table)
                  (creator/copyable))))


;;;; `CLEAR'
(defun clear (hash-table)
  (declare (xargs :guard (recognizer/copyable hash-table)))
  (let* ((hash-table (fixer/copyable hash-table))
         (hash-table (keys-set '() hash-table)))
    (%clear hash-table)))

(defthm clear{type-prescription}
  (implies (recognizer/copyable hash-table)
           (and (consp (clear hash-table))
                (true-listp (clear hash-table))))
  :rule-classes :type-prescription)

(with-books (("std/lists/len" :dir :system)
             ("std/lists/update-nth" :dir :system))
  (defthm clear{rewrite}
    (implies (recognizer/copyable hash-table)
             (equal (clear hash-table)
                    (creator/copyable)))))


;;;; `INIT'
(defun init (ht-size rehash-size rehash-threshold hash-table)
  (declare (xargs :guard (and (recognizer/copyable hash-table)
                              (or (natp ht-size)
                                  (not ht-size))
                              (or (and (rationalp rehash-size)
                                       (<= 1 rehash-size))
                                  (not rehash-size))
                              (or (and (rationalp rehash-threshold)
                                       (<= 0 rehash-threshold)
                                       (<= rehash-threshold 1))
                                  (not rehash-threshold)))))
  (let* ((hash-table (fixer/copyable hash-table))
         (hash-table (keys-set '() hash-table)))
    (%init ht-size rehash-size rehash-threshold hash-table)))

(defthm init{type-prescription}
  (implies (recognizer/copyable hash-table)
           (and (consp (init ht-size rehash-size rehash-threshold hash-table))
                (true-listp (init ht-size rehash-size rehash-threshold hash-table))))
  :rule-classes :type-prescription)

(with-books (("std/lists/len" :dir :system)
             ("std/lists/update-nth" :dir :system))
  (defthm init{rewrite}
    (implies (recognizer/copyable hash-table)
             (equal (init ht-size rehash-size rehash-threshold hash-table)
                    (creator/copyable)))))
