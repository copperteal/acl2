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


(in-package "LEM-HASH-TABLE$A")
(set-verify-guards-eagerness 2)

(include-book "std/osets/top" :dir :system)
(include-book "std/omaps/core" :dir :system)


;;;; Key Constraints
(encapsulate (((key-recognizer *) => *)
              ((default-key) => *))
  (local
    (defun key-recognizer (key)
      (declare (xargs :guard t))
      (symbolp key)))

  (defthm key-recognizer-tp
    (booleanp (key-recognizer key))
    :rule-classes :type-prescription)

  (local
    (defun default-key ()
      (declare (xargs :guard t))
      '||))

  (defthm key-recognizer-of-default-key
    (key-recognizer (default-key))))

(defun key-fixer (key)
  (declare (xargs :guard t))
  (if (key-recognizer key)
      key
      (default-key)))

(local
  (defthm key-recognizer-of-key-fixer
    (key-recognizer (key-fixer key))))

(local
  (defthm key-fixer-when-key-recognizer
    (implies (key-recognizer key)
             (equal (key-fixer key)
                    key))))

(local
  (defthm key-fixer-when-not-key-recognizer
    (implies (not (key-recognizer key))
             (equal (key-fixer key)
                    (default-key)))))

(defun key-equiv (%key key)
  (declare (xargs :guard t))
  (equal (key-fixer %key)
         (key-fixer key)))

(defequiv key-equiv)

(local
  (defcong key-equiv equal (key-fixer key) 1))

(local
  (defthm key-fixer-mod-key-equiv
    (key-equiv (key-fixer key) key)))


;;;; Value Constraints
(encapsulate (((val-recognizer *) => *)
              ((default-val) => *))
  (local
    (defun val-recognizer (val)
      (declare (xargs :guard t))
      (symbolp val)))

  (defthm val-recognizer-tp
    (booleanp (val-recognizer val))
    :rule-classes :type-prescription)

  (local
    (defun default-val ()
      (declare (xargs :guard t))
      '||))

  (defthm val-recognizer-of-default-val
    (val-recognizer (default-val))))

(defun val-fixer (val)
  (declare (xargs :guard t))
  (if (val-recognizer val)
      val
      (default-val)))

(local
  (defthm val-recognizer-of-val-fixer
    (val-recognizer (val-fixer val))))

(local
  (defthm val-fixer-when-val-recognizer
    (implies (val-recognizer val)
             (equal (val-fixer val)
                    val))))

(local
  (defthm val-fixer-when-not-val-recognizer
    (implies (not (val-recognizer val))
             (equal (val-fixer val)
                    (default-val)))))

(defun val-equiv (%val val)
  (declare (xargs :guard t))
  (equal (val-fixer %val)
         (val-fixer val)))

(defequiv val-equiv)

(local
  (defcong val-equiv equal (val-fixer val) 1))

(local
  (defthm val-fixer-mod-val-equiv
    (val-equiv (val-fixer val) val)))

(local
  (in-theory
    (disable key-fixer
             val-fixer)))


;;;; Unique Definitions
(defun recognizer/unique (hash-table)
  (declare (xargs :guard t))
  (if (consp hash-table)
      (and (consp (car hash-table))
           (key-recognizer (caar hash-table))
           (val-recognizer (cdar hash-table))
           (or (null (cdr hash-table))
               (and (consp (cdr hash-table))
                    (consp (cadr hash-table))
                    (<< (caar hash-table) (caadr hash-table))
                    (recognizer/unique (cdr hash-table)))))
      (null hash-table)))

(defun-nx creator/unique ()
  (declare (xargs :guard t))
  '())

(defun fixer/unique (hash-table)
  (declare (xargs :guard (recognizer/unique hash-table)))
  (if (recognizer/unique hash-table)
      hash-table
      (creator/unique)))

(defun equiv/unique (%hash-table hash-table)
  (declare (xargs :guard (and (recognizer/unique %hash-table)
                              (recognizer/unique hash-table))))
  (equal (fixer/unique %hash-table)
         (fixer/unique hash-table)))

(defun accessor/unique (key hash-table)
  (declare (xargs :guard (and (key-recognizer key)
                              (recognizer/unique hash-table))
                  :measure (len hash-table)))
  (let ((key (key-fixer key))
        (hash-table (fixer/unique hash-table)))
    (cond
      ((or (endp hash-table)
           (<< key (caar hash-table)))
       (default-val))
      ((equal key (caar hash-table))
       (val-fixer (cdar hash-table)))
      (t
       (accessor/unique key (cdr hash-table))))))

(defun updater/unique (key val hash-table)
  (declare (xargs :guard (and (key-recognizer key)
                              (val-recognizer val)
                              (recognizer/unique hash-table))
                  :measure (len hash-table)))
  (let ((key (key-fixer key))
        (val (val-fixer val))
        (hash-table (fixer/unique hash-table)))
    (cond
      ((endp hash-table)
       (acons key val nil))
      ((<< key (caar hash-table))
       (acons key val hash-table))
      ((equal key (caar hash-table))
       (acons key val (cdr hash-table)))
      (t
       (cons (car hash-table)
             (updater/unique key val (cdr hash-table)))))))

(defun boundp/unique (key hash-table)
  (declare (xargs :guard (and (key-recognizer key)
                              (recognizer/unique hash-table))
                  :measure (len hash-table)))
  (let ((key (key-fixer key))
        (hash-table (fixer/unique hash-table)))
    (cond
      ((or (endp hash-table)
           (<< key (caar hash-table)))
       'nil)
      ((equal key (caar hash-table))
       't)
      (t
       (boundp/unique key (cdr hash-table))))))

(defun getp/unique (key hash-table)
  (declare (xargs :guard (and (key-recognizer key)
                              (recognizer/unique hash-table))))
  (let ((key (key-fixer key))
        (hash-table (fixer/unique hash-table)))
    (mv (accessor/unique key hash-table)
        (boundp/unique key hash-table))))

(defun remover/unique (key hash-table)
  (declare (xargs :guard (and (key-recognizer key)
                              (recognizer/unique hash-table))
                  :measure (len hash-table)))
  (let ((key (key-fixer key))
        (hash-table (fixer/unique hash-table)))
    (cond
      ((endp hash-table)
       '())
      ((<< key (caar hash-table))
       hash-table)
      ((equal key (caar hash-table))
       (cdr hash-table))
      (t
       (cons (car hash-table)
             (remover/unique key (cdr hash-table)))))))

(defun count/unique (hash-table)
  (declare (xargs :guard (recognizer/unique hash-table)))
  (let ((hash-table (fixer/unique hash-table)))
    (if (consp hash-table)
        (1+ (count/unique (cdr hash-table)))
        0)))

(defun clear/unique (hash-table)
  (declare (xargs :guard (recognizer/unique hash-table))
           (ignore hash-table))
  (creator/unique))

(defun init/unique (ht-size rehash-size rehash-threshold hash-table)
  (declare (xargs :guard (and (recognizer/unique hash-table)
                              (or (natp ht-size)
                                  (not ht-size))
                              (or (and (rationalp rehash-size)
                                       (<= 1 rehash-size))
                                  (not rehash-size))
                              (or (and (rationalp rehash-threshold)
                                       (<= 0 rehash-threshold)
                                       (<= rehash-threshold 1))
                                  (not rehash-threshold))))
           (ignore ht-size rehash-size rehash-threshold hash-table))
  (creator/unique))


;;;; `OMAP' Definitions
(local
  (defthm recognizer/unique-def
    (equal (recognizer/unique map)
           (and (omap::mapp map)
                (or (omap::emptyp map)
                    (mv-let (key val)
                            (omap::head map)
                      (and (key-recognizer key)
                           (val-recognizer val)
                           (recognizer/unique (omap::tail map)))))))
    :rule-classes
    ((:definition :controller-alist ((recognizer/unique t))))
    :hints
    (("Goal"
      :in-theory (enable omap::mapp
                         omap::mfix
                         omap::emptyp
                         omap::head
                         omap::tail)))))

(local
  (defthm mapp-when-recognizer/unique
    (implies (recognizer/unique map)
             (omap::mapp map))))

(local
  (defthm recognizer/unique-when-emptyp
    (implies (omap::emptyp map)
             (equal (recognizer/unique map)
                    (omap::mapp map)))))

(local
  (defthm key-recognizer-when-not-emptyp
    (implies (and (not (omap::emptyp map))
                  (recognizer/unique map))
             (key-recognizer (mv-nth 0 (omap::head map))))))

(local
  (defthm val-recognizer-when-not-emptyp
    (implies (and (not (omap::emptyp map))
                  (recognizer/unique map))
             (val-recognizer (mv-nth 1 (omap::head map))))))

(local
  (defthm recognizer/unique-of-tail
    (implies (and (not (omap::emptyp map))
                  (recognizer/unique map))
             (recognizer/unique (omap::tail map)))))

(local
  (defthm accessor/unique-def
    (equal (accessor/unique key map)
           (let ((map (fixer/unique map)))
             (cond
               ((omap::emptyp map)
                (default-val))
               ((key-equiv key (omap::head-key map))
                (val-fixer (omap::head-val map)))
               (t
                (accessor/unique key (omap::tail map))))))
    :rule-classes
    ((:definition :controller-alist ((accessor/unique nil t))))
    :hints
    (("Goal"
      :in-theory (enable omap::mapp
                         omap::mfix
                         omap::emptyp
                         omap::head
                         omap::tail)))))

(local
  (defthm accessor/unique-when-emptyp
    (implies (omap::emptyp map)
             (equal (accessor/unique key map)
                    (default-val)))))

(local
  (defthm accessor/unique-when-hit
    (implies (and (not (omap::emptyp map))
                  (recognizer/unique map)
                  (key-equiv (double-rewrite key) (omap::head-key map)))
             (equal (accessor/unique key map)
                    (omap::head-val map)))))

(local
  (defthm accessor/unique-when-small
    (implies (<< (key-fixer (double-rewrite key)) (omap::head-key map))
             (equal (accessor/unique key map)
                    (default-val)))
    :hints
    (("Goal"
      :in-theory (enable key-fixer
                         omap::head
                         omap::tail
                         omap::emptyp
                         omap::mapp)))))

(local
  (defthm updater/unique-def
    (equal (updater/unique key val map)
           (let ((key (key-fixer (double-rewrite key)))
                 (val (val-fixer (double-rewrite val)))
                 (map (fixer/unique map)))
             (omap::update key val map)))
    :rule-classes :definition
    :hints
    (("Goal"
      :in-theory (enable omap::mapp
                         omap::mfix
                         omap::emptyp
                         omap::head
                         omap::tail
                         omap::update)))))

(local
  (defthm boundp/unique-def
    (equal (boundp/unique key map)
           (let ((key (key-fixer (double-rewrite key)))
                 (map (fixer/unique map)))
             (and (omap::assoc key map)
                  t)))
    :rule-classes :definition
    :hints
    (("Goal"
      :in-theory (enable omap::mapp
                         omap::mfix
                         omap::emptyp
                         omap::head
                         omap::tail
                         omap::update
                         omap::assoc)))))

(local
  (defthm delete-when-small
    (implies (and (not (omap::emptyp map))
                  (<< key (omap::head-key map)))
             (equal (omap::delete key map)
                    map))
    :hints
    (("Goal"
      :in-theory (enable omap::delete
                         omap::head-tail-order)))))

(local ; `REMOVER/UNIQUE-DEF'
  (encapsulate ()
    (local
      (in-theory
        (disable recognizer/unique-def
                 accessor/unique-def
                 updater/unique-def
                 boundp/unique-def)))

    (local
      (defthmd remover/unique-def-lemma-1
        (implies (and (recognizer/unique map)
                      (key-recognizer key))
                 (equal (remover/unique key map)
                        (omap::delete key map)))
        :hints
        (("Goal"
          :induct (recognizer/unique map)
          :in-theory (enable omap::emptyp
                             omap::mfix
                             omap::mapp
                             omap::head
                             omap::tail))
         ("Subgoal *1/2"
          :expand ((omap::delete key map)
                   (omap::update (car (car map))
                                 (cdr (car map))
                                 (omap::delete key (cdr map)))))
         ("Subgoal *1/1"
          :expand ((omap::delete key map)
                   (omap::update (car (car map))
                                 (cdr (car map))
                                 nil))))))

    (local
      (defthm remover/unique-def-lemma-2
        (equal (remover/unique (key-fixer key) map)
               (remover/unique key map))))

    (defthm remover/unique-def
      (equal (remover/unique key map)
             (let ((key (key-fixer (double-rewrite key)))
                   (map (fixer/unique map)))
               (omap::delete key map)))
      :rule-classes :definition
      :hints
      (("Goal"
        :do-not-induct t)
       ("Subgoal 2"
        :use ((:instance remover/unique-def-lemma-1
                         (key (key-fixer key))
                         (map (fixer/unique map)))))))))

(local
  (defthm count/unique-def
    (equal (count/unique map)
           (let ((map (fixer/unique map)))
             (omap::size map)))
    :rule-classes :definition
    :hints
    (("Goal"
      :in-theory (enable omap::size
                         omap::mapp
                         omap::emptyp
                         omap::head
                         omap::tail)))))

(local
  (defun recognizer/unique-ind-fn (map)
    (declare (xargs :guard (omap::mapp map)))
    (if (omap::emptyp map)
        map
        (recognizer/unique-ind-fn (omap::tail map)))))

(local
  (defthm recognizer/unique-ind
    t
    :rule-classes
    ((:induction :pattern (recognizer/unique map)
                 :scheme (recognizer/unique-ind-fn map)))))

(local
  (defthm size-of-update-when-assoc
    (implies (omap::assoc key map)
             (equal (omap::size (omap::update key val map))
                    (omap::size map)))
    :hints
    (("Goal"
      :induct (omap::size map)
      :in-theory (enable omap::size
                         omap::assoc
                         omap::mapp
                         omap::mfix
                         omap::emptyp
                         omap::head
                         omap::tail
                         omap::update)))))

(local
  (defthm size-of-update-when-not-assoc
    (implies (not (omap::assoc key map))
             (equal (omap::size (omap::update key val map))
                    (1+ (omap::size map))))
    :hints
    (("Goal"
      :induct (omap::size map)
      :in-theory (enable omap::size
                         omap::assoc
                         omap::mapp
                         omap::mfix
                         omap::emptyp
                         omap::head
                         omap::tail
                         omap::update)))))

(defthm size-of-update
  (equal (omap::size (omap::update key val map))
         (if (omap::assoc key map)
             (omap::size map)
             (1+ (omap::size map)))))

(defthm size-of-tail
  (implies (not (omap::emptyp map))
           (equal (omap::size (omap::tail map))
                  (1- (omap::size map))))
  :hints
  (("Goal"
    :in-theory (enable omap::size))))

(local
  (defun accessor/unique-ind-fn (key map)
    (declare (xargs :guard (omap::mapp map)
                    :measure (omap::size map)))
    (cond
      ((omap::emptyp map)
       map)
      ((key-equiv key (omap::head-key map))
       map)
      (t
       (accessor/unique-ind-fn key (omap::tail map))))))

(local
  (defthm accessor/unique-ind
    t
    :rule-classes
    ((:induction :pattern (accessor/unique key map)
                 :scheme (accessor/unique-ind-fn key map)))))

(local
  (in-theory
    (disable recognizer/unique
             accessor/unique
             updater/unique
             boundp/unique
             remover/unique
             count/unique)))


;;;; `RECOGNIZER/UNIQUE'
(defthm recognizer/unique-tp
  (booleanp (recognizer/unique hash-table))
  :rule-classes :type-prescription)

(defthm recognizer/unique-cr
  (implies (recognizer/unique hash-table)
           (true-listp hash-table))
  :rule-classes :compound-recognizer)

(defthm recognizer/unique-of-creator/unique
  (recognizer/unique (creator/unique)))

(defthm recognizer/unique-of-fixer/unique
  (recognizer/unique (fixer/unique hash-table)))

(local
  (defthm recognizer/unique-of-update
    (implies (and (key-recognizer key)
                  (val-recognizer val)
                  (recognizer/unique map))
             (recognizer/unique (omap::update key val map)))
    :hints
    (("Goal"
      :in-theory (disable omap::use-weak-update-induction))
     ("Subgoal *1/3"
      :expand (recognizer/unique (omap::update key val map))))))

(defthm recognizer/unique-of-updater/unique
  (recognizer/unique (updater/unique key val hash-table)))

(local
  (defthm recognizer/unique-of-delete
    (implies (recognizer/unique map)
             (recognizer/unique (omap::delete key map)))
    :hints
    (("Goal"
      :in-theory (enable omap::delete)))))

(defthm recognizer/unique-of-remover/unique
  (recognizer/unique (remover/unique key hash-table)))


;;;; `FIXER/UNIQUE'
(defthm fixer/unique-tp
  (true-listp (fixer/unique hash-table))
  :rule-classes :type-prescription)

(defthm fixer/unique-when-recognizer/unique
  (implies (recognizer/unique hash-table)
           (equal (fixer/unique hash-table)
                  hash-table)))

(defthm fixer/unique-when-not-recognizer/unique
  (implies (not (recognizer/unique hash-table))
           (equal (fixer/unique hash-table)
                  (creator/unique))))


;;;; `EQUIV/UNIQUE'
(defthm equiv/unique-tp
  (booleanp (equiv/unique %hash-table hash-table))
  :rule-classes :type-prescription)

(defequiv equiv/unique)

(defcong equiv/unique equal (fixer/unique hash-table) 1)

(defthm fixer/unique-mod-equiv/unique
  (equiv/unique (fixer/unique hash-table) hash-table))

(defthm equiv/unique-when-not-recognizer/unique
  (implies (not (recognizer/unique hash-table))
           (equiv/unique hash-table (creator/unique))))


;;;; `ACCESSOR/UNIQUE'
(defthm val-recognizer-of-accessor/unique
  (val-recognizer (accessor/unique key hash-table)))

(defcong key-equiv equal (accessor/unique key hash-table) 1)

(defcong equiv/unique equal (accessor/unique key hash-table) 2)

(defthm accessor/unique-when-not-key-recognizer
  (implies (not (key-recognizer key))
           (equal (accessor/unique key hash-table)
                  (accessor/unique (default-key) hash-table))))

(defthm accessor/unique-when-not-recognizer/unique
  (implies (not (recognizer/unique hash-table))
           (equal (accessor/unique key hash-table)
                  (default-val))))

(defthm accessor/unique-of-creator/unique
  (equal (accessor/unique key (creator/unique))
         (default-val)))

(local
  (defthm accessor/unique-of-update-same
    (implies (and (key-recognizer key)
                  (val-recognizer val)
                  (recognizer/unique map))
             (equal (accessor/unique key (omap::update key val map))
                    val))
    :hints
    (("Goal"
      :in-theory (disable omap::use-weak-update-induction))
     ("Subgoal *1/3"
      :expand (accessor/unique key (omap::update key val map))))))

(defthm accessor/unique-of-updater/unique-same
  (implies (key-equiv %key key)
           (equal (accessor/unique %key (updater/unique key val hash-table))
                  (val-fixer val)))
  :rule-classes
  ((:rewrite :corollary
             (implies (key-equiv %key (double-rewrite key))
                      (equal (accessor/unique %key (updater/unique key val hash-table))
                             (val-fixer (double-rewrite val))))))
  :hints
  (("Goal"
    :in-theory (enable key-fixer))))

(local
  (defthm accessor/unique-of-update-diff
    (implies (and (key-recognizer %key)
                  (key-recognizer key)
                  (not (equal %key key))
                  (val-recognizer val)
                  (recognizer/unique map))
             (equal (accessor/unique %key (omap::update key val map))
                    (accessor/unique %key (double-rewrite map))))
    :hints
    (("Goal"
      :in-theory (disable omap::use-weak-update-induction))
     ("Subgoal *1/4"
      :expand (accessor/unique %key (omap::update key val map))))))

(defthm accessor/unique-of-updater/unique-diff
  (implies (not (key-equiv %key key))
           (equal (accessor/unique %key (updater/unique key val hash-table))
                  (accessor/unique %key hash-table)))
  :rule-classes
  ((:rewrite :corollary
             (implies (not (key-equiv %key (double-rewrite key)))
                      (equal (accessor/unique %key (updater/unique key val hash-table))
                             (accessor/unique %key (double-rewrite hash-table))))))
  :hints
  (("Goal"
    :in-theory (enable key-fixer))))

(local
  (defthm accessor/unique-of-update
    (implies (and (key-recognizer %key)
                  (key-recognizer key)
                  (val-recognizer val)
                  (recognizer/unique map))
             (equal (accessor/unique %key (omap::update key val map))
                    (if (equal %key key)
                        val
                        (accessor/unique %key (double-rewrite map)))))
    :hints
    (("Goal"
      :do-not-induct t
      :cases ((equal %key key)))
     ("Subgoal 2"
      :use (:instance accessor/unique-of-update-diff))
     ("Subgoal 1"
      :use (:instance accessor/unique-of-update-same)))))

(defthm accessor/unique-of-updater/unique
  (equal (accessor/unique %key (updater/unique key val hash-table))
         (if (key-equiv %key key)
             (val-fixer val)
             (accessor/unique %key hash-table)))
  :rule-classes
  ((:rewrite :corollary
             (equal (accessor/unique %key (updater/unique key val hash-table))
                    (if (key-equiv %key (double-rewrite key))
                        (val-fixer (double-rewrite val))
                        (accessor/unique %key (double-rewrite hash-table))))))
  :hints
  (("Goal"
    :cases ((key-equiv %key key)))
   ("Subgoal 2"
    :by accessor/unique-of-updater/unique-diff)
   ("Subgoal 1"
    :by accessor/unique-of-updater/unique-same)))

(defthm accessor/unique-when-not-boundp/unique
  (implies (not (boundp/unique key hash-table))
           (equal (accessor/unique key hash-table)
                  (default-val))))

(local
  (defthm head-of-delete-when-miss
    (implies (and (not (omap::emptyp map))
                  (not (equal key (omap::head-key map))))
             (equal (omap::head (omap::delete key map))
                    (omap::head map)))
    :hints
    (("Goal"
      :in-theory (enable omap::delete
                         omap::update
                         omap::head
                         omap::tail
                         omap::emptyp
                         omap::mfix
                         omap::mapp)))))

(local
  (defthm accessor/unique-of-delete-same
    (implies (and (recognizer/unique map)
                  (equal %key key)
                  (key-recognizer %key)
                  (key-recognizer key))
             (equal (accessor/unique %key (omap::delete key map))
                    (default-val)))
    :hints
    (("Subgoal *1/3"
      :expand (omap::delete %key map)))))

(defthm accessor/unique-of-remover/unique-same
  (implies (key-equiv %key key)
           (equal (accessor/unique %key (remover/unique key hash-table))
                  (default-val)))
  :rule-classes
  ((:rewrite :corollary
             (implies (key-equiv %key (double-rewrite key))
                      (equal (accessor/unique %key (remover/unique key hash-table))
                             (default-val)))))
  :hints
  (("Goal"
    :in-theory (disable accessor/unique-of-delete-same)
    :use ((:instance accessor/unique-of-delete-same
                     (%key (key-fixer %key))
                     (key (key-fixer key))
                     (map hash-table))))))

(local
  (defthm emptyp-of-delete-when-miss
    (implies (and (not (omap::emptyp map))
                  (not (equal key (omap::head-key map))))
             (not (omap::emptyp (omap::delete key map))))
    :hints
    (("Goal"
      :in-theory (enable omap::delete)))))

(local
  (defthm accessor/unique-of-delete-diff
    (implies (and (recognizer/unique map)
                  (not (equal %key key))
                  (key-recognizer %key)
                  (key-recognizer key))
             (equal (accessor/unique %key (omap::delete key map))
                    (accessor/unique %key (double-rewrite map))))
    :hints
    (("Subgoal *1/4"
      :expand (omap::delete key map)))))

(defthm accessor/unique-of-remover/unique-diff
  (implies (not (key-equiv %key key))
           (equal (accessor/unique %key (remover/unique key hash-table))
                  (accessor/unique %key hash-table)))
  :rule-classes
  ((:rewrite :corollary
             (implies (not (key-equiv %key (double-rewrite key)))
                      (equal (accessor/unique %key (remover/unique key hash-table))
                             (accessor/unique %key (double-rewrite hash-table))))))
  :hints
  (("Goal"
    :in-theory (disable accessor/unique-of-delete-diff)
    :use ((:instance accessor/unique-of-delete-diff
                     (%key (key-fixer %key))
                     (key (key-fixer key))
                     (map hash-table))))))

(local
  (defthm accessor/unique-of-delete
    (implies (and (recognizer/unique map)
                  (key-recognizer %key)
                  (key-recognizer key))
             (equal (accessor/unique %key (omap::delete key map))
                    (if (equal %key key)
                        (default-val)
                        (accessor/unique %key (double-rewrite map)))))
    :hints
    (("Goal"
      :do-not-induct t
      :cases ((equal %key key)))
     ("Subgoal 2"
      :use (:instance accessor/unique-of-delete-diff))
     ("Subgoal 1"
      :use (:instance accessor/unique-of-delete-same)))))

(defthm accessor/unique-of-remover/unique
  (equal (accessor/unique %key (remover/unique key hash-table))
         (if (key-equiv %key key)
             (default-val)
             (accessor/unique %key hash-table)))
  :rule-classes
  ((:rewrite :corollary
             (equal (accessor/unique %key (remover/unique key hash-table))
                    (if (key-equiv %key (double-rewrite key))
                        (default-val)
                        (accessor/unique %key (double-rewrite hash-table))))))
  :hints
  (("Goal"
    :cases ((key-equiv %key key)))
   ("Subgoal 2"
    :by accessor/unique-of-remover/unique-diff)
   ("Subgoal 1"
    :by accessor/unique-of-remover/unique-same)))

(defthm accessor/unique-when-count/unique-is-zero
  (implies (equal (count/unique hash-table) 0)
           (equal (accessor/unique key hash-table)
                  (default-val)))
  :hints
  (("Goal"
    :in-theory (enable omap::unfold-equal-size-const))))

(local
  (defthm accessor/unique-of-head-key
    (implies (and (not (omap::emptyp map))
                  (recognizer/unique map))
             (equal (accessor/unique (mv-nth 0 (omap::head map)) map)
                    (omap::head-val map)))))

(local
  (defthm accessor/unique-of-tail
    (implies (and (not (omap::emptyp map))
                  (recognizer/unique map)
                  (not (key-equiv key (omap::head-key map))))
             (equal (accessor/unique key (omap::tail map))
                    (accessor/unique key (double-rewrite map))))))


;;;; `UPDATER/UNIQUE'
(defthm updater/unique-tp
  (true-listp (updater/unique key val hash-table))
  :rule-classes :type-prescription)

(defcong key-equiv equal (updater/unique key val hash-table) 1)

(defcong val-equiv equal (updater/unique key val hash-table) 2)

(defcong equiv/unique equal (updater/unique key val hash-table) 3)

(defthm updater/unique-when-not-key-recognizer
  (implies (not (key-recognizer key))
           (equal (updater/unique key val hash-table)
                  (updater/unique (default-key) val hash-table))))

(defthm updater/unique-when-not-val-recognizer
  (implies (not (val-recognizer val))
           (equal (updater/unique key val hash-table)
                  (updater/unique key (default-val) hash-table))))

(defthm updater/unique-when-not-recognizer/unique
  (implies (not (recognizer/unique hash-table))
           (equal (updater/unique key val hash-table)
                  (updater/unique key val (creator/unique)))))

(defthm updater/unique-of-accessor/unique-when-boundp/unique-free
  (implies (and (boundp/unique key hash-table)
                (val-equiv val (accessor/unique key hash-table)))
           (equal (updater/unique key val hash-table)
                  (fixer/unique hash-table))))

(defthm updater/unique-of-accessor/unique-when-boundp/unique
  (implies (and (boundp/unique %key hash-table)
                (key-equiv %key key)
                (equiv/unique %hash-table hash-table))
           (equal (updater/unique %key (accessor/unique key %hash-table) hash-table)
                  (fixer/unique hash-table)))
  :hints
  (("Goal"
    :do-not-induct t
    :in-theory (e/d (key-fixer)
                    (updater/unique-of-accessor/unique-when-boundp/unique-free))
    :use (:instance updater/unique-of-accessor/unique-when-boundp/unique-free
                    (val (accessor/unique key hash-table))
                    (key %key)
                    (hash-table (fixer/unique hash-table))))))

(defthm updater/unique-of-accessor/unique-when-not-boundp/unique
  (implies (and (not (boundp/unique %key hash-table))
                (key-equiv %key key))
           (equal (updater/unique %key (accessor/unique key hash-table) hash-table)
                  (updater/unique %key (default-val) hash-table))))

(defthm updater/unique-of-accessor/unique
  (implies (key-equiv %key key)
           (equal (updater/unique %key (accessor/unique key hash-table) hash-table)
                  (if (boundp/unique %key hash-table)
                      (fixer/unique hash-table)
                      (updater/unique %key (default-val) hash-table))))
  :hints
  (("Goal"
    :cases ((boundp/unique %key hash-table)))
   ("Subgoal 2"
    :by updater/unique-of-accessor/unique-when-not-boundp/unique)
   ("Subgoal 1"
    :use updater/unique-of-accessor/unique-when-boundp/unique)))

(defthm updater/unique-of-updater/unique-same
  (implies (key-equiv %key key)
           (equal (updater/unique %key %val (updater/unique key val hash-table))
                  (updater/unique %key %val hash-table))))

(defthm updater/unique-of-updater/unique-diff
  (implies (not (key-equiv %key key))
           (equal (updater/unique %key %val (updater/unique key val hash-table))
                  (updater/unique key val (updater/unique %key %val hash-table))))
  :rule-classes
  ((:rewrite :loop-stopper ((%key key updater/unique)))))

(defthm updater/unique-of-updater/unique
  (equal (updater/unique %key %val (updater/unique key val hash-table))
         (if (key-equiv %key key)
             (updater/unique %key %val hash-table)
             (updater/unique key val (updater/unique %key %val hash-table))))
  :rule-classes
  ((:rewrite :loop-stopper ((%key key updater/unique))))
  :hints
  (("Goal"
    :cases ((key-equiv %key key)))
   ("Subgoal 2"
    :by updater/unique-of-updater/unique-diff)
   ("Subgoal 1"
    :by updater/unique-of-updater/unique-same)))

(local
  (defthm update-of-delete-when-same
    (implies (equal %key key)
             (equal (omap::update %key val (omap::delete key map))
                    (omap::update %key val map)))
    :hints
    (("Goal"
      :induct (omap::delete %key map)
      :in-theory (enable omap::delete)))))

(defthm updater/unique-of-remover/unique-same
  (implies (key-equiv %key key)
           (equal (updater/unique %key val (remover/unique key hash-table))
                  (updater/unique %key val hash-table)))
  :rule-classes
  ((:rewrite :corollary
             (implies (key-equiv %key (double-rewrite key))
                      (equal (updater/unique %key val (remover/unique key hash-table))
                             (updater/unique %key val (double-rewrite hash-table)))))))


;;;; `BOUNDP/UNIQUE'
(defthm boundp/unique-tp
  (booleanp (boundp/unique key hash-table))
  :rule-classes :type-prescription)

(defcong key-equiv equal (boundp/unique key hash-table) 1)

(defcong equiv/unique equal (boundp/unique key hash-table) 2)

(defthm boundp/unique-when-not-key-recognizer
  (implies (not (key-recognizer key))
           (equal (boundp/unique key hash-table)
                  (boundp/unique (default-key) hash-table))))

(defthm boundp/unique-when-not-recognizer/unique
  (implies (not (recognizer/unique hash-table))
           (not (boundp/unique key hash-table))))

(defthm boundp/unique-of-creator/unique
  (not (boundp/unique key (creator/unique))))

(defthm boundp/unique-of-updater/unique-same
  (implies (key-equiv %key key)
           (equal (boundp/unique %key (updater/unique key val hash-table))
                  t)))

(defthm boundp/unique-of-updater/unique-diff
  (implies (not (key-equiv %key key))
           (equal (boundp/unique %key (updater/unique key val hash-table))
                  (boundp/unique %key hash-table))))

(defthm boundp/unique-of-updater/unique
  (equal (boundp/unique %key (updater/unique key val hash-table))
         (if (key-equiv %key key)
             t
             (boundp/unique %key hash-table)))
  :hints
  (("Goal"
    :cases ((key-equiv %key key)))
   ("Subgoal 2"
    :by boundp/unique-of-updater/unique-diff)
   ("Subgoal 1"
    :by boundp/unique-of-updater/unique-same)))

(local
  (defthm assoc-of-delete-when-same
    (implies (equal %key key)
             (not (omap::assoc %key (omap::delete key map))))
    :hints
    (("Goal"
      :in-theory (enable omap::delete)))))

(local
  (defthm assoc-of-delete-when-diff
    (implies (not (equal %key key))
             (equal (omap::assoc %key (omap::delete key map))
                    (omap::assoc %key map)))
    :hints
    (("Goal"
      :in-theory (enable omap::delete)))))

(local
  (defthm assoc-of-delete
    (equal (omap::assoc %key (omap::delete key map))
           (if (equal %key key)
               nil
               (omap::assoc %key map)))))

(defthm boundp/unique-of-remover/unique-same
  (implies (key-equiv %key key)
           (not (boundp/unique %key (remover/unique key hash-table))))
  :rule-classes
  ((:rewrite :corollary
             (implies (key-equiv %key (double-rewrite key))
                      (not (boundp/unique %key (remover/unique key hash-table)))))))

(defthm boundp/unique-of-remover/unique-diff
  (implies (not (key-equiv %key key))
           (equal (boundp/unique %key (remover/unique key hash-table))
                  (boundp/unique %key hash-table)))
  :rule-classes
  ((:rewrite :corollary
             (implies (not (key-equiv %key (double-rewrite key)))
                      (equal (boundp/unique %key (remover/unique key hash-table))
                             (boundp/unique %key (double-rewrite hash-table)))))))

(defthm boundp/unique-of-remover/unique
  (equal (boundp/unique %key (remover/unique key hash-table))
         (if (key-equiv %key key)
             nil
             (boundp/unique %key hash-table)))
  :rule-classes
  ((:rewrite :corollary
             (equal (boundp/unique %key (remover/unique key hash-table))
                    (if (key-equiv %key (double-rewrite key))
                        nil
                        (boundp/unique %key (double-rewrite hash-table))))))
  :hints
  (("Goal"
    :cases ((key-equiv %key key)))
   ("Subgoal 2"
    :by boundp/unique-of-remover/unique-diff)
   ("Subgoal 1"
    :in-theory (disable boundp/unique-of-remover/unique-same)
    :use boundp/unique-of-remover/unique-same)))

(defthm boundp/unique-when-count/unique-is-zero
  (implies (equal (count/unique hash-table) 0)
           (not (boundp/unique key hash-table)))
  :hints
  (("Goal"
    :in-theory (enable omap::unfold-equal-size-const))))

(local
  (defthm boundp/unique-of-head-key
    (implies (and (not (omap::emptyp map))
                  (recognizer/unique map))
             (equal (boundp/unique (mv-nth 0 (omap::head map)) map)
                    t))))

(local
  (encapsulate ()
    (local
      (defthm boundp/unique-of-tail-lemma
        (implies (and (recognizer/unique map)
                      (key-recognizer key))
                 (equal (boundp/unique key (omap::tail map))
                        (if (equal key (omap::head-key map))
                            nil
                            (boundp/unique key (double-rewrite map)))))))

    (defthm boundp/unique-of-tail
      (implies (recognizer/unique map)
               (equal (boundp/unique key (omap::tail map))
                      (if (key-equiv key (omap::head-key map))
                          nil
                          (boundp/unique key (double-rewrite map)))))
      :hints
      (("Goal"
        :do-not-induct t
        :use ((:instance boundp/unique-of-tail-lemma
                         (key (key-fixer key)))))))))


;;;; `GETP/UNIQUE'
(defthm getp/unique-tp
  (and (consp (getp/unique key hash-table))
       (true-listp (getp/unique key hash-table)))
  :rule-classes :type-prescription)

(defthm getp/unique-rw
  (mv-let (v0 v1)
          (getp/unique key hash-table)
    (and (equal v0 (accessor/unique key hash-table))
         (equal v1 (boundp/unique key hash-table))))
  :rule-classes
  ((:rewrite :corollary
             (mv-let (v0 v1)
                     (getp/unique key hash-table)
               (and (equal v0 (accessor/unique (double-rewrite key) (double-rewrite hash-table)))
                    (equal v1 (boundp/unique (double-rewrite key) (double-rewrite hash-table))))))))


;;;; `REMOVER/UNIQUE'
(defthm remover/unique-tp
  (true-listp (remover/unique key hash-table))
  :rule-classes :type-prescription)

(defcong key-equiv equal (remover/unique key hash-table) 1)

(defcong equiv/unique equal (remover/unique key hash-table) 2)

(defthm remover/unique-when-not-key-recognizer
  (implies (not (key-recognizer key))
           (equal (remover/unique key hash-table)
                  (remover/unique (default-key) hash-table))))

(defthm remover/unique-when-not-recognizer/unique
  (implies (not (recognizer/unique hash-table))
           (equal (remover/unique key hash-table)
                  (creator/unique))))

(defthm remover/unique-of-creator/unique
  (equal (remover/unique key (creator/unique))
         (creator/unique)))

(local
  (defthm delete-of-update-when-same
    (implies (equal %key key)
             (equal (omap::delete %key (omap::update key val map))
                    (omap::delete %key map)))
    :hints
    (("Goal"
      :in-theory (enable omap::delete
                         omap::mapp
                         omap::mfix
                         omap::emptyp
                         omap::head
                         omap::tail
                         omap::update)))))

(local
  (defthm delete-of-update-when-diff
    (implies (not (equal %key key))
             (equal (omap::delete %key (omap::update key val map))
                    (omap::update key val (omap::delete %key map))))
    :hints
    (("Goal"
      :in-theory (enable (:i omap::delete)))
     ("Subgoal *1/3"
      :expand ((omap::delete %key map)
               (omap::delete %key (omap::update key val map))))
     ("Subgoal *1/3.2"
      :in-theory (disable omap::update-different)
      :use ((:instance omap::update-different
                       (key1 (mv-nth 0 (omap::head map)))
                       (val1 (mv-nth 1 (omap::head map)))
                       (key2 key)
                       (val2 val)
                       (map (omap::delete %key (omap::tail map))))))
     ("Subgoal *1/2"
      :expand ((omap::delete (mv-nth 0 (omap::head map))
                             (omap::update key val map))
               (omap::delete (mv-nth 0 (omap::head map)) map)))
     ("Subgoal *1/1"
      :expand (omap::delete %key (omap::update key val nil))))))

(local
  (defthm delete-of-update
    (equal (omap::delete %key (omap::update key val map))
           (if (equal %key key)
               (omap::delete %key map)
               (omap::update key val (omap::delete %key map))))))

(defthm remover/unique-of-updater/unique-same
  (implies (key-equiv %key key)
           (equal (remover/unique %key (updater/unique key val hash-table))
                  (remover/unique %key hash-table))))

(defthm remover/unique-of-updater/unique-diff
  (implies (not (key-equiv %key key))
           (equal (remover/unique %key (updater/unique key val hash-table))
                  (updater/unique key val (remover/unique %key hash-table)))))

(defthm remover/unique-of-updater/unique
  (equal (remover/unique %key (updater/unique key val hash-table))
         (if (key-equiv %key key)
             (remover/unique %key hash-table)
             (updater/unique key val (remover/unique %key hash-table))))
  :hints
  (("Goal"
    :cases ((key-equiv %key key)))
   ("Subgoal 2"
    :by remover/unique-of-updater/unique-diff)
   ("Subgoal 1"
    :by remover/unique-of-updater/unique-same)))

(defthm remover/unique-when-not-boundp/unique
  (implies (not (boundp/unique key hash-table))
           (equal (remover/unique key hash-table)
                  (fixer/unique hash-table))))

(local
  (defthm delete-of-delete-when-same
    (implies (equal %key key)
             (equal (omap::delete %key (omap::delete key map))
                    (omap::delete %key map)))
    :hints
    (("Goal"
      :in-theory (enable omap::delete
                         omap::mapp
                         omap::mfix
                         omap::emptyp
                         omap::head
                         omap::tail
                         omap::update)))))

(local
  (defthm delete-of-delete-when-diff
    (implies (not (equal %key key))
             (equal (omap::delete %key (omap::delete key map))
                    (omap::delete key (omap::delete %key map))))
    :rule-classes
    ((:rewrite :loop-stopper ((%key key omap::delete))))
    :hints
    (("Goal"
      :induct (omap::size map)
      :in-theory (enable omap::size
                         omap::delete
                         omap::mapp
                         omap::mfix
                         omap::emptyp
                         omap::head
                         omap::tail
                         omap::update)))))

(local
  (defthm delete-of-delete
    (equal (omap::delete %key (omap::delete key map))
           (if (equal %key key)
               (omap::delete %key map)
               (omap::delete key (omap::delete %key map))))
    :rule-classes
    ((:rewrite :loop-stopper ((%key key omap::delete))))))

(defthm remover/unique-of-remover/unique-same
  (implies (key-equiv %key key)
           (equal (remover/unique %key (remover/unique key hash-table))
                  (remover/unique %key hash-table))))

(defthm remover/unique-of-remover/unique-diff
  (implies (not (key-equiv %key key))
           (equal (remover/unique %key (remover/unique key hash-table))
                  (remover/unique key (remover/unique %key hash-table))))
  :rule-classes
  ((:rewrite :loop-stopper ((%key key remover/unique)))))

(defthm remover/unique-of-remover/unique
  (equal (remover/unique %key (remover/unique key hash-table))
         (if (key-equiv %key key)
             (remover/unique %key hash-table)
             (remover/unique key (remover/unique %key hash-table))))
  :rule-classes
  ((:rewrite :loop-stopper ((%key key remover/unique))))
  :hints
  (("Goal"
    :cases ((key-equiv %key key)))
   ("Subgoal 2"
    :by remover/unique-of-remover/unique-diff)
   ("Subgoal 1"
    :by remover/unique-of-remover/unique-same)))

(defthm remover/unique-when-count/unique-is-zero
  (implies (equal (count/unique hash-table) 0)
           (equal (remover/unique key hash-table)
                  (creator/unique)))
  :hints
  (("Goal"
    :in-theory (enable omap::unfold-equal-size-const))))


;;;; `COUNT/UNIQUE'
(defthm count/unique-tp
  (natp (count/unique hash-table))
  :rule-classes :type-prescription)

(defcong equiv/unique equal (count/unique hash-table) 1)

(defthm count/unique-when-not-recognizer/unique
  (implies (not (recognizer/unique hash-table))
           (equal (count/unique hash-table)
                  0)))

(defthm count/unique-of-creator/unique
  (equal (count/unique (creator/unique))
         0))

(defthm count/unique-of-updater/unique-when-boundp/unique
  (implies (boundp/unique key hash-table)
           (equal (count/unique (updater/unique key val hash-table))
                  (count/unique hash-table))))

(defthm count/unique-of-updater/unique-when-not-boundp/unique
  (implies (not (boundp/unique key hash-table))
           (equal (count/unique (updater/unique key val hash-table))
                  (1+ (count/unique hash-table)))))

(defthm count/unique-of-updater/unique
  (equal (count/unique (updater/unique key val hash-table))
         (if (boundp/unique key hash-table)
             (count/unique hash-table)
             (1+ (count/unique hash-table))))
  :hints
  (("Goal"
    :cases ((boundp/unique key hash-table)))
   ("Subgoal 2"
    :by count/unique-of-updater/unique-when-not-boundp/unique)
   ("Subgoal 1"
    :by count/unique-of-updater/unique-when-boundp/unique)))

(defthm count/unique-when-boundp/unique
  (implies (boundp/unique key hash-table)
           (posp (count/unique hash-table)))
  :rule-classes :type-prescription
  :hints
  (("Goal"
    :in-theory (enable omap::unfold-equal-size-const))))

(local
  (defthm size-of-delete-when-assoc
    (implies (omap::assoc key map)
             (equal (omap::size (omap::delete key map))
                    (1- (omap::size map))))
    :hints
    (("Goal"
      :in-theory (enable omap::delete
                         omap::assoc)))))

(local
  (defthm size-of-delete-when-not-assoc
    (implies (not (omap::assoc key map))
             (equal (omap::size (omap::delete key map))
                    (omap::size map)))
    :hints
    (("Goal"
      :in-theory (enable omap::size
                         omap::delete
                         omap::assoc)))))

(local
  (defthm size-of-delete
    (equal (omap::size (omap::delete key map))
           (if (omap::assoc key map)
               (1- (omap::size map))
               (omap::size map)))))

(defthm count/unique-of-remover/unique-when-boundp/unique
  (implies (boundp/unique key hash-table)
           (equal (count/unique (remover/unique key hash-table))
                  (1- (count/unique hash-table)))))

(defthm count/unique-of-remover/unique-when-not-boundp/unique
  (implies (not (boundp/unique key hash-table))
           (equal (count/unique (remover/unique key hash-table))
                  (count/unique hash-table))))

(defthm count/unique-of-remover/unique
  (equal (count/unique (remover/unique key hash-table))
         (if (boundp/unique key hash-table)
             (1- (count/unique hash-table))
             (count/unique hash-table))))

(defthm creator/unique-when-count/unique-is-zero
  (implies (equal (count/unique hash-table) 0)
           (equiv/unique hash-table (creator/unique)))
  :rule-classes
  ((:forward-chaining :trigger-terms
                      ((count/unique hash-table))
                      :corollary
                      (implies t
                               (implies (equal (count/unique hash-table) 0)
                                        (equiv/unique hash-table (creator/unique))))))
  :hints
  (("Goal"
    :do-not-induct t
    :in-theory (enable omap::unfold-equal-size-const))))

(local
  (defthm count/unique-of-tail
    (implies (and (not (omap::emptyp map))
                  (recognizer/unique map))
             (equal (count/unique (omap::tail map))
                    (1- (count/unique (double-rewrite map)))))))


;;;; `CLEAR/UNIQUE'
(defthm clear/unique-tp
  (true-listp (clear/unique hash-table))
  :rule-classes :type-prescription)

(defthm clear/unique-rw
  (equal (clear/unique hash-table)
         (creator/unique)))


;;;; `INIT/UNIQUE'
(defthm init/unique-tp
  (true-listp (init/unique ht-size rehash-size rehash-threshold hash-table))
  :rule-classes :type-prescription)

(defthm init/unique-rw
  (equal (init/unique ht-size rehash-size rehash-threshold hash-table)
         (creator/unique)))

(local
  (in-theory
    (disable recognizer/unique
             creator/unique
             fixer/unique
             equiv/unique
             accessor/unique
             updater/unique
             boundp/unique
             getp/unique
             remover/unique
             count/unique
             clear/unique
             init/unique

             recognizer/unique-def
             accessor/unique-def
             updater/unique-def
             boundp/unique-def
             remover/unique-def
             count/unique-def

             recognizer/unique-ind-fn
             accessor/unique-ind-fn)))


;;;; Copyable Definitions
(defun keysp (set)
  (declare (xargs :guard t))
  (if (consp set)
      (and (key-recognizer (car set))
           (or (null (cdr set))
               (and (consp (cdr set))
                    (<< (car set)
                        (cadr set))
                    (keysp (cdr set)))))
      (null set)))

(defun keys-fix (set)
  (declare (xargs :guard (keysp set)))
  (if (keysp set)
      set
      '()))

(defun keys-equiv (%set set)
  (declare (xargs :guard (and (keysp %set)
                              (keysp set))))
  (equal (keys-fix %set)
         (keys-fix set)))

(defun recognizer/copyable (hash-table)
  (declare (xargs :guard t))
  (and (consp hash-table)
       (keysp (car hash-table))
       (recognizer/unique (cdr hash-table))))

(defun-nx creator/copyable ()
  (declare (xargs :guard t))
  (cons '() (creator/unique)))

(defun fixer/copyable (hash-table)
  (declare (xargs :guard (recognizer/copyable hash-table)))
  (if (recognizer/copyable hash-table)
      hash-table
      (creator/copyable)))

(defun equiv/copyable (%hash-table hash-table)
  (declare (xargs :guard (and (recognizer/copyable %hash-table)
                              (recognizer/copyable hash-table))))
  (equal (fixer/copyable %hash-table)
         (fixer/copyable hash-table)))

(defun accessor/copyable (key hash-table)
  (declare (xargs :guard (and (key-recognizer key)
                              (recognizer/copyable hash-table))))
  (let ((key (key-fixer key))
        (hash-table (fixer/copyable hash-table)))
    (accessor/unique key (cdr hash-table))))

(defun updater/copyable (key val hash-table)
  (declare (xargs :guard (and (key-recognizer key)
                              (val-recognizer val)
                              (recognizer/copyable hash-table))))
  (let ((key (key-fixer key))
        (val (val-fixer val))
        (hash-table (fixer/copyable hash-table)))
    (cons (car hash-table)
          (updater/unique key val (cdr hash-table)))))

(defun boundp/copyable (key hash-table)
  (declare (xargs :guard (and (key-recognizer key)
                              (recognizer/copyable hash-table))))
  (let ((key (key-fixer key))
        (hash-table (fixer/copyable hash-table)))
    (boundp/unique key (cdr hash-table))))

(defun getp/copyable (key hash-table)
  (declare (xargs :guard (and (key-recognizer key)
                              (recognizer/copyable hash-table))))
  (let ((key (key-fixer key))
        (hash-table (fixer/copyable hash-table)))
    (getp/unique key (cdr hash-table))))

(defun remover/copyable (key hash-table)
  (declare (xargs :guard (and (key-recognizer key)
                              (recognizer/copyable hash-table))))
  (let ((key (key-fixer key))
        (hash-table (fixer/copyable hash-table)))
    (cons (car hash-table)
          (remover/unique key (cdr hash-table)))))

(defun count/copyable (hash-table)
  (declare (xargs :guard (recognizer/copyable hash-table)))
  (let ((hash-table (fixer/copyable hash-table)))
    (count/unique (cdr hash-table))))

(defun clear/copyable (hash-table)
  (declare (xargs :guard (recognizer/copyable hash-table))
           (ignore hash-table))
  (creator/copyable))

(defun init/copyable (ht-size rehash-size rehash-threshold hash-table)
  (declare (xargs :guard (and (recognizer/copyable hash-table)
                              (or (natp ht-size)
                                  (not ht-size))
                              (or (and (rationalp rehash-size)
                                       (<= 1 rehash-size))
                                  (not rehash-size))
                              (or (and (rationalp rehash-threshold)
                                       (<= 0 rehash-threshold)
                                       (<= rehash-threshold 1))
                                  (not rehash-threshold))))
           (ignore ht-size rehash-size rehash-threshold hash-table))
  (creator/copyable))

(defun keys (hash-table)
  (declare (xargs :guard (recognizer/copyable hash-table)))
  (let ((hash-table (fixer/copyable hash-table)))
    (car hash-table)))

(defun keys-set (set hash-table)
  (declare (xargs :guard (and (keysp set)
                              (recognizer/copyable hash-table))))
  (let ((set (keys-fix set))
        (hash-table (fixer/copyable hash-table)))
    (cons set (cdr hash-table))))


;;;; `KEYSP'
(defthm keysp-tp
  (booleanp (keysp set))
  :rule-classes :type-prescription)

(defthm keysp-cr
  (implies (keysp set)
           (true-listp set))
  :rule-classes :compound-recognizer)

(defthm keysp-def
  (equal (keysp set)
         (and (set::setp set)
              (or (set::emptyp set)
                  (and (key-recognizer (set::head set))
                       (keysp (set::tail set))))))
  :rule-classes
  ((:definition :controller-alist ((keysp t))))
  :hints
  (("Goal"
    :in-theory (enable set::setp
                       set::emptyp
                       set::head
                       set::tail
                       set::sfix))))

(local
  (in-theory
    (disable keysp)))

(defthm setp-when-keysp
  (implies (keysp set)
           (set::setp set)))

(defthm keysp-when-emptyp
  (implies (set::emptyp set)
           (equal (keysp set)
                  (set::setp set))))

(defthm keysp-of-keys-fix
  (keysp (keys-fix set)))

(defthm keysp-of-keys
  (keysp (keys hash-table)))

(defthm keysp-of-sfix
  (equal (keysp (set::sfix set))
         (or (set::emptyp set)
             (keysp set)))
  :hints
  (("Goal"
    :in-theory (enable set::sfix))))

(defthm key-recognizer-of-head-when-keysp
  (implies (and (not (set::emptyp set))
                (keysp set))
           (key-recognizer (set::head set))))

(defthm keysp-of-tail-when-keysp
  (implies (and (not (set::emptyp set))
                (keysp set))
           (keysp (set::tail set))))

(defthm keysp-of-insert
  (equal (keysp (set::insert key set))
         (and (key-recognizer key)
              (or (set::emptyp set)
                  (keysp set))))
  :hints
  (("Goal"
    :in-theory (enable set::in))))

(defthm in-when-keysp
  (implies (and (keysp set)
                (not (key-recognizer key)))
           (not (set::in key set)))
  :hints
  (("Goal"
    :in-theory (enable set::in))))

(defthm subset-when-keysp
  (implies (and (not (keysp %set))
                (keysp set))
           (equal (set::subset %set set)
                  (set::emptyp %set)))
  :hints
  (("Goal"
    :in-theory (enable set::subset))))

(defthm keysp-of-delete
  (implies (keysp set)
           (keysp (set::delete key set)))
  :hints
  (("Goal"
    :in-theory (enable set::delete))))

(defthm keysp-of-union
  (implies (and (not (set::emptyp %set))
                (not (set::emptyp set)))
           (equal (keysp (set::union %set set))
                  (and (keysp %set)
                       (keysp set))))
  :hints
  (("Goal"
    :in-theory (enable set::union))))

(defthm keysp-of-intersect
  (implies (or (keysp %set)
               (keysp set))
           (keysp (set::intersect %set set)))
  :hints
  (("Goal"
    :in-theory (enable set::intersect))))

(defthm keysp-of-difference
  (implies (keysp %set)
           (keysp (set::difference %set set)))
  :hints
  (("Goal"
    :in-theory (enable set::difference))))


;;;; `KEYS-FIX'
(defthm keys-fix-tp
  (true-listp (keys-fix set))
  :rule-classes :type-prescription)

(defthm keys-fix-when-keysp
  (implies (keysp set)
           (equal (keys-fix set)
                  set)))

(defthm keys-fix-when-not-keysp
  (implies (not (keysp set))
           (not (keys-fix set))))


;;;; `KEYS-EQUIV'
(defthm keys-equiv-tp
  (booleanp (keys-equiv %set set))
  :rule-classes :type-prescription)

(defequiv keys-equiv)

(defcong keys-equiv equal (keys-fix set) 1)

(defthm keys-fix-mod-keys-equiv
  (keys-equiv (keys-fix set) set))

(defthm keys-equiv-when-not-keysp
  (implies (not (keysp set))
           (keys-equiv set ())))


;;;; `RECOGNIZER/COPYABLE'
(defthm recognizer/copyable-tp
  (booleanp (recognizer/copyable hash-table))
  :rule-classes :type-prescription)

(defthm recognizer/copyable-cr
  (implies (recognizer/copyable hash-table)
           (and (consp hash-table)
                (true-listp hash-table)))
  :rule-classes :compound-recognizer)

(defthm recognizer/copyable-of-creator/copyable
  (recognizer/copyable (creator/copyable)))

(defthm recognizer/copyable-of-fixer/copyable
  (recognizer/copyable (fixer/copyable hash-table)))

(defthm recognizer/copyable-of-updater/copyable
  (recognizer/copyable (updater/copyable key val hash-table)))

(defthm recognizer/copyable-of-remover/copyable
  (recognizer/copyable (remover/copyable key hash-table)))

(defthm recognizer/copyable-of-keys-set
  (recognizer/copyable (keys-set set hash-table)))


;;;; `FIXER/COPYABLE'
(defthm fixer/copyable-tp
  (and (consp (fixer/copyable hash-table))
       (true-listp (fixer/copyable hash-table)))
  :rule-classes :type-prescription)

(defthm fixer/copyable-when-recognizer/copyable
  (implies (recognizer/copyable hash-table)
           (equal (fixer/copyable hash-table)
                  hash-table)))

(defthm fixer/copyable-when-not-recognizer/copyable
  (implies (not (recognizer/copyable hash-table))
           (equal (fixer/copyable hash-table)
                  (creator/copyable))))


;;;; `EQUIV/COPYABLE'
(defthm equiv/copyable-tp
  (booleanp (equiv/copyable %hash-table hash-table))
  :rule-classes :type-prescription)

(defequiv equiv/copyable)

(defcong equiv/copyable equal (fixer/copyable hash-table) 1)

(defthm fixer/copyable-mod-equiv/copyable
  (equiv/copyable (fixer/copyable hash-table) hash-table))

(defthm equiv/copyable-when-not-recognizer/copyable
  (implies (not (recognizer/copyable hash-table))
           (equiv/copyable hash-table (creator/copyable))))


;;;; `ACCESSOR/COPYABLE'
(defthm val-recognizer-of-accessor/copyable
  (val-recognizer (accessor/copyable key hash-table)))

(defcong key-equiv equal (accessor/copyable key hash-table) 1
  :hints
  (("Goal"
    :use ((:instance key-equiv-implies-equal-accessor/unique-1
                     (hash-table (cdr hash-table)))))))

(defcong equiv/copyable equal (accessor/copyable key hash-table) 2)

(defthm accessor/copyable-when-not-key-recognizer
  (implies (not (key-recognizer key))
           (equal (accessor/copyable key hash-table)
                  (accessor/copyable (default-key) hash-table))))

(defthm accessor/copyable-when-not-recognizer/copyable
  (implies (not (recognizer/copyable hash-table))
           (equal (accessor/copyable key hash-table)
                  (default-val))))

(defthm accessor/copyable-of-creator/copyable
  (equal (accessor/copyable key (creator/copyable))
         (default-val)))

(defthm accessor/copyable-of-updater/copyable-same
  (implies (key-equiv %key key)
           (equal (accessor/copyable %key (updater/copyable key val hash-table))
                  (val-fixer val)))
  :rule-classes
  ((:rewrite :corollary
             (implies (key-equiv %key (double-rewrite key))
                      (equal (accessor/copyable %key (updater/copyable key val hash-table))
                             (val-fixer (double-rewrite val)))))))

(defthm accessor/copyable-of-updater/copyable-diff
  (implies (not (key-equiv %key key))
           (equal (accessor/copyable %key (updater/copyable key val hash-table))
                  (accessor/copyable %key  hash-table)))
  :rule-classes
  ((:rewrite :corollary
             (implies (not (key-equiv %key (double-rewrite key)))
                      (equal (accessor/copyable %key (updater/copyable key val hash-table))
                             (accessor/copyable %key (double-rewrite hash-table)))))))

(defthm accessor/copyable-of-updater/copyable
  (equal (accessor/copyable %key (updater/copyable key val hash-table))
         (if (key-equiv %key key)
             (val-fixer val)
             (accessor/copyable %key hash-table)))
  :rule-classes
  ((:rewrite :corollary
             (equal (accessor/copyable %key (updater/copyable key val hash-table))
                    (if (key-equiv %key (double-rewrite key))
                        (val-fixer (double-rewrite val))
                        (accessor/copyable %key (double-rewrite hash-table)))))))

(defthm accessor/copyable-when-not-boundp/copyable
  (implies (not (boundp/copyable key hash-table))
           (equal (accessor/copyable key hash-table)
                  (default-val))))

(defthm accessor/copyable-of-remover/copyable-same
  (implies (key-equiv %key key)
           (equal (accessor/copyable %key (remover/copyable key hash-table))
                  (default-val)))
  :rule-classes
  ((:rewrite :corollary
             (implies (key-equiv %key (double-rewrite key))
                      (equal (accessor/copyable %key (remover/copyable key hash-table))
                             (default-val))))))

(defthm accessor/copyable-of-remover/copyable-diff
  (implies (not (key-equiv %key key))
           (equal (accessor/copyable %key (remover/copyable key hash-table))
                  (accessor/copyable %key hash-table)))
  :rule-classes
  ((:rewrite :corollary
             (implies (not (key-equiv %key (double-rewrite key)))
                      (equal (accessor/copyable %key (remover/copyable key hash-table))
                             (accessor/copyable %key (double-rewrite hash-table)))))))

(defthm accessor/copyable-of-remover/copyable
  (equal (accessor/copyable %key (remover/copyable key hash-table))
         (if (key-equiv %key key)
             (default-val)
             (accessor/copyable %key hash-table)))
  :rule-classes
  ((:rewrite :corollary
             (equal (accessor/copyable %key (remover/copyable key hash-table))
                    (if (key-equiv %key (double-rewrite key))
                        (default-val)
                        (accessor/copyable %key (double-rewrite hash-table)))))))

(defthm accessor/copyable-of-keys-set
  (equal (accessor/copyable key (keys-set set hash-table))
         (accessor/copyable key hash-table))
  :rule-classes
  ((:rewrite :corollary
             (equal (accessor/copyable key (keys-set set hash-table))
                    (accessor/copyable key (double-rewrite hash-table))))))

(defthm accessor/copyable-when-count/copyable-is-zero
  (implies (equal (count/copyable hash-table) 0)
           (equal (accessor/copyable key hash-table)
                  (default-val))))


;;;; `UPDATER/COPYABLE'
(defthm updater/copyable-tp
  (and (consp (updater/copyable key val hash-table))
       (true-listp (updater/copyable key val hash-table)))
  :rule-classes :type-prescription)

(defcong key-equiv equal (updater/copyable key val hash-table) 1)

(defcong val-equiv equal (updater/copyable key val hash-table) 2)

(defcong equiv/copyable equal (updater/copyable key val hash-table) 3)

(defthm updater/copyable-when-not-key-recognizer
  (implies (not (key-recognizer key))
           (equal (updater/copyable key val hash-table)
                  (updater/copyable (default-key) val hash-table))))

(defthm updater/copyable-when-not-val-recognizer
  (implies (not (val-recognizer val))
           (equal (updater/copyable key val hash-table)
                  (updater/copyable key (default-val) hash-table))))

(defthm updater/copyable-when-not-recognizer/copyable
  (implies (not (recognizer/copyable hash-table))
           (equal (updater/copyable key val hash-table)
                  (updater/copyable key val (creator/copyable)))))

(defthm updater/copyable-of-accessor/copyable-when-boundp/copyable-free
  (implies (and (boundp/copyable key hash-table)
                (val-equiv val (accessor/copyable key hash-table)))
           (equal (updater/copyable key val hash-table)
                  (fixer/copyable hash-table))))

(defthm updater/copyable-of-accessor/copyable-when-boundp/copyable
  (implies (and (boundp/copyable %key hash-table)
                (key-equiv %key key)
                (equiv/copyable %hash-table hash-table))
           (equal (updater/copyable %key (accessor/copyable key %hash-table) hash-table)
                  (fixer/copyable hash-table)))
  :hints
  (("Goal"
    :do-not-induct t
    :in-theory (disable updater/copyable-of-accessor/copyable-when-boundp/copyable-free)
    :use (:instance updater/copyable-of-accessor/copyable-when-boundp/copyable-free
                    (val (accessor/copyable key hash-table))
                    (key %key)))))

(defthm updater/copyable-of-accessor/copyable-when-not-boundp/copyable
  (implies (and (not (boundp/copyable %key hash-table))
                (key-equiv %key key))
           (equal (updater/copyable %key (accessor/copyable key hash-table) hash-table)
                  (updater/copyable %key (default-val) hash-table))))

(defthm updater/copyable-of-accessor/copyable
  (implies (key-equiv %key key)
           (equal (updater/copyable %key (accessor/copyable key hash-table) hash-table)
                  (if (boundp/copyable %key hash-table)
                      (fixer/copyable hash-table)
                      (updater/copyable %key (default-val) hash-table))))
  :hints
  (("Goal"
    :cases ((boundp/copyable %key hash-table)))
   ("Subgoal 2"
    :by updater/copyable-of-accessor/copyable-when-not-boundp/copyable)
   ("Subgoal 1"
    :use updater/copyable-of-accessor/copyable-when-boundp/copyable)))

(defthm updater/copyable-of-updater/copyable-same
  (implies (key-equiv %key key)
           (equal (updater/copyable %key %val (updater/copyable key val hash-table))
                  (updater/copyable %key %val hash-table))))

(defthm updater/copyable-of-updater/copyable-diff
  (implies (not (key-equiv %key key))
           (equal (updater/copyable %key %val (updater/copyable key val hash-table))
                  (updater/copyable key val (updater/copyable %key %val hash-table))))
  :rule-classes
  ((:rewrite :loop-stopper ((%key key updater/copyable)))))

(defthm updater/copyable-of-updater/copyable
  (equal (updater/copyable %key %val (updater/copyable key val hash-table))
         (if (key-equiv %key key)
             (updater/copyable %key %val hash-table)
             (updater/copyable key val (updater/copyable %key %val hash-table))))
  :rule-classes
  ((:rewrite :loop-stopper ((%key key updater/copyable))))
  :hints
  (("Goal"
    :cases ((key-equiv %key key)))
   ("Subgoal 2"
    :by updater/copyable-of-updater/copyable-diff)
   ("Subgoal 1"
    :by updater/copyable-of-updater/copyable-same)))

(defthm updater/copyable-of-remover/copyable-same
  (implies (key-equiv %key key)
           (equal (updater/copyable %key val (remover/copyable key hash-table))
                  (updater/copyable %key val hash-table)))
  :rule-classes
  ((:rewrite :corollary
             (implies (key-equiv %key (double-rewrite key))
                      (equal (updater/copyable %key val (remover/copyable key hash-table))
                             (updater/copyable %key val (double-rewrite hash-table))))))
  :hints
  (("Goal"
    :in-theory (enable creator/unique))))


;;;; `BOUNDP/COPYABLE'
(defthm boundp/copyable-tp
  (booleanp (boundp/copyable key hash-table))
  :rule-classes :type-prescription)

(defcong key-equiv equal (boundp/copyable key hash-table) 1
  :hints
  (("Goal"
    :use ((:instance key-equiv-implies-equal-boundp/unique-1
                     (hash-table (cdr hash-table)))))))

(defcong equiv/copyable equal (boundp/copyable key hash-table) 2)

(defthm boundp/copyable-when-not-key-recognizer
  (implies (not (key-recognizer key))
           (equal (boundp/copyable key hash-table)
                  (boundp/copyable (default-key) hash-table))))

(defthm boundp/copyable-when-not-recognizer/copyable
  (implies (not (recognizer/copyable hash-table))
           (not (boundp/copyable key hash-table))))

(defthm boundp/copyable-of-creator/copyable
  (not (boundp/copyable key (creator/copyable))))

(defthm boundp/copyable-of-updater/copyable-same
  (implies (key-equiv %key key)
           (equal (boundp/copyable %key (updater/copyable key val hash-table))
                  t)))

(defthm boundp/copyable-of-updater/copyable-diff
  (implies (not (key-equiv %key key))
           (equal (boundp/copyable %key (updater/copyable key val hash-table))
                  (boundp/copyable %key hash-table))))

(defthm boundp/copyable-of-updater/copyable
  (equal (boundp/copyable %key (updater/copyable key val hash-table))
         (if (key-equiv %key key)
             t
             (boundp/copyable %key hash-table)))
  :hints
  (("Goal"
    :cases ((key-equiv %key key)))
   ("Subgoal 2"
    :by boundp/copyable-of-updater/copyable-diff)
   ("Subgoal 1"
    :by boundp/copyable-of-updater/copyable-same)))

(defthm boundp/copyable-of-remover/copyable-same
  (implies (key-equiv %key key)
           (not (boundp/copyable %key (remover/copyable key hash-table))))
  :rule-classes
  ((:rewrite :corollary
             (implies (key-equiv %key (double-rewrite key))
                      (not (boundp/copyable %key (remover/copyable key hash-table)))))))

(defthm boundp/copyable-of-remover/copyable-diff
  (implies (not (key-equiv %key key))
           (equal (boundp/copyable %key (remover/copyable key hash-table))
                  (boundp/copyable %key hash-table)))
  :rule-classes
  ((:rewrite :corollary
             (implies (not (key-equiv %key (double-rewrite key)))
                      (equal (boundp/copyable %key (remover/copyable key hash-table))
                             (boundp/copyable %key (double-rewrite hash-table)))))))

(defthm boundp/copyable-of-remover/copyable
  (equal (boundp/copyable %key (remover/copyable key hash-table))
         (if (key-equiv %key key)
             nil
             (boundp/copyable %key hash-table)))
  :rule-classes
  ((:rewrite :corollary
             (equal (boundp/copyable %key (remover/copyable key hash-table))
                    (if (key-equiv %key (double-rewrite key))
                        nil
                        (boundp/copyable %key (double-rewrite hash-table))))))
  :hints
  (("Goal"
    :cases ((key-equiv %key key)))
   ("Subgoal 2"
    :by boundp/copyable-of-remover/copyable-diff)
   ("Subgoal 1"
    :in-theory (disable boundp/copyable-of-remover/copyable-same)
    :use boundp/copyable-of-remover/copyable-same)))

(defthm boundp/copyable-of-keys-set
  (equal (boundp/copyable key (keys-set set hash-table))
         (boundp/copyable key hash-table))
  :rule-classes
  ((:rewrite :corollary
             (equal (boundp/copyable key (keys-set set hash-table))
                    (boundp/copyable key (double-rewrite hash-table))))))

(defthm boundp/copyable-when-count/copyable-is-zero
  (implies (equal (count/copyable hash-table) 0)
           (not (boundp/copyable key hash-table))))


;;;; `GETP/COPYABLE'
(defthm getp/copyable-tp
  (and (consp (getp/copyable key hash-table))
       (true-listp (getp/copyable key hash-table)))
  :rule-classes :type-prescription)

(defthm getp/copyable-rw
  (mv-let (v0 v1)
          (getp/copyable key hash-table)
    (and (equal v0 (accessor/copyable key hash-table))
         (equal v1 (boundp/copyable key hash-table))))
  :rule-classes
  ((:rewrite :corollary
             (mv-let (v0 v1)
                     (getp/copyable key hash-table)
               (and (equal v0 (accessor/copyable (double-rewrite key) (double-rewrite hash-table)))
                    (equal v1 (boundp/copyable (double-rewrite key) (double-rewrite hash-table))))))))


;;;; `REMOVER/COPYABLE'
(defthm remover/copyable-tp
  (and (consp (remover/copyable key hash-table))
       (true-listp (remover/copyable key hash-table)))
  :rule-classes :type-prescription)

(defcong key-equiv equal (remover/copyable key hash-table) 1)

(defcong equiv/copyable equal (remover/copyable key hash-table) 2)

(defthm remover/copyable-when-not-key-recognizer
  (implies (not (key-recognizer key))
           (equal (remover/copyable key hash-table)
                  (remover/copyable (default-key) hash-table))))

(defthm remover/copyable-when-not-recognizer/copyable
  (implies (not (recognizer/copyable hash-table))
           (equal (remover/copyable key hash-table)
                  (creator/copyable))))

(defthm remover/copyable-of-creator/copyable
  (equal (remover/copyable key (creator/copyable))
         (creator/copyable)))

(defthm remover/copyable-of-updater/copyable-same
  (implies (key-equiv %key key)
           (equal (remover/copyable %key (updater/copyable key val hash-table))
                  (remover/copyable %key hash-table))))

(defthm remover/copyable-of-updater/copyable-diff
  (implies (not (key-equiv %key key))
           (equal (remover/copyable %key (updater/copyable key val hash-table))
                  (updater/copyable key val (remover/copyable %key hash-table))))
  :hints
  (("Goal"
    :in-theory (enable creator/unique))))

(defthm remover/copyable-of-updater/copyable
  (equal (remover/copyable %key (updater/copyable key val hash-table))
         (if (key-equiv %key key)
             (remover/copyable %key hash-table)
             (updater/copyable key val (remover/copyable %key hash-table))))
  :hints
  (("Goal"
    :cases ((key-equiv %key key)))
   ("Subgoal 2"
    :by remover/copyable-of-updater/copyable-diff)
   ("Subgoal 1"
    :by remover/copyable-of-updater/copyable-same)))

(defthm remover/copyable-when-not-boundp/copyable
  (implies (not (boundp/copyable key hash-table))
           (equal (remover/copyable key hash-table)
                  (fixer/copyable hash-table))))

(defthm remover/copyable-of-remover/copyable-same
  (implies (key-equiv %key key)
           (equal (remover/copyable %key (remover/copyable key hash-table))
                  (remover/copyable %key hash-table))))

(defthm remover/copyable-of-remover/copyable-diff
  (implies (not (key-equiv %key key))
           (equal (remover/copyable %key (remover/copyable key hash-table))
                  (remover/copyable key (remover/copyable %key hash-table))))
  :rule-classes
  ((:rewrite :loop-stopper ((%key key remover/copyable)))))

(defthm remover/copyable-of-remover/copyable
  (equal (remover/copyable %key (remover/copyable key hash-table))
         (if (key-equiv %key key)
             (remover/copyable %key hash-table)
             (remover/copyable key (remover/copyable %key hash-table))))
  :rule-classes
  ((:rewrite :loop-stopper ((%key key remover/copyable))))
  :hints
  (("Goal"
    :cases ((key-equiv %key key)))
   ("Subgoal 2"
    :by remover/copyable-of-remover/copyable-diff)
   ("Subgoal 1"
    :by remover/copyable-of-remover/copyable-same)))

(defthm remover/copyable-when-count/copyable-is-zero
  (implies (equal (count/copyable hash-table) 0)
           (equal (remover/copyable key hash-table)
                  (keys-set (keys hash-table)
                            (creator/copyable)))))


;;;; `COUNT/COPYABLE'
(defthm count/copyable-tp
  (natp (count/copyable hash-table))
  :rule-classes :type-prescription)

(defcong equiv/copyable equal (count/copyable hash-table) 1)

(defthm count/copyable-when-not-recognizer/copyable
  (implies (not (recognizer/copyable hash-table))
           (equal (count/copyable hash-table)
                  0)))

(defthm count/copyable-of-creator/copyable
  (equal (count/copyable (creator/copyable))
         0))

(defthm count/copyable-of-updater/copyable-when-boundp/copyable
  (implies (boundp/copyable key hash-table)
           (equal (count/copyable (updater/copyable key val hash-table))
                  (count/copyable hash-table))))

(defthm count/copyable-of-updater/copyable-when-not-boundp/copyable
  (implies (not (boundp/copyable key hash-table))
           (equal (count/copyable (updater/copyable key val hash-table))
                  (1+ (count/copyable hash-table)))))

(defthm count/copyable-of-updater/copyable
  (equal (count/copyable (updater/copyable key val hash-table))
         (if (boundp/copyable key hash-table)
             (count/copyable hash-table)
             (1+ (count/copyable hash-table))))
  :hints
  (("Goal"
    :cases ((boundp/copyable key hash-table)))
   ("Subgoal 2"
    :by count/copyable-of-updater/copyable-when-not-boundp/copyable)
   ("Subgoal 1"
    :by count/copyable-of-updater/copyable-when-boundp/copyable)))

(defthm count/copyable-when-boundp/copyable
  (implies (boundp/copyable key hash-table)
           (posp (count/copyable hash-table)))
  :rule-classes :type-prescription)

(defthm count/copyable-of-remover/copyable-when-boundp/copyable
  (implies (boundp/copyable key hash-table)
           (equal (count/copyable (remover/copyable key hash-table))
                  (1- (count/copyable hash-table)))))

(defthm count/copyable-of-remover/copyable-when-not-boundp/copyable
  (implies (not (boundp/copyable key hash-table))
           (equal (count/copyable (remover/copyable key hash-table))
                  (count/copyable hash-table))))

(defthm count/copyable-of-remover/copyable
  (equal (count/copyable (remover/copyable key hash-table))
         (if (boundp/copyable key hash-table)
             (1- (count/copyable hash-table))
             (count/copyable hash-table))))

(defthm count/copyable-of-keys-set
  (equal (count/copyable (keys-set set hash-table))
         (count/copyable hash-table))
  :rule-classes
  ((:rewrite :corollary
             (equal (count/copyable (keys-set set hash-table))
                    (count/copyable (double-rewrite hash-table))))))

(defthm creator/copyable-when-count/copyable-is-zero
  (implies (and (set::emptyp (keys hash-table))
                (equal (count/copyable hash-table) 0))
           (equiv/copyable hash-table (creator/copyable)))
  :rule-classes
  ((:forward-chaining :trigger-terms
                      ((count/copyable hash-table)
                       (set::emptyp (keys hash-table)))
                      :corollary
                      (implies t
                               (implies (and (set::emptyp (keys hash-table))
                                             (equal (count/copyable hash-table) 0))
                                        (equiv/copyable hash-table (creator/copyable))))))
  :hints
  (("Goal"
    :in-theory (e/d (creator/unique
                     equiv/unique
                     set::emptyp
                     set::setp
                     set::sfix)
                    (creator/unique-when-count/unique-is-zero))
    :use ((:instance creator/unique-when-count/unique-is-zero
                     (hash-table (cdr hash-table)))))))


;;;; `CLEAR/COPYABLE'
(defthm clear/copyable-tp
  (and (consp (clear/copyable hash-table))
       (true-listp (clear/copyable hash-table)))
  :rule-classes :type-prescription)

(defthm clear/copyable-rw
  (equal (clear/copyable hash-table)
         (creator/copyable)))


;;;; `INIT/COPYABLE'
(defthm init/copyable-tp
  (and (consp (init/copyable ht-size rehash-size rehash-threshold hash-table))
       (true-listp (init/copyable ht-size rehash-size rehash-threshold hash-table)))
  :rule-classes :type-prescription)

(defthm init/copyable-rw
  (equal (init/copyable ht-size rehash-size rehash-threshold hash-table)
         (creator/copyable)))


;;;; `KEYS'
(defthm keys-tp
  (true-listp (keys hash-table))
  :rule-classes :type-prescription)

(defcong equiv/copyable equal (keys hash-table) 1)

(defthm keys-when-not-recognizer/copyable
  (implies (not (recognizer/copyable hash-table))
           (not (keys hash-table))))

(defthm keys-of-creator/copyable
  (not (keys (creator/copyable))))

(defthm keys-of-updater/copyable
  (equal (keys (updater/copyable key val hash-table))
         (keys hash-table)))

(defthm keys-of-remover/copyable
  (equal (keys (remover/copyable key hash-table))
         (keys hash-table)))

(defthm keys-of-keys-set
  (equal (keys (keys-set set hash-table))
         (keys-fix set))
  :rule-classes
  ((:rewrite :corollary
             (equal (keys (keys-set set hash-table))
                    (keys-fix (double-rewrite set))))))


;;;; `KEYS-SET'
(defthm keys-set-tp
  (and (consp (keys-set set hash-table))
       (true-listp (keys-set set hash-table)))
  :rule-classes :type-prescription)

(defcong keys-equiv equal (keys-set set hash-table) 1)

(defcong equiv/copyable equal (keys-set set hash-table) 2)

(defthm keys-set-when-not-keysp
  (implies (not (keysp set))
           (equal (keys-set set hash-table)
                  (keys-set '() hash-table))))

(defthm keys-set-when-not-recognizer/copyable
  (implies (not (recognizer/copyable hash-table))
           (equal (keys-set set hash-table)
                  (keys-set set (creator/copyable)))))

(defthm keys-set-of-creator/copyable
  (implies (set::emptyp set)
           (equal (keys-set set (creator/copyable))
                  (creator/copyable)))
  :hints
  (("Goal"
    :in-theory (enable set::emptyp))))

(defthm keys-set-of-updater/copyable
  (equal (keys-set set (updater/copyable key val hash-table))
         (updater/copyable key val (keys-set set hash-table))))

(defthm keys-set-of-remover/copyable
  (equal (keys-set set (remover/copyable key hash-table))
         (remover/copyable key (keys-set set hash-table))))

(defthm keys-set-of-keys-free
  (implies (keys-equiv set (keys hash-table))
           (equal (keys-set set hash-table)
                  (fixer/copyable hash-table))))

(defthm keys-set-of-keys
  (implies (equiv/copyable %hash-table hash-table)
           (equal (keys-set (keys %hash-table) hash-table)
                  (fixer/copyable hash-table)))
  :hints
  (("Goal"
    :do-not-induct t
    :in-theory (disable keys-set-of-keys-free)
    :use (:instance keys-set-of-keys-free
                    (set (keys hash-table))))))

(defthm keys-set-of-keys-set
  (equal (keys-set %set (keys-set set hash-table))
         (keys-set %set hash-table)))

(local
  (in-theory
    (disable keysp
             keys-fix

             recognizer/copyable
             creator/copyable
             fixer/copyable
             equiv/copyable
             accessor/copyable
             updater/copyable
             boundp/copyable
             getp/copyable
             remover/copyable
             count/copyable
             clear/copyable
             init/copyable

             keys
             keys-set

             keysp-def)))


;;;; `EQUAL/UNIQUE-FC'
(defun-sk keys-equal/unique (%hash-table hash-table)
  (declare (xargs :guard (and (recognizer/unique %hash-table)
                              (recognizer/unique hash-table))
                  :verify-guards nil))
  (forall key
    (equal (boundp/unique key %hash-table)
           (boundp/unique key hash-table)))
  :rewrite :direct)

(defun-sk vals-equal/unique (%hash-table hash-table)
  (declare (xargs :guard (and (recognizer/unique %hash-table)
                              (recognizer/unique hash-table))
                  :verify-guards nil))
  (forall key
    (equal (accessor/unique key %hash-table)
           (accessor/unique key hash-table)))
  :rewrite :direct)

(defun-nx equal/unique (%hash-table hash-table)
  (declare (xargs :guard t
                  :verify-guards nil))
  (and (recognizer/unique %hash-table)
       (recognizer/unique hash-table)
       (equal (count/unique %hash-table)
              (count/unique hash-table))
       (keys-equal/unique %hash-table hash-table)
       (vals-equal/unique %hash-table hash-table)))

(encapsulate ()
  (local
    (in-theory
      (disable keys-equal/unique
               vals-equal/unique)))

  (local
    (defthm keys-equal/unique-when-not-head-key-equal
      (implies (and (recognizer/unique %hash-table)
                    (recognizer/unique hash-table)
                    (not (omap::emptyp %hash-table))
                    (not (omap::emptyp hash-table))
                    (not (equal (omap::head-key %hash-table)
                                (omap::head-key hash-table))))
               (not (keys-equal/unique %hash-table hash-table)))
      :hints
      (("Goal"
        :do-not-induct t
        :cases ((<< (mv-nth 0 (omap::head %hash-table))
                    (mv-nth 0 (omap::head hash-table)))
                (<< (mv-nth 0 (omap::head hash-table))
                    (mv-nth 0 (omap::head %hash-table))))
        :in-theory (e/d (omap::head-key-minimal)
                        (keys-equal/unique-necc)))
       ("Subgoal 2"
        :cases ((keys-equal/unique %hash-table hash-table))
        :use ((:instance keys-equal/unique-necc
                         (key (mv-nth 0 (omap::head %hash-table)))))
        :expand (boundp/unique (mv-nth 0 (omap::head %hash-table))
                               hash-table))
       ("Subgoal 1"
        :cases ((keys-equal/unique %hash-table hash-table))
        :use ((:instance keys-equal/unique-necc
                         (key (mv-nth 0 (omap::head hash-table)))))
        :expand (boundp/unique (mv-nth 0 (omap::head hash-table))
                               %hash-table)))))

  (local
    (defthmd <<-squeeze
      (implies (and (not (<< x y))
                    (not (<< y x)))
               (equal x y))
      :rule-classes :forward-chaining))

  (local
    (defthm keys-equal/unique-of-tail-when-keys-equal/unique
      (implies (and (recognizer/unique %hash-table)
                    (recognizer/unique hash-table)
                    (not (omap::emptyp %hash-table))
                    (not (omap::emptyp hash-table))
                    (keys-equal/unique %hash-table hash-table))
               (keys-equal/unique (omap::tail %hash-table)
                                  (omap::tail hash-table)))
      :hints
      (("Goal"
        :do-not-induct t
        :cases ((<< (mv-nth 0 (omap::head %hash-table))
                    (mv-nth 0 (omap::head hash-table)))
                (<< (mv-nth 0 (omap::head hash-table))
                    (mv-nth 0 (omap::head %hash-table))))
        :in-theory (e/d (omap::head-key-minimal)
                        (keys-equal/unique-necc)))
       ("Subgoal 3"
        :use ((:instance <<-squeeze
                         (x (mv-nth 0 (omap::head %hash-table)))
                         (y (mv-nth 0 (omap::head hash-table))))
              (:instance keys-equal/unique-necc
                         (key (keys-equal/unique-witness (omap::tail %hash-table)
                                                         (omap::tail hash-table)))))
        :expand (keys-equal/unique (omap::tail %hash-table)
                                   (omap::tail hash-table)))
       ("Subgoal 2"
        :use ((:instance keys-equal/unique-necc
                         (key (mv-nth 0 (omap::head %hash-table)))))
        :expand (boundp/unique (mv-nth 0 (omap::head %hash-table))
                               hash-table))
       ("Subgoal 1"
        :use ((:instance keys-equal/unique-necc
                         (key (mv-nth 0 (omap::head hash-table)))))
        :expand (boundp/unique (mv-nth 0 (omap::head hash-table))
                               %hash-table)))))

  (local
    (defthm vals-equal/unique-when-not-head-key-equal
      (implies (and (recognizer/unique %hash-table)
                    (recognizer/unique hash-table)
                    (not (omap::emptyp %hash-table))
                    (not (omap::emptyp hash-table))
                    (keys-equal/unique %hash-table hash-table)
                    (not (equal (omap::head-val %hash-table)
                                (omap::head-val hash-table))))
               (not (vals-equal/unique %hash-table hash-table)))
      :hints
      (("Goal"
        :do-not-induct t
        :cases ((vals-equal/unique %hash-table hash-table))
        :in-theory (disable keys-equal/unique-necc
                            vals-equal/unique-necc
                            keys-equal/unique-when-not-head-key-equal)
        :use ((:instance vals-equal/unique-necc
                         (key (omap::head-key %hash-table)))
              (:instance vals-equal/unique-necc
                         (key (omap::head-key hash-table)))
              (:instance keys-equal/unique-when-not-head-key-equal))))))

  (local
    (defthm vals-equal/unique-of-tail-when-vals-equal/unique
      (implies (and (recognizer/unique %hash-table)
                    (recognizer/unique hash-table)
                    (not (omap::emptyp %hash-table))
                    (not (omap::emptyp hash-table))
                    (keys-equal/unique %hash-table hash-table)
                    (vals-equal/unique %hash-table hash-table))
               (vals-equal/unique (omap::tail %hash-table)
                                  (omap::tail hash-table)))
      :hints
      (("Goal"
        :do-not-induct t
        :cases ((<< (mv-nth 0 (omap::head %hash-table))
                    (mv-nth 0 (omap::head hash-table)))
                (<< (mv-nth 0 (omap::head hash-table))
                    (mv-nth 0 (omap::head %hash-table))))
        :in-theory (e/d (omap::head-key-minimal)
                        (keys-equal/unique-necc
                         vals-equal/unique-necc)))
       ("Subgoal 3"
        :cases ((key-equiv (vals-equal/unique-witness (omap::tail %hash-table)
                                                      (omap::tail hash-table))
                           (mv-nth 0 (omap::head %hash-table))))
        :use ((:instance <<-squeeze
                         (x (mv-nth 0 (omap::head %hash-table)))
                         (y (mv-nth 0 (omap::head hash-table))))
              (:instance vals-equal/unique-necc
                         (key (vals-equal/unique-witness (omap::tail %hash-table)
                                                         (omap::tail hash-table)))))
        :expand (vals-equal/unique (omap::tail %hash-table)
                                   (omap::tail hash-table)))
       ("Subgoal 2"
        :use ((:instance keys-equal/unique-necc
                         (key (mv-nth 0 (omap::head %hash-table)))))
        :expand (boundp/unique (mv-nth 0 (omap::head %hash-table))
                               hash-table))
       ("Subgoal 1"
        :use ((:instance keys-equal/unique-necc
                         (key (mv-nth 0 (omap::head hash-table)))))
        :expand (boundp/unique (mv-nth 0 (omap::head hash-table))
                               %hash-table)))))

  (local
    (defthmd omap-when-empty-map
      (implies (and (omap::emptyp map)
                    (omap::mapp map))
               (not map))
      :rule-classes :forward-chaining))

  (defthm equal/unique-fc
    (implies (equal/unique %hash-table hash-table)
             (equal %hash-table hash-table))
    :rule-classes
    ((:forward-chaining :trigger-terms
                        ((equal/unique %hash-table hash-table))
                        :corollary
                        (implies t
                                 (implies (equal/unique %hash-table hash-table)
                                          (equal %hash-table hash-table)))))
    :hints
    (("Goal"
      :induct (omap::omap-induction2 %hash-table hash-table))
     ("Subgoal *1/3"
      :do-not-induct t
      :use ((:instance keys-equal/unique-when-not-head-key-equal)
            (:instance vals-equal/unique-when-not-head-key-equal)))
     ("Subgoal *1/2"
      :do-not-induct t
      :in-theory (enable omap::unfold-equal-size-const)
      :expand ((count/unique %hash-table)
               (count/unique hash-table)
               (omap::size hash-table)))
     ("Subgoal *1/1"
      :do-not-induct t
      :in-theory (enable omap::unfold-equal-size-const
                         omap::size)
      :use ((:instance omap-when-empty-map
                       (map %hash-table))
            (:instance omap-when-empty-map
                       (map hash-table)))
      :expand ((count/unique %hash-table)
               (count/unique hash-table))))))

(local
  (in-theory
    (disable equal/unique)))


;;;; `EQUAL/COPYABLE-FC'
(defun-sk keys-equal/copyable (%hash-table hash-table)
  (declare (xargs :guard (and (recognizer/copyable %hash-table)
                              (recognizer/copyable hash-table))
                  :verify-guards nil))
  (forall key
    (equal (boundp/copyable key %hash-table)
           (boundp/copyable key hash-table)))
  :rewrite :direct)

(defun-sk vals-equal/copyable (%hash-table hash-table)
  (declare (xargs :guard (and (recognizer/copyable %hash-table)
                              (recognizer/copyable hash-table))
                  :verify-guards nil))
  (forall key
    (equal (accessor/copyable key %hash-table)
           (accessor/copyable key hash-table)))
  :rewrite :direct)

(defun-nx equal/copyable (%hash-table hash-table)
  (declare (xargs :guard t
                  :verify-guards nil))
  (and (recognizer/copyable %hash-table)
       (recognizer/copyable hash-table)
       (equal (keys %hash-table)
              (keys hash-table))
       (equal (count/copyable %hash-table)
              (count/copyable hash-table))
       (keys-equal/copyable %hash-table hash-table)
       (vals-equal/copyable %hash-table hash-table)))

(encapsulate ()
  (local
    (in-theory
      (disable keys-equal/unique
               vals-equal/unique
               keys-equal/copyable
               vals-equal/copyable)))

  (local
    (defthm keys-equal/copyable-iff-keys-equal/unique
      (implies (and (recognizer/copyable %hash-table)
                    (recognizer/copyable hash-table))
               (iff (keys-equal/copyable %hash-table
                                         hash-table)
                    (keys-equal/unique (cdr %hash-table)
                                       (cdr hash-table))))
      :hints
      (("Goal"
        :cases ((keys-equal/copyable %hash-table
                                     hash-table)
                (keys-equal/unique (cdr %hash-table)
                                   (cdr hash-table))))
       ("Subgoal 2"
        :in-theory (e/d (boundp/copyable)
                        (keys-equal/copyable-necc))
        :use ((:instance keys-equal/copyable-necc
                         (key (keys-equal/unique-witness (cdr %hash-table)
                                                         (cdr hash-table)))))
        :expand (keys-equal/unique (cdr %hash-table)
                                   (cdr hash-table)))
       ("Subgoal 1"
        :in-theory (e/d (boundp/copyable)
                        (keys-equal/copyable-necc))
        :expand (keys-equal/copyable %hash-table hash-table)))))

  (local
    (defthm vals-equal/copyable-iff-vals-equal/unique
      (implies (and (recognizer/copyable %hash-table)
                    (recognizer/copyable hash-table))
               (iff (vals-equal/copyable %hash-table
                                         hash-table)
                    (vals-equal/unique (cdr %hash-table)
                                       (cdr hash-table))))
      :hints
      (("Goal"
        :cases ((vals-equal/copyable %hash-table
                                     hash-table)
                (vals-equal/unique (cdr %hash-table)
                                   (cdr hash-table))))
       ("Subgoal 2"
        :in-theory (e/d (accessor/copyable)
                        (vals-equal/copyable-necc))
        :use ((:instance vals-equal/copyable-necc
                         (key (vals-equal/unique-witness (cdr %hash-table)
                                                         (cdr hash-table)))))
        :expand (vals-equal/unique (cdr %hash-table)
                                   (cdr hash-table)))
       ("Subgoal 1"
        :in-theory (e/d (accessor/copyable)
                        (vals-equal/copyable-necc))
        :expand (vals-equal/copyable %hash-table hash-table)))))

  (defthm equal/copyable-fc
    (implies (equal/copyable %hash-table hash-table)
             (equal %hash-table hash-table))
    :rule-classes
    ((:forward-chaining :trigger-terms
                        ((equal/copyable %hash-table hash-table))
                        :corollary
                        (implies t
                                 (implies (equal/copyable %hash-table hash-table)
                                          (equal %hash-table hash-table)))))
    :hints
    (("Goal"
      :do-not-induct t
      :in-theory (enable recognizer/copyable
                         count/copyable
                         keys)
      :use ((:instance equal/unique
                       (%hash-table (cdr %hash-table))
                       (hash-table (cdr hash-table))))))))

(local
  (in-theory
    (disable equal/copyable)))


;;;; Val Copy
(encapsulate (((val-coupledp *) => *))
  (local
    (defun val-coupledp (val)
      (declare (xargs :guard t)
               (ignore val))
      t))

  (defthm val-coupledp-tp
    (booleanp (val-coupledp val))
    :rule-classes :type-prescription)

  (defthm val-coupledp-when-not-val-recognizer
    (implies (not (val-recognizer val))
             (val-coupledp val)))

  (defthm val-coupledp-of-default-val
    (val-coupledp (default-val))))

(local
  (defcong val-equiv equal (val-coupledp val) 1
    :hints
    (("Goal"
      :in-theory (enable val-fixer)))))

(encapsulate (((val-copy * *) => *))
  (local
    (defun val-copy (%val val)
      (declare (xargs :guard (and (val-recognizer %val)
                                  (val-recognizer val)))
               (ignore %val))
      (if (val-coupledp val)
          (val-fixer val)
          (default-val))))

  (defthm val-recognizer-of-val-copy
    (val-recognizer (val-copy %val val)))

  (defthm val-coupledp-of-val-copy
    (val-coupledp (val-copy %val cal)))

  (defthm val-copy-ignores-1
    (equal (val-copy %value value)
           (val-copy (default-val) value))
    :rule-classes
    ((:rewrite :corollary
               (implies (syntaxp (not (and (consp %value)
                                           (eq (car %value) 'default-val))))
                        (equal (val-copy %value value)
                               (val-copy (default-val) value))))))

  (defthm val-copy-rw
    (implies (val-coupledp val)
             (equal (val-copy %val val)
                    (val-fixer val)))
    :rule-classes
    ((:rewrite :corollary
               (implies (val-coupledp (double-rewrite val))
                        (equal (val-copy %val val)
                               (val-fixer (double-rewrite val))))))))

(local
  (defcong val-equiv equal (val-copy %val val) 2
    :hints
    (("Goal"
      :in-theory (enable val-fixer)))))


;;;; `COUPLED-KEYS-P'
(defun-sk coupled-keys-p (hash-table)
  (declare (xargs :guard (recognizer/copyable hash-table)
                  :verify-guards nil))
  (forall key
    (equal (set::in key (keys hash-table))
           (and (key-recognizer key)
                (boundp/copyable key hash-table))))
  :rewrite :direct)

(defthm coupled-keys-p-tp
  (booleanp (coupled-keys-p hash-table))
  :rule-classes :type-prescription)

(defthm coupled-keys-p-when-not-recognizer/copyable
  (implies (not (recognizer/copyable hash-table))
           (coupled-keys-p hash-table)))

(defthm coupled-keys-p-of-creator/copyable
  (coupled-keys-p (creator/copyable)))

(local
  (in-theory
    (disable coupled-keys-p)))

(defcong equiv/copyable equal (coupled-keys-p hash-table) 1
  :hints
  (("Goal"
    :in-theory (enable fixer/copyable
                       equiv/copyable))))

(defthm coupled-keys-p-of-updater/copyable-when-boundp/copyable
  (implies (and (boundp/copyable key hash-table)
                (coupled-keys-p hash-table))
           (coupled-keys-p (updater/copyable key val hash-table)))
  :hints
  (("Goal"
    :expand (coupled-keys-p (updater/copyable key val hash-table)))))

(defthm coupled-keys-p-of-updater/copyable-when-not-boundp/copyable
  (implies (let* ((keys (keys hash-table))
                  (trimmed (set::delete (key-fixer key) keys)))
             (and (not (boundp/copyable key hash-table))
                  (set::in (key-fixer key) keys)
                  (coupled-keys-p (keys-set trimmed hash-table))))
           (coupled-keys-p (updater/copyable key val hash-table)))
  :hints
  (("Goal"
    :in-theory (disable coupled-keys-p-necc)
    :use ((:instance coupled-keys-p-necc
                     (key (coupled-keys-p-witness (updater/copyable key val hash-table)))
                     (hash-table (keys-set (set::delete (key-fixer key)
                                                        (keys hash-table))
                                           hash-table))))
    :expand (coupled-keys-p (updater/copyable key val hash-table)))))

(defthm coupled-keys-p-of-remover/copyable-when-boundp/copyable
  (implies (let* ((keys (keys hash-table))
                  (inserted (set::insert (key-fixer key) keys)))
             (and (boundp/copyable key hash-table)
                  (not (set::in (key-fixer key) keys))
                  (coupled-keys-p (keys-set inserted hash-table))))
           (coupled-keys-p (remover/copyable key hash-table)))
  :hints
  (("Goal"
    :in-theory (disable coupled-keys-p-necc)
    :use ((:instance coupled-keys-p-necc
                     (key (coupled-keys-p-witness (remover/copyable key hash-table)))
                     (hash-table (keys-set (set::insert (key-fixer key)
                                                        (keys hash-table))
                                           hash-table))))
    :expand (coupled-keys-p (remover/copyable key hash-table)))))

(defthm coupled-keys-p-of-remover/copyable-when-not-boundp/copyable
  (implies (and (not (boundp/copyable key hash-table))
                (coupled-keys-p hash-table))
           (coupled-keys-p (remover/copyable key hash-table))))

(local
  (in-theory
    (disable coupled-keys-p)))


;;;; `COUPLED-VALS-P'
(defun-sk coupled-vals-p (hash-table)
  (declare (xargs :guard (recognizer/copyable hash-table)
                  :verify-guards nil))
  (forall key
    (val-coupledp (accessor/copyable key hash-table)))
  :rewrite :direct)

(defthm coupled-vals-p-tp
  (booleanp (coupled-vals-p hash-table))
  :rule-classes :type-prescription)

(defthm coupled-vals-p-when-not-recognizer
  (implies (not (recognizer/copyable hash-table))
           (coupled-vals-p hash-table)))

(defthm coupled-vals-p-of-creator/copyable
  (coupled-vals-p (creator/copyable)))

(local
  (in-theory
    (disable coupled-vals-p)))

(defcong equiv/copyable equal (coupled-vals-p hash-table) 1
  :hints
  (("Goal"
    :in-theory (enable fixer/copyable
                       equiv/copyable))))

(defthm coupled-vals-p-of-updater/copyable
  (implies (coupled-vals-p hash-table)
           (equal (coupled-vals-p (updater/copyable key val hash-table))
                  (val-coupledp val)))
  :hints
  (("Goal"
    :cases ((coupled-vals-p (updater/copyable key val hash-table))))
   ("Subgoal 2"
    :expand (coupled-vals-p (updater/copyable key val hash-table)))
   ("Subgoal 1"
    :in-theory (disable coupled-vals-p-necc)
    :use ((:instance coupled-vals-p-necc
                     (key key)
                     (hash-table (updater/copyable key val hash-table)))))))

(defthm coupled-vals-p-of-remover/copyable
  (implies (coupled-vals-p hash-table)
           (coupled-vals-p (remover/copyable key hash-table)))
  :hints
  (("Goal"
    :expand (coupled-vals-p (remover/copyable key hash-table)))))

(defthm coupled-vals-p-of-keys-set
  (equal (coupled-vals-p (keys-set keys hash-table))
         (coupled-vals-p hash-table))
  :hints
  (("Goal"
    :cases ((coupled-vals-p (keys-set keys hash-table))))
   ("Subgoal 2"
    :expand (coupled-vals-p (keys-set keys hash-table)))
   ("Subgoal 1"
    :in-theory (disable coupled-vals-p-necc)
    :use ((:instance coupled-vals-p-necc
                     (key (coupled-vals-p-witness hash-table))
                     (hash-table (keys-set keys hash-table))))
    :expand (coupled-vals-p hash-table))))


;;;; `COUPLEDP'
(defun-nx coupledp (hash-table)
  (declare (xargs :guard (recognizer/copyable hash-table)
                  :verify-guards nil))
  (and (equal (set::cardinality (keys hash-table))
              (count/copyable hash-table))
       (coupled-keys-p hash-table)
       (coupled-vals-p hash-table)))

(defthm coupledp-tp
  (booleanp (coupledp hash-table))
  :rule-classes :type-prescription)

(defthm coupledp-when-not-recognizer/copyable
  (implies (not (recognizer/copyable hash-table))
           (coupledp hash-table)))

(defthm coupledp-of-creator/copyable
  (coupledp (creator/copyable)))

(defcong equiv/copyable equal (coupledp hash-table) 1
  :hints
  (("Goal"
    :in-theory (enable fixer/copyable
                       equiv/copyable))))

(defthm val-coupledp-of-accessor/copyable
  (implies (coupledp hash-table)
           (val-coupledp (accessor/copyable key hash-table))))

(defthm coupledp-of-updater/copyable-when-boundp/copyable
  (implies (and (boundp/copyable key hash-table)
                (coupledp hash-table))
           (equal (coupledp (updater/copyable key val hash-table))
                  (val-coupledp val))))

(defthm coupledp-of-updater/copyable-when-not-boundp/copyable
  (implies (let* ((keys (keys hash-table))
                  (trimmed (set::delete (key-fixer key) keys)))
             (and (not (boundp/copyable key hash-table))
                  (set::in (key-fixer key) keys)
                  (coupledp (keys-set trimmed hash-table))))
           (equal (coupledp (updater/copyable key val hash-table))
                  (val-coupledp val)))
  :hints
  (("Goal"
    :in-theory (enable set::delete-cardinality))))

(defthm in-of-keys-when-coupledp
  (implies (coupledp hash-table)
           (equal (set::in key (keys hash-table))
                  (and (key-recognizer key)
                       (boundp/copyable key hash-table))))
  :rule-classes
  ((:rewrite :corollary
             (implies (coupledp hash-table)
                      (equal (set::in key (keys hash-table))
                             (and (key-recognizer key)
                                  (boundp/copyable (double-rewrite key) hash-table)))))))

(defthm coupledp-of-remover/copyable-when-boundp/copyable
  (implies (let* ((keys (keys hash-table))
                  (inserted (set::insert (key-fixer key) keys)))
             (and (boundp/copyable key hash-table)
                  (not (set::in (key-fixer key) keys))
                  (coupledp (keys-set inserted hash-table))))
           (coupledp (remover/copyable key hash-table)))
  :hints
  (("Goal"
    :in-theory (enable set::insert-cardinality))))

(defthm coupledp-of-remover/copyable-when-not-boundp/copyable
  (implies (and (not (boundp/copyable key hash-table))
                (coupledp hash-table))
           (coupledp (remover/copyable key hash-table))))

(defthm cardinality-of-keys-when-coupledp
  (implies (coupledp hash-table)
           (equal (set::cardinality (keys hash-table))
                  (count/copyable hash-table))))

(defthm emptyp-of-keys-when-coupledp
  (implies (coupledp hash-table)
           (equal (set::emptyp (keys hash-table))
                  (equiv/copyable hash-table (creator/copyable))))
  :hints
  (("Goal"
    :cases ((set::emptyp (keys hash-table))))
   ("Subgoal 1"
    :in-theory (disable set::cardinality-zero-emptyp)
    :use ((:instance set::cardinality-zero-emptyp
                     (x (keys hash-table)))))))

(local
  (in-theory
    (disable coupledp)))


;;;; `COPY-REC'
(defun copy-rec (set %hash-table hash-table)
  (declare (xargs :guard (and (keysp set)
                              (recognizer/copyable %hash-table)
                              (recognizer/copyable hash-table)
                              (set::subset set (keys hash-table)))
                  :guard-hints
                  (("Goal"
                    :in-theory (enable set::subset)))))
  (if (or (set::emptyp set)
          (not (keysp set)))
      (fixer/copyable %hash-table)
      (let* ((key (set::head set))
             (val (accessor/copyable key hash-table))
             (%val (accessor/copyable key %hash-table))
             (%val (val-copy %val val))
             (%hash-table (updater/copyable key %val %hash-table))
             (hash-table (updater/copyable key val hash-table)))
        (copy-rec (set::tail set) %hash-table hash-table))))

(local
  (defthm recognizer/copyable-of-copy-rec
    (recognizer/copyable (copy-rec set %hash-table hash-table))))

(local
  (defcong keys-equiv equal (copy-rec set %hash-table hash-table) 1
    :hints
    (("Goal"
      :in-theory (enable keys-fix)))))

(local
  (defcong equiv/copyable equal (copy-rec set %hash-table hash-table) 2))

(local
  (defcong equiv/copyable equal (copy-rec set %hash-table hash-table) 3))

(local
  (defthm copy-rec-of-updater/copyable-2
    (implies (keysp set)
             (equal (copy-rec set (updater/copyable key val %hash-table) hash-table)
                    (if (set::in (key-fixer key) set)
                        (copy-rec set %hash-table hash-table)
                        (updater/copyable key val (copy-rec set %hash-table hash-table)))))
    :hints
    (("Goal"
      :induct (copy-rec set %hash-table hash-table)
      :in-theory (enable set::subset
                         set::in)
      :expand (copy-rec set (updater/copyable key val %hash-table) hash-table)))))

(local
  (defthm copy-rec-of-updater/copyable-3
    (implies (and (keysp set)
                  (not (set::in (key-fixer key) set)))
             (equal (copy-rec set %hash-table (updater/copyable key val hash-table))
                    (copy-rec set %hash-table hash-table)))
    :hints
    (("Goal"
      :in-theory (enable set::subset
                         set::in)
      :expand (copy-rec set %hash-table (updater/copyable key val hash-table))))))

(local
  (defthm accessor/copyable-of-copy-rec
    (implies (keysp set)
             (equal (accessor/copyable key (copy-rec set %hash-table hash-table))
                    (if (set::in (key-fixer key) set)
                        (val-copy (default-val)
                                  (accessor/copyable key hash-table))
                        (accessor/copyable key %hash-table))))
    :hints
    (("Goal"
      :induct (copy-rec set %hash-table hash-table)
      :in-theory (enable set::in
                         set::subset)))))

(local
  (defthm boundp/copyable-of-copy-rec
    (implies (keysp set)
             (equal (boundp/copyable key (copy-rec set %hash-table hash-table))
                    (or (boundp/copyable key %hash-table)
                        (set::in (key-fixer key) set))))
    :hints
    (("Goal"
      :induct (copy-rec set %hash-table hash-table)
      :in-theory (enable set::in
                         set::subset)))))

(local
  (defthm count/copyable-of-copy-rec
    (implies (keysp set)
             (equal (count/copyable (copy-rec set %hash-table hash-table))
                    (cond
                      ((or (set::emptyp set)
                           (not (keysp set)))
                       (count/copyable %hash-table))
                      ((boundp/copyable (set::head set) %hash-table)
                       (count/copyable (copy-rec (set::tail set) %hash-table hash-table)))
                      (t
                       (1+ (count/copyable (copy-rec (set::tail set) %hash-table hash-table)))))))
    :rule-classes
    ((:rewrite :corollary
               (implies (and (syntaxp (not (and (consp set)
                                                (eq (car set) 'set::tail))))
                             (set::subset set (keys hash-table)))
                        (equal (count/copyable (copy-rec set %hash-table hash-table))
                               (cond
                                 ((or (set::emptyp set)
                                      (not (keysp set)))
                                  (count/copyable %hash-table))
                                 ((boundp/copyable (set::head set) %hash-table)
                                  (count/copyable (copy-rec (set::tail set) %hash-table hash-table)))
                                 (t
                                  (1+ (count/copyable (copy-rec (set::tail set) %hash-table hash-table)))))))))))

(local
  (defthm count/copyable-of-copy-rec-of-creator/copyable
    (implies (keysp set)
             (equal (count/copyable (copy-rec set (creator/copyable) hash-table))
                    (set::cardinality set)))
    :hints
    (("Goal"
      :in-theory (enable set::cardinality)))))

(local
  (defthm keys-of-copy-rec
    (equal (keys (copy-rec set %hash-table hash-table))
           (keys %hash-table))))

(local
  (defthm copy-rec-of-keys-set
    (equal (copy-rec %set (keys-set set %hash-table) hash-table)
           (keys-set set (copy-rec %set %hash-table hash-table)))))

(local
  (defthm coupled-vals-p-of-copy-rec
    (implies (coupled-vals-p %hash-table)
             (coupled-vals-p (copy-rec set %hash-table hash-table)))))

(local
  (in-theory
    (disable copy-rec)))


;;;; `COPY'
(defun copy (%hash-table hash-table)
  (declare (xargs :guard (and (recognizer/copyable %hash-table)
                              (recognizer/copyable hash-table))))
  (let* ((keys (keys hash-table))
         (count (count/copyable hash-table))
         (%hash-table (init/copyable count nil nil %hash-table))
         (%hash-table (keys-set keys %hash-table)))
    (copy-rec keys %hash-table hash-table)))

(defthm recognizer/copyable-of-copy
  (recognizer/copyable (copy %hash-table hash-table)))

(defthm copy-ignores-1
  (equal (copy %hash-table hash-table)
         (copy (creator/copyable) hash-table))
  :rule-classes
  ((:rewrite :corollary
             (implies (syntaxp (not (and (consp %hash-table)
                                         (eq (car %hash-table) 'creator/copyable))))
                      (equal (copy %hash-table hash-table)
                             (copy (creator/copyable) hash-table)))))
  :hints
  (("Goal"
    :use ((:instance equal/copyable
                     (%hash-table (copy %hash-table hash-table))
                     (hash-table (copy (creator/copyable) hash-table)))))))

(defcong equiv/copyable equal (copy %hash-table hash-table) 2
  :hints
  (("Goal"
    :use ((:instance equal/copyable
                     (%hash-table (copy %hash-table hash-table))
                     (hash-table (copy %hash-table hash-table-equiv)))))))

(defthm coupled-keys-p-of-copy
  (coupled-keys-p (copy %hash-table hash-table))
  :hints
  (("Goal"
    :expand (coupled-keys-p (keys-set (keys hash-table)
                                      (copy-rec (keys hash-table)
                                                (creator/copyable)
                                                hash-table))))))

(defthm coupled-vals-p-of-copy
  (coupled-vals-p (copy %hash-table hash-table)))

(defthm count/copyable-of-copy
  (equal (count/copyable (copy %hash-table hash-table))
         (set::cardinality (keys hash-table))))

(defthm accessor/copyable-of-copy
  (equal (accessor/copyable key (copy %hash-table hash-table))
         (if (set::in (key-fixer key) (keys hash-table))
             (val-copy (default-val) (accessor/copyable key hash-table))
             (default-val))))

(defthm boundp/copyable-of-copy
  (equal (boundp/copyable key (copy %hash-table hash-table))
         (set::in (key-fixer key) (keys hash-table))))

(defthm keys-of-copy
  (equal (keys (copy %hash-table hash-table))
         (keys hash-table)))

(defthm coupledp-of-copy
  (coupledp (copy %hash-table hash-table))
  :hints
  (("Goal"
    :in-theory (enable coupledp))))

(defthm copy-of-updater/copyable
  (equal (copy %hash-table (updater/copyable key val hash-table))
         (if (set::in (key-fixer key) (keys hash-table))
             (updater/copyable key
                               (val-copy (default-val) val)
                               (copy %hash-table hash-table))
             (copy %hash-table hash-table)))
  :hints
  (("Goal"
    :use ((:instance equal/copyable
                     (%hash-table (copy %hash-table (updater/copyable key val hash-table)))
                     (hash-table (if (set::in (key-fixer key) (keys hash-table))
                                     (updater/copyable key
                                                       (val-copy (default-val) val)
                                                       (copy %hash-table hash-table))
                                     (copy %hash-table hash-table))))))))

(defthm copy-of-remover/copyable
  (equal (copy %hash-table (remover/copyable key hash-table))
         (if (set::in (key-fixer key) (keys hash-table))
             (updater/copyable key
                               (default-val)
                               (copy %hash-table hash-table))
             (copy %hash-table hash-table)))
  :hints
  (("Goal"
    :use ((:instance equal/copyable
                     (%hash-table (copy %hash-table (remover/copyable key hash-table)))
                     (hash-table (if (set::in (key-fixer key) (keys hash-table))
                                     (updater/copyable key
                                                       (default-val)
                                                       (copy %hash-table hash-table))
                                     (copy %hash-table hash-table))))))))

(local
  (in-theory
    (disable copy)))

(defthm copy-rw
  (implies (coupledp hash-table)
           (equal (copy %hash-table hash-table)
                  (fixer/copyable hash-table)))
  :hints
  (("Goal"
    :use ((:instance equal/copyable
                     (%hash-table (copy %hash-table hash-table))
                     (hash-table (fixer/copyable hash-table)))))))


;;;; Value Export
(encapsulate (((name) => *)
              ((val-export-p *) => *)
              ((val-export *) => *)
              ((val-import * *) => *))
  (local
    (defun name ()
      (declare (xargs :guard t))
      nil))

  (defthm name-tp
    (symbolp (name))
    :rule-classes :type-prescription)

  (local
    (defun val-export-p (export)
      (declare (xargs :guard t))
      (and (val-recognizer export)
           (val-coupledp export))))

  (defthm val-export-p-tp
    (booleanp (val-export-p export))
    :rule-classes :type-prescription)

  (local
    (defun val-export (val)
      (declare (xargs :guard (val-recognizer val)))
      (if (val-coupledp val)
          (val-fixer val)
          (default-val))))

  (defthm val-export-p-of-val-export
    (val-export-p (val-export val)))

  (defcong val-equiv equal (val-export val) 1
    :hints
    (("Goal"
      :in-theory (disable val-equiv))))

  (local
    (defun val-import (export val)
      (declare (xargs :guard (and (val-export-p export)
                                  (val-recognizer val)))
               (ignore val))
      (if (val-coupledp export)
          (val-fixer export)
          (default-val))))

  (defthm val-recognizer-of-val-import
    (val-recognizer (val-import export val)))

  (defthm val-coupledp-of-val-import
    (val-coupledp (val-import export val)))

  (defthm val-import-when-not-val-export-p
    (implies (not (val-export-p export))
             (equal (val-import export val)
                    (default-val))))

  (defthm val-import-ignores-2
    (equal (val-import export val)
           (val-import export (default-val)))
    :rule-classes
    ((:rewrite :corollary
               (implies (syntaxp (not (and (consp val)
                                           (eq (car val) 'default-val))))
                        (equal (val-import export val)
                               (val-import export (default-val)))))))

  (defthm val-export-of-val-import
    (implies (val-export-p export)
             (equal (val-export (val-import export val))
                    export)))

  (defthm val-import-of-val-export
    (implies (val-coupledp %val)
             (equal (val-import (val-export %val) val)
                    (val-fixer %val)))))


;;;; `EXPORTP-REC'
(defun exportp-rec (map)
  (declare (xargs :guard t))
  (if (consp map)
      (and (consp (car map))
           (key-recognizer (caar map))
           (val-export-p (cdar map))
           (or (null (cdr map))
               (and (consp (cdr map))
                    (consp (cadr map))
                    (<< (caar map) (caadr map))
                    (exportp-rec (cdr map)))))
      (null map)))

(defthm exportp-rec-tp
  (booleanp (exportp-rec map))
  :rule-classes :type-prescription)

(defthm exportp-rec-cr
  (implies (exportp-rec map)
           (true-listp map))
  :rule-classes :compound-recognizer)

(local
  (defthm exportp-rec-def
    (equal (exportp-rec map)
           (if (omap::emptyp map)
               (null map)
               (mv-let (key val)
                       (omap::head map)
                 (and (key-recognizer key)
                      (val-export-p val)
                      (exportp-rec (omap::tail map))))))
    :rule-classes
    ((:definition :controller-alist ((exportp-rec t))))
    :hints
    (("Goal"
      :in-theory (enable omap::mapp
                         omap::mfix
                         omap::emptyp
                         omap::head
                         omap::tail)))))

(local
  (in-theory
    (disable exportp-rec)))

(defthm mapp-when-exportp-rec
  (implies (exportp-rec map)
           (omap::mapp map))
  :hints
  (("Goal"
    :expand (exportp-rec map))))

(local
  (defthm exportp-rec-when-emptyp
    (implies (omap::emptyp map)
             (equal (exportp-rec map)
                    (null map)))))

(defthm key-recognizer-head-when-exportp-rec
  (implies (and (not (omap::emptyp map))
                (exportp-rec map))
           (key-recognizer (mv-nth 0 (omap::head map)))))

(defthm val-export-p-head-when-exportp-rec
  (implies (and (not (omap::emptyp map))
                (exportp-rec map))
           (val-export-p (mv-nth 1 (omap::head map)))))

(defthm exportp-rec-of-tail
  (implies (exportp-rec map)
           (exportp-rec (omap::tail map))))

(local
  (defthm key-recognizer-when-exportp-rec
    (implies (and (exportp-rec map)
                  (not (key-recognizer key)))
             (not (set::in key (omap::keys map))))
    :hints
    (("Goal"
      :in-theory (enable omap::keys)))))

(local
  (defthm val-export-p-when-exportp-rec
    (implies (and (exportp-rec map)
                  (not (val-export-p val)))
             (not (set::in val (omap::values map))))
    :hints
    (("Goal"
      :in-theory (enable omap::values)))))

(defthm exportp-rec-of-update
  (implies (and (exportp-rec map)
                (key-recognizer key)
                (val-export-p val))
           (exportp-rec (omap::update key val map)))
  :hints
  (("Goal"
    :induct (omap::size map)
    :in-theory (enable omap::size))
   ("Subgoal *1/2"
    :expand (exportp-rec (omap::update key val map)))))

(defthm keysp-of-keys-when-exportp-rec
  (implies (exportp-rec map)
           (keysp (omap::keys map)))
  :hints
  (("Goal"
    :induct (omap::keys map)
    :in-theory (enable keysp-def
                       omap::keys))))

(local
  (in-theory
    (disable exportp-rec)))


;;;; `EXPORTP'
(defun exportp (export)
  (declare (xargs :guard t))
  (and (consp export)
       (equal (car export) (name))
       (exportp-rec (cdr export))))

(defthm exportp-tp
  (booleanp (exportp export))
  :rule-classes :type-prescription)

(defthm exportp-cr
  (implies (exportp export)
           (and (consp export)
                (true-listp export)))
  :rule-classes :compound-recognizer)

(local
  (in-theory
    (disable exportp)))


;;;; `EXPORT-ACC'
(defun export-acc (set acc hash-table)
  (declare (xargs :guard (and (keysp set)
                              (exportp-rec acc)
                              (recognizer/copyable hash-table))))
  (if (or (set::emptyp set)
          (not (keysp set)))
      (omap::mfix acc)
      (let* ((key (set::head set))
             (val (accessor/copyable key hash-table))
             (export (val-export val)))
        ;; TODO: I'd like this function to run in linear time by consing a list,
        ;; reversing it, and then proving that the result is the desired omap.
        ;; Time does not permit.
        (export-acc (set::tail set) (omap::update key export acc) hash-table))))

(local
  (defthm export-acc-tp
    (true-listp (export-acc set acc hash-table))
    :rule-classes :type-prescription))

(local
  (defthm exportp-rec-of-export-acc
    (implies (exportp-rec acc)
             (exportp-rec (export-acc set acc hash-table)))))

(local
  (defcong equiv/copyable equal (export-acc set acc hash-table) 3))

(local
  (defthm keys-of-export-acc
    (equal (omap::keys (export-acc set acc hash-table))
           (if (keysp set)
               (set::union set (omap::keys acc))
               (omap::keys acc)))
    :hints
    (("Goal"
      :in-theory (enable set::union)))))

(local
  (defthm export-acc-of-keys-set
    (equal (export-acc %set acc (keys-set set hash-table))
           (export-acc %set acc hash-table))))

(local
  (defthm export-acc-of-update-2
    (equal (export-acc set (omap::update key val acc) hash-table)
           (cond
             ((or (set::emptyp set)
                  (not (keysp set)))
              (omap::update key val acc))
             ((set::in key set)
              (export-acc set acc hash-table))
             (t
              (omap::update key val (export-acc set acc hash-table)))))
    :hints
    (("Goal"
      :in-theory (enable set::in)))))

(local
  (defthm export-acc-of-update-3
    (implies (and (not (set::in (key-fixer key) set)))
             (equal (export-acc set acc (updater/copyable key val hash-table))
                    (export-acc set acc hash-table)))
    :hints
    (("Goal"
      :in-theory (enable set::in)))))

(local
  (defthm export-acc-of-insert-lemma
    (implies (and (set::in key set)
                  (key-recognizer key)
                  (keysp set))
             (equal (omap::update key
                                  (val-export (accessor/copyable key hash-table))
                                  (export-acc set acc hash-table))
                    (export-acc set acc hash-table)))))

(local
  (defthm export-acc-of-insert
    (implies (key-recognizer key)
             (equal (export-acc (set::insert key set) acc hash-table)
                    (cond
                      ((set::emptyp set)
                       (omap::update key
                                     (val-export (accessor/copyable key hash-table))
                                     acc))
                      ((not (keysp set))
                       (omap::mfix acc))
                      (t
                       (omap::update key
                                     (val-export (accessor/copyable key hash-table))
                                     (export-acc set acc hash-table))))))
    :rule-classes
    ((:rewrite :corollary
               (implies (key-recognizer key)
                        (equal (export-acc (set::insert key set) acc hash-table)
                               (cond
                                 ((set::emptyp set)
                                  (omap::update key
                                                (val-export (accessor/copyable (double-rewrite key) hash-table))
                                                acc))
                                 ((not (keysp set))
                                  (omap::mfix acc))
                                 (t
                                  (omap::update key
                                                (val-export (accessor/copyable (double-rewrite key) hash-table))
                                                (export-acc set acc hash-table))))))))
    :hints
    (("Subgoal 1"
      :induct (set::weak-insert-induction key set))
     ("Subgoal *1/5"
      :expand ((export-acc (set::insert key set)
                           acc hash-table)
               (export-acc set acc hash-table)))
     ("Subgoal *1/3"
      :expand ((export-acc (set::insert key set)
                           acc hash-table)
               (export-acc set acc hash-table))))))

(local
  (defthm cardinality-of-keys
    (equal (set::cardinality (omap::keys map))
           (omap::size map))
    :hints
    (("Goal"
      :in-theory (enable set::cardinality
                         omap::size
                         omap::keys
                         set::insert-cardinality)))))

(local
  #!omap
  (defthm size-of-mfix-map
    ;; BUG: This theorem is listed in the docs but not in the source!
    (equal (size (mfix map)) (size map))
    :hints
    (("Goal"
      :in-theory (enable size)))))

(local
  (defthm size-of-export-acc
    (equal (omap::size (export-acc set acc hash-table))
           (if (keysp set)
               (set::cardinality (set::union set (omap::keys acc)))
               (omap::size acc)))
    :hints
    (("Goal"
      :induct (export-acc set acc hash-table)
      :in-theory (enable set::insert-cardinality
                         set::cardinality
                         set::intersect
                         set::in
                         omap::assoc-to-in-of-keys)))))

(local
  (defthm assoc-of-export-acc
    (equal (omap::assoc key (export-acc set acc hash-table))
           (if (and (keysp set)
                    (set::in key set))
               (cons key (val-export (accessor/copyable (double-rewrite key) hash-table)))
               (omap::assoc key acc)))))

(local
  (in-theory
    (disable export-acc)))


;;;; `EXPORT'
(defun export (hash-table)
  (declare (xargs :guard (recognizer/copyable hash-table)))
  (cons (name)
        (export-acc (keys hash-table) () hash-table)))

(defthm export-tp
  (and (consp (export hash-table))
       (true-listp (export hash-table)))
  :rule-classes :type-prescription)

(defthm exportp-of-export
  (exportp (export hash-table))
  :hints
  (("Goal"
    :in-theory (enable exportp))))

(local
  (defcong equiv/copyable equal (export hash-table) 1))

(local
  (defthm keys-of-export
    (equal (omap::keys (cdr (export hash-table)))
           (keys hash-table))))

(local
  (defthm size-of-export
    (equal (omap::size (cdr (export hash-table)))
           (set::cardinality (keys hash-table)))))

(local
  (defthm assoc-of-export
    (equal (omap::assoc key (cdr (export hash-table)))
           (and (set::in key (keys hash-table))
                (cons key (val-export (accessor/copyable key hash-table)))))
    :rule-classes
    ((:rewrite :corollary
               (equal (omap::assoc key (cdr (export hash-table)))
                      (and (set::in key (keys hash-table))
                           (cons key (val-export (accessor/copyable (double-rewrite key) hash-table)))))))))

(local
  (in-theory
    (disable export)))


;;;; `IMPORT-REC'
(defun import-rec (map hash-table)
  (declare (xargs :guard (and (exportp-rec map)
                              (recognizer/copyable hash-table))))
  (if (or (omap::emptyp map)
          (not (exportp-rec map)))
      (fixer/copyable hash-table)
      (mv-let (key val-export)
              (omap::head map)
        (let* ((val (accessor/copyable key hash-table))
               (val (val-import val-export val))
               (hash-table (updater/copyable key val hash-table)))
          (import-rec (omap::tail map) hash-table)))))

(defthm import-rec-tp
  (and (consp (import-rec map hash-table))
       (true-listp (import-rec map hash-table)))
  :rule-classes :type-prescription)

(local
  (defthm recognizer/copyable-of-import-rec
    (recognizer/copyable (import-rec map hash-table))))

(local
  (defcong equiv/copyable equal (import-rec map hash-table) 2))

(local
  (defthm keys-of-import-rec
    (equal (keys (import-rec map hash-table))
           (keys hash-table))
    :rule-classes
    ((:rewrite :corollary
               (equal (keys (import-rec map hash-table))
                      (keys (double-rewrite hash-table)))))))

(local
  (defthm import-rec-of-updater/copyable
    (implies (exportp-rec map)
             (equal (import-rec map (updater/copyable key val hash-table))
                    (if (omap::assoc (key-fixer key) map)
                        (import-rec map hash-table)
                        (updater/copyable key val (import-rec map hash-table)))))
    :otf-flg t))

(local
  (defthm boundp/copyable-of-import-rec
    (implies (exportp-rec map)
             (equal (boundp/copyable key (import-rec map hash-table))
                    (and (or (boundp/copyable key hash-table)
                             (omap::assoc (key-fixer key) map))
                         t)))
    :rule-classes
    ((:rewrite :corollary
               (implies (exportp-rec map)
                        (equal (boundp/copyable key (import-rec map hash-table))
                               (and (or (boundp/copyable key (double-rewrite hash-table))
                                        (omap::assoc (key-fixer key) map))
                                    t)))))))

(local
  (defthm accessor/copyable-of-import-rec
    (implies (exportp-rec map)
             (equal (accessor/copyable key (import-rec map hash-table))
                    (let ((pair (omap::assoc (key-fixer key) map)))
                      (if pair
                          (val-import (cdr pair) (default-val))
                          (accessor/copyable key hash-table)))))))

(local
  (defthm count/copyable-of-import-rec
    (implies (exportp-rec map)
             (equal (count/copyable (import-rec map hash-table))
                    (cond
                      ((omap::emptyp map)
                       (count/copyable hash-table))
                      ((boundp/copyable (omap::head-key map) hash-table)
                       (count/copyable (import-rec (omap::tail map) hash-table)))
                      (t
                       (1+ (count/copyable (import-rec (omap::tail map) hash-table)))))))
    :rule-classes
    ((:rewrite :corollary
               (implies (and (syntaxp (not (and (consp map)
                                                (eq (car map) 'omap::tail))))
                             (exportp-rec map))
                        (equal (count/copyable (import-rec map hash-table))
                               (cond
                                 ((omap::emptyp map)
                                  (count/copyable (double-rewrite hash-table)))
                                 ((boundp/copyable (omap::head-key map) (double-rewrite hash-table))
                                  (count/copyable (import-rec (omap::tail map) hash-table)))
                                 (t
                                  (1+ (count/copyable (import-rec (omap::tail map) hash-table)))))))))))

(local
  (defthm count/copyable-of-import-rec-of-creator/copyable
    (implies (exportp-rec map)
             (equal (count/copyable (import-rec map (creator/copyable)))
                    (omap::size map)))))

(local
  (defthm coupled-keys-p-of-keys-set-of-import-rec
    (implies (exportp-rec map)
             (coupled-keys-p (keys-set (omap::keys map)
                                       (import-rec map (creator/copyable)))))
    :hints
    (("Goal"
      :in-theory (enable omap::keys)))))

(local
  (defthm coupled-vals-p-of-import-rec
    (implies (coupled-vals-p hash-table)
             (coupled-vals-p (import-rec map hash-table)))))

(local
  (in-theory
    (disable import-rec)))


;;;; `IMPORT'
(defun import (export hash-table)
  (declare (xargs :guard (and (exportp export)
                              (recognizer/copyable hash-table))
                  :guard-hints
                  (("Goal"
                    :in-theory (enable exportp)))))
  (if (exportp export)
      (let* ((map (cdr export))
             (count (omap::size map))
             (hash-table (init/copyable count nil nil hash-table))
             (hash-table (import-rec map hash-table))
             (hash-table (keys-set (omap::keys map) hash-table)))
        hash-table)
      (creator/copyable)))

(defthm import-tp
  (and (consp (import export hash-table))
       (true-listp (import export hash-table)))
  :rule-classes :type-prescription)

(defthm recognizer/copyable-of-import
  (recognizer/copyable (import export hash-table)))

(defthm coupledp-of-import
  (coupledp (import export hash-table))
  :hints
  (("Goal"
    :in-theory (enable coupledp
                       exportp))))

(defthm import-when-not-exportp
  (implies (not (exportp export))
           (equal (import export hash-table)
                  (creator/copyable))))

(defthm import-ignores-2
  (equal (import export hash-table)
         (import export (creator/copyable)))
  :rule-classes
  ((:rewrite :corollary
             (implies (syntaxp (not (and (consp hash-table)
                                         (eq (car hash-table) 'creator/copyable))))
                      (equal (import export hash-table)
                             (import export (creator/copyable)))))))

(defthm keys-of-import
  (equal (keys (import export hash-table))
         (and (exportp export)
              (omap::keys (cdr export))))
  :hints
  (("Goal"
    :in-theory (enable exportp))))

(defthm boundp/copyable-of-import
  (equal (boundp/copyable key (import export hash-table))
         (and (omap::assoc (key-fixer key) (cdr export))
              (exportp export)))
  :hints
  (("Goal"
    :in-theory (enable exportp))))

(defthm accessor/copyable-of-import
  (equal (accessor/copyable key (import export hash-table))
         (let ((pair (omap::assoc (key-fixer key) (cdr export))))
           (if (and (exportp export)
                    pair)
               (val-import (cdr pair) (default-val))
               (default-val))))
  :hints
  (("Goal"
    :in-theory (enable exportp))))

(encapsulate ()
  (local
    (defthm count/copyable-of-import-lemma
      (implies (exportp-rec map)
               (equal (count/copyable (import-rec map (creator/copyable)))
                      (omap::size map)))
      :hints
      (("Goal"
        :in-theory (enable omap::size)))))

  (defthm count/copyable-of-import
    (equal (count/copyable (import export hash-table))
           (if (exportp export)
               (omap::size (cdr export))
               0))
    :hints
    (("Goal"
      :in-theory (e/d (exportp)
                      (count/copyable-of-import-rec))))))

(local
  (in-theory
    (disable import)))


;;;; `EXPORT' and `IMPORT' Composition Theorems
(local
  (defthm emptyp-of-keys
    (equal (set::emptyp (omap::keys map))
           (omap::emptyp map))
    :hints
    (("Goal"
      :in-theory (enable omap::keys)))))

(encapsulate ()
  (local
    (defthm export-of-import-lemma-1
      (implies (and (not (omap::emptyp map))
                    (exportp-rec map))
               (key-recognizer (mv-nth 0 (omap::head map))))))

  (local
    (defthm export-of-import-lemma-2
      (implies (and (not (omap::emptyp map))
                    (exportp-rec map))
               (val-export-p (mv-nth 1 (omap::head map))))))

  (local
    (defthm export-of-import-lemma-3
      (implies (and (not (omap::emptyp map))
                    (exportp-rec map))
               (equal (export-acc (omap::keys map)
                                  nil
                                  (import-rec map
                                              (creator/copyable)))
                      map))
      :hints
      (("Goal"
        :induct (omap::keys map)
        :in-theory (enable omap::keys
                           omap::assoc))
       ("Subgoal *1/1"
        :expand (import-rec map (creator/copyable))))))

  (defthm export-of-import
    (implies (exportp export)
             (equal (export (import export hash-table))
                    export))
    :hints
    (("Goal"
      :do-not-induct t
      :in-theory (e/d (exportp
                       export
                       import)
                      (cons-equal))
      :use ((:instance cons-equal
                       (x1 (name))
                       (y1 (export-acc (omap::keys (cdr export))
                                       nil
                                       (keys-set (omap::keys (cdr export))
                                                 (import-rec (cdr export)
                                                             (creator/copyable)))))
                       (x2 (car export))
                       (y2 (cdr export)))))
     ("Subgoal 1"
      :expand ((import-rec nil (creator/copyable))
               (export-acc nil nil (creator/copyable)))))))

(defthm import-of-export
  (implies (coupledp %hash-table)
           (equal (import (export %hash-table) hash-table)
                  (fixer/copyable %hash-table)))
  :hints
  (("Goal"
    :in-theory (disable import
                        export)
    :use ((:instance equal/copyable
                     (%hash-table (import (export %hash-table) (creator/copyable)))
                     (hash-table (fixer/copyable %hash-table)))))))
