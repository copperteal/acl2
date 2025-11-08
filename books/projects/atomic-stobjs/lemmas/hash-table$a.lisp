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

(include-book "misc/total-order" :dir :system)
(include-book "std/osets/top" :dir :system)
(local
  (include-book "std/omaps/top" :dir :system))

(local
  (include-book "total-order"))
(local
  (include-book "osets"))
(local
  (include-book "omaps"))

(encapsulate (((key-recognizer *) => *)
              ((default-key) => *)
              ((key-fixer *) => *)
              ((val-recognizer *) => *)
              ((default-val) => *)
              ((val-fixer *) => *))
  (local
    (defun key-recognizer (key)
      (declare (xargs :guard t))
      (symbolp key)))

  (defthm key-recognizer-constraint
    (booleanp (key-recognizer key))
    :rule-classes :type-prescription)

  (local
    (defun default-key ()
      (declare (xargs :guard t))
      '||))

  (defthm default-key-constraint
    (key-recognizer (default-key)))

  (local
    (defun key-fixer (key)
      (declare (xargs :guard (key-recognizer key)))
      (if (key-recognizer key)
          key
          (default-key))))

  (defthm key-fixer-constraint
    (equal (key-fixer key)
           (if (key-recognizer key)
               key
               (default-key))))

  (local
    (defun val-recognizer (val)
      (declare (xargs :guard t))
      (symbolp val)))

  (defthm val-recognizer-constraint
    (booleanp (val-recognizer val))
    :rule-classes :type-prescription)

  (local
    (defun default-val ()
      (declare (xargs :guard t))
      '||))

  (defthm default-val-constraint
    (val-recognizer (default-val)))

  (local
    (defun val-fixer (val)
      (declare (xargs :guard (val-recognizer val)))
      (if (val-recognizer val)
          val
          (default-val))))

  (defthm val-fixer-constraint
    (equal (val-fixer val)
           (if (val-recognizer val)
               val
               (default-val)))))

(defun keysp (set)
  (declare (xargs :guard t))
  (if (atom set)
      (null set)
      (and (key-recognizer (car set))
           (or (null (cdr set))
               (and (consp (cdr set))
                    (<< (car set)
                        (cadr set))
                    (keysp (cdr set)))))))

(defun keys-fix (set)
  (declare (xargs :guard (keysp set)))
  (if (keysp set)
      set
      ()))

(defun recognizer/unique (hash-table)
  (declare (xargs :guard t))
  (if (atom hash-table)
      (null hash-table)
      (and (consp (car hash-table))
           (key-recognizer (caar hash-table))
           (val-recognizer (cdar hash-table))
           (or (null (cdr hash-table))
               (and (consp (cdr hash-table))
                    (consp (cadr hash-table))
                    (<< (caar hash-table) (caadr hash-table))
                    (recognizer/unique (cdr hash-table)))))))

(defun recognizer/copyable (hash-table)
  (declare (xargs :guard t))
  (and (consp hash-table)
       (keysp (car hash-table))
       (recognizer/unique (cdr hash-table))))

(defun creator/unique ()
  (declare (xargs :guard t))
  '())

(defun creator/copyable ()
  (declare (xargs :guard t))
  (cons '() (creator/unique)))

(defun fixer/unique (hash-table)
  (declare (xargs :guard (recognizer/unique hash-table)))
  (if (recognizer/unique hash-table)
      hash-table
      (creator/unique)))

(defun fixer/copyable (hash-table)
  (declare (xargs :guard (recognizer/copyable hash-table)))
  (if (recognizer/copyable hash-table)
      hash-table
      (creator/copyable)))

(defun accessor/unique (key hash-table)
  (declare (xargs :guard (and (key-recognizer key)
                              (recognizer/unique hash-table))
                  :measure (len hash-table)))
  (let ((key (key-fixer key))
        (hash-table (fixer/unique hash-table)))
    (cond
      ((or (atom hash-table)
           (<< key (caar hash-table)))
       (default-val))
      ((equal key (caar hash-table))
       (val-fixer (cdar hash-table)))
      (t
       (accessor/unique key (cdr hash-table))))))

(defun accessor/copyable (key hash-table)
  (declare (xargs :guard (and (key-recognizer key)
                              (recognizer/copyable hash-table))))
  (let ((key (key-fixer key))
        (hash-table (fixer/copyable hash-table)))
    (accessor/unique key (cdr hash-table))))

(defun updater/unique (key val hash-table)
  (declare (xargs :guard (and (key-recognizer key)
                              (val-recognizer val)
                              (recognizer/unique hash-table))
                  :measure (len hash-table)))
  (let ((key (key-fixer key))
        (val (val-fixer val))
        (hash-table (fixer/unique hash-table)))
    (cond
      ((atom hash-table)
       (list (cons key val)))
      ((<< key (caar hash-table))
       (cons (cons key val)
             hash-table))
      ((equal key (caar hash-table))
       (cons (cons key val)
             (cdr hash-table)))
      (t
       (cons (car hash-table)
             (updater/unique key val (cdr hash-table)))))))

(defun updater/copyable (key val hash-table)
  (declare (xargs :guard (and (key-recognizer key)
                              (val-recognizer val)
                              (recognizer/copyable hash-table))))
  (let ((key (key-fixer key))
        (val (val-fixer val))
        (hash-table (fixer/copyable hash-table)))
    (cons (car hash-table)
          (updater/unique key val (cdr hash-table)))))

(defun boundp/unique (key hash-table)
  (declare (xargs :guard (and (key-recognizer key)
                              (recognizer/unique hash-table))
                  :measure (len hash-table)))
  (let ((key (key-fixer key))
        (hash-table (fixer/unique hash-table)))
    (cond
      ((or (atom hash-table)
           (<< key (caar hash-table)))
       'nil)
      ((equal key (caar hash-table))
       't)
      (t
       (boundp/unique key (cdr hash-table))))))

(defun boundp/copyable (key hash-table)
  (declare (xargs :guard (and (key-recognizer key)
                              (recognizer/copyable hash-table))))
  (let ((key (key-fixer key))
        (hash-table (fixer/copyable hash-table)))
    (boundp/unique key (cdr hash-table))))

(defun getp/unique (key hash-table)
  (declare (xargs :guard (and (key-recognizer key)
                              (recognizer/unique hash-table))))
  (let ((key (key-fixer key))
        (hash-table (fixer/unique hash-table)))
    (mv (accessor/unique key hash-table)
        (boundp/unique key hash-table))))

(defun getp/copyable (key hash-table)
  (declare (xargs :guard (and (key-recognizer key)
                              (recognizer/copyable hash-table))))
  (let ((key (key-fixer key))
        (hash-table (fixer/copyable hash-table)))
    (getp/unique key (cdr hash-table))))

(defun remover/unique (key hash-table)
  (declare (xargs :guard (and (key-recognizer key)
                              (recognizer/unique hash-table))
                  :measure (len hash-table)))
  (let ((key (key-fixer key))
        (hash-table (fixer/unique hash-table)))
    (cond
      ((atom hash-table)
       '())
      ((<< key (caar hash-table))
       hash-table)
      ((equal key (caar hash-table))
       (cdr hash-table))
      (t
       (cons (car hash-table)
             (remover/unique key (cdr hash-table)))))))

(defun remover/copyable (key hash-table)
  (declare (xargs :guard (and (key-recognizer key)
                              (recognizer/copyable hash-table))))
  (let ((key (key-fixer key))
        (hash-table (fixer/copyable hash-table)))
    (cons (car hash-table)
          (remover/unique key (cdr hash-table)))))

(defun count/unique (hash-table)
  (declare (xargs :guard (recognizer/unique hash-table)))
  (let ((hash-table (fixer/unique hash-table)))
    (if (atom hash-table)
        0
        (1+ (count/unique (cdr hash-table))))))

(defun count/copyable (hash-table)
  (declare (xargs :guard (recognizer/copyable hash-table)))
  (let ((hash-table (fixer/copyable hash-table)))
    (count/unique (cdr hash-table))))

(defun clear/unique (hash-table)
  (declare (xargs :guard (recognizer/unique hash-table))
           (ignore hash-table))
  (creator/unique))

(defun clear/copyable (hash-table)
  (declare (xargs :guard (recognizer/copyable hash-table))
           (ignore hash-table))
  (creator/copyable))

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


;;;; `OMAPS'
(local
  (defthm keysp{definition}
    (equal (keysp set)
           (and (set::setp set)
                (or (set::emptyp set)
                    (and (key-recognizer (set::head set))
                         (keysp (set::tail set))))))
    :rule-classes
    ((:rewrite :corollary
               (implies (keysp set)
                        (set::setp set)))
     (:rewrite :corollary
               (implies (and (keysp set)
                             (not (set::emptyp set)))
                        (key-recognizer (set::head set))))
     (:rewrite :corollary
               (implies (and (keysp set)
                             (not (set::emptyp set)))
                        (keysp (set::tail set))))
     (:definition :controller-alist ((keysp t))))
    :hints
    (("Goal"
      :in-theory (enable set::setp
                         set::emptyp
                         set::head
                         set::tail
                         set::sfix)))))

(local
  (in-theory
    (disable keysp)))

(local
  (defthm recognizer/unique{definition}
    (equal (recognizer/unique hash-table)
           (and (omap::mapp hash-table)
                (or (omap::emptyp hash-table)
                    (mv-let (key val)
                            (omap::head hash-table)
                      (and (key-recognizer key)
                           (val-recognizer val)
                           (recognizer/unique (omap::tail hash-table)))))))
    :rule-classes
    ((:rewrite :corollary
               (implies (recognizer/unique hash-table)
                        (omap::mapp hash-table)))
     (:rewrite :corollary
               (implies (and (recognizer/unique hash-table)
                             (not (omap::emptyp hash-table)))
                        (key-recognizer (mv-nth 0 (omap::head hash-table)))))
     (:rewrite :corollary
               (implies (and (recognizer/unique hash-table)
                             (not (omap::emptyp hash-table)))
                        (val-recognizer (mv-nth 1 (omap::head hash-table)))))
     (:rewrite :corollary
               (implies (and (recognizer/unique hash-table)
                             (not (omap::emptyp hash-table)))
                        (recognizer/unique (omap::tail hash-table))))
     (:definition :controller-alist ((recognizer/unique t))))
    :hints
    (("Goal"
      :in-theory (enable omap::mapp
                         omap::emptyp
                         omap::mfix
                         omap::head
                         omap::tail)))))

(local
  (in-theory
    (disable recognizer/unique)))

(local
  (defthm accessor/unique{definition}
    (equal (accessor/unique key hash-table)
           (let ((key (key-fixer key))
                 (hash-table (fixer/unique hash-table)))
             (cond
               ((omap::emptyp hash-table)
                (default-val))
               ((equal key (omap::head-key hash-table))
                (val-fixer (omap::head-val hash-table)))
               (t
                (accessor/unique key (omap::tail hash-table))))))
    :rule-classes
    ((:definition :controller-alist ((accessor/unique nil t))))
    :hints
    (("Goal"
      :cases ((recognizer/unique hash-table))
      :in-theory (enable omap::mapp
                         omap::emptyp
                         omap::head
                         omap::tail)))))

(local
  (in-theory
    (disable accessor/unique)))

(local
  (defthm updater/unique{definition}
    (equal (updater/unique key val hash-table)
           (let ((key (key-fixer key))
                 (val (val-fixer val))
                 (hash-table (fixer/unique hash-table)))
             (omap::update key val hash-table)))
    :rule-classes :definition
    :hints
    (("Goal"
      :cases ((recognizer/unique hash-table))
      :in-theory (enable omap::update
                         omap::mapp
                         omap::head
                         omap::tail)))))

(local
  (in-theory
    (disable updater/unique)))

(local
  (defthm boundp/unique{definition}
    (equal (boundp/unique key hash-table)
           (let ((key (key-fixer key))
                 (hash-table (fixer/unique hash-table)))
             (and (omap::assoc key hash-table)
                  t)))
    :rule-classes :definition
    :hints
    (("Goal"
      :cases ((recognizer/unique hash-table))
      :in-theory (enable omap::assoc
                         omap::mapp
                         omap::head
                         omap::tail)))))

(local
  (in-theory
    (disable boundp/unique)))

(local
  (encapsulate ()
    (local
      (defthmd remover/unique{definition}-lemma-0
        (implies (and (consp pair)
                      (not (omap::emptyp hash-table))
                      (<< (car pair)
                          (caar hash-table)))
                 (equal (cons pair
                              (omap::delete key (cdr (cons pair hash-table))))
                        (omap::update (car pair)
                                      (cdr pair)
                                      (omap::delete key hash-table))))
        :hints
        (("Goal"
          :in-theory (enable omap::mapp
                             omap::emptyp
                             omap::mfix
                             omap::head
                             omap::tail
                             omap::update
                             omap::delete)))))

    (local
      (defthm remover/unique{definition}-lemma-1
        (implies (and (recognizer/unique hash-table)
                      (key-recognizer key))
                 (equal (remover/unique key hash-table)
                        (omap::delete key hash-table)))
        :hints
        (("Goal"
          :in-theory (enable omap::delete
                             omap::update
                             omap::mapp
                             omap::emptyp
                             omap::head
                             omap::tail
                             omap::update))
         ("Subgoal *1/4.1"
          :use (:instance remover/unique{definition}-lemma-0
                          (pair (car hash-table))
                          (hash-table (cdr hash-table)))))))

    (local
      (defthm remover/unique{definition}-lemma-2
        (implies (and (recognizer/unique hash-table)
                      (not (key-recognizer key)))
                 (equal (remover/unique key hash-table)
                        (omap::delete (default-key)
                                      hash-table)))
        :hints
        (("Goal"
          :in-theory (enable omap::delete
                             omap::update
                             omap::mapp
                             omap::emptyp
                             omap::head
                             omap::tail
                             omap::update))
         ("Subgoal *1/6"
          :use (:instance remover/unique{definition}-lemma-0
                          (pair (CAR HASH-TABLE))
                          (hash-table (cdr hash-table))
                          (key (default-key))))
         ("Subgoal *1/5"
          :use (:instance remover/unique{definition}-lemma-0
                          (pair (car hash-table))
                          (hash-table (cdr hash-table))
                          (key (default-key)))))))

    (defthm remover/unique{definition}
      (equal (remover/unique key hash-table)
             (let ((key (key-fixer key))
                   (hash-table (fixer/unique hash-table)))
               (omap::delete key hash-table)))
      :rule-classes :definition
      :hints
      (("Goal"
        :cases ((recognizer/unique hash-table))
        :in-theory (enable omap::delete
                           omap::update
                           omap::mapp
                           omap::head
                           omap::tail
                           omap::update))))))

(local
  (in-theory
    (disable remover/unique)))

(local
  (defthm count/unique{definition}
    (equal (count/unique hash-table)
           (let ((hash-table (fixer/unique hash-table)))
             (omap::size hash-table)))
    :rule-classes :definition
    :hints
    (("Goal"
      :in-theory (enable omap::size
                         omap::mapp
                         omap::emptyp
                         omap::head
                         omap::tail)))))

(local
  (in-theory
    (disable count/unique)))

(local
  (defun recognizer/unique{induction}-fn (hash-table)
    (declare (xargs :guard (omap::mapp hash-table)))
    (or (omap::emptyp hash-table)
        (recognizer/unique{induction}-fn (omap::tail hash-table)))))

(local
  (defthm recognizer/unique{induction}
    t
    :rule-classes
    ((:induction :pattern (recognizer/unique hash-table)
                 :scheme (recognizer/unique{induction}-fn hash-table)))))

(local
  (defun accessor/unique{induction}-fn (key hash-table)
    (declare (xargs :guard (omap::mapp hash-table)
                    :measure (omap::size hash-table)))
    (let ((key (key-fixer key)))
      (or (omap::emptyp hash-table)
          (equal key (omap::head-key hash-table))
          (accessor/unique{induction}-fn key (omap::tail hash-table))))))

(local
  (defthm accessor/unique{induction}
    t
    :rule-classes
    ((:induction :pattern (accessor/unique key hash-table)
                 :scheme (accessor/unique{induction}-fn key hash-table)))))


;;;; `KEYSP'
(defthm keysp{type-prescription}
  (booleanp (keysp set))
  :rule-classes :type-prescription)

(defthm keysp{compound-recognizer}
  (implies (keysp set)
           (true-listp set))
  :rule-classes :compound-recognizer)

(defthm keysp-of-keys-fix
  (keysp (keys-fix set)))

(defthm setp-when-keysp
  (implies (keysp set)
           (set::setp set)))

(defthm key-recognizer-of-head-when-keysp
  (implies (and (keysp set)
                (not (set::emptyp set)))
           (key-recognizer (set::head set))))

(defthm keysp-of-tail-when-keysp
  (implies (and (keysp set)
                (not (set::emptyp set)))
           (keysp (set::tail set))))

(defthm in-when-not-key-recognizer
  (implies (and (keysp set)
                (not (key-recognizer key)))
           (not (set::in key set)))
  :hints
  (("Goal"
    :in-theory (enable set::in))))

(defthm keysp-of-insert
  (implies (keysp set)
           (equal (keysp (set::insert key set))
                  (key-recognizer key)))
  :hints
  (("Goal"
    :induct (set::cardinality set)
    :in-theory (enable set::cardinality)
    :expand (keysp (set::insert key set)))))


;;;; `KEYS-FIX'
(defthm keys-fix{type-prescription}
  (true-listp (keys-fix set))
  :rule-classes :type-prescription)

(defthm keys-fix-when-keysp
  (implies (keysp set)
           (equal (keys-fix set)
                  set)))

(defthm keys-fix-when-not-keysp
  (implies (not (keysp set))
           (not (keys-fix set))))


;;;; `RECOGNIZER/UNIQUE'
(defthm recognizer/unique{type-prescription}
  (booleanp (recognizer/unique hash-table))
  :rule-classes :type-prescription)

(defthm recognizer/unique{compound-recognizer}
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
                  (recognizer/unique hash-table))
             (recognizer/unique (omap::update key val hash-table)))
    :hints
    (("Goal"
      :in-theory (disable omap::use-weak-update-induction
                          omap::weak-update-induction))
     ("Subgoal *1/3"
      :expand (recognizer/unique (omap::update key val hash-table))))))

(defthm recognizer/unique-of-updater/unique
  (recognizer/unique (updater/unique key val hash-table)))

(local
  (defthm recognizer/unique-of-tail
    (implies (recognizer/unique hash-table)
             (recognizer/unique (omap::tail hash-table)))))

(local
  (defthm recognizer/unique-of-delete
    (implies (recognizer/unique hash-table)
             (recognizer/unique (omap::delete key hash-table)))
    :hints
    (("Goal"
      :in-theory (enable omap::delete)))))

(defthm recognizer/unique-of-remover/unique
  (recognizer/unique (remover/unique key hash-table)))


;;;; `RECOGNIZER/COPYABLE'
(encapsulate ()
  (local
    (in-theory
      (disable recognizer/unique{definition}
               accessor/unique{definition}
               updater/unique{definition}
               boundp/unique{definition}
               remover/unique{definition}
               count/unique{definition})))

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

  (defthm recognizer/copyable-of-fixer/copyable
    (recognizer/copyable (fixer/copyable hash-table)))

  (defthm recognizer/copyable-of-updater/copyable
    (recognizer/copyable (updater/copyable key val hash-table)))

  (defthm recognizer/copyable-of-remover/copyable
    (recognizer/copyable (remover/copyable key hash-table)))

  (defthm recognizer/copyable-of-keys-set
    (recognizer/copyable (keys-set set hash-table))))


;;;; `FIXER/UNIQUE'
(defthm fixer/unique{type-prescription}
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


;;;; `FIXER/COPYABLE'
(encapsulate ()
  (local
    (in-theory
      (disable recognizer/unique{definition}
               accessor/unique{definition}
               updater/unique{definition}
               boundp/unique{definition}
               remover/unique{definition}
               count/unique{definition})))

  (defthm fixer/copyable{type-prescription}
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
                    (creator/copyable)))))


;;;; `ACCESSOR/UNIQUE'
(defthm val-recognizer-of-accessor/unique
  (val-recognizer (accessor/unique key hash-table)))

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

(defthm accessor/unique-of-key-fixer
  (equal (accessor/unique (key-fixer key) hash-table)
         (accessor/unique key hash-table)))

(defthm accessor/unique-of-fixer/unique
  (equal (accessor/unique key (fixer/unique hash-table))
         (accessor/unique key hash-table)))

(local
  (defthm accessor/unique-of-update-same
    (implies (and (key-recognizer key)
                  (val-recognizer val)
                  (recognizer/unique hash-table))
             (equal (accessor/unique key (omap::update key val hash-table))
                    val))
    :hints
    (("Goal"
      :in-theory (disable omap::assoc-of-update
                          omap::use-weak-update-induction
                          omap::weak-update-induction))
     ("Subgoal *1/3"
      :expand (accessor/unique key (omap::update key val hash-table))))))

(defthm accessor/unique-of-updater/unique-same
  (implies (equal (key-fixer %key) (key-fixer key))
           (equal (accessor/unique %key (updater/unique key val hash-table))
                  (val-fixer val))))

(local
  (defthm accessor/unique-of-update-diff
    (implies (and (key-recognizer %key)
                  (key-recognizer key)
                  (not (equal %key key))
                  (val-recognizer val)
                  (recognizer/unique hash-table))
             (equal (accessor/unique %key (omap::update key val hash-table))
                    (accessor/unique %key hash-table)))
    :hints
    (("Goal"
      :in-theory (disable omap::assoc-of-update
                          omap::use-weak-update-induction
                          omap::weak-update-induction))
     ("Subgoal *1/6"
      :expand (accessor/unique %key (omap::update key val hash-table))))))

(defthm accessor/unique-of-updater/unique-diff
  (implies (not (equal (key-fixer %key) (key-fixer key)))
           (equal (accessor/unique %key (updater/unique key val hash-table))
                  (accessor/unique %key hash-table))))

(defthm accessor/unique-of-updater/unique
  (equal (accessor/unique %key (updater/unique key val hash-table))
         (if (equal (key-fixer %key) (key-fixer key))
             (val-fixer val)
             (accessor/unique %key hash-table)))
  :hints
  (("Goal"
    :cases ((equal (key-fixer %key) (key-fixer key))))
   ("Subgoal 2"
    :by accessor/unique-of-updater/unique-diff)
   ("Subgoal 1"
    :by accessor/unique-of-updater/unique-same)))

(defthm accessor/unique-when-not-boundp/unique
  (implies (not (boundp/unique key hash-table))
           (equal (accessor/unique key hash-table)
                  (default-val))))

(defthm accessor/unique-of-remover/unique-same
  (implies (equal (key-fixer %key) (key-fixer key))
           (equal (accessor/unique %key (remover/unique key hash-table))
                  (default-val))))

(defthm accessor/unique-of-remover/unique-diff
  (implies (not (equal (key-fixer %key) (key-fixer key)))
           (equal (accessor/unique %key (remover/unique key hash-table))
                  (accessor/unique %key hash-table))))

(defthm accessor/unique-of-remover/unique
  (equal (accessor/unique %key (remover/unique key hash-table))
         (if (equal (key-fixer %key) (key-fixer key))
             (default-val)
             (accessor/unique %key hash-table)))
  :hints
  (("Goal"
    :cases ((equal (key-fixer %key) (key-fixer key))))
   ("Subgoal 2"
    :by accessor/unique-of-remover/unique-diff)
   ("Subgoal 1"
    :by accessor/unique-of-remover/unique-same)))


;;;; `ACCESSOR/COPYABLE'
(encapsulate ()
  (local
    (in-theory
      (disable recognizer/unique{definition}
               updater/unique{definition}
               boundp/unique{definition}
               remover/unique{definition}
               count/unique{definition})))

  (defthm val-recognizer-of-accessor/copyable
    (val-recognizer (accessor/copyable key hash-table)))

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

  (defthm accessor/copyable-of-key-fixer
    (equal (accessor/copyable (key-fixer key) hash-table)
           (accessor/copyable key hash-table)))

  (defthm accessor/copyable-of-fixer/copyable
    (equal (accessor/copyable key (fixer/copyable hash-table))
           (accessor/copyable key hash-table)))

  (defthm accessor/copyable-of-updater/copyable-same
    (implies (equal (key-fixer %key) (key-fixer key))
             (equal (accessor/copyable %key (updater/copyable key val hash-table))
                    (val-fixer val))))

  (defthm accessor/copyable-of-updater/copyable-diff
    (implies (not (equal (key-fixer %key) (key-fixer key)))
             (equal (accessor/copyable %key (updater/copyable key val hash-table))
                    (accessor/copyable %key hash-table))))

  (defthm accessor/copyable-of-updater/copyable
    (equal (accessor/copyable %key (updater/copyable key val hash-table))
           (if (equal (key-fixer %key) (key-fixer key))
               (val-fixer val)
               (accessor/copyable %key hash-table))))

  (defthm accessor/copyable-when-not-boundp/copyable
    (implies (not (boundp/copyable key hash-table))
             (equal (accessor/copyable key hash-table)
                    (default-val))))

  (defthm accessor/copyable-of-remover/copyable-same
    (implies (equal (key-fixer %key) (key-fixer key))
             (equal (accessor/copyable %key (remover/copyable key hash-table))
                    (default-val))))

  (defthm accessor/copyable-of-remover/copyable-diff
    (implies (not (equal (key-fixer %key) (key-fixer key)))
             (equal (accessor/copyable %key (remover/copyable key hash-table))
                    (accessor/copyable %key hash-table))))

  (defthm accessor/copyable-of-remover/copyable
    (equal (accessor/copyable %key (remover/copyable key hash-table))
           (if (equal (key-fixer %key) (key-fixer key))
               (default-val)
               (accessor/copyable %key hash-table))))

  (defthm accessor/copyable-of-keys-set
    (equal (accessor/copyable key (keys-set set hash-table))
           (accessor/copyable key hash-table))))


;;;; `UPDATER/UNIQUE'
(defthm updater/unique{type-prescription}
  (true-listp (updater/unique key val hash-table))
  :rule-classes :type-prescription)

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

(defthm updater/unique-of-key-fixer
  (equal (updater/unique (key-fixer key) val hash-table)
         (updater/unique key val hash-table)))

(defthm updater/unique-of-val-fixer
  (equal (updater/unique key (val-fixer val) hash-table)
         (updater/unique key val hash-table)))

(defthm updater/unique-of-fixer/unique
  (equal (updater/unique key val (fixer/unique hash-table))
         (updater/unique key val hash-table)))

(defthm updater/unique-of-accessor/unique-when-boundp/unique-free
  (implies (and (boundp/unique key hash-table)
                (equal (val-fixer val) (accessor/unique key hash-table)))
           (equal (updater/unique key val hash-table)
                  (fixer/unique hash-table))))

(defthm updater/unique-of-accessor/unique-when-boundp/unique
  (implies (and (boundp/unique %key hash-table)
                (equal (key-fixer %key) (key-fixer key)))
           (equal (updater/unique %key (accessor/unique key hash-table) hash-table)
                  (fixer/unique hash-table)))
  :hints
  (("Goal"
    :in-theory (disable updater/unique-of-accessor/unique-when-boundp/unique-free)
    :use (:instance updater/unique-of-accessor/unique-when-boundp/unique-free
                    (val (accessor/unique key hash-table))
                    (key %key)))))

(defthm updater/unique-of-accessor/unique-when-not-boundp/unique
  (implies (and (not (boundp/unique %key hash-table))
                (equal (key-fixer %key) (key-fixer key)))
           (equal (updater/unique %key (accessor/unique key hash-table) hash-table)
                  (updater/unique %key (default-val) hash-table))))

(defthm updater/unique-of-accessor/unique
  (implies (equal (key-fixer %key) (key-fixer key))
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
    :by updater/unique-of-accessor/unique-when-boundp/unique)))

(defthm updater/unique-of-updater/unique-same
  (implies (equal (key-fixer %key) (key-fixer key))
           (equal (updater/unique %key %val (updater/unique key val hash-table))
                  (updater/unique %key %val hash-table))))

(defthm updater/unique-of-updater/unique-diff
  (implies (not (equal (key-fixer %key) (key-fixer key)))
           (equal (updater/unique %key %val (updater/unique key val hash-table))
                  (updater/unique key val (updater/unique %key %val hash-table))))
  :rule-classes
  ((:rewrite :loop-stopper ((%key key updater/unique)))))

(defthm updater/unique-of-updater/unique
  (equal (updater/unique %key %val (updater/unique key val hash-table))
         (if (equal (key-fixer %key) (key-fixer key))
             (updater/unique %key %val hash-table)
             (updater/unique key val (updater/unique %key %val hash-table))))
  :rule-classes
  ((:rewrite :loop-stopper ((%key key updater/unique))))
  :hints
  (("Goal"
    :cases ((equal (key-fixer %key) (key-fixer key))))
   ("Subgoal 2"
    :by updater/unique-of-updater/unique-diff)
   ("Subgoal 1"
    :by updater/unique-of-updater/unique-same)))

(defthm updater/unique-of-remover/unique-same
  (implies (equal (key-fixer %key) (key-fixer key))
           (equal (updater/unique %key val (remover/unique key hash-table))
                  (updater/unique %key val hash-table))))


;;;; `UPDATER/COPYABLE'
(encapsulate ()
  (local
    (in-theory
      (disable recognizer/unique{definition}
               accessor/unique{definition}
               updater/unique{definition}
               boundp/unique{definition}
               remover/unique{definition}
               count/unique{definition})))

  (defthm updater/copyable{type-prescription}
    (and (consp (updater/copyable key val hash-table))
         (true-listp (updater/copyable key val hash-table)))
    :rule-classes :type-prescription)

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

  (defthm updater/copyable-of-key-fixer
    (equal (updater/copyable (key-fixer key) val hash-table)
           (updater/copyable key val hash-table)))

  (defthm updater/copyable-of-val-fixer
    (equal (updater/copyable key (val-fixer val) hash-table)
           (updater/copyable key val hash-table)))

  (defthm updater/copyable-of-fixer/copyable
    (equal (updater/copyable key val (fixer/copyable hash-table))
           (updater/copyable key val hash-table)))

  (defthm updater/copyable-of-accessor/copyable-when-boundp/copyable-free
    (implies (and (boundp/copyable key hash-table)
                  (equal (val-fixer val) (accessor/copyable key hash-table)))
             (equal (updater/copyable key val hash-table)
                    (fixer/copyable hash-table))))

  (defthm updater/copyable-of-accessor/copyable-when-boundp/copyable
    (implies (and (boundp/copyable %key hash-table)
                  (equal (key-fixer %key) (key-fixer key)))
             (equal (updater/copyable %key (accessor/copyable key hash-table) hash-table)
                    (fixer/copyable hash-table)))
    :hints
    (("Goal"
      :in-theory (disable updater/copyable-of-accessor/copyable-when-boundp/copyable-free)
      :use (:instance updater/copyable-of-accessor/copyable-when-boundp/copyable-free
                      (val (accessor/copyable key hash-table))
                      (key %key)))))

  (defthm updater/copyable-of-accessor/copyable-when-not-boundp/copyable
    (implies (and (not (boundp/copyable %key hash-table))
                  (equal (key-fixer %key) (key-fixer key)))
             (equal (updater/copyable %key (accessor/copyable key hash-table) hash-table)
                    (updater/copyable %key (default-val) hash-table))))

  (defthm updater/copyable-of-accessor/copyable
    (implies (equal (key-fixer %key) (key-fixer key))
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
      :by updater/copyable-of-accessor/copyable-when-boundp/copyable)))

  (defthm updater/copyable-of-updater/copyable-same
    (implies (equal (key-fixer %key) (key-fixer key))
             (equal (updater/copyable %key %val (updater/copyable key val hash-table))
                    (updater/copyable %key %val hash-table))))

  (defthm updater/copyable-of-updater/copyable-diff
    (implies (not (equal (key-fixer %key) (key-fixer key)))
             (equal (updater/copyable %key %val (updater/copyable key val hash-table))
                    (updater/copyable key val (updater/copyable %key %val hash-table))))
    :rule-classes
    ((:rewrite :loop-stopper ((%key key updater/copyable)))))

  (defthm updater/copyable-of-updater/copyable
    (equal (updater/copyable %key %val (updater/copyable key val hash-table))
           (if (equal (key-fixer %key) (key-fixer key))
               (updater/copyable %key %val hash-table)
               (updater/copyable key val (updater/copyable %key %val hash-table))))
    :rule-classes
    ((:rewrite :loop-stopper ((%key key updater/copyable))))
    :hints
    (("Goal"
      :cases ((equal (key-fixer %key) (key-fixer key))))
     ("Subgoal 2"
      :by updater/copyable-of-updater/copyable-diff)
     ("Subgoal 1"
      :by updater/copyable-of-updater/copyable-same)))

  (defthm updater/copyable-of-remover/copyable-same
    (implies (equal (key-fixer %key) (key-fixer key))
             (equal (updater/copyable %key val (remover/copyable key hash-table))
                    (updater/copyable %key val hash-table)))))


;;;; `BOUNDP/UNIQUE'
(defthm boundp/unique{type-prescription}
  (booleanp (boundp/unique key hash-table))
  :rule-classes :type-prescription)

(defthm boundp/unique-when-not-key-recognizer
  (implies (not (key-recognizer key))
           (equal (boundp/unique key hash-table)
                  (boundp/unique (default-key) hash-table))))

(defthm boundp/unique-when-not-recognizer/unique
  (implies (not (recognizer/unique hash-table))
           (not (boundp/unique key hash-table))))

(defthm boundp/unique-of-creator/unique
  (not (boundp/unique key (creator/unique))))

(defthm boundp/unique-of-key-fixer
  (equal (boundp/unique (key-fixer key) hash-table)
         (boundp/unique key hash-table)))

(defthm boundp/unique-of-fixer/unique
  (equal (boundp/unique key (fixer/unique hash-table))
         (boundp/unique key hash-table)))

(defthm boundp/unique-of-updater/unique-same
  (implies (equal (key-fixer %key) (key-fixer key))
           (equal (boundp/unique %key (updater/unique key val hash-table))
                  t)))

(defthm boundp/unique-of-updater/unique-diff
  (implies (not (equal (key-fixer %key) (key-fixer key)))
           (equal (boundp/unique %key (updater/unique key val hash-table))
                  (boundp/unique %key hash-table))))

(defthm boundp/unique-of-updater/unique
  (equal (boundp/unique %key (updater/unique key val hash-table))
         (if (equal (key-fixer %key) (key-fixer key))
             t
             (boundp/unique %key hash-table)))
  :hints
  (("Goal"
    :cases ((equal (key-fixer %key) (key-fixer key))))
   ("Subgoal 2"
    :by boundp/unique-of-updater/unique-diff)
   ("Subgoal 1"
    :by boundp/unique-of-updater/unique-same)))

(defthm boundp/unique-of-remover/unique-same
  (implies (equal (key-fixer %key) (key-fixer key))
           (not (boundp/unique %key (remover/unique key hash-table)))))

(defthm boundp/unique-of-remover/unique-diff
  (implies (not (equal (key-fixer %key) (key-fixer key)))
           (equal (boundp/unique %key (remover/unique key hash-table))
                  (boundp/unique %key hash-table))))

(defthm boundp/unique-of-remover/unique
  (equal (boundp/unique %key (remover/unique key hash-table))
         (if (equal (key-fixer %key) (key-fixer key))
             nil
             (boundp/unique %key hash-table)))
  :hints
  (("Goal"
    :cases ((equal (key-fixer %key) (key-fixer key))))
   ("Subgoal 2"
    :by boundp/unique-of-remover/unique-diff)
   ("Subgoal 1"
    :in-theory (disable boundp/unique-of-remover/unique-same)
    :use boundp/unique-of-remover/unique-same)))

(defthm boundp/unique-when-zp-count/unique
  (implies (zp (count/unique hash-table))
           (not (boundp/unique key hash-table)))
  :hints
  (("Goal"
    :in-theory (enable omap::unfold-equal-size-const))))


;;;; `BOUNDP/COPYABLE'
(encapsulate ()
  (local
    (in-theory
      (disable recognizer/unique{definition}
               accessor/unique{definition}
               updater/unique{definition}
               boundp/unique{definition}
               remover/unique{definition}
               count/unique{definition})))

  (defthm boundp/copyable{type-prescription}
    (booleanp (boundp/copyable key hash-table))
    :rule-classes :type-prescription)

  (defthm boundp/copyable-when-not-key-recognizer
    (implies (not (key-recognizer key))
             (equal (boundp/copyable key hash-table)
                    (boundp/copyable (default-key) hash-table))))

  (defthm boundp/copyable-when-not-recognizer/copyable
    (implies (not (recognizer/copyable hash-table))
             (not (boundp/copyable key hash-table))))

  (defthm boundp/copyable-of-creator/copyable
    (not (boundp/copyable key (creator/copyable))))

  (defthm boundp/copyable-of-key-fixer
    (equal (boundp/copyable (key-fixer key) hash-table)
           (boundp/copyable key hash-table)))

  (defthm boundp/copyable-of-fixer/copyable
    (equal (boundp/copyable key (fixer/copyable hash-table))
           (boundp/copyable key hash-table)))

  (defthm boundp/copyable-of-updater/copyable-same
    (implies (equal (key-fixer %key) (key-fixer key))
             (equal (boundp/copyable %key (updater/copyable key val hash-table))
                    t)))

  (defthm boundp/copyable-of-updater/copyable-diff
    (implies (not (equal (key-fixer %key) (key-fixer key)))
             (equal (boundp/copyable %key (updater/copyable key val hash-table))
                    (boundp/copyable %key hash-table))))

  (defthm boundp/copyable-of-updater/copyable
    (equal (boundp/copyable %key (updater/copyable key val hash-table))
           (if (equal (key-fixer %key) (key-fixer key))
               t
               (boundp/copyable %key hash-table)))
    :hints
    (("Goal"
      :cases ((equal (key-fixer %key) (key-fixer key))))
     ("Subgoal 2"
      :by boundp/copyable-of-updater/copyable-diff)
     ("Subgoal 1"
      :by boundp/copyable-of-updater/copyable-same)))

  (defthm boundp/copyable-of-remover/copyable-same
    (implies (equal (key-fixer %key) (key-fixer key))
             (not (boundp/copyable %key (remover/copyable key hash-table)))))

  (defthm boundp/copyable-of-remover/copyable-diff
    (implies (not (equal (key-fixer %key) (key-fixer key)))
             (equal (boundp/copyable %key (remover/copyable key hash-table))
                    (boundp/copyable %key hash-table))))

  (defthm boundp/copyable-of-remover/copyable
    (equal (boundp/copyable %key (remover/copyable key hash-table))
           (if (equal (key-fixer %key) (key-fixer key))
               nil
               (boundp/copyable %key hash-table)))
    :hints
    (("Goal"
      :cases ((equal (key-fixer %key) (key-fixer key))))
     ("Subgoal 2"
      :by boundp/copyable-of-remover/copyable-diff)
     ("Subgoal 1"
      :in-theory (disable boundp/copyable-of-remover/copyable-same)
      :use boundp/copyable-of-remover/copyable-same)))

  (defthm boundp/copyable-of-keys-set
    (equal (boundp/copyable key (keys-set set hash-table))
           (boundp/copyable key hash-table)))

  (defthm boundp/copyable-when-zp-count/copyable
    (implies (zp (count/copyable hash-table))
             (not (boundp/copyable key hash-table)))))


;;;; `GETP/UNIQUE'
(defthm getp/unique{type-prescription}
  (and (consp (getp/unique key hash-table))
       (true-listp (getp/unique key hash-table)))
  :rule-classes :type-prescription)

(defthm getp/unique{rewrite}
  (mv-let (v0 v1)
          (getp/unique key hash-table)
    (and (equal v0 (accessor/unique key hash-table))
         (equal v1 (boundp/unique key hash-table)))))


;;;; `GETP/COPYABLE'
(defthm getp/copyable{type-prescription}
  (and (consp (getp/copyable key hash-table))
       (true-listp (getp/copyable key hash-table)))
  :rule-classes :type-prescription)

(defthm getp/copyable{rewrite}
  (mv-let (v0 v1)
          (getp/copyable key hash-table)
    (and (equal v0 (accessor/copyable key hash-table))
         (equal v1 (boundp/copyable key hash-table)))))


;;;; `REMOVER/UNIQUE'
(defthm remover/unique{type-prescription}
  (true-listp (remover/unique key hash-table))
  :rule-classes :type-prescription)

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

(defthm remover/unique-of-key-fixer
  (equal (remover/unique (key-fixer key) hash-table)
         (remover/unique key hash-table)))

(defthm remover/unique-of-fixer/unique
  (equal (remover/unique key (fixer/unique hash-table))
         (remover/unique key hash-table)))

(defthm remover/unique-of-updater/unique-same
  (implies (equal (key-fixer %key) (key-fixer key))
           (equal (remover/unique %key (updater/unique key val hash-table))
                  (remover/unique %key hash-table))))

(defthm remover/unique-of-updater/unique-diff
  (implies (not (equal (key-fixer %key) (key-fixer key)))
           (equal (remover/unique %key (updater/unique key val hash-table))
                  (updater/unique key val (remover/unique %key hash-table)))))

(defthm remover/unique-of-updater/unique
  (equal (remover/unique %key (updater/unique key val hash-table))
         (if (equal (key-fixer %key) (key-fixer key))
             (remover/unique %key hash-table)
             (updater/unique key val (remover/unique %key hash-table))))
  :hints
  (("Goal"
    :cases ((equal (key-fixer %key) (key-fixer key))))
   ("Subgoal 2"
    :by remover/unique-of-updater/unique-diff)
   ("Subgoal 1"
    :by remover/unique-of-updater/unique-same)))

(defthm remover/unique-when-not-boundp/unique
  (implies (not (boundp/unique key hash-table))
           (equal (remover/unique key hash-table)
                  (fixer/unique hash-table))))

(defthm remover/unique-of-remover/unique-same
  (implies (equal (key-fixer %key) (key-fixer key))
           (equal (remover/unique %key (remover/unique key hash-table))
                  (remover/unique %key hash-table))))

(defthm remover/unique-of-remover/unique-diff
  (implies (not (equal (key-fixer %key) (key-fixer key)))
           (equal (remover/unique %key (remover/unique key hash-table))
                  (remover/unique key (remover/unique %key hash-table))))
  :rule-classes
  ((:rewrite :loop-stopper ((%key key remover/unique)))))

(defthm remover/unique-of-remover/unique
  (equal (remover/unique %key (remover/unique key hash-table))
         (if (equal (key-fixer %key) (key-fixer key))
             (remover/unique %key hash-table)
             (remover/unique key (remover/unique %key hash-table))))
  :rule-classes
  ((:rewrite :loop-stopper ((%key key remover/unique))))
  :hints
  (("Goal"
    :cases ((equal (key-fixer %key) (key-fixer key))))
   ("Subgoal 2"
    :by remover/unique-of-remover/unique-diff)
   ("Subgoal 1"
    :by remover/unique-of-remover/unique-same)))


;;;; `REMOVER/COPYABLE'
(encapsulate ()
  (local
    (in-theory
      (disable accessor/unique{definition}
               count/unique{definition})))

  (defthm remover/copyable{type-prescription}
    (and (consp (remover/copyable key hash-table))
         (true-listp (remover/copyable key hash-table)))
    :rule-classes :type-prescription)

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

  (defthm remover/copyable-of-key-fixer
    (equal (remover/copyable (key-fixer key) hash-table)
           (remover/copyable key hash-table)))

  (defthm remover/copyable-of-fixer/copyable
    (equal (remover/copyable key (fixer/copyable hash-table))
           (remover/copyable key hash-table)))

  (defthm remover/copyable-of-updater/copyable-same
    (implies (equal (key-fixer %key) (key-fixer key))
             (equal (remover/copyable %key (updater/copyable key val hash-table))
                    (remover/copyable %key hash-table))))

  (defthm remover/copyable-of-updater/copyable-diff
    (implies (not (equal (key-fixer %key) (key-fixer key)))
             (equal (remover/copyable %key (updater/copyable key val hash-table))
                    (updater/copyable key val (remover/copyable %key hash-table)))))

  (defthm remover/copyable-of-updater/copyable
    (equal (remover/copyable %key (updater/copyable key val hash-table))
           (if (equal (key-fixer %key) (key-fixer key))
               (remover/copyable %key hash-table)
               (updater/copyable key val (remover/copyable %key hash-table))))
    :hints
    (("Goal"
      :cases ((equal (key-fixer %key) (key-fixer key))))
     ("Subgoal 2"
      :by remover/copyable-of-updater/copyable-diff)
     ("Subgoal 1"
      :by remover/copyable-of-updater/copyable-same)))

  (defthm remover/copyable-when-not-boundp/copyable
    (implies (not (boundp/copyable key hash-table))
             (equal (remover/copyable key hash-table)
                    (fixer/copyable hash-table))))

  (defthm remover/copyable-of-remover/copyable-same
    (implies (equal (key-fixer %key) (key-fixer key))
             (equal (remover/copyable %key (remover/copyable key hash-table))
                    (remover/copyable %key hash-table))))

  (defthm remover/copyable-of-remover/copyable-diff
    (implies (not (equal (key-fixer %key) (key-fixer key)))
             (equal (remover/copyable %key (remover/copyable key hash-table))
                    (remover/copyable key (remover/copyable %key hash-table))))
    :rule-classes
    ((:rewrite :loop-stopper ((%key key remover/copyable)))))

  (defthm remover/copyable-of-remover/copyable
    (equal (remover/copyable %key (remover/copyable key hash-table))
           (if (equal (key-fixer %key) (key-fixer key))
               (remover/copyable %key hash-table)
               (remover/copyable key (remover/copyable %key hash-table))))
    :rule-classes
    ((:rewrite :loop-stopper ((%key key remover/copyable))))
    :hints
    (("Goal"
      :cases ((equal (key-fixer %key) (key-fixer key))))
     ("Subgoal 2"
      :by remover/copyable-of-remover/copyable-diff)
     ("Subgoal 1"
      :by remover/copyable-of-remover/copyable-same))))


;;;; `COUNT/UNIQUE'
(defthm count/unique{type-prescription}
  (natp (count/unique hash-table))
  :rule-classes :type-prescription)

(defthm count/unique-when-not-recognizer/unique
  (implies (not (recognizer/unique hash-table))
           (equal (count/unique hash-table)
                  0)))

(defthm count/unique-of-creator/unique
  (equal (count/unique (creator/unique))
         0))

(defthm count/unique-of-fixer/unique
  (equal (count/unique (fixer/unique hash-table))
         (count/unique hash-table)))

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


;;;; `COUNT/COPYABLE'
(encapsulate ()
  (local
    (in-theory
      (disable recognizer/unique{definition}
               accessor/unique{definition}
               updater/unique{definition}
               boundp/unique{definition}
               remover/unique{definition}
               count/unique{definition})))

  (defthm count/copyable{type-prescription}
    (natp (count/copyable hash-table))
    :rule-classes :type-prescription)

  (defthm count/copyable-when-not-recognizer/copyable
    (implies (not (recognizer/copyable hash-table))
             (equal (count/copyable hash-table)
                    0)))

  (defthm count/copyable-of-creator/copyable
    (equal (count/copyable (creator/copyable))
           0))

  (defthm count/copyable-of-fixer/copyable
    (equal (count/copyable (fixer/copyable hash-table))
           (count/copyable hash-table)))

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
           (count/copyable hash-table))))


;;;; `CLEAR/UNIQUE'
(defthm clear/unique{type-prescription}
  (true-listp (clear/unique hash-table))
  :rule-classes :type-prescription)

(defthm clear/unique{rewrite}
  (equal (clear/unique hash-table)
         (creator/unique)))


;;;; `CLEAR/COPYABLE'
(defthm clear/copyable{type-prescription}
  (and (consp (clear/copyable hash-table))
       (true-listp (clear/copyable hash-table)))
  :rule-classes :type-prescription)

(defthm clear/copyable{rewrite}
  (equal (clear/copyable hash-table)
         (creator/copyable)))


;;;; `INIT/UNIQUE'
(defthm init/unique{type-prescription}
  (true-listp (init/unique ht-size rehash-size rehash-threshold hash-table))
  :rule-classes :type-prescription)

(defthm init/unique{rewrite}
  (equal (init/unique ht-size rehash-size rehash-threshold hash-table)
         (creator/unique)))


;;;; `INIT/COPYABLE'
(defthm init/copyable{type-prescription}
  (and (consp (init/copyable ht-size rehash-size rehash-threshold hash-table))
       (true-listp (init/copyable ht-size rehash-size rehash-threshold hash-table)))
  :rule-classes :type-prescription)

(defthm init/copyable{rewrite}
  (equal (init/copyable ht-size rehash-size rehash-threshold hash-table)
         (creator/copyable)))


;;;; `KEYS'
(defthm keys{type-prescription}
  (true-listp (keys hash-table))
  :rule-classes :type-prescription)

(defthm keysp-of-keys
  (keysp (keys hash-table)))

(defthm keys-when-not-recognizer/copyable
  (implies (not (recognizer/copyable hash-table))
           (not (keys hash-table))))

(defthm keys-of-creator/copyable
  (not (keys (creator/copyable))))

(defthm keys-of-fixer/copyable
  (equal (keys (fixer/copyable hash-table))
         (keys hash-table)))

(defthm keys-of-updater/copyable
  (equal (keys (updater/copyable key val hash-table))
         (keys hash-table)))

(defthm keys-of-remover/copyable
  (equal (keys (remover/copyable key hash-table))
         (keys hash-table)))

(defthm keys-of-keys-set
  (equal (keys (keys-set set hash-table))
         (keys-fix set)))


;;;; `KEYS-SET'
(defthm keys-set{type-prescription}
  (and (consp (keys-set set hash-table))
       (true-listp (keys-set set hash-table)))
  :rule-classes :type-prescription)

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

(defthm keys-set-of-keys-fix
  (equal (keys-set (keys-fix set) hash-table)
         (keys-set set hash-table)))

(defthm keys-set-of-fixer/copyable
  (equal (keys-set set (fixer/copyable hash-table))
         (keys-set set hash-table)))

(defthm keys-set-of-updater/copyable
  (equal (keys-set set (updater/copyable key val hash-table))
         (updater/copyable key val (keys-set set hash-table))))

(defthm keys-set-of-remover/copyable
  (equal (keys-set set (remover/copyable key hash-table))
         (remover/copyable key (keys-set set hash-table))))

(defthm keys-set-of-keys-free
  (implies (equal (keys-fix set) (keys hash-table))
           (equal (keys-set set hash-table)
                  (fixer/copyable hash-table))))

(defthm keys-set-of-keys
  (equal (keys-set (keys hash-table) hash-table)
         (fixer/copyable hash-table))
  :hints
  (("Goal"
    :in-theory (disable keys-set-of-keys-free)
    :use (:instance keys-set-of-keys-free
                    (set (keys hash-table))))))

(defthm keys-set-of-keys-set
  (equal (keys-set %set (keys-set set hash-table))
         (keys-set %set hash-table)))


;;;; `EQUAL/UNIQUE{FORWARD-CHAINING}'
(defun-sk keys-equal/unique (%hash-table hash-table)
  (declare (xargs :guard (and (recognizer/unique %hash-table)
                              (recognizer/unique hash-table))
                  :verify-guards nil))
  (forall key
    (implies (key-recognizer key)
             (equal (boundp/unique key %hash-table)
                    (boundp/unique key hash-table))))
  :rewrite :direct)

(defun-sk vals-equal/unique (%hash-table hash-table)
  (declare (xargs :guard (and (recognizer/unique %hash-table)
                              (recognizer/unique hash-table))
                  :verify-guards nil))
  (forall key
    (implies (key-recognizer key)
             (equal (accessor/unique key %hash-table)
                    (accessor/unique key hash-table))))
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
    (defthm head-key-equal-when-keys-equal/unique
      (implies (and (recognizer/unique %hash-table)
                    (recognizer/unique hash-table)
                    (not (omap::emptyp %hash-table))
                    (not (omap::emptyp hash-table))
                    (keys-equal/unique %hash-table hash-table))
               (equal (omap::head-key %hash-table)
                      (omap::head-key hash-table)))
      :rule-classes
      ((:rewrite :match-free :all))
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
                         (key (mv-nth 0 (omap::head %hash-table))))))
       ("Subgoal 1"
        :cases ((keys-equal/unique %hash-table hash-table))
        :use ((:instance keys-equal/unique-necc
                         (key (mv-nth 0 (omap::head hash-table)))))))))

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
      :rule-classes
      ((:rewrite :match-free :all))
      :hints
      (("Goal"
        :do-not-induct t
        :cases ((<< (mv-nth 0 (omap::head %hash-table))
                    (mv-nth 0 (omap::head hash-table)))
                (<< (mv-nth 0 (omap::head hash-table))
                    (mv-nth 0 (omap::head %hash-table))))
        :in-theory (disable keys-equal/unique-necc))
       ("Subgoal 3"
        :use ((:instance <<-squeeze
                         (x (mv-nth 0 (omap::head %hash-table)))
                         (y (mv-nth 0 (omap::head hash-table)))))
        :expand ((keys-equal/unique (omap::tail %hash-table)
                                    (omap::tail hash-table))))
       ("Subgoal 3.2"
        :use ((:instance keys-equal/unique-necc
                         (key (keys-equal/unique-witness (omap::tail %hash-table)
                                                         (omap::tail hash-table))))
              (:instance omap::head-key-minimal
                         (key (mv-nth 0 (omap::head %hash-table)))
                         (map (omap::tail hash-table)))
              (:instance omap::head-tail-order
                         (x hash-table)))
        :expand ((omap::assoc (keys-equal/unique-witness (omap::tail %hash-table)
                                                         (omap::tail hash-table))
                              %hash-table)))
       ("Subgoal 3.1"
        :use ((:instance keys-equal/unique-necc
                         (key (keys-equal/unique-witness (omap::tail %hash-table)
                                                         (omap::tail hash-table)))))
        :expand (omap::assoc (keys-equal/unique-witness (omap::tail %hash-table)
                                                        (omap::tail hash-table))
                             hash-table))
       ("Subgoal 2"
        :use ((:instance head-key-equal-when-keys-equal/unique)))
       ("Subgoal 1"
        :use ((:instance head-key-equal-when-keys-equal/unique))))))

  (local
    (defthm head-val-equal-when-vals-equal/unique
      (implies (and (recognizer/unique %hash-table)
                    (recognizer/unique hash-table)
                    (not (omap::emptyp %hash-table))
                    (not (omap::emptyp hash-table))
                    (keys-equal/unique %hash-table hash-table)
                    (vals-equal/unique %hash-table hash-table))
               (equal (omap::head-val %hash-table)
                      (omap::head-val hash-table)))
      :rule-classes
      ((:rewrite :match-free :all))
      :hints
      (("Goal"
        :in-theory (disable keys-equal/unique-necc
                            vals-equal/unique-necc)
        :use ((:instance vals-equal/unique-necc
                         (key (omap::head-key %hash-table)))
              (:instance vals-equal/unique-necc
                         (key (omap::head-key hash-table)))
              (:instance head-key-equal-when-keys-equal/unique))))))

  (local
    (defthmd accessor/unique-when-small
      (implies (<< (key-fixer key) (omap::head-key map))
               (equal (accessor/unique key map)
                      (default-val)))
      :hints
      (("Subgoal *1/3.9"
        :in-theory (disable omap::head-tail-order)
        :use ((:instance omap::head-tail-order
                         (x map))))
       ("Subgoal *1/3.2"
        :in-theory (disable omap::head-tail-order)
        :use ((:instance omap::head-tail-order
                         (x map)))
        :expand (accessor/unique (default-key) map))
       ("Subgoal *1/3.1"
        :expand (accessor/unique (default-key) map)))))

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
      :rule-classes
      ((:rewrite :match-free :all))
      :hints
      (("Goal"
        :do-not-induct t
        :cases ((<< (mv-nth 0 (omap::head %hash-table))
                    (mv-nth 0 (omap::head hash-table)))
                (<< (mv-nth 0 (omap::head hash-table))
                    (mv-nth 0 (omap::head %hash-table))))
        :in-theory (disable keys-equal/unique-necc
                            vals-equal/unique-necc))
       ("Subgoal 3"
        :use ((:instance <<-squeeze
                         (x (mv-nth 0 (omap::head %hash-table)))
                         (y (mv-nth 0 (omap::head hash-table))))
              (:instance vals-equal/unique-necc
                         (key (vals-equal/unique-witness (omap::tail %hash-table)
                                                         (omap::tail hash-table))))
              (:instance accessor/unique-when-small
                         (key (mv-nth 0 (omap::head %hash-table)))
                         (map (omap::tail hash-table)))
              (:instance omap::head-tail-order
                         (x hash-table)))
        :expand ((vals-equal/unique (omap::tail %hash-table)
                                    (omap::tail hash-table))))
       ("Subgoal 2"
        :use ((:instance head-key-equal-when-keys-equal/unique)))
       ("Subgoal 1"
        :use ((:instance head-key-equal-when-keys-equal/unique))))))

  (local
    (defthmd emptyp-iff-zp-size
      (iff (omap::emptyp map)
           (zp (omap::size map)))
      :hints
      (("Goal"
        :in-theory (enable omap::size)))))

  (local
    (defthm count/unique-of-tail
      (implies (and (recognizer/unique hash-table)
                    (not (omap::emptyp hash-table)))
               (equal (count/unique (omap::tail hash-table))
                      (1- (count/unique hash-table))))))

  (defthm equal/unique{forward-chaining}
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
      :use ((:instance head-key-equal-when-keys-equal/unique)
            (:instance keys-equal/unique-of-tail-when-keys-equal/unique)
            (:instance head-val-equal-when-vals-equal/unique)
            (:instance vals-equal/unique-of-tail-when-vals-equal/unique)))
     ("Subgoal *1/2"
      :do-not-induct t
      :in-theory (enable emptyp-iff-zp-size))
     ("Subgoal *1/1"
      :do-not-induct t
      :in-theory (enable omap::mapp
                         omap::mfix
                         omap::emptyp
                         omap::head
                         omap::tail)
      :use ((:instance emptyp-iff-zp-size
                       (map hash-table)))))))


;;;; `EQUAL/COPYABLE{FORWARD-CHAINING}'
(defun-sk keys-equal/copyable (%hash-table hash-table)
  (declare (xargs :guard (and (recognizer/copyable %hash-table)
                              (recognizer/copyable hash-table))
                  :verify-guards nil))
  (forall key
    (implies (key-recognizer key)
             (equal (boundp/copyable key %hash-table)
                    (boundp/copyable key hash-table))))
  :rewrite :direct)

(defun-sk vals-equal/copyable (%hash-table hash-table)
  (declare (xargs :guard (and (recognizer/copyable %hash-table)
                              (recognizer/copyable hash-table))
                  :verify-guards nil))
  (forall key
    (implies (key-recognizer key)
             (equal (accessor/copyable key %hash-table)
                    (accessor/copyable key hash-table))))
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
      (disable recognizer/unique{definition}
               accessor/unique{definition}
               updater/unique{definition}
               boundp/unique{definition}
               remover/unique{definition}
               count/unique{definition}
               keys-equal/unique
               vals-equal/unique
               equal/unique)))

  (local
    (defthmd keys-equal/copyable-when-keys-equal/unique
      (implies (and (recognizer/copyable %hash-table)
                    (recognizer/copyable hash-table)
                    (keys-equal/unique (cdr %hash-table)
                                       (cdr hash-table)))
               (keys-equal/copyable %hash-table
                                    hash-table))))

  (local
    (defthmd keys-equal/unique-when-keys-equal/copyable
      (implies (and (recognizer/copyable %hash-table)
                    (recognizer/copyable hash-table)
                    (keys-equal/copyable %hash-table
                                         hash-table))
               (keys-equal/unique (cdr %hash-table)
                                  (cdr hash-table)))
      :hints
      (("Goal"
        :in-theory (disable keys-equal/copyable
                            keys-equal/copyable-necc)
        :use ((:instance keys-equal/copyable-necc
                         (key (keys-equal/unique-witness (cdr %hash-table)
                                                         (cdr hash-table)))))
        :expand (keys-equal/unique (cdr %hash-table)
                                   (cdr hash-table))))))

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
        :use (keys-equal/unique-when-keys-equal/copyable
              keys-equal/copyable-when-keys-equal/unique)))))

  (local
    (defthmd vals-equal/copyable-when-vals-equal/unique
      (implies (and (recognizer/copyable %hash-table)
                    (recognizer/copyable hash-table)
                    (vals-equal/unique (cdr %hash-table)
                                       (cdr hash-table)))
               (vals-equal/copyable %hash-table
                                    hash-table))))

  (local
    (defthmd vals-equal/unique-when-vals-equal/copyable
      (implies (and (recognizer/copyable %hash-table)
                    (recognizer/copyable hash-table)
                    (vals-equal/copyable %hash-table
                                         hash-table))
               (vals-equal/unique (cdr %hash-table)
                                  (cdr hash-table)))
      :hints
      (("Goal"
        :in-theory (disable vals-equal/copyable
                            vals-equal/copyable-necc)
        :use ((:instance vals-equal/copyable-necc
                         (key (vals-equal/unique-witness (cdr %hash-table)
                                                         (cdr hash-table)))))
        :expand (vals-equal/unique (cdr %hash-table)
                                   (cdr hash-table))))))

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
        :use (vals-equal/unique-when-vals-equal/copyable
              vals-equal/copyable-when-vals-equal/unique)))))

  (local
    (in-theory
      (disable keys-equal/copyable
               vals-equal/copyable)))

  (defthm equal/copyable{forward-chaining}
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
      :use ((:instance equal/unique
                       (%hash-table (cdr %hash-table))
                       (hash-table (cdr hash-table))))))))
