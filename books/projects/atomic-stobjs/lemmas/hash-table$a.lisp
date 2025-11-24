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

#||
(include-book "std/lists/top" :dir :system)
(include-book "std/alists/top" :dir :system)
||#

(include-book "std/osets/top" :dir :system)
(include-book "std/omaps/top" :dir :system)

(include-book "../utilities/with-books")
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
      ((or (endp hash-table)
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
      ((endp hash-table)
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
      ((or (endp hash-table)
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
      ((endp hash-table)
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
    (if (endp hash-table)
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
(defthm keysp{definition}
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
                          (pair (car hash-table))
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

(defthm keysp-when-emptyp
  (implies (set::emptyp set)
           (equal (keysp set)
                  (set::setp set))))

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

(defthm in-when-keysp
  (implies (and (keysp set)
                (not (key-recognizer key)))
           (not (set::in key set)))
  :hints
  (("Goal"
    :in-theory (enable set::in))))

(defthm keysp-when-subset
  (implies (and (not (keysp %set))
                (keysp set))
           (equal (set::subset %set set)
                  (set::emptyp %set)))
  :hints
  (("Goal"
    :induct (set::cardinality %set)
    :in-theory (enable set::cardinality)
    :expand (set::subset %set set))
   ("Subgoal *1/"
    :in-theory (enable set::emptyp))))

(defthm keysp-of-insert
  (equal (keysp (set::insert key set))
         (and (key-recognizer key)
              (or (set::emptyp set)
                  (keysp set))))
  :hints
  (("Goal"
    :induct (set::cardinality set)
    :in-theory (enable set::cardinality)
    :expand (keysp (set::insert key set)))))

(defthm keysp-of-delete
  (implies (keysp set)
           (keysp (set::delete key set)))
  :hints
  (("Goal"
    :in-theory (enable set::delete))))


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


(local
  (in-theory
    (disable keysp
             keysp{definition}
             keys-fix
             recognizer/unique
             recognizer/copyable
             creator/unique
             (:e creator/unique)
             creator/copyable
             (:e creator/copyable)
             fixer/unique
             fixer/copyable
             accessor/unique
             accessor/copyable
             updater/unique
             updater/copyable
             boundp/unique
             boundp/copyable
             getp/unique
             getp/copyable
             remover/unique
             remover/copyable
             count/unique
             count/copyable
             clear/unique
             clear/copyable
             init/unique
             init/copyable
             keys
             keys-set
             accessor/unique{definition}
             updater/unique{definition}
             boundp/unique{definition}
             remover/unique{definition}
             count/unique{definition}
             recognizer/unique{induction}-fn
             accessor/unique{induction}-fn
             equal/unique
             equal/copyable)))


;;;; Val Copy
(encapsulate (((val-coupled-p *) => *))
  (local
    (defun val-coupled-p (val)
      (declare (xargs :guard t)
               (ignore val))
      t))

  (defthm val-coupled-p-constraint
    (booleanp (val-coupled-p val))
    :rule-classes :type-prescription)

  (defthm val-coupled-p-of-default-val
    (val-coupled-p (default-val)))

  (defthm val-coupled-p-when-not-val-recognizer
    (implies (not (val-recognizer val))
             (val-coupled-p val))))

(encapsulate (((val-copy * *) => *))
  (local
    (defun val-copy (%val val)
      (declare (xargs :guard (and (val-recognizer %val)
                                  (val-recognizer val)))
               (ignore %val))
      (val-fixer val)))

  (defthm val-recognizer-of-val-copy
    (val-recognizer (val-copy %val val)))

  (defthm val-copy-ignores-1
    (implies (syntaxp (not (and (consp %value)
                                (eq (car %value) 'default-val))))
             (equal (val-copy %value value)
                    (val-copy (default-val) value))))

  (defthm val-copy{rewrite}
    (implies (val-coupled-p val)
             (equal (val-copy %val val)
                    (val-fixer val)))))


;;;; `COUPLED-KEYS-P'
(defun-sk coupled-keys-p (hash-table)
  (declare (xargs :guard (recognizer/copyable hash-table)
                  :verify-guards nil))
  (forall key
    (equal (set::in key (keys hash-table))
           (and (key-recognizer key)
                (boundp/copyable key hash-table))))
  :rewrite :direct)

(defthm coupled-keys-p-when-not-recognizer/copyable
  (implies (not (recognizer/copyable hash-table))
           (coupled-keys-p hash-table)))

(defthm coupled-keys-p-of-creator/copyable
  (coupled-keys-p (creator/copyable)))

(defthm coupled-keys-p-of-fixer/copyable
  (equal (coupled-keys-p (fixer/copyable hash-table))
         (coupled-keys-p hash-table))
  :hints
  (("Goal"
    :in-theory (enable fixer/copyable))))

(defthm coupled-keys-p-of-updater/copyable-when-boundp/copyable
  (implies (and (boundp/copyable key hash-table)
                (coupled-keys-p hash-table))
           (coupled-keys-p (updater/copyable key val hash-table))))

(defthm coupled-keys-p-of-updater/copyable-when-not-boundp/copyable
  (implies (let* ((keys (keys hash-table))
                  (trimmed (set::delete (key-fixer key) keys)))
             (and (not (boundp/copyable key hash-table))
                  (set::in (key-fixer key) keys)
                  (coupled-keys-p (keys-set trimmed hash-table))))
           (coupled-keys-p (updater/copyable key val hash-table)))
  :hints
  (("Goal"
    :in-theory (disable coupled-keys-p)
    :expand (:free (key)
                   (coupled-keys-p (updater/copyable key val hash-table))))
   ("Subgoal 3"
    :use ((:instance coupled-keys-p-necc
                     (key (coupled-keys-p-witness (updater/copyable key val hash-table)))
                     (hash-table (keys-set (set::delete key (keys hash-table))
                                           hash-table)))))
   ("Subgoal 1"
    :use ((:instance coupled-keys-p-necc
                     (key (coupled-keys-p-witness (updater/copyable (default-key)
                                                                    val hash-table)))
                     (hash-table (keys-set (set::delete (default-key)
                                                        (keys hash-table))
                                           hash-table)))))))

(defthm coupled-keys-p-of-remover/copyable-when-boundp/copyable
  (implies (let* ((keys (keys hash-table))
                  (inserted (set::insert (key-fixer key) keys)))
             (and (boundp/copyable key hash-table)
                  (not (set::in (key-fixer key) keys))
                  (coupled-keys-p (keys-set inserted hash-table))))
           (coupled-keys-p (remover/copyable key hash-table)))
  :hints
  (("Goal"
    :in-theory (disable coupled-keys-p)
    :expand (:free (key)
                   (coupled-keys-p (remover/copyable key hash-table))))
   ("Subgoal 3"
    :use ((:instance coupled-keys-p-necc
                     (key (coupled-keys-p-witness (remover/copyable key hash-table)))
                     (hash-table (keys-set (set::insert key (keys hash-table))
                                           hash-table)))))
   ("Subgoal 1"
    :use ((:instance coupled-keys-p-necc
                     (key (coupled-keys-p-witness (remover/copyable (default-key)
                                                                    hash-table)))
                     (hash-table (keys-set (set::insert (default-key)
                                                        (keys hash-table))
                                           hash-table)))))))

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
    (val-coupled-p (accessor/copyable key hash-table)))
  :rewrite :direct)

(defthm coupled-vals-p-when-not-recognizer
  (implies (not (recognizer/copyable hash-table))
           (coupled-vals-p hash-table)))

(defthm coupled-vals-p-of-creator/copyable
  (coupled-vals-p (creator/copyable)))

(defthm coupled-vals-p-of-fixer/copyable
  (equal (coupled-vals-p (fixer/copyable hash-table))
         (coupled-vals-p hash-table))
  :hints
  (("Goal"
    :in-theory (enable fixer/copyable))))

(defthm coupled-vals-p-of-updater/copyable
  (implies (coupled-vals-p hash-table)
           (equal (coupled-vals-p (updater/copyable key val hash-table))
                  (val-coupled-p val)))
  :hints
  (("Goal"
    :cases ((coupled-vals-p (updater/copyable key val hash-table)))
    :in-theory (disable coupled-vals-p))
   ("Subgoal 2"
    :expand (:free (key)
                   (coupled-vals-p (updater/copyable key val hash-table))))
   ("Subgoal 1"
    :use ((:instance coupled-vals-p-necc
                     (key key)
                     (hash-table (updater/copyable key val hash-table)))))))

(defthm coupled-vals-p-of-remover/copyable
  (implies (coupled-vals-p hash-table)
           (coupled-vals-p (remover/copyable key hash-table))))

(defthm coupled-vals-p-of-keys-set
  (equal (coupled-vals-p (keys-set keys hash-table))
         (coupled-vals-p hash-table))
  :hints
  (("Goal"
    :cases ((coupled-vals-p hash-table))
    :in-theory (disable coupled-vals-p))
   ("Subgoal 2"
    :use ((:instance coupled-vals-p-necc
                     (key (coupled-vals-p-witness hash-table))
                     (hash-table (keys-set keys hash-table))))
    :expand (coupled-vals-p hash-table))
   ("Subgoal 1"
    :expand (:free (keys)
                   (coupled-vals-p (keys-set keys hash-table))))))

(local
  (in-theory
    (disable coupled-vals-p)))


;;;; `COUPLEDP'
(defun-nx coupledp (hash-table)
  (declare (xargs :guard (recognizer/copyable hash-table)
                  :verify-guards nil))
  (and (equal (set::cardinality (keys hash-table))
              (count/copyable hash-table))
       (coupled-keys-p hash-table)
       (coupled-vals-p hash-table)))

(defthm coupledp-when-not-recognizer/copyable
  (implies (not (recognizer/copyable hash-table))
           (coupledp hash-table)))

(defthm coupledp-of-creator/copyable
  (coupledp (creator/copyable)))

(defthm coupledp-of-fixer/copyable
  (equal (coupledp (fixer/copyable hash-table))
         (coupledp hash-table)))

(defthm val-coupled-p-of-accessor/copyable
  (implies (coupledp hash-table)
           (val-coupled-p (accessor/copyable key hash-table))))

(defthm coupledp-of-updater/copyable-when-boundp/copyable
  (implies (and (boundp/copyable key hash-table)
                (coupledp hash-table))
           (equal (coupledp (updater/copyable key val hash-table))
                  (val-coupled-p val))))

(defthm coupledp-of-updater/copyable-when-not-boundp/copyable
  (implies (let* ((keys (keys hash-table))
                  (trimmed (set::delete (key-fixer key) keys)))
             (and (not (boundp/copyable key hash-table))
                  (set::in (key-fixer key) keys)
                  (coupledp (keys-set trimmed hash-table))))
           (equal (coupledp (updater/copyable key val hash-table))
                  (val-coupled-p val))))

(defthm in-of-keys-when-coupledp
  (implies (coupledp hash-table)
           (equal (set::in key (keys hash-table))
                  (and (key-recognizer key)
                       (boundp/copyable key hash-table)))))

(defthm coupledp-of-remover/copyable-when-boundp/copyable
  (implies (let* ((keys (keys hash-table))
                  (inserted (set::insert (key-fixer key) keys)))
             (and (boundp/copyable key hash-table)
                  (not (set::in (key-fixer key) keys))
                  (coupledp (keys-set inserted hash-table))))
           (coupledp (remover/copyable key hash-table))))

(defthm coupledp-of-remover/copyable-when-not-boundp/copyable
  (implies (and (not (boundp/copyable key hash-table))
                (coupledp hash-table))
           (coupledp (remover/copyable key hash-table))))

(defthm cardinality-of-keys-when-coupledp
  (implies (coupledp hash-table)
           (equal (set::cardinality (keys hash-table))
                  (count/copyable hash-table))))

(encapsulate ()
  (local
    (defthm keysp-when-emptyp-alt
      (implies (set::emptyp (keys hash-table))
               (not (keys hash-table)))
      :hints
      (("Goal"
        :in-theory (enable keysp{definition}
                           set::emptyp)))))

  (defthm emptyp-of-keys-when-coupledp
    (implies (coupledp hash-table)
             (equal (set::emptyp (keys hash-table))
                    (or (not (recognizer/copyable hash-table))
                        (equal hash-table (creator/copyable)))))
    :hints
    (("Goal"
      :cases ((set::emptyp (keys hash-table)))
      :in-theory (enable fixer/copyable))
     ("Subgoal 1"
      :use ((:instance equal/copyable
                       (%hash-table (creator/copyable))))))))

(local
  (in-theory
    (disable coupledp)))


;;;; `COPY-REC'
(defun copy-rec (set %hash-table hash-table)
  (declare (xargs :guard (and (keysp set)
                              (recognizer/copyable %hash-table)
                              (recognizer/copyable hash-table)
                              (set::subset set (keys hash-table)))))
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

(defthm recognizer/copyable-of-copy-rec
  (recognizer/copyable (copy-rec set %hash-table hash-table)))

(defthm copy-rec-of-fixer/copyable-1
  (equal (copy-rec set (fixer/copyable %hash-table) hash-table)
         (copy-rec set %hash-table hash-table)))

(defthm copy-rec-of-fixer/copyable-2
  (equal (copy-rec set %hash-table (fixer/copyable hash-table))
         (copy-rec set %hash-table hash-table)))

(defthm copy-rec-of-updater/copyable
  (implies (and (coupledp hash-table)
                (set::subset set (keys hash-table)))
           (equal (copy-rec set (updater/copyable key val %hash-table) hash-table)
                  (if (set::in (key-fixer key) set)
                      (copy-rec set %hash-table hash-table)
                      (updater/copyable key val (copy-rec set %hash-table hash-table)))))
  :hints
  (("Goal"
    :induct (copy-rec set %hash-table hash-table)
    :expand (set::subset set (keys hash-table)))
   ("Subgoal *1/2.8"
    :use ((:instance in-of-keys-when-coupledp
                     (key (default-key))))
    :expand ((set::in (default-key) set)
             (:free (key val)
                    (copy-rec set (updater/copyable key val %hash-table) hash-table))))
   ("Subgoal *1/2.7"
    :expand ((set::in (default-key) set)
             (:free (key val)
                    (copy-rec set (updater/copyable key val %hash-table) hash-table))))
   ("Subgoal *1/2.5"
    :expand ((set::in (default-key) set)
             (:free (key val)
                    (copy-rec set (updater/copyable key val %hash-table) hash-table))))
   ("Subgoal *1/2.4"
    :expand ((set::in (default-key) set)
             (:free (key val)
                    (copy-rec set (updater/copyable key val %hash-table) hash-table))))
   ("Subgoal *1/2.3"
    :expand ((set::in (default-key) set)
             (:free (key val)
                    (copy-rec set (updater/copyable key val %hash-table) hash-table))))
   ("Subgoal *1/2.1"
    :expand ((set::in (default-key) set)
             (:free (key val)
                    (copy-rec set (updater/copyable key val %hash-table) hash-table))))))

(defthm accessor/copyable-of-copy-rec
  (implies (and (coupledp hash-table)
                (set::subset set (keys hash-table)))
           (equal (accessor/copyable key (copy-rec set %hash-table hash-table))
                  (if (set::in (key-fixer key) set)
                      (accessor/copyable key hash-table)
                      (accessor/copyable key %hash-table))))
  :hints
  (("Goal"
    :induct (copy-rec set %hash-table hash-table)
    :in-theory (enable set::in)
    :expand (set::subset set (keys hash-table)))
   ("Subgoal *1/2.9"
    :expand (set::in (default-key) set))))

(defthm boundp/copyable-of-copy-rec
  (implies (and (coupledp hash-table)
                (set::subset set (keys hash-table)))
           (equal (boundp/copyable key (copy-rec set %hash-table hash-table))
                  (or (boundp/copyable key %hash-table)
                      (set::in (key-fixer key) set))))
  :hints
  (("Goal"
    :induct (copy-rec set %hash-table hash-table)
    :in-theory (enable set::in)
    :expand (set::subset set (keys hash-table)))
   ("Subgoal *1/2.11"
    :expand (set::in (default-key) set))
   ("Subgoal *1/2.9"
    :expand (set::in key set))
   ("Subgoal *1/2.1"
    :expand (set::in (default-key) set))))

(defthmd count/copyable-of-copy-rec
  (implies (and (coupledp hash-table)
                (set::subset set (keys hash-table)))
           (equal (count/copyable (copy-rec set %hash-table hash-table))
                  (cond
                    ((or (set::emptyp set)
                         (not (keysp set)))
                     (count/copyable %hash-table))
                    ((boundp/copyable (set::head set) %hash-table)
                     (count/copyable (copy-rec (set::tail set) %hash-table hash-table)))
                    (t
                     (1+ (count/copyable (copy-rec (set::tail set) %hash-table hash-table)))))))
  :hints
  (("Goal"
    :induct (copy-rec set %hash-table hash-table)
    :expand ((keysp set)
             (set::subset set (keys hash-table))))))

(defthm keys-of-copy-rec
  (equal (keys (copy-rec set %hash-table hash-table))
         (keys %hash-table)))

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

(defthmd copy-ignores-1
  (equal (copy %hash-table hash-table)
         (copy (creator/copyable) hash-table))
  :hints
  (("Goal"
    :use ((:instance equal/copyable
                     (%hash-table (copy %hash-table hash-table))
                     (hash-table (copy (creator/copyable) hash-table)))))))

(local
  (defthm copy-ignores-1-local
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
      :by (:functional-instance copy-ignores-1)))))

(defthm copy-of-fixer/copyable-2
  (equal (copy %hash-table (fixer/copyable hash-table))
         (copy %hash-table hash-table)))

(defthm coupled-keys-p-of-copy
  (implies (coupledp hash-table)
           (coupled-keys-p (copy %hash-table hash-table)))
  :hints
  (("Goal"
    :expand (coupled-keys-p (copy-rec (keys hash-table)
                                      (keys-set (keys hash-table)
                                                (creator/copyable))
                                      hash-table)))))

(defthm coupled-vals-p-of-copy
  (implies (coupledp hash-table)
           (coupled-vals-p (copy %hash-table hash-table)))
  :hints
  (("Goal"
    :expand (coupled-vals-p (copy-rec (keys hash-table)
                                      (keys-set (keys hash-table)
                                                (creator/copyable))
                                      hash-table)))))

(encapsulate ()
  (local
    (defthm coupledp-of-copy-lemma-0
      (implies (and (set::subset %set (keys hash-table))
                    (keysp set)
                    (coupledp hash-table))
               (equal (count/copyable (copy-rec %set (keys-set set (creator/copyable)) hash-table))
                      (count/copyable (copy-rec %set (creator/copyable) hash-table))))
      :hints
      (("Goal"
        :induct (set::cardinality %set)
        :in-theory (enable (:i set::cardinality)))
       ("Subgoal *1/2"
        :expand ((set::subset %set (keys hash-table))
                 (:free (%hash-table)
                        (copy-rec %set %hash-table hash-table))))
       ("Subgoal *1/1"
        :expand ((set::subset %set (keys hash-table))
                 (:free (%hash-table)
                        (copy-rec %set %hash-table hash-table)))))))

  (local
    (defthm coupledp-of-copy-lemma-1
      (implies (and (set::subset set (keys hash-table))
                    (coupledp hash-table))
               (equal (count/copyable (copy-rec set (creator/copyable) hash-table))
                      (set::cardinality set)))
      :hints
      (("Goal"
        :induct (set::cardinality set)
        :in-theory (enable set::cardinality
                           keysp{definition}))
       ("Subgoal *1/2"
        :expand ((set::subset set (keys hash-table))
                 (copy-rec set (creator/copyable) hash-table)))
       ("Subgoal *1/1"
        :expand ((copy-rec set (creator/copyable) hash-table))))))

  (defthm coupledp-of-copy
    ;; TODO: This should be equality rather than implication.  That is,
    ;; ```(equal (coupledp (copy %hash-table hash-table))
    ;;           (coupledp hash-table))'''
    ;; looks like a theorem.
    (implies (coupledp hash-table)
             (coupledp (copy %hash-table hash-table)))
    :hints
    (("Goal"
      :in-theory (enable coupled-keys-p
                         coupled-vals-p)
      :expand (coupledp (copy-rec (keys hash-table)
                                  (keys-set (keys hash-table)
                                            (creator/copyable))
                                  hash-table)))))

  (defthm count/copyable-of-copy
    (implies (coupledp hash-table)
             (equal (count/copyable (copy %hash-table hash-table))
                    (count/copyable hash-table)))))

(defthm accessor/copyable-of-copy
  (implies (coupledp hash-table)
           (equal (accessor/copyable key (copy %hash-table hash-table))
                  (accessor/copyable key hash-table))))

(defthm boundp/copyable-of-copy
  (implies (coupledp hash-table)
           (equal (boundp/copyable key (copy %hash-table hash-table))
                  (boundp/copyable key hash-table))))

(defthm keys-of-copy
  (equal (keys (copy %hash-table hash-table))
         (keys hash-table)))

(local
  (in-theory
    (disable copy)))

(defthm copy{rewrite}
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

  (defthm name-constraint
    (symbolp (name))
    :rule-classes :type-prescription)

  (local
    (defun val-export-p (export)
      (declare (xargs :guard t))
      (val-recognizer export)))

  (defthm val-export-p-constraint
    (booleanp (val-export-p export))
    :rule-classes :type-prescription)

  (local
    (defun val-export (val)
      (declare (xargs :guard (val-recognizer val)))
      (val-fixer val)))

  (defthm val-export-p-of-val-export
    (val-export-p (val-export val)))

  (local
    (defun val-import (export val)
      (declare (xargs :guard (and (val-export-p export)
                                  (val-recognizer val)))
               (ignore val))
      (val-fixer export)))

  (defthm val-recognizer-of-val-import
    (val-recognizer (val-import export val)))

  (defthm val-import-when-not-val-export-p
    (implies (not (val-export-p export))
             (equal (val-import export val)
                    (default-val))))

  (defthm val-import-ignores-val
    (implies (syntaxp (not (and (consp val)
                                (eq (car val) 'default-val))))
             (equal (val-import export val)
                    (val-import export (default-val)))))

  (defthm val-export-of-val-import
    (implies (val-export-p export)
             (equal (val-export (val-import export val))
                    export)))

  (defthm val-import-of-val-export
    (implies (val-coupled-p %val)
             (equal (val-import (val-export %val) val)
                    (val-fixer %val)))))


;;;; `ALL-KEYS-RECOGNIZED-P'
(defun-sk all-keys-recognized-p (omap)
  (declare (xargs :guard (omap::mapp omap)
                  :verify-guards nil))
  (forall key
    (implies (set::in key (omap::keys omap))
             (key-recognizer key)))
  :rewrite :direct)

(local
  (in-theory
    (disable all-keys-recognized-p)))

(defthm all-keys-recognized-p-of-tail
  (implies (and (not (omap::emptyp omap))
                (all-keys-recognized-p omap))
           (all-keys-recognized-p (omap::tail omap)))
  :hints
  (("Goal"
    :expand (all-keys-recognized-p (omap::tail omap)))))

(defthm all-keys-recognized-p-of-update
  (implies (and (key-recognizer key)
                (all-keys-recognized-p omap))
           (all-keys-recognized-p (omap::update key val omap)))
  :hints
  (("Goal"
    :expand (all-keys-recognized-p (omap::update key val omap)))))


;;;; `ALL-VALS-EXPORTS-P'
(defun-sk all-vals-exports-p (omap)
  (declare (xargs :guard (omap::mapp omap)
                  :verify-guards nil))
  (forall val
    (implies (set::in val (omap::values omap))
             (val-export-p val)))
  :rewrite :direct)

(local
  (in-theory
    (disable all-vals-exports-p)))

(defthm all-vals-exports-p-of-tail
  (implies (and (not (omap::emptyp omap))
                (all-vals-exports-p omap))
           (all-vals-exports-p (omap::tail omap)))
  :hints
  (("Goal"
    :in-theory (disable all-vals-exports-p-necc)
    :use ((:instance all-vals-exports-p-necc
                     (val (all-vals-exports-p-witness (omap::tail omap)))))
    :expand ((all-vals-exports-p (omap::tail omap))
             (omap::values omap)))))

(local
  (defthm values-of-update
    (implies (and (set::in %val (omap::values (omap::update key val omap)))
                  (not (equal %val val)))
             (set::in %val (omap::values omap)))
    :hints
    (("Goal"
      :in-theory (enable omap::mapp
                         omap::emptyp
                         omap::mfix
                         omap::head
                         omap::tail
                         omap::update
                         omap::values)))))

(defthm all-vals-exports-p-of-update
  (implies (and (val-export-p val)
                (all-vals-exports-p omap))
           (all-vals-exports-p (omap::update key val omap)))
  :hints
  (("Goal"
    :expand (all-vals-exports-p (omap::update key val omap)))
   ("Subgoal *1/2"
    :cases ((equal val (all-vals-exports-p-witness (omap::update key val omap))))
    :in-theory (disable all-vals-exports-p-necc)
    :use ((:instance all-vals-exports-p-necc
                     (val (all-vals-exports-p-witness (omap::update key val omap))))))))


;;;; `EXPORTP-REC'
(defun exportp-rec (omap)
  (declare (xargs :guard t))
  (if (atom omap)
      (null omap)
      (and (consp (car omap))
           (key-recognizer (caar omap))
           (val-export-p (cdar omap))
           (or (null (cdr omap))
               (and (consp (cdr omap))
                    (consp (cadr omap))
                    (<< (caar omap) (caadr omap))
                    (exportp-rec (cdr omap)))))))

(defthm exportp-rec{type-prescription}
  (booleanp (exportp-rec omap))
  :rule-classes :type-prescription)

(defthm exportp-rec{compound-recognizer}
  (implies (exportp-rec omap)
           (true-listp omap))
  :rule-classes :compound-recognizer)

(encapsulate ()
  (defthm mapp-when-exportp-rec
    (implies (exportp-rec omap)
             (omap::mapp omap))
    :hints
    (("Goal"
      :in-theory (enable omap::mapp))))

  (defthm all-keys-recognized-p-when-exportp-rec
    (implies (exportp-rec omap)
             (all-keys-recognized-p omap))
    :hints
    (("Subgoal *1/4"
      :in-theory (enable omap::head
                         omap::tail)
      :expand ((all-keys-recognized-p omap)
               (omap::keys omap)))
     ("Subgoal *1/2"
      :in-theory (enable omap::head
                         omap::tail)
      :expand ((all-keys-recognized-p omap)
               (omap::keys omap)))
     ("Subgoal *1/1"
      :expand (all-keys-recognized-p nil))))

  (defthm all-vals-recognized-p-when-exportp-rec
    (implies (exportp-rec omap)
             (all-vals-exports-p omap))
    :hints
    (("Subgoal *1/4"
      :in-theory (enable omap::head
                         omap::tail)
      :expand ((all-vals-exports-p omap)
               (omap::values omap)))
     ("Subgoal *1/2"
      :in-theory (enable omap::head
                         omap::tail)
      :expand ((all-vals-exports-p omap)
               (omap::values omap)))
     ("Subgoal *1/1"
      :expand (all-vals-exports-p nil))))

  (local
    (defthm exportp-rec{definition}-lemma
      (implies (and (omap::mapp omap)
                    (all-keys-recognized-p omap)
                    (all-vals-exports-p omap))
               (exportp-rec omap))
      :hints
      (("Goal"
        :induct (exportp-rec omap))
       ("Subgoal *1/9"
        :expand (omap::mapp omap))
       ("Subgoal *1/8"
        :in-theory (e/d (omap::head
                         omap::tail
                         omap::keys)
                        (all-keys-recognized-p-necc))
        :use ((:instance all-keys-recognized-p-necc
                         (key (caar omap)))))
       ("Subgoal *1/7"
        :in-theory (e/d (omap::head
                         omap::tail
                         omap::values)
                        (all-vals-exports-p-necc))
        :use ((:instance all-vals-exports-p-necc
                         (val (cdar omap)))))
       ("Subgoal *1/6"
        :in-theory (enable omap::mapp))
       ("Subgoal *1/5"
        :in-theory (enable omap::mapp))
       ("Subgoal *1/4"
        :in-theory (enable omap::mapp))
       ("Subgoal *1/3.3"
        :in-theory (enable omap::mapp))
       ("Subgoal *1/3.2"
        :in-theory (e/d (omap::values
                         omap::head
                         omap::tail)
                        (all-vals-exports-p-necc))
        :use ((:instance all-vals-exports-p-necc
                         (val (all-vals-exports-p-witness (cdr omap)))))
        :expand (all-vals-exports-p (cdr omap)))
       ("Subgoal *1/3.1"
        :in-theory (e/d (omap::keys
                         omap::head
                         omap::tail)
                        (all-keys-recognized-p-necc))
        :use ((:instance all-keys-recognized-p-necc
                         (key (all-keys-recognized-p-witness (cdr omap)))))
        :expand (all-keys-recognized-p (cdr omap)))
       ("Subgoal *1/1"
        :in-theory (enable omap::mapp)))))

  (defthm exportp-rec{definition}
    (equal (exportp-rec omap)
           (and (omap::mapp omap)
                (all-keys-recognized-p omap)
                (all-vals-exports-p omap)))
    :rule-classes :definition
    :hints
    (("Subgoal 2"
      :cases ((all-vals-exports-p omap))))))

(defthm keysp-of-keys-when-exportp-rec
  (implies (exportp-rec omap)
           (keysp (omap::keys omap)))
  :hints
  (("Goal"
    :induct (omap::keys omap)
    :in-theory (enable omap::keys))))

(defthm val-export-p-when-exportp-rec
  (implies (and (exportp-rec omap)
                (omap::assoc key omap))
           (val-export-p (cdr (omap::assoc key omap))))
  :hints
  (("Goal"
    :in-theory (enable omap::assoc))
   ("Subgoal *1/2"
    :in-theory (disable all-vals-exports-p-necc)
    :use ((:instance all-vals-exports-p-necc
                     (val (mv-nth 1 (omap::head omap)))))
    :expand (omap::values omap))))

(local
  (in-theory
    (disable exportp-rec)))


;;;; `EXPORTP'
(defun exportp (export)
  (declare (xargs :guard t))
  (and (consp export)
       (equal (car export) (name))
       (exportp-rec (cdr export))))

(defthm exportp{type-prescription}
  (booleanp (exportp export))
  :rule-classes :type-prescription)

(defthm exportp{compound-recognizer}
  (implies (exportp export)
           (and (consp export)
                (true-listp export)))
  :rule-classes :compound-recognizer)


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

(defthm export-acc{type-prescription}
  (implies (true-listp acc)
           (true-listp (export-acc set acc hash-table)))
  :rule-classes :type-prescription)

(defthm exportp-rec-of-export-acc
  (implies (exportp-rec acc)
           (exportp-rec (export-acc set acc hash-table))))

(defthm keys-of-export-acc
  (equal (omap::keys (export-acc set acc hash-table))
         (if (keysp set)
             (set::union set (omap::keys acc))
             (omap::keys acc)))
  :hints
  (("Goal"
    :in-theory (enable set::union))))

(defthm export-acc-of-keys-set
  (equal (export-acc %set acc (keys-set set hash-table))
         (export-acc %set acc hash-table)))

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
    :in-theory (enable set::in))))

(defthm export-acc-of-update-3
  (implies (and (not (set::in (key-fixer key) set)))
           (equal (export-acc set acc (updater/copyable key val hash-table))
                  (export-acc set acc hash-table)))
  :hints
  (("Goal"
    :in-theory (enable set::in))))

(local
  (defthm export-acc-of-insert-lemma
    (implies (and (set::in key set)
                  (key-recognizer key)
                  (keysp set))
             (equal (omap::update key
                                  (val-export (accessor/copyable key hash-table))
                                  (export-acc set acc hash-table))
                    (export-acc set acc hash-table)))))

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
                     (omap::update (key-fixer key)
                                   (val-export (accessor/copyable key hash-table))
                                   (export-acc set acc hash-table))))))
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
             (export-acc set acc hash-table)))))

(defthm size-of-export-acc
  (equal (omap::size (export-acc set acc hash-table))
         (if (keysp set)
             (set::cardinality (set::union set (omap::keys acc)))
             (omap::size acc)))
  :hints
  (("Goal"
    :in-theory (enable omap::size
                       set::cardinality
                       set::intersect
                       omap::assoc-to-in-of-keys))
   ("Subgoal 2"
    :induct (set::cardinality set))
   ("Subgoal *1/3"
    :expand (export-acc set acc hash-table))))

(defthm assoc-of-export-acc
  (equal (omap::assoc key (export-acc set acc hash-table))
         (if (and (keysp set)
                  (set::in key set))
             (cons key (val-export (accessor/copyable key hash-table)))
             (omap::assoc key acc))))

(local
  (in-theory
    (disable export-acc)))


;;;; `EXPORT'
(defun export (hash-table)
  (declare (xargs :guard (recognizer/copyable hash-table)))
  (cons (name)
        (export-acc (keys hash-table) () hash-table)))

(defthm export{type-prescription}
  (and (consp (export hash-table))
       (true-listp (export hash-table)))
  :rule-classes :type-prescription)

(defthm exportp-of-export
  (exportp (export hash-table)))

(defthm keys-of-export
  (equal (omap::keys (cdr (export hash-table)))
         (keys hash-table)))

(defthm size-of-export
  (implies (coupledp hash-table)
           (equal (omap::size (cdr (export hash-table)))
                  (count/copyable hash-table))))

(defthm assoc-of-export
  (implies (and (key-recognizer key)
                (coupledp hash-table))
           (equal (omap::assoc key (cdr (export hash-table)))
                  (and (boundp/copyable key hash-table)
                       (cons key (val-export (accessor/copyable key hash-table)))))))


;;;; `IMPORT-REC'
(defun import-rec (omap hash-table)
  (declare (xargs :guard (and (exportp-rec omap)
                              (recognizer/copyable hash-table))))
  (if (or (omap::emptyp omap)
          (not (exportp-rec omap)))
      (fixer/copyable hash-table)
      (mv-let (key val-export)
              (omap::head omap)
        (let* ((val (accessor/copyable key hash-table))
               (val (val-import val-export val))
               (hash-table (updater/copyable key val hash-table)))
          (import-rec (omap::tail omap) hash-table)))))

(defthm import-rec{type-prescription}
  (and (consp (import-rec omap hash-table))
       (true-listp (import-rec omap hash-table)))
  :rule-classes :type-prescription)

(defthm recognizer/copyable-of-import-rec
  (recognizer/copyable (import-rec omap hash-table)))

(defthm keys-of-import-rec
  (equal (keys (import-rec omap hash-table))
         (keys hash-table)))

(defthm import-rec-of-updater/copyable
  (implies (exportp-rec omap)
           (equal (import-rec omap (updater/copyable key val hash-table))
                  (if (omap::assoc (key-fixer key) omap)
                      (import-rec omap hash-table)
                      (updater/copyable key val (import-rec omap hash-table)))))
  ;; BUG: This proof fails without the following flag.
  :otf-flg t)

(defthm boundp/copyable-of-import-rec
  (implies (exportp-rec omap)
           (equal (boundp/copyable key (import-rec omap hash-table))
                  (and (or (boundp/copyable key hash-table)
                           (omap::assoc (key-fixer key) omap))
                       t))))

(defthm accessor/copyable-of-import-rec
  (implies (exportp-rec omap)
           (equal (accessor/copyable key (import-rec omap hash-table))
                  (let ((pair (omap::assoc (key-fixer key) omap)))
                    (if pair
                        (val-import (cdr pair) (default-val))
                        (accessor/copyable key hash-table))))))

(defthmd count/copyable-of-import-rec
  (implies (exportp-rec omap)
           (equal (count/copyable (import-rec omap hash-table))
                  (cond
                    ((omap::emptyp omap)
                     (count/copyable hash-table))
                    ((boundp/copyable (omap::head-key omap) hash-table)
                     (count/copyable (import-rec (omap::tail omap) hash-table)))
                    (t
                     (1+ (count/copyable (import-rec (omap::tail omap) hash-table))))))))

(local
  (in-theory
    (disable import-rec)))


;;;; `IMPORT'
(defun import (export hash-table)
  (declare (xargs :guard (and (exportp export)
                              (recognizer/copyable hash-table))))
  (if (exportp export)
      (let* ((omap (cdr export))
             (hash-table (clear/copyable hash-table))
             (hash-table (import-rec omap hash-table))
             (hash-table (keys-set (omap::keys omap) hash-table)))
        hash-table)
      (creator/copyable)))

(defthm import{type-prescription}
  (and (consp (import export hash-table))
       (true-listp (import export hash-table)))
  :rule-classes :type-prescription)

(defthm recognizer/copyable-of-import
  (recognizer/copyable (import export hash-table)))

(defthm import-when-not-exportp
  (implies (not (exportp export))
           (equal (import export hash-table)
                  (creator/copyable))))

(defthm import-ignores-hash-table
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
              (omap::keys (cdr export)))))

(defthm boundp/copyable-of-import
  (equal (boundp/copyable key (import export hash-table))
         (and (omap::assoc (key-fixer key) (cdr export))
              (exportp export))))

(defthm accessor/copyable-of-import
  (equal (accessor/copyable key (import export hash-table))
         (let ((pair (omap::assoc (key-fixer key) (cdr export))))
           (if (and (exportp export)
                    pair)
               (val-import (cdr pair) (default-val))
               (default-val)))))

(encapsulate ()
  (local
    (defthm count/copyable-of-import-lemma
      (implies (and (omap::mapp omap)
                    (all-keys-recognized-p omap)
                    (all-vals-exports-p omap))
               (equal (count/copyable (import-rec omap (creator/copyable)))
                      (omap::size omap)))
      :hints
      (("Goal"
        :in-theory (enable omap::size))
       ("Subgoal *1/5"
        :use ((:instance count/copyable-of-import-rec
                         (hash-table (creator/copyable)))))
       ("Subgoal *1/1"
        :use ((:instance count/copyable-of-import-rec
                         (hash-table (creator/copyable))))))))

  (defthm count/copyable-of-import
    (equal (count/copyable (import export hash-table))
           (if (exportp export)
               (omap::size (cdr export))
               0))))


;;;; `EXPORT' and `IMPORT' Composition Theorems
(local
  (defthm export-of-import-lemma
    (implies (and (omap::mapp omap)
                  (all-keys-recognized-p omap)
                  (all-vals-exports-p omap))
             (equal (export-acc (omap::keys omap)
                                nil
                                (import-rec omap
                                            (creator/copyable)))
                    omap))
    :hints
    (("Goal"
      :induct (omap::keys omap)
      :in-theory (enable omap::keys))
     ("Subgoal *1/2.3"
      :do-not-induct t
      :expand (import-rec omap (creator/copyable)))
     ("Subgoal *1/1"
      :expand (export-acc nil nil
                          (import-rec omap (creator/copyable)))))))

(defthm export-of-import
  (implies (exportp export)
           (equal (export (import export hash-table))
                  export))
  :hints
  (("Goal"
    :do-not-induct t
    :in-theory (disable cons-equal)
    :use ((:instance cons-equal
                     (x1 (name))
                     (y1 (export-acc (omap::keys (cdr export))
                                     nil
                                     (keys-set (omap::keys (cdr export))
                                               (import-rec (cdr export)
                                                           (creator/copyable)))))
                     (x2 (car export))
                     (y2 (cdr export)))))))

(defthm import-of-export
  (implies (coupledp %hash-table)
           (equal (import (export %hash-table) hash-table)
                  (fixer/copyable %hash-table)))
  :hints
  (("Goal"
    :in-theory (disable import
                        export)
    :use ((:instance equal/copyable
                     (%hash-table (import (export %hash-table) hash-table))
                     (hash-table (fixer/copyable %hash-table)))))))
