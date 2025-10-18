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


(in-package "DEFINE-HASH-TABLE")
(set-verify-guards-eagerness 2)

(include-book "total-order")
(include-book "omaps")

(deflabel define-hash-table-lemmas-begin)

(deftheory omap::primitives
  #!omap
  '(mapp emptyp mfix head tail update))

(deftheory omap::definitions
  #!omap
  '(assoc compatiblep delete delete* from-lists
    in* keys values lookup lookup* restrict
    rlookup rlookup* size submap update*))

(deftheory omap::aggressive
  #!omap
  '(delete-when-small
    delete-when-hit
    delete-when-not-assoc
    assoc-when-emptyp-of-delete
    size-0-iff-empty))

(in-theory
  (disable omap::aggressive))


;;;; `ATOMIC-STOBJ' Constraints
(encapsulate (((key-recognizer *) => *)
              ((key-fixer *) => *)
              ((key-default) => *)
              ((val-recognizer *) => *)
              ((val-fixer *) => *)
              ((val-default) => *)

              ((recognizer *) => *)
              ((creator) => *)
              ((fixer *) => *)
              ((accessor * *) => *)
              ((updater * * *) => *)
              ((boundp * *) => *)
              ((remover * *) => *)
              ((count *) => *))
  (local
    (defun key-recognizer (x)
      (declare (xargs :guard t)
               (ignorable x))
      t))

  (local
    (defun key-fixer (x)
      (declare (xargs :guard t))
      x))

  (local
    (defun key-default ()
      (declare (xargs :guard t))
      t))

  (defthm key-recognizer{type-prescription}
    (booleanp (key-recognizer x))
    :rule-classes :type-prescription)

  (defthm key-recognizer-of-default
    (key-recognizer (key-default)))

  (defthm key-recognizer-of-fixer
    (key-recognizer (key-fixer x)))

  (defthm key-fixer-when-recognizer
    (implies (key-recognizer x)
             (equal (key-fixer x) x)))

  (defthm key-fixer-when-not-recognizer
    (implies (not (key-recognizer x))
             (equal (key-fixer x) (key-default))))

  (local
    (defun val-recognizer (x)
      (declare (xargs :guard t)
               (ignorable x))
      t))

  (local
    (defun val-fixer (x)
      (declare (xargs :guard t))
      x))

  (local
    (defun val-default ()
      (declare (xargs :guard t))
      t))

  (defthm val-recognizer{type-prescription}
    (booleanp (val-recognizer x))
    :rule-classes :type-prescription)

  (defthm val-recognizer-of-default
    (val-recognizer (val-default)))

  (defthm val-recognizer-of-fixer
    (val-recognizer (val-fixer x)))

  (defthm val-fixer-when-recognizer
    (implies (val-recognizer x)
             (equal (val-fixer x) x)))

  (defthm val-fixer-when-not-recognizer
    (implies (not (val-recognizer x))
             (equal (val-fixer x) (val-default))))

  (local
    (defun recognizer (map)
      (declare (xargs :guard t))
      (if (consp map)
          (let ((a (car map))
                (d (cdr map)))
            (and (consp a)
                 (let ((key (car a))
                       (val (cdr a)))
                   (and (key-recognizer key)
                        (val-recognizer val)
                        (or (null d)
                            (and (consp d)
                                 (consp (car d))
                                 (<< key (caar d))
                                 (recognizer d)))))))
          (null map))))

  (defthm recognizer{definition}-0
    (equal (recognizer map)
           (if (consp map)
               (let ((a (car map))
                     (d (cdr map)))
                 (and (consp a)
                      (let ((key (car a))
                            (val (cdr a)))
                        (and (key-recognizer key)
                             (val-recognizer val)
                             (or (null d)
                                 (and (consp d)
                                      (consp (car d))
                                      (<< key (caar d))
                                      (recognizer d)))))))
               (null map)))
    :rule-classes :definition)

  (local
    (defun creator ()
      (declare (xargs :guard t))
      ()))

  (defthm recognizer-of-creator
    (recognizer (creator)))

  (defthm emptyp-of-creator
    (omap::emptyp (creator)))

  (local
    (defun fixer (map)
      (declare (xargs :guard t))
      (if (recognizer map)
          map
          (creator))))

  (defthm fixer{definition}-0
    (equal (fixer map)
           (if (recognizer map)
               map
               (creator)))
    :rule-classes :definition)

  (local
    (defun accessor (key map)
      (declare (xargs :guard t
                      :measure (len map)))
      (let ((key (key-fixer key))
            (map (fixer map)))
        (cond
          ((or (null map)
               (<< key (caar map)))
           (val-default))
          ((equal key (caar map))
           (val-fixer (cdar map)))
          (t
           (accessor key (cdr map)))))))

  (defthm accessor{definition}-0
    (equal (accessor key map)
           (let ((key (key-fixer key))
                 (map (fixer map)))
             (cond
               ((or (null map)
                    (<< key (caar map)))
                (val-default))
               ((equal key (caar map))
                (val-fixer (cdar map)))
               (t
                (accessor key (cdr map))))))
    :rule-classes :definition)

  (local
    (defun updater (key val map)
      (declare (xargs :guard t
                      :measure (len map)))
      (let ((key (key-fixer key))
            (val (val-fixer val))
            (map (fixer map)))
        (if (endp map)
            (list (cons key val))
            (let* ((a (car map))
                   (d (cdr map))
                   (k (car a)))
              (cond
                ((<< key k)
                 (cons (cons key val)
                       map))
                ((equal key k)
                 (cons (cons key val) d))
                (t
                 (cons a (updater key val d)))))))))

  (defthm updater{definition}-0
    (equal (updater key val map)
           (let ((key (key-fixer key))
                 (val (val-fixer val))
                 (map (fixer map)))
             (if (endp map)
                 (list (cons key val))
                 (let* ((a (car map))
                        (d (cdr map))
                        (k (car a)))
                   (cond
                     ((<< key k)
                      (cons (cons key val)
                            map))
                     ((equal key k)
                      (cons (cons key val) d))
                     (t
                      (cons a (updater key val d))))))))
    :rule-classes :definition)

  (local
    (defun boundp (key map)
      (declare (xargs :guard t
                      :measure (len map)))
      (let ((key (key-fixer key))
            (map (fixer map)))
        (cond
          ((or (null map)
               (<< key (caar map)))
           'nil)
          ((equal key (caar map))
           't)
          (t
           (boundp key (cdr map)))))))

  (defthm boundp{definition}-0
    (equal (boundp key map)
           (let ((key (key-fixer key))
                 (map (fixer map)))
             (cond
               ((or (null map)
                    (<< key (caar map)))
                'nil)
               ((equal key (caar map))
                't)
               (t
                (boundp key (cdr map))))))
    :rule-classes :definition)

  (local
    (defun remover (key map)
      (declare (xargs :guard t
                      :measure (len map)))
      (let ((key (key-fixer key))
            (map (fixer map)))
        (cond
          ((null map)
           '())
          ((<< key (caar map))
           map)
          ((equal key (caar map))
           (cdr map))
          (t
           (cons (car map)
                 (remover key (cdr map))))))))

  (defthm remover{definition}-0
    (equal (remover key map)
           (let ((key (key-fixer key))
                 (map (fixer map)))
             (cond
               ((null map)
                '())
               ((<< key (caar map))
                map)
               ((equal key (caar map))
                (cdr map))
               (t
                (cons (car map)
                      (remover key (cdr map)))))))
    :rule-classes :definition)

  (local
    (defun count (map)
      (declare (xargs :guard t))
      (len (fixer map))))

  (defthm count{definition}-0
    (equal (count map)
           (let ((map (fixer map)))
             (if (consp map)
                 (1+ (count (cdr map)))
                 0)))
    :rule-classes :definition))


;;;; `OMAP' Definitions
(encapsulate ()
  (local
    (in-theory
      (enable omap::definitions)))

  (defthm recognizer{definition}-1
    (equal (recognizer map)
           (and (omap::mapp map)
                (or (omap::emptyp map)
                    (mv-let (key val) (omap::head map)
                      (and (key-recognizer key)
                           (val-recognizer val)
                           (recognizer (omap::tail map)))))))
    :rule-classes
    ((:rewrite :corollary
               (implies (recognizer map)
                        (omap::mapp map)))
     (:rewrite :corollary
               (implies (and (recognizer map)
                             (not (omap::emptyp map)))
                        (key-recognizer (mv-nth 0 (omap::head map)))))
     (:rewrite :corollary
               (implies (and (recognizer map)
                             (not (omap::emptyp map)))
                        (val-recognizer (mv-nth 1 (omap::head map)))))
     (:rewrite :corollary
               (implies (and (recognizer map)
                             (not (omap::emptyp map)))
                        (recognizer (omap::tail map))))
     (:definition :controller-alist ((recognizer t))))
    :hints
    (("Goal"
      :in-theory (enable omap::primitives))))

  (defun recognizer{induction}-fn (map)
    (declare (xargs :guard (omap::mapp map)))
    (or (omap::emptyp map)
        (recognizer{induction}-fn (omap::tail map))))

  (defthm recognizer{induction}
    t
    :rule-classes
    ((:induction :pattern (recognizer map)
                 :scheme (recognizer{induction}-fn map))))

  (in-theory
    (disable recognizer{definition}-0))

  (local
    (defthm fixer-when-recognizer
      (implies (recognizer map)
               (equal (fixer map) map))))

  (local
    (defthm fixer-when-not-recognizer
      (implies (not (recognizer map))
               (equal (fixer map) (creator)))))

  (local
    (in-theory
      (disable fixer{definition}-0)))

  (defthm not-creator
    (not (creator))
    :hints
    (("Goal"
      :in-theory (e/d (omap::primitives)
                      (emptyp-of-creator))
      :use ((:instance emptyp-of-creator)))))

  (defthm accessor{definition}-1
    (equal (accessor key map)
           (let ((key (key-fixer key))
                 (map (fixer map)))
             (cond
               ((omap::emptyp map)
                (val-default))
               ((equal key (omap::head-key map))
                (val-fixer (omap::head-val map)))
               (t
                (accessor key (omap::tail map))))))
    :rule-classes
    ((:definition :controller-alist ((accessor nil t))))
    :hints
    (("Goal"
      :cases ((recognizer map))
      :expand ((accessor key map)))
     ("Subgoal 1"
      :in-theory (enable omap::primitives))))

  (defun accessor{induction}-fn (key map)
    (declare (xargs :guard (omap::mapp map)
                    :measure (omap::size map)))
    (let ((key (key-fixer key)))
      (or (omap::emptyp map)
          (equal key (omap::head-key map))
          (accessor{induction}-fn key (omap::tail map)))))

  (defthm accessor{induction}
    t
    :rule-classes
    ((:induction :pattern (accessor key map)
                 :scheme (accessor{induction}-fn key map))))

  (in-theory
    (disable accessor{definition}-0))

  (defthm updater{definition}-1
    (equal (updater key val map)
           (let ((key (key-fixer key))
                 (val (val-fixer val))
                 (map (fixer map)))
             (omap::update key val map)))
    :rule-classes :definition
    :hints
    (("Goal"
      :cases ((recognizer map))
      :expand (updater key val map))
     ("Subgoal 2"
      :in-theory (enable omap::primitives))
     ("Subgoal 1.4"
      :in-theory (enable omap::primitives))
     ("Subgoal 1.3"
      :in-theory (enable omap::primitives))
     ("Subgoal 1.2"
      :induct (len map))
     ("Subgoal 1.1"
      :in-theory (enable omap::primitives))
     ("Subgoal *1/5"
      :in-theory (enable omap::primitives))
     ("Subgoal *1/4"
      :in-theory (e/d (omap::primitives)
                      (key-recognizer-of-fixer))
      :use ((:instance key-recognizer-of-fixer
                       (x key))))
     ("Subgoal *1/3"
      :in-theory (enable omap::primitives))
     ("Subgoal *1/2"
      :in-theory (enable omap::primitives))
     ("Subgoal *1/1"
      :in-theory (enable omap::primitives))))

  (in-theory
    (disable updater{definition}-0))

  (defthm boundp{definition}-1
    (equal (boundp key map)
           (let ((key (key-fixer key))
                 (map (fixer map)))
             (and (omap::assoc key map)
                  t)))
    :rule-classes :definition
    :hints
    (("Goal"
      :cases ((recognizer map))
      :expand (boundp key map))
     ("Subgoal 1.5"
      :in-theory (e/d (omap::primitives)
                      (omap::assoc-of-head))
      :use ((:instance omap::assoc-of-head
                       (map map))))
     ("Subgoal 1.4"
      :induct (len map))
     ("Subgoal 1.2"
      :in-theory (e/d (omap::primitives)
                      (omap::head-key-minimal))
      :use ((:instance omap::head-key-minimal
                       (key (key-fixer key))
                       (map map))))
     ("Subgoal 1.1"
      :induct (len map))
     ("Subgoal *2/5"
      :expand (omap::assoc (key-fixer key)
                           map))
     ("Subgoal *2/4"
      :do-not-induct t
      :in-theory (enable omap::primitives)
      :expand ((boundp (key-fixer key)
                       (cdr map))))
     ("Subgoal *2/3"
      :do-not-induct t
      :in-theory (enable omap::primitives)
      :expand (omap::assoc (key-fixer key)
                           map))
     ("Subgoal *2/2"
      :do-not-induct t
      :in-theory (enable omap::primitives)
      :expand (omap::assoc (key-fixer key)
                           map))
     ("Subgoal *2/1"
      :do-not-induct t
      :in-theory (enable omap::primitives)
      :expand (omap::assoc (key-fixer key)
                           map))
     ("Subgoal *1/5"
      :do-not-induct t
      :in-theory (enable omap::primitives)
      :expand (boundp (key-fixer key)
                      (cdr map)))
     ("Subgoal *1/4"
      :do-not-induct t
      :in-theory (enable omap::primitives)
      :expand (boundp (key-fixer key)
                      (cdr map)))
     ("Subgoal *1/3"
      :do-not-induct t
      :in-theory (enable omap::primitives)
      :expand (boundp (key-fixer key)
                      (cdr map)))))

  (in-theory
    (disable boundp{definition}-0))

  (local
    (defthm remover{definition}-1/lemma-0
      (omap::mapp (remover key map))
      :hints
      (("Goal"
        :cases ((recognizer map)))
       ("Subgoal 1"
        :induct (omap::mapp map)
        :in-theory (enable (:i omap::mapp))
        :expand (recognizer map))
       ("Subgoal *1/8"
        :expand (omap::mapp map))
       ("Subgoal *1/6"
        :expand (omap::mapp map))
       ("Subgoal *1/5"
        :expand (omap::mapp map))
       ("Subgoal *1/4"
        :do-not-induct t
        :in-theory (enable omap::primitives)
        :expand (remover key map))
       ("Subgoal *1/3"
        :do-not-induct t
        :in-theory (enable omap::primitives))
       ("Subgoal *1/2"
        :do-not-induct t
        :in-theory (enable omap::primitives)
        :expand (remover key map))
       ("Subgoal *1/1"
        :do-not-induct t
        :in-theory (enable omap::primitives)
        :expand (remover key map)))))

  (defthm remover{definition}-1
    (equal (remover key map)
           (let ((key (key-fixer key))
                 (map (fixer map)))
             (omap::delete key map)))
    :rule-classes :definition
    :hints
    (("Goal"
      :cases ((recognizer map))
      :expand (remover key map))
     ("Subgoal 1.3"
      :do-not-induct t
      :expand (omap::delete (key-fixer key)
                            map))
     ("Subgoal 1.3.2"
      :in-theory (enable omap::primitives))
     ("Subgoal 1.3.1"
      :do-not-induct t
      :in-theory (enable omap::primitives)
      :use ((:instance omap::delete-when-small
                       (key (key-fixer key))
                       (map map))))
     ("Subgoal 1.2"
      :induct (len map))
     ("Subgoal 1.1"
      :do-not-induct t
      :in-theory (enable omap::primitives)
      :expand (omap::delete (key-fixer key)
                            map))
     ("Subgoal *1/6"
      :do-not-induct t
      :in-theory (enable omap::primitives)
      :expand (omap::delete (key-fixer key)
                            map))
     ("Subgoal *1/5"
      :do-not-induct t
      :in-theory (enable omap::primitives))
     ("Subgoal *1/4"
      :do-not-induct t
      :in-theory (enable omap::primitives))
     ("Subgoal *1/3"
      :do-not-induct t
      :in-theory (e/d (omap::primitives)
                      (omap::delete-when-small))
      :use ((:instance omap::delete-when-small
                       (key (key-fixer key))
                       (map (cdr map))))
      :expand (omap::delete (key-fixer key)
                            map))
     ("Subgoal *1/2"
      :do-not-induct t
      :in-theory (enable omap::primitives)
      :expand (omap::delete (key-fixer key)
                            map))
     ("Subgoal *1/1"
      :do-not-induct t
      :in-theory (enable omap::primitives))))

  (in-theory
    (disable remover{definition}-0))

  (defthm count{definition}-1
    (equal (count map)
           (let ((map (fixer map)))
             (omap::size map)))
    :rule-classes :definition
    :hints
    (("Goal"
      :cases ((recognizer map)))
     ("Subgoal 1"
      :induct (omap::size map)
      :in-theory (enable omap::primitives))))

  (in-theory
    (disable count{definition}-0)))


;;;; `OMAP' Identifiers
(encapsulate (((hash-table) => *)
              ((%hash-table) => *)
              ((key) => *)
              ((%key) => *)
              ((val) => *)
              ((%val) => *))
  (local
    (defun hash-table ()
      (declare (xargs :guard t))
      t))

  (local
    (defun %hash-table ()
      (declare (xargs :guard t))
      t))

  (local
    (defun key ()
      (declare (xargs :guard t))
      t))

  (local
    (defun %key ()
      (declare (xargs :guard t))
      t))

  (local
    (defun val ()
      (declare (xargs :guard t))
      t))

  (local
    (defun %val ()
      (declare (xargs :guard t))
      t)))


;;;; Theorems
(defthm recognizer-of-creator
  (recognizer (creator)))

(local
  (defthm recognizer-of-fixer/lemma
    (recognizer (fixer hash-table))))

(defthm recognizer-of-fixer
  (recognizer (fixer (hash-table)))
  :hints
  (("Goal"
    :by (:instance recognizer-of-fixer/lemma
                   (hash-table (hash-table))))))

(local
  (defthm fixer-when-recognizer/lemma
    (implies (recognizer hash-table)
             (equal (fixer hash-table) hash-table))))

(defthm fixer-when-recognizer
  (implies (recognizer (hash-table))
           (equal (fixer (hash-table)) (hash-table)))
  :hints
  (("Goal"
    :by (:instance fixer-when-recognizer/lemma
                   (hash-table (hash-table))))))

(local
  (defthm fixer-when-not-recognizer/lemma
    (implies (not (recognizer hash-table))
             (equal (fixer hash-table) (creator)))))

(defthm fixer-when-not-recognizer
  (implies (not (recognizer (hash-table)))
           (equal (fixer (hash-table)) (creator)))
  :hints
  (("Goal"
    :by (:instance fixer-when-not-recognizer/lemma
                   (hash-table (hash-table))))))

(local
  (defthm val-recognizer-of-accessor/lemma
    (val-recognizer (accessor key hash-table))))

(defthm val-recognizer-of-accessor
  (val-recognizer (accessor (key) (hash-table)))
  :hints
  (("Goal"
    :by (:instance val-recognizer-of-accessor/lemma
                   (key (key))
                   (hash-table (hash-table))))))

(local
  (defthm accessor-of-key-fixer/lemma
    (equal (accessor (key-fixer key) hash-table)
           (accessor key hash-table))))

(defthm accessor-of-key-fixer
  (equal (accessor (key-fixer (key)) (hash-table))
         (accessor (key) (hash-table)))
  :hints
  (("Goal"
    :by (:instance accessor-of-key-fixer/lemma
                   (key (key))
                   (hash-table (hash-table))))))

(local
  (defthm accessor-of-fixer/lemma
    (equal (accessor key (fixer hash-table))
           (accessor key hash-table))))

(defthm accessor-of-fixer
  (equal (accessor (key) (fixer (hash-table)))
         (accessor (key) (hash-table)))
  :hints
  (("Goal"
    :by (:instance accessor-of-fixer/lemma
                   (key (key))
                   (hash-table (hash-table))))))

(local
  (defthm accessor-when-not-key-recognizer/lemma
    (implies (not (key-recognizer key))
             (equal (accessor key hash-table)
                    (accessor (key-default) hash-table)))))

(defthm accessor-when-not-key-recognizer
  (implies (not (key-recognizer (key)))
           (equal (accessor (key) (hash-table))
                  (accessor (key-default) (hash-table))))
  :hints
  (("Goal"
    :by (:instance accessor-when-not-key-recognizer/lemma
                   (key (key))
                   (hash-table (hash-table))))))

(local
  (defthm recognizer-of-update
    (implies (and (recognizer hash-table)
                  (key-recognizer key)
                  (val-recognizer val))
             (recognizer (omap::update key val hash-table)))
    :hints
    (("Goal"
      :induct (accessor key hash-table))
     ("Subgoal *1/3"
      :do-not-induct t
      :expand (recognizer (omap::update key val hash-table))))))

(local
  (defthm recognizer-of-updater/lemma
    (recognizer (updater key val hash-table))))

(defthm recognizer-of-updater
  (recognizer (updater (key) (val) (hash-table)))
  :hints
  (("Goal"
    :by (:instance recognizer-of-updater/lemma
                   (key (key))
                   (val (val))
                   (hash-table (hash-table))))))

(local
  (defthm updater-of-key-fixer/lemma
    (equal (updater (key-fixer key) val hash-table)
           (updater key val hash-table))))

(defthm updater-of-key-fixer
  (equal (updater (key-fixer (key)) (val) (hash-table))
         (updater (key) (val) (hash-table)))
  :hints
  (("Goal"
    :by (:instance updater-of-key-fixer/lemma
                   (key (key))
                   (val (val))
                   (hash-table (hash-table))))))

(local
  (defthm updater-of-val-fixer/lemma
    (equal (updater key (val-fixer val) hash-table)
           (updater key val hash-table))))

(defthm updater-of-val-fixer
  (equal (updater (key) (val-fixer (val)) (hash-table))
         (updater (key) (val) (hash-table)))
  :hints
  (("Goal"
    :by (:instance updater-of-val-fixer/lemma
                   (key (key))
                   (val (val))
                   (hash-table (hash-table))))))

(local
  (defthm updater-of-fixer/lemma
    (equal (updater key val (fixer hash-table))
           (updater key val hash-table))))

(defthm updater-of-fixer
  (equal (updater (key) (val) (fixer (hash-table)))
         (updater (key) (val) (hash-table)))
  :hints
  (("Goal"
    :by (:instance updater-of-fixer/lemma
                   (key (key))
                   (val (val))
                   (hash-table (hash-table))))))

(local
  (defthm updater-when-not-key-recognizer/lemma
    (implies (not (key-recognizer key))
             (equal (updater key val hash-table)
                    (updater (key-default) val hash-table)))))

(defthm updater-when-not-key-recognizer
  (implies (not (key-recognizer (key)))
           (equal (updater (key) (val) (hash-table))
                  (updater (key-default) (val) (hash-table))))
  :hints
  (("Goal"
    :by (:instance updater-when-not-key-recognizer/lemma
                   (key (key))
                   (val (val))
                   (hash-table (hash-table))))))

(local
  (defthm updater-when-not-val-recognizer/lemma
    (implies (not (val-recognizer val))
             (equal (updater key val hash-table)
                    (updater key (val-default) hash-table)))))

(defthm updater-when-not-val-recognizer
  (implies (not (val-recognizer (val)))
           (equal (updater (key) (val) (hash-table))
                  (updater (key) (val-default) (hash-table))))
  :hints
  (("Goal"
    :by (:instance updater-when-not-val-recognizer/lemma
                   (key (key))
                   (val (val))
                   (hash-table (hash-table))))))

(local
  (defthm boundp-of-key-fixer/lemma
    (equal (boundp (key-fixer key) hash-table)
           (boundp key hash-table))))

(defthm boundp-of-key-fixer
  (equal (boundp (key-fixer (key)) (hash-table))
         (boundp (key) (hash-table)))
  :hints
  (("Goal"
    :by (:instance boundp-of-key-fixer/lemma
                   (key (key))
                   (hash-table (hash-table))))))

(local
  (defthm boundp-of-fixer/lemma
    (equal (boundp key (fixer hash-table))
           (boundp key hash-table))))

(defthm boundp-of-fixer
  (equal (boundp (key) (fixer (hash-table)))
         (boundp (key) (hash-table)))
  :hints
  (("Goal"
    :by (:instance boundp-of-fixer/lemma
                   (key (key))
                   (hash-table (hash-table))))))

(local
  (defthm boundp-when-not-key-recognizer/lemma
    (implies (not (key-recognizer key))
             (equal (boundp key hash-table)
                    (boundp (key-default) hash-table)))))

(defthm boundp-when-not-key-recognizer
  (implies (not (key-recognizer (key)))
           (equal (boundp (key) (hash-table))
                  (boundp (key-default) (hash-table))))
  :hints
  (("Goal"
    :by (:instance boundp-when-not-key-recognizer/lemma
                   (key (key))
                   (hash-table (hash-table))))))

(local
  (defthm recognizer-of-delete
    (implies (and (recognizer hash-table)
                  (key-recognizer key))
             (recognizer (omap::delete key hash-table)))
    :hints
    (("Goal"
      :induct (accessor key hash-table))
     ("Subgoal *1/2"
      :do-not-induct t
      :in-theory (enable omap::definitions)
      :expand (recognizer (omap::delete key hash-table))))))

(local
  (defthm recognizer-of-remover/lemma
    (recognizer (remover key hash-table))))

(defthm recognizer-of-remover
  (recognizer (remover (key) (hash-table)))
  :hints
  (("Goal"
    :by (:instance recognizer-of-remover/lemma
                   (key (key))
                   (hash-table (hash-table))))))

(local
  (defthm remover-of-key-fixer/lemma
    (equal (remover (key-fixer key) hash-table)
           (remover key hash-table))))

(defthm remover-of-key-fixer
  (equal (remover (key-fixer (key)) (hash-table))
         (remover (key) (hash-table)))
  :hints
  (("Goal"
    :by (:instance remover-of-key-fixer/lemma
                   (key (key))
                   (hash-table (hash-table))))))

(local
  (defthm remover-of-fixer/lemma
    (equal (remover key (fixer hash-table))
           (remover key hash-table))))

(defthm remover-of-fixer
  (equal (remover (key) (fixer (hash-table)))
         (remover (key) (hash-table)))
  :hints
  (("Goal"
    :by (:instance remover-of-fixer/lemma
                   (key (key))
                   (hash-table (hash-table))))))

(local
  (defthm remover-when-not-key-recognizer/lemma
    (implies (not (key-recognizer key))
             (equal (remover key hash-table)
                    (remover (key-default) hash-table)))))

(defthm remover-when-not-key-recognizer
  (implies (not (key-recognizer (key)))
           (equal (remover (key) (hash-table))
                  (remover (key-default) (hash-table))))
  :hints
  (("Goal"
    :by (:instance remover-when-not-key-recognizer/lemma
                   (key (key))
                   (hash-table (hash-table))))))

(defthm count{type-prescription}
  (and (integerp (count hash-table))
       (<= 0 (count hash-table))
       (implies (and (recognizer hash-table)
                     (not (omap::emptyp hash-table)))
                (< 0 (count hash-table))))
  :rule-classes
  ((:type-prescription :corollary
                       (and (integerp (count hash-table))
                            (<= 0 (count hash-table))))
   (:type-prescription :corollary
                       (implies (and (recognizer hash-table)
                                     (not (omap::emptyp hash-table)))
                                (and (integerp (count hash-table))
                                     (< 0 (count hash-table))))))
  :hints
  (("Goal"
    :expand (recognizer hash-table))))

(local
  (defthm count-of-fixer/lemma
    (equal (count (fixer hash-table))
           (count hash-table))))

(defthm count-of-fixer
  (equal (count (fixer (hash-table)))
         (count (hash-table)))
  :hints
  (("Goal"
    :by (:instance count-of-fixer/lemma
                   (hash-table (hash-table))))))

(local
  (defthm accessor-of-creator/lemma
    (equal (accessor key (creator)) (val-default))))

(defthm accessor-of-creator
  (equal (accessor (key) (creator)) (val-default))
  :hints
  (("Goal"
    :by (:instance accessor-of-creator/lemma
                   (key (key))))))

(local
  (defthm boundp-of-creator/lemma
    (not (boundp key (creator)))))

(defthm boundp-of-creator
  (not (boundp (key) (creator)))
  :hints
  (("Goal"
    :by (:instance boundp-of-creator/lemma
                   (key (key))))))

(local
  (defthm remover-of-creator/lemma
    (equal (remover key (creator)) (creator))))

(defthm remover-of-creator
  (equal (remover (key) (creator)) (creator))
  :hints
  (("Goal"
    :by (:instance remover-of-creator/lemma
                   (key (key))))))

(defthm count-of-creator
  (equal (count (creator)) 0))

(local
  (defthm count-of-updater-when-boundp/lemma
    (implies (boundp key hash-table)
             (equal (count (updater key val hash-table))
                    (count hash-table)))))

(defthm count-of-updater-when-boundp
  (implies (boundp (key) (hash-table))
           (equal (count (updater (key) (val) (hash-table)))
                  (count (hash-table))))
  :hints
  (("Goal"
    :by (:instance count-of-updater-when-boundp/lemma
                   (key (key))
                   (val (val))
                   (hash-table (hash-table))))))

(local
  (defthm count-of-updater-when-not-boundp/lemma
    (implies (not (boundp key hash-table))
             (equal (count (updater key val hash-table))
                    (1+ (count hash-table))))))

(defthm count-of-updater-when-not-boundp
  (implies (not (boundp (key) (hash-table)))
           (equal (count (updater (key) (val) (hash-table)))
                  (1+ (count (hash-table)))))
  :hints
  (("Goal"
    :by (:instance count-of-updater-when-not-boundp/lemma
                   (key (key))
                   (val (val))
                   (hash-table (hash-table))))))

(local
  (defthm count-of-updater/lemma
    (equal (count (updater key val hash-table))
           (if (boundp key hash-table)
               (count hash-table)
               (1+ (count hash-table))))))

(defthm count-of-updater
  (equal (count (updater (key) (val) (hash-table)))
         (if (boundp (key) (hash-table))
             (count (hash-table))
             (1+ (count (hash-table)))))
  :hints
  (("Goal"
    :by (:instance count-of-updater/lemma
                   (key (key))
                   (val (val))
                   (hash-table (hash-table))))))

(local
  (defthm count-of-remover-when-boundp/lemma
    (implies (boundp key hash-table)
             (equal (count (remover key hash-table))
                    (1- (count hash-table))))))

(defthm count-of-remover-when-boundp
  (implies (boundp (key) (hash-table))
           (equal (count (remover (key) (hash-table)))
                  (1- (count (hash-table)))))
  :hints
  (("Goal"
    :by (:instance count-of-remover-when-boundp/lemma
                   (key (key))
                   (hash-table (hash-table))))))

(local
  (defthm count-of-remover-when-not-boundp/lemma
    (implies (not (boundp key hash-table))
             (equal (count (remover key hash-table))
                    (count hash-table)))))

(defthm count-of-remover-when-not-boundp
  (implies (not (boundp (key) (hash-table)))
           (equal (count (remover (key) (hash-table)))
                  (count (hash-table))))
  :hints
  (("Goal"
    :by (:instance count-of-remover-when-not-boundp/lemma
                   (key (key))
                   (hash-table (hash-table))))))

(local
  (defthm count-of-remover/lemma
    (equal (count (remover key hash-table))
           (if (boundp key hash-table)
               (1- (count hash-table))
               (count hash-table)))))

(defthm count-of-remover
  (equal (count (remover (key) (hash-table)))
         (if (boundp (key) (hash-table))
             (1- (count (hash-table)))
             (count (hash-table))))
  :hints
  (("Goal"
    :by (:instance count-of-remover/lemma
                   (key (key))
                   (hash-table (hash-table))))))

(local
  (defthm accessor-of-update-same
    (implies (and (recognizer hash-table)
                  (val-recognizer val))
             (equal (accessor key (omap::update (key-fixer key) val hash-table))
                    val))
    :hints
    (("Goal"
      :induct (accessor key hash-table))
     ("Subgoal *1/3"
      :do-not-induct t
      :expand (accessor key (omap::update (key-fixer key) val hash-table))))))

(local
  (defthm accessor-of-updater-same/lemma
    (implies (equal (key-fixer key) (key-fixer %key))
             (equal (accessor key (updater %key val hash-table))
                    (val-fixer val)))))

(defthm accessor-of-updater-same
  (implies (equal (key-fixer (key)) (key-fixer (%key)))
           (equal (accessor (key) (updater (%key) (val) (hash-table)))
                  (val-fixer (val))))
  :hints
  (("Goal"
    :by (:instance accessor-of-updater-same/lemma
                   (key (key))
                   (%key (%key))
                   (val (val))
                   (hash-table (hash-table))))))

(local
  (defthm accessor-of-update-diff
    (implies (and (recognizer hash-table)
                  (key-recognizer %key)
                  (val-recognizer val)
                  (not (equal (key-fixer key) %key)))
             (equal (accessor key (omap::update %key val hash-table))
                    (accessor key hash-table)))
    :hints
    (("Goal"
      :induct (accessor key hash-table))
     ("Subgoal *1/3"
      :do-not-induct t
      :expand (accessor key (omap::update %key val hash-table)))
     ("Subgoal *1/2"
      :do-not-induct t
      :expand (accessor key (omap::update %key val hash-table))))))

(local
  (defthm accessor-of-updater-diff/lemma
    (implies (not (equal (key-fixer key) (key-fixer %key)))
             (equal (accessor key (updater %key val hash-table))
                    (accessor key hash-table)))))

(defthm accessor-of-updater-diff
  (implies (not (equal (key-fixer (key)) (key-fixer (%key))))
           (equal (accessor (key) (updater (%key) (val) (hash-table)))
                  (accessor (key) (hash-table))))
  :hints
  (("Goal"
    :by (:instance accessor-of-updater-diff/lemma
                   (key (key))
                   (%key (%key))
                   (val (val))
                   (hash-table (hash-table))))))

(local
  (defthm accessor-of-updater/lemma
    (equal (accessor key (updater %key val hash-table))
           (if (equal (key-fixer key) (key-fixer %key))
               (val-fixer val)
               (accessor key hash-table)))))

(defthm accessor-of-updater
  (equal (accessor (key) (updater (%key) (val) (hash-table)))
         (if (equal (key-fixer (key)) (key-fixer (%key)))
             (val-fixer (val))
             (accessor (key) (hash-table))))
  :hints
  (("Goal"
    :by (:instance accessor-of-updater/lemma
                   (key (key))
                   (%key (%key))
                   (val (val))
                   (hash-table (hash-table))))))

(local
  (defthm accessor-when-not-boundp/lemma
    (implies (not (boundp key hash-table))
             (equal (accessor key hash-table)
                    (val-default)))))

(defthm accessor-when-not-boundp
  (implies (not (boundp (key) (hash-table)))
           (equal (accessor (key) (hash-table))
                  (val-default)))
  :hints
  (("Goal"
    :by (:instance accessor-when-not-boundp/lemma
                   (key (key))
                   (hash-table (hash-table))))))

(local
  (defthm accessor-of-remover-same/lemma
    (implies (equal (key-fixer key) (key-fixer %key))
             (equal (accessor key (remover %key hash-table))
                    (val-default)))))

(defthm accessor-of-remover-same
  (implies (equal (key-fixer (key)) (key-fixer (%key)))
           (equal (accessor (key) (remover (%key) (hash-table)))
                  (val-default)))
  :hints
  (("Goal"
    :by (:instance accessor-of-remover-same/lemma
                   (key (key))
                   (%key (%key))
                   (hash-table (hash-table))))))

(local
  (defthm accessor-of-delete-diff
    (implies (and (not (equal (key-fixer key) %key))
                  (recognizer hash-table)
                  (key-recognizer %key))
             (equal (accessor key (omap::delete %key hash-table))
                    (accessor key hash-table)))
    :hints
    (("Goal"
      :induct (accessor key hash-table))
     ("Subgoal *1/3"
      :do-not-induct t
      :in-theory (enable omap::definitions)))))

(local
  (defthm accessor-of-remover-diff/lemma
    (implies (not (equal (key-fixer key) (key-fixer %key)))
             (equal (accessor key (remover %key hash-table))
                    (accessor key hash-table)))
    :hints
    (("Goal"
      :induct (accessor key hash-table))
     ("Subgoal *1/3"
      :do-not-induct t
      :in-theory (enable omap::definitions)))))

(defthm accessor-of-remover-diff
  (implies (not (equal (key-fixer (key)) (key-fixer (%key))))
           (equal (accessor (key) (remover (%key) (hash-table)))
                  (accessor (key) (hash-table))))
  :hints
  (("Goal"
    :by (:instance accessor-of-remover-diff/lemma
                   (key (key))
                   (%key (%key))
                   (hash-table (hash-table))))))

(local
  (defthm accessor-of-remover/lemma
    (equal (accessor key (remover %key hash-table))
           (if (equal (key-fixer key) (key-fixer %key))
               (val-default)
               (accessor key hash-table)))))

(defthm accessor-of-remover
  (equal (accessor (key) (remover (%key) (hash-table)))
         (if (equal (key-fixer (key)) (key-fixer (%key)))
             (val-default)
             (accessor (key) (hash-table))))
  :hints
  (("Goal"
    :by (:instance accessor-of-remover/lemma
                   (key (key))
                   (%key (%key))
                   (hash-table (hash-table))))))

(local
  (defthm updater-of-accessor-when-boundp/lemma
    (implies (and (equal (key-fixer key) (key-fixer %key))
                  (boundp key hash-table))
             (equal (updater key (accessor %key hash-table) hash-table)
                    (fixer hash-table)))))

(defthm updater-of-accessor-when-boundp
  (implies (and (equal (key-fixer (key)) (key-fixer (%key)))
                (boundp (key) (hash-table)))
           (equal (updater (key) (accessor (%key) (hash-table)) (hash-table))
                  (fixer (hash-table))))
  :hints
  (("Goal"
    :by (:instance updater-of-accessor-when-boundp/lemma
                   (key (key))
                   (%key (%key))
                   (hash-table (hash-table))))))

(local
  (defthm updater-of-accessor-when-not-boundp/lemma
    (implies (and (equal (key-fixer key) (key-fixer %key))
                  (not (boundp key hash-table)))
             (equal (updater key (accessor %key hash-table) hash-table)
                    (updater key (val-default) hash-table)))))

(defthm updater-of-accessor-when-not-boundp
  (implies (and (equal (key-fixer (key)) (key-fixer (%key)))
                (not (boundp (key) (hash-table))))
           (equal (updater (key) (accessor (%key) (hash-table)) (hash-table))
                  (updater (key) (val-default) (hash-table))))
  :hints
  (("Goal"
    :by (:instance updater-of-accessor-when-not-boundp/lemma
                   (key (key))
                   (%key (%key))
                   (hash-table (hash-table))))))

(local
  (defthm updater-of-accessor/lemma
    (implies (equal (key-fixer key) (key-fixer %key))
             (equal (updater key (accessor %key hash-table) hash-table)
                    (if (boundp key hash-table)
                        (fixer hash-table)
                        (updater key (val-default) hash-table))))))

(defthm updater-of-accessor
  (implies (equal (key-fixer (key)) (key-fixer (%key)))
           (equal (updater (key) (accessor (%key) (hash-table)) (hash-table))
                  (if (boundp (key) (hash-table))
                      (fixer (hash-table))
                      (updater (key) (val-default) (hash-table)))))
  :hints
  (("Goal"
    :by (:instance updater-of-accessor/lemma
                   (key (key))
                   (%key (%key))
                   (hash-table (hash-table))))))

(local
  (defthm updater-of-updater-same/lemma
    (implies (equal (key-fixer key) (key-fixer %key))
             (equal (updater key val (updater %key %val hash-table))
                    (updater key val hash-table)))))

(defthm updater-of-updater-same
  (implies (equal (key-fixer (key)) (key-fixer (%key)))
           (equal (updater (key) (val) (updater (%key) (%val) (hash-table)))
                  (updater (key) (val) (hash-table))))
  :hints
  (("Goal"
    :by (:instance updater-of-updater-same/lemma
                   (key (key))
                   (%key (%key))
                   (val (val))
                   (%val (%val))
                   (hash-table (hash-table))))))

(local
  (defthm updater-of-updater-diff/lemma
    (implies (not (equal (key-fixer key) (key-fixer %key)))
             (equal (updater key val (updater %key %val hash-table))
                    (updater %key %val (updater key val hash-table))))
    :rule-classes
    ((:rewrite :loop-stopper ((key %key updater))))))

(defthm updater-of-updater-diff
  (implies (not (equal (key-fixer (key)) (key-fixer (%key))))
           (equal (updater (key) (val) (updater (%key) (%val) (hash-table)))
                  (updater (%key) (%val) (updater (key) (val) (hash-table)))))
  :hints
  (("Goal"
    :by (:instance updater-of-updater-diff/lemma
                   (key (key))
                   (%key (%key))
                   (val (val))
                   (%val (%val))
                   (hash-table (hash-table))))))

(local
  (defthm updater-of-updater/lemma
    (equal (updater key val (updater %key %val hash-table))
           (if (equal (key-fixer key) (key-fixer %key))
               (updater key val hash-table)
               (updater %key %val (updater key val hash-table))))
    :rule-classes
    ((:rewrite :loop-stopper ((key %key updater))))))

(defthm updater-of-updater
  (equal (updater (key) (val) (updater (%key) (%val) (hash-table)))
         (if (equal (key-fixer (key)) (key-fixer (%key)))
             (updater (key) (val) (hash-table))
             (updater (%key) (%val) (updater (key) (val) (hash-table)))))
  :hints
  (("Goal"
    :by (:instance updater-of-updater/lemma
                   (key (key))
                   (%key (%key))
                   (val (val))
                   (%val (%val))
                   (hash-table (hash-table))))))

(local
  (defthm updater-of-remover/lemma
    (implies (equal (key-fixer key) (key-fixer %key))
             (equal (updater key val (remover %key hash-table))
                    (updater key val hash-table)))))

(defthm updater-of-remover
  (implies (equal (key-fixer (key)) (key-fixer (%key)))
           (equal (updater (key) (val) (remover (%key) (hash-table)))
                  (updater (key) (val) (hash-table))))
  :hints
  (("Goal"
    :by (:instance updater-of-remover/lemma
                   (key (key))
                   (%key (%key))
                   (val (val))
                   (hash-table (hash-table))))))

(local
  (defthm boundp-of-updater-same/lemma
    (implies (equal (key-fixer key) (key-fixer %key))
             (equal (boundp key (updater %key val hash-table))
                    t))))

(defthm boundp-of-updater-same
  (implies (equal (key-fixer (key)) (key-fixer (%key)))
           (equal (boundp (key) (updater (%key) (val) (hash-table)))
                  t))
  :hints
  (("Goal"
    :by (:instance boundp-of-updater-same/lemma
                   (key (key))
                   (%key (%key))
                   (val (val))
                   (hash-table (hash-table))))))

(local
  (defthm boundp-of-updater-diff/lemma
    (implies (not (equal (key-fixer key) (key-fixer %key)))
             (equal (boundp key (updater %key val hash-table))
                    (boundp key hash-table)))))

(defthm boundp-of-updater-diff
  (implies (not (equal (key-fixer (key)) (key-fixer (%key))))
           (equal (boundp (key) (updater (%key) (val) (hash-table)))
                  (boundp (key) (hash-table))))
  :hints
  (("Goal"
    :by (:instance boundp-of-updater-diff/lemma
                   (key (key))
                   (%key (%key))
                   (val (val))
                   (hash-table (hash-table))))))

(local
  (defthm boundp-of-updater/lemma
    (equal (boundp key (updater %key val hash-table))
           (or (equal (key-fixer key) (key-fixer %key))
               (boundp key hash-table)))))

(defthm boundp-of-updater
  (equal (boundp (key) (updater (%key) (val) (hash-table)))
         (or (equal (key-fixer (key)) (key-fixer (%key)))
             (boundp (key) (hash-table))))
  :hints
  (("Goal"
    :by (:instance boundp-of-updater/lemma
                   (key (key))
                   (%key (%key))
                   (val (val))
                   (hash-table (hash-table))))))

(local
  (defthm boundp-of-remover-same/lemma
    (implies (equal (key-fixer key) (key-fixer %key))
             (not (boundp key (remover %key hash-table))))))

(defthm boundp-of-remover-same
  (implies (equal (key-fixer (key)) (key-fixer (%key)))
           (not (boundp (key) (remover (%key) (hash-table)))))
  :hints
  (("Goal"
    :by (:instance boundp-of-remover-same/lemma
                   (key (key))
                   (%key (%key))
                   (hash-table (hash-table))))))

(local
  (defthm boundp-of-remover-diff/lemma
    (implies (not (equal (key-fixer key) (key-fixer %key)))
             (equal (boundp key (remover %key hash-table))
                    (boundp key hash-table)))))

(defthm boundp-of-remover-diff
  (implies (not (equal (key-fixer (key)) (key-fixer (%key))))
           (equal (boundp (key) (remover (%key) (hash-table)))
                  (boundp (key) (hash-table))))
  :hints
  (("Goal"
    :by (:instance boundp-of-remover-diff/lemma
                   (key (key))
                   (%key (%key))
                   (hash-table (hash-table))))))

(local
  (defthm boundp-of-remover/lemma
    (equal (boundp key (remover %key hash-table))
           (and (not (equal (key-fixer key) (key-fixer %key)))
                (boundp key hash-table)))
    :hints
    (("Goal"
      :use ((:instance boundp-of-remover-same/lemma)
            (:instance boundp-of-remover-diff/lemma))))))

(defthm boundp-of-remover
  (equal (boundp (key) (remover (%key) (hash-table)))
         (and (not (equal (key-fixer (key)) (key-fixer (%key))))
              (boundp (key) (hash-table))))
  :hints
  (("Goal"
    :by (:instance boundp-of-remover/lemma
                   (key (key))
                   (%key (%key))
                   (hash-table (hash-table))))))

(local
  (defthm boundp-when-zp-count/lemma
    (implies (zp (count hash-table))
             (not (boundp key hash-table)))
    :hints
    (("Goal"
      :in-theory (enable omap::aggressive)))))

(defthm boundp-when-zp-count
  (implies (zp (count (hash-table)))
           (not (boundp (key) (hash-table))))
  :hints
  (("Goal"
    :by (:instance boundp-when-zp-count/lemma
                   (key (key))
                   (hash-table (hash-table))))))

(local
  (defthm remover-of-updater-same/lemma
    (implies (equal (key-fixer key) (key-fixer %key))
             (equal (remover key (updater %key val hash-table))
                    (remover key hash-table)))))

(defthm remover-of-updater-same
  (implies (equal (key-fixer (key)) (key-fixer (%key)))
           (equal (remover (key) (updater (%key) (val) (hash-table)))
                  (remover (key) (hash-table))))
  :hints
  (("Goal"
    :by (:instance remover-of-updater-same/lemma
                   (key (key))
                   (%key (%key))
                   (val (val))
                   (hash-table (hash-table))))))

(local
  (defthm remover-of-updater-diff/lemma
    (implies (not (equal (key-fixer key) (key-fixer %key)))
             (equal (remover key (updater %key val hash-table))
                    (updater %key val (remover key hash-table))))))

(defthm remover-of-updater-diff
  (implies (not (equal (key-fixer (key)) (key-fixer (%key))))
           (equal (remover (key) (updater (%key) (val) (hash-table)))
                  (updater (%key) (val) (remover (key) (hash-table)))))
  :hints
  (("Goal"
    :by (:instance remover-of-updater-diff/lemma
                   (key (key))
                   (%key (%key))
                   (val (val))
                   (hash-table (hash-table))))))

(local
  (defthm remover-of-updater/lemma
    (equal (remover key (updater %key val hash-table))
           (if (equal (key-fixer key) (key-fixer %key))
               (remover key hash-table)
               (updater %key val (remover key hash-table))))))

(defthm remover-of-updater
  (equal (remover (key) (updater (%key) (val) (hash-table)))
         (if (equal (key-fixer (key)) (key-fixer (%key)))
             (remover (key) (hash-table))
             (updater (%key) (val) (remover (key) (hash-table)))))
  :hints
  (("Goal"
    :by (:instance remover-of-updater/lemma
                   (key (key))
                   (%key (%key))
                   (val (val))
                   (hash-table (hash-table))))))

(local
  (defthm remover-when-not-boundp/lemma
    (implies (not (boundp key hash-table))
             (equal (remover key hash-table)
                    (fixer hash-table)))))

(defthm remover-when-not-boundp
  (implies (not (boundp (key) (hash-table)))
           (equal (remover (key) (hash-table))
                  (fixer (hash-table))))
  :hints
  (("Goal"
    :by (:instance remover-when-not-boundp/lemma
                   (key (key))
                   (hash-table (hash-table))))))

(local
  (defthm remover-of-remover-same/lemma
    (implies (equal (key-fixer key) (key-fixer %key))
             (equal (remover key (remover %key hash-table))
                    (remover key hash-table)))))

(defthm remover-of-remover-same
  (implies (equal (key-fixer (key)) (key-fixer (%key)))
           (equal (remover (key) (remover (%key) (hash-table)))
                  (remover (key) (hash-table))))
  :hints
  (("Goal"
    :by (:instance remover-of-remover-same/lemma
                   (key (key))
                   (%key (%key))
                   (hash-table (hash-table))))))

(local
  (defthm remover-of-remover-diff/lemma
    (implies (not (equal (key-fixer key) (key-fixer %key)))
             (equal (remover key (remover %key hash-table))
                    (remover %key (remover key hash-table))))
    :rule-classes
    ((:rewrite :loop-stopper ((key %key remover))))))

(defthm remover-of-remover-diff
  (implies (not (equal (key-fixer (key)) (key-fixer (%key))))
           (equal (remover (key) (remover (%key) (hash-table)))
                  (remover (%key) (remover (key) (hash-table)))))
  :hints
  (("Goal"
    :by (:instance remover-of-remover-diff/lemma
                   (key (key))
                   (%key (%key))
                   (hash-table (hash-table))))))

(local
  (defthm remover-of-remover/lemma
    (equal (remover key (remover %key hash-table))
           (if (equal (key-fixer key) (key-fixer %key))
               (remover key hash-table)
               (remover %key (remover key hash-table))))))

(defthm remover-of-remover
  (equal (remover (key) (remover (%key) (hash-table)))
         (if (equal (key-fixer (key)) (key-fixer (%key)))
             (remover (key) (hash-table))
             (remover (%key) (remover (key) (hash-table)))))
  :hints
  (("Goal"
    :by (:instance remover-of-remover/lemma
                   (key (key))
                   (%key (%key))
                   (hash-table (hash-table))))))


;;;; `HASH-TABLE-EQUAL'
(encapsulate ()
  (defun-sk hash-table-keys-equal (%hash-table hash-table)
    (declare (xargs :guard (and (recognizer %hash-table)
                                (recognizer hash-table))
                    :verify-guards nil))
    (forall key
      (implies (key-recognizer key)
               (equal (boundp key %hash-table)
                      (boundp key hash-table))))
    :rewrite :direct)

  (defun-sk hash-table-vals-equal (%hash-table hash-table)
    (declare (xargs :guard (and (recognizer %hash-table)
                                (recognizer hash-table))
                    :verify-guards nil))
    (forall key
      (implies (key-recognizer key)
               (equal (accessor key %hash-table)
                      (accessor key hash-table))))
    :rewrite :direct)

  (defun-nx hash-table-equal (%hash-table hash-table)
    (declare (xargs :guard t
                    :verify-guards nil))
    (and (recognizer %hash-table)
         (recognizer hash-table)
         (= (count %hash-table) (count hash-table))
         (hash-table-keys-equal %hash-table hash-table)
         (hash-table-vals-equal %hash-table hash-table)))

  (local
    (defthmd <<-squeeze
      (implies (and (not (<< x y))
                    (not (<< y x)))
               (equal x y))
      :rule-classes :forward-chaining))

  (local
    (defthmd head-key-equal-when-hash-table-keys-equal
      (implies (and (recognizer %hash-table)
                    (recognizer hash-table)
                    (not (omap::emptyp %hash-table))
                    (not (omap::emptyp hash-table))
                    (hash-table-keys-equal %hash-table hash-table))
               (equal (omap::head-key %hash-table) (omap::head-key hash-table)))
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
                        (hash-table-keys-equal
                         hash-table-keys-equal-necc)))
       ("Subgoal 2"
        :use ((:instance hash-table-keys-equal-necc
                         (key (mv-nth 0 (omap::head %hash-table))))))
       ("Subgoal 1"
        :use ((:instance hash-table-keys-equal-necc
                         (key (mv-nth 0 (omap::head hash-table)))))))))

  (local
    (defthmd hash-table-keys-equal-of-tail-when-hash-table-keys-equal
      (implies (and (recognizer %hash-table)
                    (recognizer hash-table)
                    (not (omap::emptyp %hash-table))
                    (not (omap::emptyp hash-table))
                    (hash-table-keys-equal %hash-table hash-table))
               (hash-table-keys-equal (omap::tail %hash-table) (omap::tail hash-table)))
      :rule-classes
      ((:rewrite :match-free :all))
      :hints
      (("Goal"
        :do-not-induct t
        :cases ((<< (mv-nth 0 (omap::head %hash-table))
                    (mv-nth 0 (omap::head hash-table)))
                (<< (mv-nth 0 (omap::head hash-table))
                    (mv-nth 0 (omap::head %hash-table))))
        :in-theory (disable hash-table-keys-equal
                            hash-table-keys-equal-necc))
       ("Subgoal 3"
        :use ((:instance <<-squeeze
                         (x (mv-nth 0 (omap::head %hash-table)))
                         (y (mv-nth 0 (omap::head hash-table)))))
        :expand (hash-table-keys-equal (omap::tail %hash-table)
                                       (omap::tail hash-table)))
       ("Subgoal 3.2"
        :use ((:instance hash-table-keys-equal-necc
                         (key (hash-table-keys-equal-witness (omap::tail %hash-table)
                                                             (omap::tail hash-table))))
              (:instance omap::head-key-minimal
                         (key (mv-nth 0 (omap::head %hash-table)))
                         (map (omap::tail hash-table)))
              (:instance omap::head-tail-order
                         (x hash-table)))
        :expand (omap::assoc (hash-table-keys-equal-witness (omap::tail %hash-table)
                                                            (omap::tail hash-table))
                             %hash-table))
       ("Subgoal 3.1"
        :use ((:instance hash-table-keys-equal-necc
                         (key (hash-table-keys-equal-witness (omap::tail %hash-table)
                                                             (omap::tail hash-table)))))
        :expand (omap::assoc (hash-table-keys-equal-witness (omap::tail %hash-table)
                                                            (omap::tail hash-table))
                             hash-table))
       ("Subgoal 2"
        :use ((:instance head-key-equal-when-hash-table-keys-equal)))
       ("Subgoal 1"
        :use ((:instance head-key-equal-when-hash-table-keys-equal))))))

  (local
    (defthmd head-val-equal-when-hash-table-vals-equal
      (implies (and (recognizer %hash-table)
                    (recognizer hash-table)
                    (not (omap::emptyp %hash-table))
                    (not (omap::emptyp hash-table))
                    (hash-table-keys-equal %hash-table hash-table)
                    (hash-table-vals-equal %hash-table hash-table))
               (equal (omap::head-val %hash-table) (omap::head-val hash-table)))
      :rule-classes
      ((:rewrite :match-free :all))
      :hints
      (("Goal"
        :in-theory (disable hash-table-keys-equal
                            hash-table-keys-equal-necc
                            hash-table-vals-equal
                            hash-table-vals-equal-necc)
        :use ((:instance hash-table-vals-equal-necc
                         (key (omap::head-key %hash-table)))
              (:instance hash-table-vals-equal-necc
                         (key (omap::head-key hash-table)))
              (:instance head-key-equal-when-hash-table-keys-equal))))))

  (local
    (defthmd accessor-when-small
      (implies (<< (key-fixer key) (omap::head-key map))
               (equal (accessor key map)
                      (val-default)))
      :hints
      (("Goal"
        :expand (accessor key map))
       ("Subgoal *1/3.7"
        :use ((:instance omap::head-tail-order
                         (x map)))))))

  (local
    (defthmd hash-table-vals-equal-of-tail-when-hash-table-vals-equal
      (implies (and (recognizer %hash-table)
                    (recognizer hash-table)
                    (not (omap::emptyp %hash-table))
                    (not (omap::emptyp hash-table))
                    (hash-table-keys-equal %hash-table hash-table)
                    (hash-table-vals-equal %hash-table hash-table))
               (hash-table-vals-equal (omap::tail %hash-table) (omap::tail hash-table)))
      :rule-classes
      ((:rewrite :match-free :all))
      :hints
      (("Goal"
        :do-not-induct t
        :cases ((<< (mv-nth 0 (omap::head %hash-table))
                    (mv-nth 0 (omap::head hash-table)))
                (<< (mv-nth 0 (omap::head hash-table))
                    (mv-nth 0 (omap::head %hash-table))))
        :in-theory (disable hash-table-keys-equal
                            hash-table-keys-equal-necc
                            hash-table-vals-equal
                            hash-table-vals-equal-necc))
       ("Subgoal 3"
        :use ((:instance <<-squeeze
                         (x (mv-nth 0 (omap::head %hash-table)))
                         (y (mv-nth 0 (omap::head hash-table))))
              (:instance hash-table-vals-equal-necc
                         (key (hash-table-vals-equal-witness (omap::tail %hash-table)
                                                             (omap::tail hash-table))))
              (:instance accessor-when-small
                         (key (mv-nth 0 (omap::head %hash-table)))
                         (map (omap::tail hash-table)))
              (:instance omap::head-tail-order
                         (x hash-table)))
        :expand ((hash-table-vals-equal (omap::tail %hash-table)
                                        (omap::tail hash-table))))
       ("Subgoal 2"
        :use ((:instance head-key-equal-when-hash-table-keys-equal)))
       ("Subgoal 1"
        :use ((:instance head-key-equal-when-hash-table-keys-equal))))))

  (local
    (in-theory
      (disable hash-table-keys-equal
               hash-table-vals-equal)))

  (local
    (defthmd emptyp-iff-zp-size
      (iff (omap::emptyp map)
           (zp (omap::size map)))
      :hints
      (("Goal"
        :in-theory (enable omap::size)))))

  (local
    (defthm hash-table-equal{forward-chaining}/lemma
      (implies (hash-table-equal %hash-table hash-table)
               (equal %hash-table hash-table))
      :rule-classes
      ((:forward-chaining :trigger-terms
                          ((hash-table-equal %hash-table hash-table))
                          :corollary
                          (implies t
                                   (implies (hash-table-equal %hash-table hash-table)
                                            (equal %hash-table hash-table)))))
      :hints
      (("Goal"
        :induct (omap::omap-induction2 %hash-table hash-table))
       ("Subgoal *1/3"
        :do-not-induct t
        :use ((:instance head-key-equal-when-hash-table-keys-equal)
              (:instance hash-table-keys-equal-of-tail-when-hash-table-keys-equal)
              (:instance head-val-equal-when-hash-table-vals-equal)
              (:instance hash-table-vals-equal-of-tail-when-hash-table-vals-equal)))
       ("Subgoal *1/2"
        :do-not-induct t
        :in-theory (enable emptyp-iff-zp-size))
       ("Subgoal *1/1"
        :do-not-induct t
        :in-theory (enable omap::primitives)
        :use ((:instance emptyp-iff-zp-size
                         (map hash-table)))))))

  (defthm hash-table-equal{forward-chaining}
    (implies (hash-table-equal (%hash-table) (hash-table))
             (equal (%hash-table) (hash-table)))
    :rule-classes :forward-chaining))


;;;; `HASH-TABLE-KEYS'
(encapsulate (((keys *) => *))
  (local
    (in-theory
      (e/d (recognizer{definition}-0)
           (recognizer{definition}-1))))

  (local
    (defun keys (map)
      (declare (xargs :guard t))
      (let ((map (fixer map)))
        (and (consp map)
             (let ((key (key-fixer (caar map))))
               (cons key (keys (cdr map))))))))

  (defthm keys{definition}-0
    (equal (keys map)
           (let ((map (fixer map)))
             (and (consp map)
                  (let ((key (key-fixer (caar map))))
                    (cons key (keys (cdr map)))))))
    :rule-classes :definition))

(defthm keys{definition}-1
  (equal (keys map)
         (omap::keys (fixer map)))
  :rule-classes :definition
  :hints
  (("Goal"
    :cases ((recognizer map))
    :in-theory (e/d (omap::primitives
                     omap::definitions
                     recognizer{definition}-0)
                    (recognizer{definition}-1
                     omap::setp-of-keys)))
   ("Subgoal 1"
    :induct (len map))
   ("Subgoal *1/2.4"
    :expand (set::insert (car (car map)) nil))
   ("Subgoal *1/2.2"
    :use ((:instance omap::setp-of-keys
                     (map (cdr map))))
    :expand ((set::insert (car (car map))
                          (keys (cdr map)))
             (set::head (keys (cdr map)))
             (set::emptyp (keys (cdr map)))))))

(local
  (in-theory
    (disable keys{definition}-0)))

(local
  (defthm setp-of-keys/lemma
    (set::setp (keys hash-table))))

(defthm setp-of-keys
  (set::setp (keys (hash-table)))
  :hints
  (("Goal"
    :by (:instance setp-of-keys/lemma
                   (hash-table (hash-table))))))

(local
  (defthm emptyp-of-keys/lemma
    (equal (set::emptyp (keys hash-table))
           (equal (fixer hash-table) (creator)))))

(defthm emptyp-of-keys
  (equal (set::emptyp (keys (hash-table)))
         (equal (fixer (hash-table)) (creator)))
  :hints
  (("Goal"
    :by (:instance emptyp-of-keys/lemma
                   (hash-table (hash-table))))))

(local
  (defthm head-of-keys/lemma
    (equal (set::head (keys hash-table))
           (omap::head-key (fixer hash-table)))))

(defthm head-of-keys
  (equal (set::head (keys (hash-table)))
         (omap::head-key (fixer (hash-table))))
  :hints
  (("Goal"
    :by (:instance head-of-keys/lemma
                   (hash-table (hash-table))))))

(local
  (defthm tail-of-keys/lemma
    (equal (set::tail (keys hash-table))
           (keys (omap::tail (fixer hash-table))))))

(defthm tail-of-keys
  (equal (set::tail (keys (hash-table)))
         (keys (omap::tail (fixer (hash-table)))))
  :hints
  (("Goal"
    :by (:instance tail-of-keys/lemma
                   (hash-table (hash-table))))))

(local
  (defthm cardinality-of-keys/lemma
    (equal (set::cardinality (keys hash-table))
           (count hash-table))))

(defthm cardinality-of-keys
  (equal (set::cardinality (keys (hash-table)))
         (count (hash-table)))
  :hints
  (("Goal"
    :by (:instance cardinality-of-keys/lemma
                   (hash-table (hash-table))))))

(local
  (defthmd key-recognizer-when-assoc
    (implies (and (recognizer hash-table)
                  (omap::assoc key hash-table))
             (key-recognizer key))
    :rule-classes
    ((:rewrite :match-free :all))))

(local
  (defthm in-of-keys/lemma
    (equal (set::in key (keys hash-table))
           (and (key-recognizer key)
                (boundp key hash-table)))
    :hints
    (("Goal"
      ;; TODO: Put in my modified omap theory?
      :in-theory (enable omap::in-of-keys-to-assoc)
      :use ((:instance key-recognizer-when-assoc))))))

(defthm in-of-keys
  (equal (set::in (key) (keys (hash-table)))
         (and (key-recognizer (key))
              (boundp (key) (hash-table))))
  :hints
  (("Goal"
    :by (:instance in-of-keys/lemma
                   (hash-table (hash-table))))))

(local
  (defthm keys-of-updater/lemma
    (equal (keys (updater key val hash-table))
           (set::insert (key-fixer key) (keys hash-table)))))

(defthm keys-of-updater
  (equal (keys (updater (key) (val) (hash-table)))
         (set::insert (key-fixer (key)) (keys (hash-table))))
  :hints
  (("Goal"
    :by (:instance keys-of-updater/lemma
                   (key (key))
                   (val (val))
                   (hash-table (hash-table))))))

(local
  (defthm keys-of-remover/lemma
    (equal (keys (remover key hash-table))
           (set::delete (key-fixer key) (keys hash-table)))))

(defthm keys-of-remover
  (equal (keys (remover (key) (hash-table)))
         (set::delete (key-fixer (key)) (keys (hash-table))))
  :hints
  (("Goal"
    :by (:instance keys-of-remover/lemma
                   (key (key))
                   (hash-table (hash-table))))))


;;;; `HASH-TABLE-COPY'
(encapsulate ()
  (defun copier-rec (set %hash-table hash-table)
    (declare (xargs :guard (and (set::setp set)
                                (set::subset set (keys hash-table)))
                    :guard-hints
                    (("Goal"
                      :expand (set::subset set (omap::keys hash-table))))
                    :measure (set::cardinality set)
                    :hints
                    (("Goal"
                      :in-theory (enable set::cardinality)))))
    (if (set::emptyp set)
        (fixer %hash-table)
        (let* ((key (set::head set))
               (val (accessor key hash-table))
               (%hash-table (updater key val %hash-table)))
          (copier-rec (set::tail set) %hash-table hash-table))))

  (local
    (in-theory
      (disable keys{definition}-1)))

  (local
    (defthm recognizer-of-copier-rec
      (recognizer (copier-rec set %hash-table hash-table))))

  (local
    (defthm subset-tail-when-subset
      (implies (and (not (set::emptyp x))
                    (set::subset x y))
               (set::subset (set::tail x) y))
      :hints
      (("Goal"
        :expand (set::subset x y)))))

  (local
    (defthm key-recognizer-of-head-when-subset
      (implies (and (not (set::emptyp set))
                    (set::subset set (keys hash-table)))
               (key-recognizer (set::head set)))
      :rule-classes
      ((:rewrite :match-free :all))
      :hints
      (("Goal"
        :cases ((recognizer hash-table))
        :in-theory (disable set::subset-in))
       ("Subgoal 1"
        :use ((:instance set::subset-in
                         (x set)
                         (y (keys hash-table))
                         (a (set::head set))))))))

  (local
    (defthm copier-rec-of-update
      (implies (and (key-recognizer key)
                    (val-recognizer val)
                    (recognizer %hash-table)
                    (recognizer hash-table)
                    (not (set::emptyp set))
                    (set::subset set (keys hash-table))
                    (<< key (set::head set)))
               (equal (copier-rec set
                                  (omap::update key
                                                val
                                                %hash-table)
                                  hash-table)
                      (omap::update key
                                    val
                                    (copier-rec set
                                                %hash-table
                                                hash-table))))
      :hints
      (("Goal"
        :cases ((equal key (set::head set)))
        :in-theory (enable set::head-tail-order))
       ("Subgoal *1/4"
        :do-not-induct t
        :cases ((equal key (set::head set))))
       ("Subgoal *1/3"
        :do-not-induct t
        :cases ((equal key (set::head set))))
       ("Subgoal *1/2"
        :do-not-induct t
        :cases ((equal key (set::head set))))
       ("Subgoal *1/1"
        :do-not-induct t
        :cases ((equal key (set::head set)))))))

  (defthm copier-rec{definition}-0
    (implies (set::subset set (keys hash-table))
             (equal (copier-rec set %hash-table hash-table)
                    (if (set::emptyp set)
                        (fixer %hash-table)
                        (omap::update (key-fixer (set::head set))
                                      (accessor (set::head set) hash-table)
                                      (copier-rec (set::tail set) %hash-table hash-table)))))
    :rule-classes :definition
    :hints
    (("Goal"
      :do-not-induct t
      :cases ((recognizer %hash-table)
              (recognizer hash-table))
      :in-theory (enable set::head-tail-order)
      :expand (copier-rec set %hash-table hash-table))
     ("Subgoal 2"
      :cases ((set::emptyp (set::tail set)))
      :use ((:instance copier-rec-of-update
                       (set (set::tail set))
                       (key (key-fixer (set::head set)))
                       (val (accessor (set::head set) hash-table)))))
     ("Subgoal 1"
      :cases ((set::emptyp (set::tail set))))
     ("Subgoal 1.2.1"
      :expand ((copier-rec (set::tail set)
                           nil hash-table)
               (copier-rec (set::tail set)
                           %hash-table hash-table)))))

  (local
    (defthm boundp-of-copier-rec
      (implies (and (set::setp set)
                    (set::subset set (keys hash-table)))
               (equal (boundp key (copier-rec set %hash-table hash-table))
                      (set::in (key-fixer key) (set::union set (keys %hash-table)))))
      :hints
      (("Goal"
        :induct (set::cardinality set)
        :in-theory (enable set::cardinality)))))

  (local
    (defthm accessor-of-copier-rec
      (implies (and (set::setp set)
                    (set::subset set (keys hash-table)))
               (equal (accessor key (copier-rec set %hash-table hash-table))
                      (if (set::in (key-fixer key) set)
                          (accessor key hash-table)
                          (accessor key %hash-table))))
      :hints
      (("Goal"
        :cases ((set::in (key-fixer key) set))
        :in-theory (enable set::cardinality))
       ("Subgoal 2"
        :induct (set::cardinality set))
       ("Subgoal 1"
        :induct (set::cardinality set))
       ("Subgoal *2/3"
        :cases ((equal (key-fixer key) (key-fixer (set::head set)))))
       ("Subgoal *1/3"
        :cases ((equal (key-fixer key) (key-fixer (set::head set))))))))

  (local
    (defthm count-of-copier-rec
      (implies (and (set::setp set)
                    (set::subset set (keys hash-table)))
               (equal (count (copier-rec set %hash-table hash-table))
                      (set::cardinality (set::union set (keys %hash-table)))))
      :hints
      (("Goal"
        :induct (set::cardinality set)
        :in-theory (e/d (set::cardinality)
                        (boundp-of-copier-rec))
        :expand ((set::intersect set (keys %hash-table))))
       ("Subgoal *1/2"
        :use ((:instance boundp-of-copier-rec
                         (key (set::head set))
                         (set (set::tail set))))))))

  (defun copier (%hash-table hash-table)
    (declare (xargs :guard t)
             (ignore %hash-table))
    (let ((keys (keys hash-table))
          (%hash-table (creator)))
      (copier-rec keys %hash-table hash-table)))

  (local
    (defthm recognizer-of-copier
      (recognizer (copier %hash-table hash-table))))

  (local
    (defthm boundp-of-copier
      (equal (boundp key (copier %hash-table hash-table))
             (boundp key hash-table))
      :hints
      (("Goal"
        :in-theory (disable boundp{definition}-1)))))

  (local
    (defthm accessor-of-copier
      (equal (accessor key (copier %hash-table hash-table))
             (accessor key hash-table))
      :hints
      (("Goal"
        :in-theory (disable accessor{definition}-1)))))

  (local
    (defthm count-of-copier
      (equal (count (copier %hash-table hash-table))
             (count hash-table))
      :hints
      (("Goal"
        :in-theory (disable count{definition}-1)))))

  (local
    (defthm copier{rewrite}/lemma
      (equal (copier %hash-table hash-table)
             (fixer hash-table))
      :hints
      (("Goal"
        :in-theory (disable copier
                            boundp{definition}-1
                            accessor{definition}-1
                            count{definition}-1
                            fixer{definition}-0)
        :use ((:functional-instance
               hash-table-equal{forward-chaining}
               (%hash-table (lambda () (copier %hash-table hash-table)))
               (hash-table (lambda () (fixer hash-table)))))))))

  (defthm copier{rewrite}
    (equal (copier (%hash-table) (hash-table))
           (fixer (hash-table)))
    :hints
    (("Goal"
      :by (:instance copier{rewrite}/lemma
                     (%hash-table (%hash-table))
                     (hash-table (hash-table)))))))

(in-theory
  (current-theory 'define-hash-table-lemmas-begin))
