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


(in-package "OMAP")
(set-verify-guards-eagerness 2)

(include-book "std/omaps/top" :dir :system)

(include-book "total-order")
(include-book "osets")

(in-theory
  (e/d (
        head-tail-order
        )
       (
        )))

(defsection auxiliary-emptyp-theorems
  :extension emptyp

  "<p>The following theorem is available in
@('[books]/projects/atomic-stobjs/omaps').</p>"

  (defthm emptyp-of-delete-when-miss
    (implies (and (not (emptyp map))
                  (not (equal key (head-key map))))
             (not (emptyp (delete key map))))
    :hints
    (("Goal"
      :in-theory (enable delete)))))

(defsection auxiliary-head-theorems
  :extension head

  "<p>The following theorem is available in
@('[books]/projects/atomic-stobjs/omaps').</p>"

  (defthm head-of-delete-when-miss
    (implies (and (not (emptyp map))
                  (not (equal key (head-key map))))
             (equal (head (delete key map))
                    (head map)))
    :hints
    (("Goal"
      :in-theory (enable delete
                         update
                         head
                         tail
                         emptyp
                         mfix
                         mapp)))))

(defsection auxiliary-update-theorems
  :extension update

  "<p>The following theorems are available in
@('[books]/projects/atomic-stobjs/omaps').</p>"

  (defthm update-of-delete-when-same
    (implies (equal key0 key1)
             (equal (update key0 val (delete key1 map))
                    (update key0 val map)))
    :hints
    (("Goal"
      :induct (delete key0 map)
      :in-theory (enable delete))))

  (defthm update-of-lookup-when-assoc
    (implies (and (assoc key0 map0)
                  (equal key0 key1)
                  (equal map0 map1))
             (equal (update key0 (lookup key1 map0) map1)
                    map1))
    :hints
    (("Goal"
      :in-theory (enable assoc
                         lookup)))))

(defsection auxiliary-delete-theorems
  :extension delete

  "<p>The following theorems are available in
@('[books]/projects/atomic-stobjs/omaps').</p>"

  (local
    (in-theory
      (enable delete)))

  (defthm delete-when-small
    (implies (and (not (emptyp map))
                  (<< key (head-key map)))
             (equal (delete key map)
                    map)))

  (defthm delete-when-hit
    (implies (and (not (emptyp map))
                  (equal key (head-key map)))
             (equal (delete key map)
                    (tail map))))

  (defthm delete-when-not-assoc
    (implies (and (mapp map)
                  (not (assoc key map)))
             (equal (delete key map)
                    map)))

  (defthm delete-of-tail
    (implies (and (not (emptyp map))
                  (not (emptyp (tail map)))
                  (<< (head-key (tail map)) key))
             (equal (delete key (tail map))
                    (tail (delete key map))))
    :hints
    (("Goal"
      :in-theory (enable mapp
                         mfix
                         emptyp
                         head
                         tail
                         update))))

  (local
    (defthm delete-of-update-when-same
      (implies (equal key0 key1)
               (equal (delete key0 (update key1 val map))
                      (delete key0 map)))
      :hints
      (("Goal"
        :in-theory (enable mapp
                           mfix
                           emptyp
                           head
                           tail
                           update)))))

  (local
    (defthm delete-of-update-when-diff
      (implies (not (equal key0 key1))
               (equal (delete key0 (update key1 val map))
                      (update key1 val (delete key0 map))))
      :hints
      (("Subgoal *1/3"
        :expand (delete key0 (update key1 val map)))
       ("Subgoal *1/2"
        :expand (delete (mv-nth 0 (head map))
                        (update key1 val map))))))

  (defthm delete-of-update
    (equal (delete key0 (update key1 val map))
           (if (equal key0 key1)
               (delete key0 map)
               (update key1 val (delete key0 map)))))

  (defthm delete-of-delete-when-same
    (implies (equal key0 key1)
             (equal (delete key0 (delete key1 map))
                    (delete key0 map)))
    :hints
    (("Goal"
      :in-theory (enable mapp
                         mfix
                         emptyp
                         head
                         tail
                         update))))

  (defthm delete-of-delete-when-diff
    (implies (not (equal key0 key1))
             (equal (delete key0 (delete key1 map))
                    (delete key1 (delete key0 map))))
    :rule-classes
    ((:rewrite :loop-stopper ((key0 key1 delete))))
    :hints
    (("Goal"
      :induct (size map)
      :in-theory (enable size
                         mapp
                         mfix
                         emptyp
                         head
                         tail
                         update)))))

(defsection auxiliary-assoc-theorems
  :extension assoc

  "<p>The following theorems are available in
@('[books]/projects/atomic-stobjs/omaps').</p>"

  (local
    (in-theory
      (enable assoc)))

  (local
    (defthm assoc-of-delete-when-same
      (implies (equal key1 key2)
               (not (assoc key1 (delete key2 map))))
      :hints
      (("Goal"
        :in-theory (enable delete)))))

  (local
    (defthm assoc-of-delete-when-diff
      (implies (not (equal key1 key2))
               (equal (assoc key1 (delete key2 map))
                      (assoc key1 map)))))

  (defthm assoc-of-delete
    (equal (assoc key1 (delete key2 map))
           (and (not (equal key1 key2))
                (assoc key1 map))))

  (defthmd assoc-when-emptyp-of-delete
    (implies (and (not (equal key0 key1))
                  (emptyp (delete key0 map)))
             (not (assoc key1 map)))
    :rule-classes
    ((:rewrite :match-free :all))))

(defsection auxiliary-lookup-theorems
  :extension lookup

  "<p>The following theorem is available in
@('[books]/projects/atomic-stobjs/omaps').</p>"

  (local
    (in-theory
      (enable lookup)))

  (local
    (defthm lookup-of-delete-when-same
      (implies (equal key0 key1)
               (not (lookup key0 (delete key1 map))))))

  (local
    (defthm lookup-of-delete-when-diff
      (implies (not (equal key0 key1))
               (equal (lookup key0 (delete key1 map))
                      (lookup key0 map)))))

  (defthm lookup-of-delete
    (equal (lookup key0 (delete key1 map))
           (and (not (equal key0 key1))
                (lookup key0 map)))))

(defsection auxiliary-size-theorems
  :extension size

  "<p>The following theorems are available in
@('[books]/projects/atomic-stobjs/omaps').</p>"

  (local
    (in-theory
      (enable size)))

  (defthmd size-0-iff-empty
    (iff (equal (size map) 0)
         (emptyp map)))

  (defthm size-of-tail
    (implies (not (emptyp map))
             (equal (size (tail map))
                    (1- (size map)))))

  (local
    (defthm size-of-update-when-assoc
      (implies (assoc key map)
               (equal (size (update key val map))
                      (size map)))
      :hints
      (("Goal"
        :induct (size map)
        :in-theory (enable assoc
                           mapp
                           mfix
                           emptyp
                           head
                           tail
                           update)))))

  (local
    (defthm size-of-update-when-not-assoc
      (implies (not (assoc key map))
               (equal (size (update key val map))
                      (1+ (size map))))
      :hints
      (("Goal"
        :induct (size map)
        :in-theory (enable assoc
                           mapp
                           mfix
                           emptyp
                           head
                           tail
                           update)))))

  (defthm size-of-update
    (equal (size (update key val map))
           (if (assoc key map)
               (size map)
               (1+ (size map)))))

  (local
    (defthm size-of-delete-when-assoc
      (implies (assoc key map)
               (equal (size (delete key map))
                      (1- (size map))))
      :hints
      (("Goal"
        :in-theory (enable delete
                           assoc)))))

  (local
    (defthm size-of-delete-when-not-assoc
      (implies (not (assoc key map))
               (equal (size (delete key map))
                      (size map)))
      :hints
      (("Goal"
        :in-theory (enable delete
                           assoc)))))

  (defthm size-of-delete
    (equal (size (delete key map))
           (if (assoc key map)
               (1- (size map))
               (size map)))))

(defsection auxiliary-keys-theorems
  :extension keys

  "<p>The following theorems are available in
@('[books]/projects/atomic-stobjs/omaps').</p>"

  (local
    (in-theory
      (enable keys
              in-of-keys-to-assoc
              head-tail-order
              set::head-insert
              set::tail-insert
              set::insert-cardinality)))

  (defthm emptyp-of-keys
    (equal (set::emptyp (keys map))
           (emptyp map)))

  (defthm head-of-keys
    (equal (set::head (keys map))
           (head-key map))
    :hints
    (("Goal"
      :do-not-induct t
      :expand (keys map))
     ("Subgoal 1"
      :induct (size map)
      :in-theory (enable size))))

  (defthm tail-of-keys
    (equal (set::tail (keys map))
           (keys (tail map))))

  (defthm cardinality-of-keys
    (equal (set::cardinality (keys map))
           (size map))
    :hints
    (("Goal"
      :induct (size map)
      :in-theory (enable size))))

  (defthm keys-of-delete
    (equal (keys (delete key map))
           (set::delete key (keys map)))
    :hints
    (("Goal"
      :induct (size map)
      :in-theory (enable size)))))
