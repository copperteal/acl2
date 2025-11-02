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


(in-package "ACL2") ; TODO: delete?
(set-verify-guards-eagerness 2)

;;; `HONS-REMOVE-DUPLICATES'
(include-book "std/lists/remove-duplicates" :dir :system)
;;; `ALIST-KEYS'
(include-book "std/alists/alist-keys" :dir :system)

(local
  (include-book "std/lists/top" :dir :system))
(local
  (include-book "std/alists/top" :dir :system))


;;;; Miscellaneous
(defthm count-keys-of-hons-acons
  (equal (count-keys (hons-acons key value alist))
         (if (hons-assoc-equal key alist)
             (count-keys alist)
             (1+ (count-keys alist)))))

(defthm count-keys-of-hons-remove-assoc
  (equal (count-keys (hons-remove-assoc key alist))
         (if (hons-assoc-equal key alist)
             (1- (count-keys alist))
             (count-keys alist))))

(defthm alist-keys-of-hons-remove-assoc
  (implies (alistp alist)
           (equal (alist-keys (hons-remove-assoc key alist))
                  (remove-equal key (alist-keys alist))))
  :hints
  (("Goal"
    :induct (len alist))))


;;;; `HONS-REMOVE-DUPLICATES'
(local
  (defthm hons-remove-duplicates-of-cons/lemma
    (equal (rev (remove-duplicates-equal (append list (list value))))
           (cons value (rev (remove-equal value (remove-duplicates-equal list)))))))

(defthm hons-remove-duplicates-of-cons
  (equal (hons-remove-duplicates (cons value list))
         (cons value (remove value (hons-remove-duplicates list))))
  :hints
  (("Goal"
    :expand ((hons-remove-duplicates (cons value list))
             (hons-remove-duplicates list)))))

(local
  (defthm hons-remove-duplicates-of-remove/lemma
    (equal (remove-duplicates-equal (rev (remove-equal value (rev list))))
           (remove-equal value (remove-duplicates-equal list)))))

(defthm hons-remove-duplicates-of-remove
  (equal (hons-remove-duplicates (remove value list))
         (remove value (hons-remove-duplicates list)))
  :hints
  (("Goal"
    :in-theory (disable hons-remove-duplicates-of-remove/lemma)
    :expand ((hons-remove-duplicates (remove-equal value list))
             (hons-remove-duplicates list))
    :use ((:instance hons-remove-duplicates-of-remove/lemma
                     (list (rev list)))))))


;;;; `RESIZE-LIST'
(local
  (defun resize-list-of-repeat/induction (n0 n1)
    (declare (xargs :guard t))
    (and (posp n0)
         (posp n1)
         (resize-list-of-repeat/induction (1- n0) (1- n1)))))

(defthm resize-list-of-repeat
  (implies (and (integerp n0)
                (integerp n1)
                (<= 0 n0)
                (<= 0 n1))
           (equal (resize-list (repeat n1 default-value)
                               n0 default-value)
                  (repeat n0 default-value)))
  :hints
  (("Goal"
    :induct (resize-list-of-repeat/induction n0 n1))
   ("Subgoal *1/1"
    :expand ((repeat n0 default-value)
             (repeat n1 default-value)
             (resize-list (cons default-value (repeat (+ -1 n1) default-value))
                          n0 default-value)))))

(local
  (defthm resize-list-of-resize-list/increasing
    (implies (and (integerp n0)
                  (integerp n1)
                  (<= 0 n0)
                  (<= n0 n1)
                  (<= n1 (len list)))
             (equal (resize-list (resize-list list n1 default-value)
                                 n0 default-value)
                    (resize-list list n0 default-value)))
    :hints
    (("Goal"
      :induct (and (nth n0 list)
                   (nth n1 list)))
     ("Subgoal *1/3.1"
      :expand ((resize-list (cons (car list)
                                  (resize-list (cdr list)
                                               (+ -1 n1)
                                               default-value))
                            n0 default-value)
               (resize-list list n0 default-value)
               (resize-list list n1 default-value))))))

(local
  (defthm resize-list-of-resize-list/bounded
    (implies (and (integerp n0)
                  (integerp n1)
                  (<= (len list) n0)
                  (<= (len list) n1))
             (equal (resize-list (resize-list list n1 default-value)
                                 n0 default-value)
                    (resize-list list n0 default-value)))
    :hints
    (("Goal"
      :induct (and (nth n0 list)
                   (nth n1 list)))
     ("Subgoal *1/3.2"
      :expand ((resize-list list n0 default-value)
               (resize-list list n1 default-value)
               (resize-list (cons (car list)
                                  (resize-list (cdr list)
                                               (+ -1 n1)
                                               default-value))
                            n0 default-value))))))

(defthm resize-list-of-resize-list
  (implies (and (integerp n0)
                (integerp n1)
                (or (and (<= 0 n0)
                         (<= n0 n1)
                         (<= n1 (len list)))
                    (and (<= (len list) n0)
                         (<= (len list) n1))))
           (equal (resize-list (resize-list list n1 default-value)
                               n0 default-value)
                  (resize-list list n0 default-value))))

(defthmd resize-list-is-take
  (implies (and (integerp n)
                (< 0 n)
                (<= n (len list)))
           (equal (resize-list list n default-value)
                  (take n list)))
  :hints
  (("Goal"
    :induct (nth n list))
   ("Subgoal *1/3.3"
    :expand (resize-list list 1 default-value))
   ("Subgoal *1/3.2"
    :expand ((resize-list list n default-value)
             (take n list)))))

(defthmd resize-list-is-append-repeat
  (implies (and (integerp n)
                (<= 0 n)
                (< (len list) n))
           (equal (resize-list list n default-value)
                  (append list (repeat (+ n (- (len list)))
                                       default-value))))
  :hints
  (("Goal"
    :induct (nth n list))
   ("Subgoal *1/3.1"
    :expand ((resize-list list n default-value)
             (append list
                     (repeat (+ n (- (len list)))
                             default-value))))))

(local
  (defthm resize-list-of-append/lemma-0
    (implies (and (integerp n)
                  (<= 0 n)
                  (<= n (len x)))
             (equal (resize-list (append x y) n default-value)
                    (take n x)))
    :hints
    (("Goal"
      :induct (nth n x))
     ("Subgoal *1/3.1"
      :expand ((resize-list (append x y)
                            n default-value)
               (take n x))))))

(local
  (defthm resize-list-of-append/lemma-1
    (implies (and (integerp n)
                  (< (len x) n)
                  (<= n (+ (len x) (len y))))
             (equal (resize-list (append x y) n default-value)
                    (take n (append x y))))
    :hints
    (("Goal"
      :induct (nth n x)
      :in-theory (enable resize-list-is-take))
     ("Subgoal *1/3.3"
      :expand ((resize-list (append x y)
                            n default-value)
               (append x (take (+ n (- (len x))) y)))))))

(local
  (defthm resize-list-of-append/lemma-2
    (implies (and (integerp n)
                  (<= 0 n)
                  (< (+ (len x) (len y)) n))
             (equal (resize-list (append x y) n default-value)
                    (append x y (repeat (- n (+ (len x) (len y))) default-value))))
    :hints
    (("Goal"
      :induct (nth n x)
      :in-theory (enable resize-list-is-append-repeat))
     ("Subgoal *1/3.1"
      :expand ((resize-list (append x y)
                            n default-value)
               (append x y
                       (repeat (+ n (- (len x)) (- (len y)))
                               default-value)))))))

(defthm resize-list-of-append
  (implies (and (integerp n)
                (<= 0 n))
           (equal (resize-list (append x y) n default-value)
                  (cond
                    ((<= n (len x))
                     (take n x))
                    ((<= n (+ (len x) (len y)))
                     (take n (append x y)))
                    (t
                     (append x y (repeat (- n (+ (len x) (len y))) default-value)))))))

(local
  (defthm resize-list-of-update-nth/lemma-0
    (implies (and (integerp i)
                  (<= 0 i)
                  (integerp n)
                  (<= 0 n)
                  (atom list))
             (equal (resize-list (update-nth i value list) n default-value)
                    (and (< 0 n)
                         (resize-list (append (repeat i nil) (list value))
                                      n default-value))))))

(local
  (defthm resize-list-of-update-nth/lemma-1
    (implies (and (integerp i)
                  (<= 0 i)
                  (integerp n)
                  (<= 0 n)
                  (consp list)
                  (< i (len list))
                  (< i n))
             (equal (resize-list (update-nth i value list) n default-value)
                    (update-nth i value (resize-list list n default-value))))
    :hints
    (("Goal"
      :induct (and (nth i list)
                   (nth n list))
      :expand ((resize-list (cons value (cdr list))
                            n default-value)
               (resize-list list n default-value)))
     ("Subgoal *1/3.7"
      :expand ((resize-list (cons (car list)
                                  (update-nth (+ -1 i) value (cdr list)))
                            n default-value))))))

(local
  (defthm resize-list-of-update-nth/lemma-2
    (implies (and (integerp i)
                  (<= 0 i)
                  (integerp n)
                  (<= 0 n)
                  (consp list)
                  (< i (len list))
                  (<= n i))
             (equal (resize-list (update-nth i value list) n default-value)
                    (resize-list list n default-value)))
    :hints
    (("Goal"
      :induct (and (nth i list)
                   (nth n list))
      :in-theory (enable resize-list-is-take))
     ("Subgoal *1/3.2"
      :expand ((resize-list (cons (car list)
                                  (update-nth (+ -1 i) value (cdr list)))
                            n default-value)))
     ("Subgoal *1/3.2'"
      :in-theory (disable resize-list-is-take)
      :use ((:instance resize-list-is-take
                       (list (cdr list))
                       (n (+ -1 n))))))))

(local
  (defthm resize-list-of-update-nth/lemma-3
    (implies (and (integerp i)
                  (<= 0 i)
                  (integerp n)
                  (<= 0 n)
                  (consp list)
                  (<= (len list) i)
                  (< i n))
             (equal (resize-list (update-nth i value list) n default-value)
                    (append list
                            (repeat (- i (len list)) nil)
                            (list value)
                            (repeat (1- (- n i)) default-value))))
    :hints
    (("Goal"
      :induct (and (nth i list)
                   (nth n list)))
     ("Subgoal *1/3.7"
      :expand ((resize-list (cons (car list)
                                  (update-nth (+ -1 i) value (cdr list)))
                            n default-value)))
     ("Subgoal *1/3.1"
      :expand ((resize-list (cons (car list)
                                  (append (repeat (+ -1 i) nil)
                                          (list value)))
                            n default-value))))))

(local
  (defthm resize-list-of-update-nth/lemma-4
    (implies (and (integerp i)
                  (<= 0 i)
                  (integerp n)
                  (<= 0 n)
                  (consp list)
                  (<= n i)
                  (<= n (len list)))
             (equal (resize-list (update-nth i value list) n default-value)
                    (resize-list list n default-value)))
    :hints
    (("Goal"
      :induct (and (nth i list)
                   (nth n list))
      :in-theory (disable resize-list-is-take))
     ("Subgoal *1/3.3"
      :expand (resize-list (cons (car list)
                                 (append (repeat (+ -1 i) nil)
                                         (list value)))
                           n default-value))
     ("Subgoal *1/3.2"
      :expand ((resize-list (cons (car list)
                                  (update-nth (+ -1 i) value (cdr list)))
                            n default-value)
               (resize-list list n default-value))))))

(local
  (defthm resize-list-of-update-nth/lemma-5
    (implies (and (integerp i)
                  (<= 0 i)
                  (integerp n)
                  (<= 0 n)
                  (consp list)
                  (<= n i)
                  (<= (len list) i)
                  (< (len list) n))
             (equal (resize-list (update-nth i value list) n default-value)
                    (append list (repeat (- n (len list)) nil))))
    :hints
    (("Goal"
      :induct (and (nth i list)
                   (nth n list))
      :in-theory (enable resize-list-is-take
                         resize-list-is-append-repeat)))))

(defthm resize-list-of-update-nth
  (implies (and (integerp i)
                (<= 0 i)
                (integerp n)
                (<= 0 n))
           (equal (resize-list (update-nth i value list) n default-value)
                  (cond
                    ((atom list)
                     (and (< 0 n)
                          (resize-list (append (repeat i nil) (list value))
                                       n default-value)))
                    ((and (< i (len list))
                          (< i n))
                     (update-nth i value (resize-list list n default-value)))
                    ((and (< i (len list))
                          (<= n i))
                     (resize-list list n default-value))
                    ((and (<= (len list) i)
                          (< i n))
                     (append list
                             (repeat (- i (len list)) nil)
                             (list value)
                             (repeat (1- (- n i)) default-value)))
                    ((and (<= (len list) i)
                          (<= n i))
                     (if (<= n (len list))
                         (resize-list list n default-value)
                         (append list (repeat (- n (len list)) nil))))))))
