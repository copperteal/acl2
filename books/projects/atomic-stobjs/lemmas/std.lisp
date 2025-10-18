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


(in-package "ACL2")
(set-verify-guards-eagerness 2)

#||
(include-book "std/lists/top" :dir :system)
(include-book "std/alists/top" :dir :system)
||#

(local
  (include-book "std/basic/inductions" :dir :system))

(include-book "../utilities/with-books")

(defun repeat (n x)
  ;; MAINTENANCE: Keep in sync with ("std/lists/repeat" :dir :system)
  (declare (xargs :guard (natp n)
                  :verify-guards nil))
  (mbe :logic (if (zp n)
                  nil
                  (cons x (repeat (- n 1) x)))
       :exec (make-list n :initial-element x)))

(in-theory
  (e/d ((:d repeat)
        (:i repeat))
       ((:e make-list-ac)
        (:e repeat))))

(defthm len-of-make-list-ac
  (implies (natp n)
           (equal (len (make-list-ac n val ac))
                  (+ n (len ac)))))

(defthm true-listp-of-make-list-ac
  (equal (true-listp (make-list-ac n val ac))
         (true-listp ac))
  :rule-classes
  (:rewrite
   (:type-prescription :typed-term
                       (make-list-ac n val ac)
                       :corollary
                       (implies (true-listp ac)
                                (true-listp (make-list-ac n val ac))))))

(defthm consp-of-make-list-ac
  (equal (consp (make-list-ac n val ac))
         (or (posp n)
             (consp ac)))
  :rule-classes
  (:rewrite
   (:type-prescription :typed-term
                       (make-list-ac n val ac)
                       :corollary
                       (implies (or (posp n)
                                    (consp ac))
                                (consp (make-list-ac n val ac)))))
  :hints
  (("Goal"
    :expand (make-list-ac 1 val ac))))

;; (defthm resize-list-of-make-list-ac
;;   (implies (equal v d)
;;            (equal (resize-list (make-list-ac n v ac) m d)
;;                   (cond
;;                     ((zp m)
;;                      ())
;;                     ((zp n)
;;                      (resize-list ac m d))
;;                     ((<= m n)
;;                      (make-list-ac m d ()))
;;                     (t
;;                      (make-list-ac n d (resize-list ac (- m n) d)))))))

;; (defthm make-list-ac-of-make-list-ac
;;   (implies (equal v w)
;;            (equal (make-list-ac n v (make-list-ac m w ac))
;;                   (make-list-ac (+ (nfix n)
;;                                    (nfix m))
;;                                 w ac))))

;; (defthm nth-of-make-list-ac
;;   (equal (nth i (make-list-ac n val ac))
;;          (cond
;;            ((zp n)
;;             (nth i ac))
;;            ((zp i)
;;             val)
;;            ((< i n)
;;             val)
;;            (t
;;             (nth (- i n) ac)))))

(defthmd nth-of-cons
  (equal (nth i (cons x y))
         (if (zp i)
             x
             (nth (1- i) y))))

(with-books (("std/lists/repeat" :dir :system))
  (defthm update-nth-of-repeat
    ;; TODO: share this
    (implies (and (equal val x)
                  (natp key)
                  (posp n)
                  (< key n))
             (equal (update-nth key val (repeat n x))
                    (repeat n x)))
    :hints
    (("Goal"
      :induct (dec-dec-induct key n)
      :expand (repeat n val)))))

;; (defthmd resize-list-removal
;;   (implies (and (not (zp n))
;;                 (consp lst))
;;            (equal (resize-list lst n default-value)
;;                   (if (< (len lst) n)
;;                       (append lst (repeat (- n (len lst)) default-value))
;;                       (take n lst)))))

(with-books (("std/lists/resize-list" :dir :system)
             ("std/lists/repeat" :dir :system))
  (defthm resize-list-of-repeat
    ;; TODO: share this
    (implies (equal x d)
             (equal (resize-list (repeat n x) m d)
                    (repeat m d)))
    :hints
    (("Goal"
      :induct (dec-dec-induct n m)
      :expand ((repeat m d)
               (repeat n d))))))

(with-books (("std/lists/resize-list" :dir :system)
             ("std/lists/take" :dir :system)
             ("std/lists/repeat" :dir :system)
             ("std/lists/len" :dir :system))
  (defthm resize-list-of-resize-list
    ;; TODO: share
    (implies (and (equal d e)
                  (consp lst)
                  (natp n)
                  (natp m)
                  (or (<= m n)
                      (<= (len lst) n)))
             (equal (resize-list (resize-list lst n d) m e)
                    (resize-list lst m e)))
    :hints
    (("Goal"
      :induct (and (nth n lst)
                   (nth m lst))))))

(with-books (("std/lists/resize-list" :dir :system)
             ("std/lists/repeat" :dir :system))
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

  (defthm resize-list-of-update-nth-keep
    ;; TODO: share
    (implies (and (natp key)
                  (natp n)
                  (< key (len l))
                  (< key n))
             (equal (resize-list (update-nth key val l)
                                 n default-value)
                    (update-nth key val (resize-list l n default-value))))
    :hints
    (("Goal"
      :induct (resize-list-of-update-nth/induction key l n)
      :expand ((repeat n default-value)))))

  (defthm resize-list-of-update-nth-drop
    ;; TODO: share
    (implies (and (natp key)
                  (natp n)
                  (< key (len l))
                  (<= n key))
             (equal (resize-list (update-nth key val l)
                                 n default-value)
                    (resize-list l n default-value)))
    :hints
    (("Goal"
      :induct (resize-list-of-update-nth/induction key l n)
      :expand ((repeat n default-value))))))

(with-books (("std/lists/update-nth" :dir :system)
             ("std/lists/resize-list" :dir :system))
  (defthm update-nth-of-resize-list
    ;; TODO: share
    (implies (and (and (natp key)
                       (natp n)
                       (< key n))
                  (equal val (if (< key (len lst))
                                 (nth key lst)
                                 default-value)))
             (equal (update-nth key val (resize-list lst n default-value))
                    (resize-list lst n default-value)))))

(defthm consp-of-resize-list
  ;; TODO: share
  (equal (consp (resize-list lst n default-value))
         (posp n))
  :rule-classes
  (:rewrite
   (:type-prescription :typed-term
                       (resize-list lst n default-value)
                       :corollary
                       (implies (posp n)
                                (consp (resize-list lst n default-value))))))

(defthmd car-of-resize-list
  (implies (posp n)
           (equal (car (resize-list lst n default-value))
                  (if (consp lst)
                      (car lst)
                      default-value))))

(defthmd cdr-of-resize-list
  (implies (posp n)
           (equal (cdr (resize-list lst n default-value))
                  (if (consp lst)
                      (resize-list (cdr lst) (1- n) default-value)
                      (resize-list lst (1- n) default-value)))))

(with-books (("std/alists/hons-remove-assoc" :dir :system))
  ;; TODO: share
  (defthm count-keys-of-hons-remove-assoc-when-hons-assoc-equal
    (implies (hons-assoc-equal k alist)
             (equal (count-keys (hons-remove-assoc k alist))
                    (1- (count-keys alist)))))

  (defthm count-keys-of-hons-remove-assoc-when-not-hons-assoc-equal
    (implies (not (hons-assoc-equal k alist))
             (equal (count-keys (hons-remove-assoc k alist))
                    (count-keys alist)))))

(defthm hons-assoc-equal-when-no-keys
  ;; TODO: share?
  (implies (zp (count-keys alist))
           (not (hons-assoc-equal k alist))))

(defthm update-nth-of-make-list-ac
  (implies (and (natp key)
                (natp n)
                (< key (+ n (len ac)))
                (equal val (if (< key n)
                               v
                               (nth (- key n) ac))))
           (equal (update-nth key val (make-list-ac n v ac))
                  (make-list-ac n v ac))))

(defun alist-fix (x)
  (declare (xargs :guard t))
  (if (atom x)
      nil
      (if (consp (car x))
          (cons (car x) (alist-fix (cdr x)))
          (alist-fix (cdr x)))))

(with-books (("std/alists/hons-remove-assoc" :dir :system))
  (defthm count-keys-of-alist-fix
    (equal (count-keys (alist-fix x))
           (count-keys x))))
