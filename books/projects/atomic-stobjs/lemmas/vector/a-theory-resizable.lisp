;;; Copyright 2026 J. David Taylor
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


(in-package "LEM/VECTOR$A/THEORY")
(set-verify-guards-eagerness 2)

(include-book "nat-defuns")
(local
  (include-book "nat-theory"))


;;;; Vector Axioms
(encapsulate (((name) => *)
              ((default-length) => *)
              ((initial-element) => *)
              ((element-recognizer *) => *)
              ((element-fixer *) => *)
              ((element-equiv * *) => *)
              ((recognizer *) => *)
              ((creator) => *)
              ((fixer *) => *)
              ((length *) => *)
              ((resizer * *) => *)
              ((accessor * *) => *)
              ((updater * * *) => *)
              ((equiv-rec * * *) => *))
  (local
    (include-book "a-defuns-resizable"))

  (local
    (defun name ()
      (declare (xargs :guard t
                      :type-prescription :none
                      :verify-guards nil))
      (lem/vector$a/defuns::name)))

  (defthm name-tp
    (and (symbolp (name))
         (not (equal (name) nil))
         (not (equal (name) t)))
    :rule-classes :type-prescription)

  (local
    (defun default-length ()
      (declare (xargs :guard t
                      :type-prescription :none
                      :verify-guards nil))
      (lem/vector$a/defuns::default-length)))

  (defthm default-length-tp
    (natp (default-length))
    :rule-classes :type-prescription)

  (local
    (defun initial-element ()
      (declare (xargs :guard t
                      :type-prescription :none
                      :verify-guards nil))
      (lem/vector$a/defuns::initial-element)))

  (local
    (defun element-recognizer (element)
      (declare (xargs :guard t
                      :type-prescription :none
                      :verify-guards nil))
      (lem/vector$a/defuns::element-recognizer element)))

  (defthm element-recognizer-of-initial-element
    (element-recognizer (initial-element))
    :rule-classes
    ((:forward-chaining :trigger-terms ((initial-element)))))

  (local
    (defun element-fixer (element)
      (declare (xargs :guard t
                      :type-prescription :none
                      :verify-guards nil))
      (lem/vector$a/defuns::element-fixer element)))

  (defthm element-recognizer-of-element-fixer
    (element-recognizer (element-fixer element))
    :rule-classes
    ((:forward-chaining :trigger-terms ((element-fixer element)))))

  (defthm element-fixer-when-element-recognizer
    (implies (element-recognizer element)
             (equal (element-fixer element)
                    element)))

  (local
    (defun element-equiv (element1 element2)
      (declare (xargs :guard t
                      :type-prescription :none
                      :verify-guards nil))
      (equal (element-fixer element1)
             (element-fixer element2))))

  (defthm element-equiv-rw
    (equal (element-equiv element1 element2)
           (equal (element-fixer element1)
                  (element-fixer element2))))

  (local
    (defun recognizer (vector)
      (declare (xargs :guard t
                      :type-prescription :none
                      :verify-guards nil))
      (lem/vector$a/defuns::recognizer vector)))

  (local
    (defun creator ()
      (declare (xargs :guard t
                      :type-prescription :none
                      :verify-guards nil))
      (lem/vector$a/defuns::creator)))

  (local
    (defun fixer (vector)
      (declare (xargs :guard t
                      :type-prescription :none
                      :verify-guards nil))
      (lem/vector$a/defuns::fixer vector)))

  (defthm fixer-def
    (equal (fixer vector)
           (if (recognizer vector)
               vector
               (creator)))
    :rule-classes :definition
    :hints
    (("Goal"
      :in-theory (enable lem/vector$a/defuns::fixer))))

  (local
    (defun length (vector)
      (declare (xargs :guard t
                      :type-prescription :none
                      :verify-guards nil))
      (lem/vector$a/defuns::length vector)))

  (local
    (defun resizer (length vector)
      (declare (xargs :guard t
                      :type-prescription :none
                      :verify-guards nil))
      (lem/vector$a/defuns::resizer length vector)))

  (local
    (defun accessor (index vector)
      (declare (xargs :guard t
                      :type-prescription :none
                      :verify-guards nil))
      (lem/vector$a/defuns::accessor index vector)))

  (local
    (defun updater (index element vector)
      (declare (xargs :guard t
                      :type-prescription :none
                      :verify-guards nil))
      (lem/vector$a/defuns::updater index element vector)))

  (local
    (defun equiv-rec (bound vector1 vector2)
      (declare (xargs :guard (natp bound)
                      :type-prescription :none
                      :verify-guards nil))
      (if (zp bound)
          t
          (let ((bound (1- bound)))
            (and (equal (accessor bound vector1)
                        (accessor bound vector2))
                 (equiv-rec bound vector1 vector2))))))

  (defthm equiv-rec-def
    (equal (equiv-rec bound vector1 vector2)
           (if (zp bound)
               t
               (let ((bound (1- bound)))
                 (and (equal (accessor bound vector1)
                             (accessor bound vector2))
                      (equiv-rec bound vector1 vector2)))))
    :rule-classes :definition)

  (defthm recognizer-of-creator
    (recognizer (creator))
    :rule-classes
    ((:forward-chaining :trigger-terms ((creator)))))

  (defthm natp-of-length
    (natp (length vector))
    :rule-classes :type-prescription)

  (defthm recognizer-of-resizer
    (recognizer (resizer length vector))
    :rule-classes
    ((:forward-chaining :trigger-terms
                        ((resizer length vector)))))

  (defthm element-recognizer-of-accessor
    (element-recognizer (accessor index vector))
    :rule-classes
    ((:forward-chaining :trigger-terms ((accessor index vector)))))

  (defthm recognizer-of-updater
    (recognizer (updater index element vector))
    :rule-classes
    ((:forward-chaining :trigger-terms ((updater index element vector)))))

  (defthm length-bad-arg-1
    (implies (not (recognizer vector))
             (equal (length vector)
                    (default-length))))

  (defthm resizer-bad-arg-1
    (implies (not (natp length))
             (equal (resizer length vector)
                    (resizer 0 vector))))

  (defthm resizer-bad-arg-2
    (implies (not (recognizer vector))
             (equal (resizer length vector)
                    (resizer length (creator)))))

  (defthm accessor-bad-arg-1
    (implies (not (natp index))
             (equal (accessor index vector)
                    (accessor 0 vector))))

  (defthm accessor-bad-arg-2
    (implies (not (recognizer vector))
             (equal (accessor index vector)
                    (initial-element))))

  (defthm updater-bad-arg-1
    (implies (not (natp index))
             (equal (updater index element vector)
                    (updater 0 element vector))))

  (defthm updater-bad-arg-2
    (implies (not (element-recognizer element))
             (equal (updater index (element-fixer element) vector)
                    (updater index element vector))))

  (defthm updater-bad-arg-3
    (implies (not (recognizer vector))
             (equal (updater index element vector)
                    (updater index element (creator)))))

  (defthm length-of-creator
    (equal (length (creator))
           (default-length)))

  (defthm length-of-resizer-weak
    (implies (natp length)
             (equal (length (resizer length vector))
                    length)))

  (defthm length-of-updater
    (equal (length (updater index element vector))
           (length vector)))

  (defthm accessor-oob-weak
    (implies (and (integerp index)
                  (<= (length vector) index))
             (equal (accessor index vector)
                    (initial-element))))

  (defthm accessor-of-creator
    (equal (accessor index (creator))
           (initial-element)))

  (defthm accessor-of-resizer-weak
    (implies (and (natp index)
                  (natp length))
             (equal (accessor index (resizer length vector))
                    (if (< index length)
                        (accessor index vector)
                        (initial-element)))))

  (defthm accessor-of-updater-weak
    (implies (and (natp index1)
                  (natp index2)
                  (< index2 (length vector))
                  (element-recognizer element))
             (equal (accessor index1 (updater index2 element vector))
                    (if (equal index1 index2)
                        element
                        (accessor index1 vector)))))

  (defthm updater-oob-weak
    (implies (and (integerp index)
                  (<= (length vector) index)
                  (recognizer vector))
             (equal (updater index element vector)
                    vector)))

  (defthmd vector-equality
    (implies (or (recognizer vector1)
                 (recognizer vector2))
             (equal (equal vector1 vector2)
                    (and (recognizer vector1)
                         (recognizer vector2)
                         (equal (length vector1)
                                (length vector2))
                         (equiv-rec (length vector1) vector1 vector2))))
    :hints
    (("Goal"
      :use ((:instance (:functional-instance
                        lem/vector$a/defuns::vector-equality
                        (lem/vector$a/defuns::equiv-rec equiv-rec))
                       (lem/vector$a/defuns::vector1 vector1)
                       (lem/vector$a/defuns::vector2 vector2)))))))


;;;; `FIXER'
(defthm recognizer-of-fixer
  (recognizer (fixer vector))
  :rule-classes
  ((:forward-chaining :trigger-terms ((fixer vector)))))

(defthm fixer-when-recognizer
  (implies (recognizer vector)
           (equal (fixer vector) vector)))

(defthm fixer-when-not-recognizer
  (implies (not (recognizer vector))
           (equal (fixer vector) (creator))))

(local
  (encapsulate ()
    (defthm length-of-fixer
      (equal (length (fixer vector))
             (length vector)))

    (defthm resizer-of-fixer
      (equal (resizer length (fixer vector))
             (resizer length vector)))

    (defthm accessor-of-fixer
      (equal (accessor index (fixer vector))
             (accessor index vector)))

    (defthm updater-of-fixer
      (equal (updater index element (fixer vector))
             (updater index element vector)))))

(local
  (in-theory
    (disable fixer-def)))


;;;; `EQUIV-REC'
(local
  (defun equiv-rec-induction (bound vector1 vector2)
    (declare (xargs :guard (natp bound)))
    (if (zp bound)
        (list bound vector1 vector2)
        (equiv-rec-induction (1- bound) vector1 vector2))))

(local
  (defthm equiv-rec-ind
    t
    :rule-classes
    ((:induction :pattern (equiv-rec bound vector1 vector2)
                 :scheme (equiv-rec-induction bound vector1 vector2)))))

(defthm equiv-rec-tp
  (booleanp (equiv-rec bound vector1 vector2))
  :rule-classes :type-prescription)

(defthm equiv-rec-reflexive
  (equiv-rec b x x))

(defthmd equiv-rec-symmetric
  (implies (equiv-rec b x y)
           (equiv-rec b y x))
  :rule-classes
  ((:rewrite :loop-stopper ((x y equiv-rec)))))

(defthm equiv-rec-transitive
  (implies (and (equiv-rec b x y)
                (equiv-rec b y z))
           (equiv-rec b x z))
  :rule-classes nil)

(local
  (defthm equiv-rec-of-fixer
    (and (equal (equiv-rec bound (fixer vector1) vector2)
                (equiv-rec bound vector1 vector2))
         (equal (equiv-rec bound vector2 (fixer vector1))
                (equiv-rec bound vector1 vector2)))))


;;;; `EQUIV'
(defun equiv (vector1 vector2)
  (declare (xargs :guard t
                  :type-prescription :none))
  (and (equal (length vector1) (length vector2))
       (equiv-rec (length vector1) vector1 vector2)))

(defthm equiv-tp
  (booleanp (equiv vector1 vector2))
  :rule-classes :type-prescription)

(defthm equiv-def
  (equal (equiv vector1 vector2)
         (equal (fixer vector1) (fixer vector2)))
  :rule-classes :definition
  :hints
  (("Goal"
    :in-theory (enable vector-equality))))

(in-theory
  (disable equiv))

(defequiv equiv)


;;;; Congruences
(encapsulate ()
  (local
    (in-theory
      (enable natp
              nfix
              nat-equiv
              fixer-def)))

  (defequiv element-equiv)

  (defcong element-equiv equal (element-fixer element) 1)

  (defthm element-fixer-mod-element-equiv
    (element-equiv (element-fixer element) element))

  (defcong equiv equal (length vector) 1)

  (defcong nat-equiv equal (resizer length vector) 1)

  (defcong equiv equal (resizer length vector) 2)

  (defcong nat-equiv equal (accessor index vector) 1)

  (defcong equiv equal (accessor index vector) 2)

  (defcong nat-equiv equal (updater index element vector) 1)

  (defcong element-equiv equal (updater index element vector) 2
    :hints
    (("Goal"
      :in-theory (disable updater-bad-arg-2)
      :use ((:instance updater-bad-arg-2)
            (:instance updater-bad-arg-2
                       (element element-equiv))))))

  (defcong equiv equal (updater index element vector) 3)

  (defcong equiv equal (fixer vector) 1)

  (defthm fixer-mod-equiv
    (equiv (fixer vector) vector))

  (defcong nat-equiv equal (equiv-rec bound vector1 vector2) 1)

  (defcong equiv equal (equiv-rec bound vector1 vector2) 2)

  (defcong equiv equal (equiv-rec bound vector1 vector2) 3))


;;;; Bounding Theorems
(encapsulate ()
  (local
    (in-theory
      (enable nfix
              fixer-def)))

  (defthm accessor-oob
    (implies (<= (length vector) (nfix index))
             (equal (accessor index vector)
                    (initial-element))))

  (defthm updater-oob
    (implies (<= (length vector) (nfix index))
             (equal (updater index element vector)
                    (fixer vector)))))


;;;; Composition Theorems
(defthm length-of-resizer
  (equal (length (resizer length vector))
         (nfix length))
  :hints
  (("Goal"
    :in-theory (disable length-of-resizer-weak)
    :use ((:instance length-of-resizer-weak
                     (length (nfix length)))))))

(defthm accessor-of-resizer
  (equal (accessor index (resizer length vector))
         (if (< (nfix index) (nfix length))
             (accessor index vector)
             (initial-element)))
  :hints
  (("Goal"
    :in-theory (disable accessor-of-resizer-weak)
    :use ((:instance accessor-of-resizer-weak
                     (index (nfix index))
                     (length (nfix length)))))))

(defthm accessor-of-updater
  (equal (accessor index1 (updater index2 element vector))
         (cond
           ((<= (length vector) (nfix index1))
            (initial-element))
           ((nat-equiv index1 index2)
            (element-fixer element))
           (t
            (accessor index1 vector))))
  :hints
  (("Goal"
    :in-theory (e/d (nat-equiv)
                    (accessor-of-updater-weak))
    :use ((:instance accessor-of-updater-weak
                     (index1 (nfix index1))
                     (index2 (nfix index2))
                     (element (element-fixer element))
                     (vector (fixer vector)))))))

(local
  (in-theory
    (enable vector-equality)))

(local
  (defthm resizer-of-creator-lemma
    (equiv-rec bound
               (resizer (default-length) (creator))
               (creator))))

(defthm resizer-of-creator
  (implies (nat-equiv length (default-length))
           (equal (resizer length (creator))
                  (creator))))

(local
  (defthm resizer-of-length-lemma
    (equiv-rec bound
               vector
               (resizer (length vector) vector))))

(defthm resizer-of-length
  (equal (resizer (length vector) vector)
         (fixer vector)))

(local
  (defthm resizer-of-resizer-lemma-1
    (implies (<= (nfix length1) (nfix length2))
             (equiv-rec bound
                        (resizer length1 (resizer length2 vector))
                        (resizer length1 vector)))))

(local
  (defthm resizer-of-resizer-lemma-2
    (implies (<= (length vector) (nfix length2))
             (equiv-rec bound
                        (resizer length1 (resizer length2 vector))
                        (resizer length1 vector)))))

(defthm resizer-of-resizer
  (implies (or (<= (nfix length1) (nfix length2))
               (<= (length vector) (nfix length2)))
           (equal (resizer length1 (resizer length2 vector))
                  (resizer length1 vector))))

(local
  (defthm resizer-of-updater-lemma-1
    (implies (and (< (nfix index) (nfix length))
                  (< (nfix index) (length vector)))
             (equiv-rec bound
                        (resizer length (updater index element vector))
                        (updater index element (resizer length vector))))))

(local
  (defthm resizer-of-updater-lemma-2
    (implies (not (and (< (nfix index) (nfix length))
                       (< (nfix index) (length vector))))
             (equiv-rec bound
                        (resizer length (updater index element vector))
                        (resizer length vector)))))

(defthm resizer-of-updater
  (equal (resizer length (updater index element vector))
         (if (and (< (nfix index) (nfix length))
                  (< (nfix index) (length vector)))
             (updater index element (resizer length vector))
             (resizer length vector))))

(local
  (in-theory
    (disable element-equiv-rw)))

(local
  (defthm updater-of-creator-lemma
    (equiv-rec bound
               (updater index (initial-element) (creator))
               (creator))))

(defthm updater-of-creator
  (implies (element-equiv element (initial-element))
           (equal (updater index element (creator))
                  (creator))))

(local
  (defthm updater-of-resizer-lemma
    (equiv-rec bound
               (updater index
                        (accessor index vector)
                        (resizer length vector))
               (resizer length vector))))

(defthm updater-of-resizer
  (implies (element-equiv element (accessor index vector))
           (equal (updater index element (resizer length vector))
                  (resizer length vector))))

(local
  (defthm updater-of-accessor-lemma
    (equiv-rec bound
               vector
               (updater index1 (accessor index1 vector)
                        vector))))

(defthm updater-of-accessor
  (implies (element-equiv (accessor index1 vector)
                          (accessor index2 vector))
           (equal (updater index1 (accessor index2 vector) vector)
                  (fixer vector))))

(local
  (defthm updater-of-updater-same-lemma
    (equiv-rec bound
               (updater index1 element
                        (updater index1 element2 vector))
               (updater index1 element vector))))

(defthm updater-of-updater-same
  (implies (nat-equiv index1 index2)
           (equal (updater index1 element (updater index2 element2 vector))
                  (updater index1 element vector))))

(local
  (defthm updater-of-updater-diff-lemam
    (implies (not (nat-equiv index1 index2))
             (equiv-rec bound
                        (updater index1 element1
                                 (updater index2 element2 vector))
                        (updater index2 element2
                                 (updater index1 element1 vector))))))

(defthm updater-of-updater-diff
  (implies (not (nat-equiv index1 index2))
           (equal (updater index1 element1 (updater index2 element2 vector))
                  (updater index2 element2 (updater index1 element1 vector))))
  :rule-classes
  ((:rewrite :loop-stopper ((index1 index2 updater)))))


;;;; Constraints
(defconst *exports* '(name
                      default-length
                      initial-element
                      element-recognizer
                      element-fixer
                      element-equiv

                      recognizer
                      creator
                      fixer
                      length
                      resizer
                      accessor
                      updater
                      equiv-rec
                      equiv))

(encapsulate ()
  (local
    (include-book "../../utilities/top"))

  (make-event
    `(defconst *constraints*
       ',(collect-constraint-info *exports* (w state)))))
