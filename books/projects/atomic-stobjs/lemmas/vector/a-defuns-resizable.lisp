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


(in-package "LEM/VECTOR$A/DEFUNS")
(set-verify-guards-eagerness 2)


;;;; Element Constraints
(encapsulate (((name) => *)
              ((default-length) => *)
              ((initial-element) => *)
              ((element-recognizer *) => *)
              ((element-fixer *) => *))
  (local
    (defun name ()
      (declare (xargs :guard t
                      :type-prescription :none
                      :verify-guards nil))
      :||))

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
      0))

  (defthm default-length-tp
    (natp (default-length))
    :rule-classes :type-prescription)

  (local
    (defun initial-element ()
      (declare (xargs :guard t
                      :type-prescription :none
                      :verify-guards nil))
      nil))

  (local
    (defun element-recognizer (element)
      (declare (xargs :guard t
                      :type-prescription :none
                      :verify-guards nil)
               (ignore element))
      t))

  (defthm element-recognizer-of-initial-element
    (element-recognizer (initial-element))
    :rule-classes
    ((:forward-chaining :trigger-terms ((initial-element)))))

  (local
    (defun element-fixer (element)
      (declare (xargs :guard t
                      :type-prescription :none
                      :verify-guards nil))
      element))

  (defthm element-recognizer-of-element-fixer
    (element-recognizer (element-fixer element))
    :rule-classes
    ((:forward-chaining :trigger-terms ((element-fixer element)))))

  (defthm element-fixer-when-element-recognizer
    (implies (element-recognizer element)
             (equal (element-fixer element)
                    element))))


;;;; Shared Definitions
(defun recognizer (vector)
  (declare (xargs :guard t
                  :type-prescription :none))
  (if (consp vector)
      (and (element-recognizer (car vector))
           (recognizer (cdr vector)))
      (equal vector (name))))

(defun creator-rec (length)
  (declare (xargs :guard (natp length)
                  :type-prescription :none))
  (if (zp length)
      (name)
      (cons (initial-element)
            (creator-rec (1- length)))))

(defun creator ()
  (declare (xargs :guard t
                  :type-prescription :none))
  (creator-rec (default-length)))

(defun fixer (vector)
  (declare (xargs :guard t
                  :type-prescription :none))
  (if (recognizer vector)
      vector
      (creator)))

(defun length (vector)
  (declare (xargs :guard t
                  :type-prescription :none))
  (len (fixer vector)))

(defun resizer-rec (length vector)
  (declare (xargs :guard (natp length)
                  :type-prescription :none))
  (if (zp length)
      (name)
      (if (consp vector)
          (cons (car vector)
                (resizer-rec (1- length)
                             (cdr vector)))
          (cons (initial-element)
                (resizer-rec (1- length)
                             vector)))))

(defun resizer (length vector)
  (declare (xargs :guard t
                  :type-prescription :none))
  (let ((length (nfix length))
        (vector (fixer vector)))
    (resizer-rec length vector)))

(defun accessor-rec (index vector)
  (declare (xargs :guard (natp index)
                  :type-prescription :none))
  (if (zp index)
      (if (consp vector)
          (car vector)
          (initial-element))
      (accessor-rec (1- index)
                    (if (consp vector)
                        (cdr vector)
                        vector))))

(defun accessor (index vector)
  (declare (xargs :guard t
                  :type-prescription :none))
  (let ((index (nfix index))
        (vector (fixer vector)))
    (accessor-rec index vector)))

(defun updater-rec (index element vector)
  (declare (xargs :guard (natp index)
                  :type-prescription :none))
  (if (consp vector)
      (if (zp index)
          (cons element
                (fixer (cdr vector)))
          (cons (car vector)
                (updater-rec (1- index)
                             element
                             (cdr vector))))
      (name)))

(defun updater (index element vector)
  (declare (xargs :guard t
                  :type-prescription :none))
  (let ((index (nfix index))
        (element (element-fixer element))
        (vector (fixer vector)))
    (updater-rec index element vector)))


;;;; Return Types
(local
  (defthm recognizer-of-creator-rec
    (recognizer (creator-rec length))
    :rule-classes
    ((:forward-chaining :trigger-terms ((creator-rec length))))))

(defthm recognizer-of-creator
  (recognizer (creator))
  :rule-classes
  ((:forward-chaining :trigger-terms ((creator)))))

(defthm natp-of-length
  (natp (length vector))
  :rule-classes :type-prescription)

(local
  (defthm recognizer-of-resizer-rec
    (implies (recognizer vector)
             (recognizer (resizer-rec length vector)))))

(defthm recognizer-of-resizer
  (recognizer (resizer length vector))
  :rule-classes
  ((:forward-chaining :trigger-terms
                      ((resizer length vector)))))

(local
  (defthm element-recognizer-of-accessor-rec
    (implies (recognizer vector)
             (element-recognizer (accessor-rec index vector)))))

(local
  (in-theory
    (disable (:e creator-rec))))

(local
  (defthm car-of-creator-rec
    (implies (posp length)
             (equal (car (creator-rec length))
                    (initial-element)))
    :hints
    (("Goal"
      :expand (creator-rec 1)))))

(local
  (defthm cdr-of-creator-rec
    (implies (posp length)
             (equal (cdr (creator-rec length))
                    (creator-rec (1- length))))))

(local
  (defthm consp-of-creator-rec
    (equal (consp (creator-rec length))
           (posp length))))

(defthm element-recognizer-of-accessor
  (element-recognizer (accessor index vector))
  :rule-classes
  ((:forward-chaining :trigger-terms ((accessor index vector)))))

(local
  (defthm recognizer-of-updater-rec
    (implies (and (element-recognizer element)
                  (recognizer vector))
             (recognizer (updater-rec index element vector)))))

(defthm recognizer-of-updater
  (recognizer (updater index element vector))
  :rule-classes
  ((:forward-chaining :trigger-terms ((updater index element vector)))))


;;;; Bad Arguments
(local
  (defthm len-of-creator-rec
    (implies (natp length)
             (equal (len (creator-rec length))
                    length))))

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

(local
  (defun accessor-rec-of-creator-rec-ind (index length)
    (declare (xargs :guard (and (natp index)
                                (natp length))))
    (if (or (zp index)
            (zp length))
        (list index length)
        (accessor-rec-of-creator-rec-ind (1- index)
                                         (1- length)))))

(local
  (defthm accessor-rec-of-creator-rec
    (equal (accessor-rec index (creator-rec length))
           (initial-element))
    :hints
    (("Goal"
      :induct (accessor-rec-of-creator-rec-ind index length)))))

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


;;;; Lengths
(defthm length-of-creator
  (equal (length (creator))
         (default-length)))

(local
  (defthm len-of-resizer-rec
    (implies (natp length)
             (equal (len (resizer-rec length vector))
                    length))))

(defthm length-of-resizer
  (implies (natp length)
           (equal (length (resizer length element))
                  length)))

(local
  (defthm len-of-updater-rec
    (implies (recognizer vector)
             (equal (len (updater-rec index element vector))
                    (len vector)))
    :hints
    (("Goal"
      :in-theory (enable recognizer)))))

(defthm length-of-updater
  (equal (length (updater index element vector))
         (length vector))
  :hints
  (("Goal"
    :in-theory (enable recognizer))))


;;;; Elements
(defthm accessor-oob
  (implies (and (integerp index)
                (<= (length vector) index))
           (equal (accessor index vector)
                  (initial-element))))

(defthm accessor-of-creator
  (equal (accessor index (creator))
         (initial-element)))

(local
  (defthm consp-of-resizer-rec
    (equal (consp (resizer-rec length vector))
           (posp length))))

(local
  (defthm car-of-resizer-rec
    (implies (and (posp length)
                  (recognizer vector))
             (equal (car (resizer-rec length vector))
                    (if (consp vector)
                        (car vector)
                        (initial-element))))))

(local
  (defun accessor-rec-of-resizer-rec-ind (index length vector)
    (declare (xargs :guard (and (natp index)
                                (natp length))))
    (if (or (zp index)
            (zp length))
        (list index length vector)
        (accessor-rec-of-resizer-rec-ind (1- index)
                                         (1- length)
                                         (if (consp vector)
                                             (cdr vector)
                                             vector)))))

(local
  (defthm accessor-rec-of-resizer-rec
    (implies (and (natp index)
                  (natp length)
                  (recognizer vector))
             (equal (accessor-rec index (resizer-rec length vector))
                    (if (< index length)
                        (accessor-rec index vector)
                        (initial-element))))
    :hints
    (("Goal"
      :induct (accessor-rec-of-resizer-rec-ind index length vector)))))

(defthm accessor-of-resizer
  (implies (and (natp index)
                (natp length))
           (equal (accessor index (resizer length vector))
                  (if (< index length)
                      (accessor index vector)
                      (initial-element)))))

(local
  (defthm consp-of-updater-rec
    (equal (consp (updater-rec index element vector))
           (consp vector))))

(local
  (defthm accessor-rec-of-updater-rec
    (implies (and (natp index1)
                  (natp index2)
                  (< index2 (length vector))
                  (element-recognizer element)
                  (recognizer vector))
             (equal (accessor-rec index1 (updater-rec index2 element vector))
                    (if (equal index1 index2)
                        element
                        (accessor-rec index1 vector))))
    :hints
    (("Goal"
      :induct (accessor-rec-of-resizer-rec-ind index1 index2 vector)))))

(defthm accessor-of-updater
  (implies (and (natp index1)
                (natp index2)
                (< index2 (length vector))
                (element-recognizer element))
           (equal (accessor index1 (updater index2 element vector))
                  (if (equal index1 index2)
                      element
                      (accessor index1 vector)))))

(defthm updater-oob
  (implies (and (integerp index)
                (<= (length vector) index)
                (recognizer vector))
           (equal (updater index element vector)
                  vector)))


;;;; EQUIV-REC
(defun equiv-rec (bound vector1 vector2)
  (declare (xargs :guard (natp bound)
                  :type-prescription :none))
  (if (zp bound)
      t
      (let ((bound (1- bound)))
        (and (equal (accessor bound vector1)
                    (accessor bound vector2))
             (equiv-rec bound vector1 vector2)))))

(encapsulate ()
  (local
    (defthm zero-len-rw
      (implies (recognizer vector)
               (equal (equal 0 (len vector))
                      (equal (name) vector)))))

  (local
    (defun subgoal-8-ind (vector1 vector2)
      (declare (xargs :guard t))
      (if (or (atom vector1)
              (atom vector2))
          (list vector1 vector2)
          (subgoal-8-ind (cdr vector1) (cdr vector2)))))

  (local
    (defthm subgoal-8
      (implies (and (recognizer vector1)
                    (not (equal vector1 vector2))
                    (recognizer vector2)
                    (equal (len vector1) (len vector2)))
               (not (equiv-rec (len vector1) vector1 vector2)))
      :hints
      (("Goal"
        :induct (subgoal-8-ind vector1 vector2)))))

  (local
    (defthm equiv-rec-symmetric
      (equal (equiv-rec bound vector1 vector1)
             t)))

  (defthm vector-equality
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
      :do-not-induct t))))


;;;; Constraints
(defconst *interface* '(name
                        default-length
                        initial-element
                        element-recognizer
                        element-fixer
                        recognizer
                        creator-rec
                        creator
                        fixer
                        length
                        resizer-rec
                        resizer
                        accessor-rec
                        accessor
                        updater-rec
                        updater
                        equiv-rec))

(encapsulate ()
  (local
    (include-book "../../utilities/top"))

  (make-event
    `(defconst *defun-constraints*
       ',(collect-constraint-info *interface* (w state)))))

(in-theory
  (disable recognizer
           creator-rec
           creator
           fixer
           length
           resizer-rec
           resizer
           accessor-rec
           accessor
           updater-rec
           updater
           equiv-rec))


;;;; Constraints
(defconst *exports* '(name
                      default-length
                      initial-element
                      element-recognizer
                      element-fixer

                      recognizer
                      creator-rec
                      creator
                      fixer
                      length
                      resizer-rec
                      resizer
                      accessor-rec
                      accessor
                      updater-rec
                      updater
                      equiv-rec))

(encapsulate ()
  (local
    (include-book "../../utilities/top"))

  (make-event
    `(defconst *constraints*
       ',(collect-constraint-info *exports* (w state)))))
