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


(in-package "LEM-VECTOR$ABS")

#||
(include-book "std/lists/top" :dir :system)
||#

(include-book "vector$c")
(include-book "vector$a")
(include-book "../utilities/with-books")
(local
  (include-book "std"))
(set-verify-guards-eagerness 2) ; TODO: propagate

(in-theory
  (disable lem-vector$c::contents-recognizer
           lem-vector$c::recognizer/resizable
           lem-vector$c::recognizer/fixed
           lem-vector$c::length/resizable
           lem-vector$c::length/fixed
           lem-vector$c::resizer/resizable
           lem-vector$c::resizer/fixed
           lem-vector$c::creator
           (:e lem-vector$c::creator)
           lem-vector$c::accessor
           lem-vector$c::updater
           lem-vector$c::fixer/resizable
           lem-vector$c::fixer/fixed
           lem-vector$a::contents-recognizer
           lem-vector$a::recognizer/resizable
           lem-vector$a::recognizer/fixed
           lem-vector$a::creator
           (:e lem-vector$a::creator)
           lem-vector$a::fixer/resizable
           lem-vector$a::fixer/fixed
           lem-vector$a::length/resizable
           lem-vector$a::length/fixed
           lem-vector$a::resizer/resizable
           lem-vector$a::resizer/fixed
           lem-vector$a::accessor/resizable
           lem-vector$a::accessor/fixed
           lem-vector$a::updater/resizable
           lem-vector$a::updater/fixed
           lem-vector$a::contents-equal/resizable
           lem-vector$a::equal/resizable
           lem-vector$a::contents-equal/fixed
           lem-vector$a::equal/fixed))

(defun-sk corr-contents/resizable (vector$c vector$a)
  (declare (xargs :guard t
                  :verify-guards nil))
  (forall index
    (implies (and (natp index)
                  (< index (lem-vector$c::length/resizable vector$c)))
             (equal (lem-vector$c::accessor index vector$c)
                    (lem-vector$a::accessor/resizable index vector$a))))
  :rewrite :direct)

(defun-nx corr/resizable (vector$c vector$a)
  (declare (xargs :guard (and (lem-vector$c::recognizer/resizable vector$c)
                              (lem-vector$a::recognizer/resizable vector$a))
                  :verify-guards nil))
  (and (lem-vector$c::recognizer/resizable vector$c)
       (lem-vector$a::recognizer/resizable vector$a)
       (equal (lem-vector$c::length/resizable vector$c)
              (lem-vector$a::length/resizable vector$a))
       (corr-contents/resizable vector$c vector$a)))

(defun-sk corr-contents/fixed (vector$c vector$a)
  (declare (xargs :guard t
                  :verify-guards nil))
  (forall index
    (implies (and (natp index)
                  (< index (lem-vector$c::length/fixed vector$c)))
             (equal (lem-vector$c::accessor index vector$c)
                    (lem-vector$a::accessor/fixed index vector$a))))
  :rewrite :direct)

(defun-nx corr/fixed (vector$c vector$a)
  (declare (xargs :guard (and (lem-vector$c::recognizer/fixed vector$c)
                              (lem-vector$a::recognizer/fixed vector$a))
                  :verify-guards nil))
  (and (lem-vector$c::recognizer/fixed vector$c)
       (lem-vector$a::recognizer/fixed vector$a)
       (equal (lem-vector$c::length/fixed vector$c)
              (lem-vector$a::length/fixed vector$a))
       (corr-contents/fixed vector$c vector$a)))

(defun hypothesis ()
  (declare (xargs :guard t))
  (and (equal (lem-vector$c::default-length)
              (lem-vector$a::default-length))
       (equal (lem-vector$c::initial-element)
              (lem-vector$a::initial-element))))


;;;; `CREATOR/RESIZABLE'
(defthm creator/resizable{correspondence}
  (implies (hypothesis)
           (corr/resizable (lem-vector$c::creator)
                           (lem-vector$a::creator))))

(defthm creator/resizable{preserved}
  (lem-vector$a::recognizer/resizable (lem-vector$a::creator)))


;;;; `CREATOR/FIXED'
(defthm creator/fixed{correspondence}
  (implies (hypothesis)
           (corr/fixed (lem-vector$c::creator)
                       (lem-vector$a::creator))))

(defthm creator/fixed{preserved}
  (lem-vector$a::recognizer/fixed (lem-vector$a::creator)))


;;;; `FIXER/RESIZABLE'
(defthm fixer/resizable{correspondence}
  (implies (corr/resizable vector$c vector$a)
           (corr/resizable (lem-vector$c::fixer/resizable vector$c)
                           (lem-vector$a::fixer/resizable vector$a))))

(defthm fixer/resizable{preserved}
  (implies (lem-vector$a::recognizer/resizable vector$a)
           (lem-vector$a::recognizer/resizable (lem-vector$a::fixer/resizable vector$a))))


;;;; `FIXER/FIXED'
(defthm fixer/fixed{correspondence}
  (implies (corr/fixed vector$c vector$a)
           (corr/fixed (lem-vector$c::fixer/fixed vector$c)
                       (lem-vector$a::fixer/fixed vector$a))))

(defthm fixer/fixed{preserved}
  (implies (lem-vector$a::recognizer/fixed vector$a)
           (lem-vector$a::recognizer/fixed (lem-vector$a::fixer/fixed vector$a))))


;;;; `LENGTH/RESIZABLE'
(defthm length/resizable{correspondence}
  (implies (corr/resizable vector$c vector$a)
           (equal (lem-vector$c::length/resizable vector$c)
                  (lem-vector$a::length/resizable vector$a))))


;;;; `LENGTH/FIXED'
(defthm length/fixed{correspondence}
  (implies (corr/fixed vector$c vector$a)
           (equal (lem-vector$c::length/fixed vector$c)
                  (lem-vector$a::length/fixed vector$a))))


;;;; `RESIZER/RESIZABLE'
(defthm resizer/resizable{correspondence}
  (implies (and (corr/resizable vector$c vector$a)
                (natp index)
                (hypothesis))
           (corr/resizable (lem-vector$c::resizer/resizable index vector$c)
                           (lem-vector$a::resizer/resizable index vector$a)))
  :hints
  (("Goal"
    :in-theory (disable corr-contents/resizable)
    :expand (corr-contents/resizable
             (lem-vector$c::resizer/resizable index vector$c)
             (lem-vector$a::resizer/resizable index vector$a)))))

(defthm resizer/resizable{preserved}
  (lem-vector$a::recognizer/resizable (lem-vector$a::resizer/resizable index vector$a)))


;;;; `RESIZER/FIXED'
(defthm resizer/fixed{correspondence}
  (implies (and (corr/fixed vector$c vector$a)
                (natp index)
                (hypothesis))
           (corr/fixed (lem-vector$c::resizer/fixed index vector$c)
                       (lem-vector$a::resizer/fixed index vector$a)))
  :hints
  (("Goal"
    :in-theory (disable corr-contents/fixed)
    :expand (corr-contents/fixed
             (lem-vector$c::resizer/fixed index vector$c)
             (lem-vector$a::resizer/fixed index vector$a)))))

(defthm resizer/fixed{preserved}
  (lem-vector$a::recognizer/fixed (lem-vector$a::resizer/fixed index vector$a)))


;;;; `ACCESSOR/RESIZABLE'
(defthm accessor/resizable{correspondence}
  (implies (and (corr/resizable vector$c vector$a)
                (natp index)
                (< index (lem-vector$a::length/resizable vector$a)))
           (equal (lem-vector$c::accessor index vector$c)
                  (lem-vector$a::accessor/resizable index vector$a)))
  :hints
  (("Goal"
    :in-theory (disable corr-contents/resizable))))

(defthm accessor/resizable{guard-thm}
  (implies (and (corr/resizable vector$c vector$a)
                (natp index)
                (< index (lem-vector$a::length/resizable vector$a)))
           (< index (lem-vector$c::length/resizable vector$c))))


;;;; `ACCESSOR/FIXED'
(defthm accessor/fixed{correspondence}
  (implies (and (corr/fixed vector$c vector$a)
                (natp index)
                (< index (lem-vector$a::length/fixed vector$a)))
           (equal (lem-vector$c::accessor index vector$c)
                  (lem-vector$a::accessor/fixed index vector$a)))
  :hints
  (("Goal"
    :in-theory (disable corr-contents/fixed))))

(defthm accessor/fixed{guard-thm}
  (implies (and (corr/fixed vector$c vector$a)
                (natp index)
                (< index (lem-vector$a::length/fixed vector$a)))
           (< index (lem-vector$c::length/fixed vector$c))))


;;;; `UPDATER/RESIZABLE'
(defthm updater/resizable{correspondence}
  (implies (and (corr/resizable vector$c vector$a)
                (natp index)
                (lem-vector$a::element-recognizer value)
                (lem-vector$c::element-recognizer value)
                (< index (lem-vector$a::length/resizable vector$a)))
           (corr/resizable (lem-vector$c::updater index value vector$c)
                           (lem-vector$a::updater/resizable index value vector$a)))
  :hints
  (("Goal"
    :in-theory (disable corr-contents/resizable)
    :expand (corr-contents/resizable
             (lem-vector$c::updater index value vector$c)
             (lem-vector$a::updater/resizable index value vector$a)))))

(defthm updater/resizable{guard-thm}
  (implies (corr/resizable vector$c vector$a)
           (lem-vector$c::recognizer/resizable vector$c)))

(defthm updater/resizable{preserved}
  (lem-vector$a::recognizer/resizable (lem-vector$a::updater/resizable index value vector$a)))


;;;; `UPDATER/FIXED'
(defthm updater/fixed{correspondence}
  (implies (and (corr/fixed vector$c vector$a)
                (natp index)
                (lem-vector$a::element-recognizer value)
                (lem-vector$c::element-recognizer value)
                (< index (lem-vector$a::length/fixed vector$a)))
           (corr/fixed (lem-vector$c::updater index value vector$c)
                       (lem-vector$a::updater/fixed index value vector$a)))
  :hints
  (("Goal"
    :in-theory (disable corr-contents/fixed)
    :expand (corr-contents/fixed
             (lem-vector$c::updater index value vector$c)
             (lem-vector$a::updater/fixed index value vector$a)))))

(defthm updater/fixed{guard-thm}
  (implies (corr/fixed vector$c vector$a)
           (lem-vector$c::recognizer/fixed vector$c)))

(defthm updater/fixed{preserved}
  (lem-vector$a::recognizer/fixed (lem-vector$a::updater/fixed index value vector$a)))
