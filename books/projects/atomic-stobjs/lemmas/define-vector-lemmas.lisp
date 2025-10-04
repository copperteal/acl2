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
;;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS”
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


(in-package "DEFINE-VECTOR")

(deflabel define-vector-lemmas-begin)

(encapsulate (((element-recognizer *) => *)
              ((recognizer *) => *))
  (local
    (defun element-recognizer (x)
      (declare (xargs :guard t)
               (ignorable x))
      t))

  (defthm element-recognizer{type-prescription}
    (booleanp (element-recognizer x))
    :rule-classes :type-prescription)

  (local
    (defun recognizer (x)
      (declare (xargs :guard t))
      (if (consp x)
          (recognizer (cdr x))
          (null x))))

  (defthm recognizer{type-prescription}
    (booleanp (recognizer x))
    :rule-classes :type-prescription)

  (defthm recognizer-when-atom
    (implies (atom x)
             (equal (recognizer x)
                    (null x))))

  (defthm recognizer-when-consp
    (implies (consp x)
             (equal (recognizer x)
                    (and (element-recognizer (car x))
                         (recognizer (cdr x)))))))

(defthm recognizer{compound-recognizer}
  (implies (recognizer x)
           (true-listp x))
  :rule-classes :compound-recognizer)

(defthm recognizer-of-resize-list
  (implies (recognizer lst)
           (equal (recognizer (resize-list lst n default-value))
                  (or (<= (nfix n) (len lst))
                      (element-recognizer default-value)))))

(defthm element-recognizer-of-nth-when-recognizer
  (implies (and (recognizer l)
                (< (nfix n) (len l)))
           (element-recognizer (nth n l))))

(defthm recognizer-of-update-nth
  (implies (and (recognizer l)
                (element-recognizer val)
                (or (element-recognizer nil)
                    (<= key (len l))))
           (recognizer (update-nth key val l))))

(in-theory
  (current-theory 'define-vector-lemmas-begin))
