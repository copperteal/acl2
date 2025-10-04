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


(in-package "ACL2")

(include-book "../constructors/define-vector")
(include-book "std/basic/nfix" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)

(defthm nfix-when-not-natp
  (implies (not (natp x))
           (equal (nfix x) 0)))


;;;; Stobj Values
(defstobj foo$c
  a
  :inline t
  :non-memoizable t
  :non-executable t)

(defthm foo$cp-of-create-foo$c
  (foo$cp (create-foo$c)))

(defun create-foo$c$a ()
  (declare (xargs :guard t))
  '(nil))

(defthm create-foo$c$a{rewrite}
  (equal (create-foo$c$a)
         (create-foo$c)))

(in-theory
  (disable (:d create-foo$c$a)
           (:e create-foo$c$a)))

(defun foo$c-fix (x)
  (declare (xargs :guard t))
  (if (foo$cp x)
      x
      (create-foo$c$a)))

(defthm foo$c-fix{rewrite}
  (equal (foo$c-fix x)
         (if (foo$cp x)
             x
             (create-foo$c))))

(in-theory
  (disable (:d create-foo$c)
           (:e create-foo$c)))


(atomic-stobjs::define-vector$a arr/stobj-0 0
  :element-recognizer foo$cp
  :element-fixer foo$c-fix
  :element foo$c
  :initial-element (create-foo$c$a)
  :resizable nil)

(atomic-stobjs::define-vector$a arr/stobj-1 876
  :element-recognizer foo$cp
  :element-fixer foo$c-fix
  :element foo$c
  :initial-element (create-foo$c$a)
  :resizable nil)

(atomic-stobjs::define-vector$a arr/stobj-2 0
  :element-recognizer foo$cp
  :element-fixer foo$c-fix
  :element foo$c
  :initial-element (create-foo$c$a)
  :resizable t)

(atomic-stobjs::define-vector$a arr/stobj-3 876
  :element-recognizer foo$cp
  :element-fixer foo$c-fix
  :element foo$c
  :initial-element (create-foo$c$a)
  :resizable t)


;;;; `DEFINE-VECTOR$A/INSTANCE'
(defmacro define-vector$a/instance (element)
  (declare (xargs :guard (symbolp element)))
  (let* ((witness "ACL2")
         (element-recognizer (symbolicate witness element '-recognizer))
         (element-fixer (symbolicate witness element '-fixer))
         (initial-element (symbolicate witness 'initial- element))

         (booleanp-of-element-recognizer (symbolicate witness 'booleanp-of- element-recognizer))
         (element-recognizer-of-initial-element (symbolicate witness element-recognizer '-of- initial-element))
         (element-recognizer-of-element-fixer (symbolicate witness element-recognizer '-of- element-fixer))
         (element-fixer-when-element-recognizer (symbolicate witness element-fixer '-of- element-recognizer))
         (element-fixer-when-not-element-recognizer (symbolicate witness element-fixer '-when-not- element-recognizer)))
    `(encapsulate (((,element-recognizer *) => *)
                   ((,element-fixer *) => *)
                   ((,initial-element) => *))
       (local
         (defun ,element-recognizer (,element)
           (declare (xargs :guard t)
                    (ignore ,element))
           t))

       (local
         (defun ,initial-element ()
           (declare (xargs :guard t))
           t))

       (local
         (defun ,element-fixer (,element)
           (declare (xargs :guard t))
           (if (,element-recognizer ,element)
               ,element
               (,initial-element))))

       (defthm ,booleanp-of-element-recognizer
         (booleanp (,element-recognizer ,element)))

       (defthm ,element-recognizer-of-initial-element
         (,element-recognizer (,initial-element)))

       (defthm ,element-recognizer-of-element-fixer
         (,element-recognizer (,element-fixer ,element)))

       (defthm ,element-fixer-when-element-recognizer
         (implies (,element-recognizer ,element)
                  (equal (,element-fixer ,element)
                         ,element)))

       (defthm ,element-fixer-when-not-element-recognizer
         (implies (not (,element-recognizer ,element))
                  (equal (,element-fixer ,element)
                         (,initial-element)))))))

(define-vector$a/instance elt-instance)


;;;; Functional Instances
(atomic-stobjs::define-vector$a arr$a/0 #xffff
  :element-recognizer elt-instance-recognizer
  :element-fixer elt-instance-fixer
  :element elt-instance
  :initial-element (initial-elt-instance)
  :resizable t
  :testp t)

(atomic-stobjs::define-vector$a arr$a/1 0
  :element-recognizer elt-instance-recognizer
  :element-fixer elt-instance-fixer
  :element elt-instance
  :initial-element (initial-elt-instance)
  :resizable t
  :testp t)

(atomic-stobjs::define-vector$a arr$a/2 #xffff
  :element-recognizer elt-instance-recognizer
  :element-fixer elt-instance-fixer
  :element elt-instance
  :initial-element (initial-elt-instance)
  :resizable nil
  :testp t)

(atomic-stobjs::define-vector$a arr$a/3 0
  :element-recognizer elt-instance-recognizer
  :element-fixer elt-instance-fixer
  :element elt-instance
  :initial-element (initial-elt-instance)
  :resizable nil
  :testp t)


;;;; Concrete Tests
(atomic-stobjs::define-vector$a arr/0 0)

(atomic-stobjs::define-vector$a arr/1 #xbabe)

(atomic-stobjs::define-vector$a arr/2 0
  :resizable t)

(atomic-stobjs::define-vector$a arr/3 #xbabe
  :resizable t)


;;;; `NATP' Elements
;;; dimensions, element-type, resizable
(atomic-stobjs::define-vector$a arr$a/10-nat-t 10
  :element-recognizer natp
  :element-fixer nfix
  :element nat
  :initial-element 0
  :resizable t)

(atomic-stobjs::define-vector$a arr$a/10-nat-nil 10
  :element-recognizer natp
  :element-fixer nfix
  :element nat
  :initial-element 0)

(atomic-stobjs::define-vector$a arr$a/0-nat-t 0
  :element-recognizer natp
  :element-fixer nfix
  :element nat
  :initial-element 0
  :resizable t)

(atomic-stobjs::define-vector$a arr$a/0-nat-nil 0
  :element-recognizer natp
  :element-fixer nfix
  :element nat
  :initial-element 0)


;;;; `BOOLEANP' Elements
;;; dimensions, element-type, resizable
(atomic-stobjs::define-vector$a arr$a/10-boolean-t 10
  :element-recognizer booleanp
  :element-fixer bool-fix
  :element boolean
  :initial-element t
  :resizable t)

(atomic-stobjs::define-vector$a arr$a/10-boolean-nil 10
  :element-recognizer booleanp
  :element-fixer bool-fix
  :element boolean
  :initial-element t)

(atomic-stobjs::define-vector$a arr$a/0-boolean-t 0
  :element-recognizer booleanp
  :element-fixer bool-fix
  :element boolean
  :initial-element t
  :resizable t)

(atomic-stobjs::define-vector$a arr$a/0-boolean-nil 0
  :element-recognizer booleanp
  :element-fixer bool-fix
  :element boolean
  :initial-element t)
