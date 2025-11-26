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

(include-book "xdoc/top" :dir :system)

(deflabel symbolic-ordinals-begin-label)

(defsection symbolic-ordinals
  :parents (ordinals)
  :short "A library for symbolic reasoning on ordinals."
  :long "<p>The @('symbolic-ordinals') library enforces the distinction between
the @(see ordinals) interface and the @('ordinals') implementation.  Including
this book ensures that @('o<') is enabled and the functions @(tsee
o-first-expt), @(tsee o-first-coeff), @(tsee o-rst), @(tsee o-p), @(tsee
o-finp), and @(tsee make-ord) are disabled.  The theory @('symbolic-ordinals')
contains every theorem in this book.</p>"

  (local
    (in-theory
      (enable o<)))

  ;; `O-FIRST-EXPT'
  (defthm o-first-expt-tp
    (and (implies (o-p ord)
                  (or (consp (o-first-expt ord))
                      (natp (o-first-expt ord))))
         (implies (and (o-p ord)
                       (o-infp ord))
                  (or (consp (o-first-expt ord))
                      (posp (o-first-expt ord)))))
    :rule-classes
    ((:type-prescription :corollary
                         (implies (force (o-p ord))
                                  (or (consp (o-first-expt ord))
                                      (natp (o-first-expt ord)))))
     (:type-prescription :corollary
                         (implies (and (force (o-p ord))
                                       (o-infp ord))
                                  (or (consp (o-first-expt ord))
                                      (posp (o-first-expt ord)))))))

  (defthm o-p-of-o-first-expt
    (implies (force (o-p ord))
             (o-p (o-first-expt ord))))

  (defthm o-first-expt-of-make-ord
    (equal (o-first-expt (make-ord fe fco rst))
           fe))

  (defthm o-first-expt-when-o-finp
    (implies (and (force (o-p ord))
                  (o-finp ord))
             (equal (o-first-expt ord) 0)))

  ;; `O-FIRST-COEFF'
  (defthm o-first-coeff-tp
    (and (implies (o-p ord)
                  (natp (o-first-coeff ord)))
         (implies (and (o-p ord)
                       (o-infp ord))
                  (posp (o-first-coeff ord))))
    :rule-classes
    ((:type-prescription :corollary
                         (implies (force (o-p ord))
                                  (natp (o-first-coeff ord))))
     (:type-prescription :corollary
                         (implies (and (force (o-p ord))
                                       (o-infp ord))
                                  (posp (o-first-coeff ord))))))

  (defthm o-first-coeff-of-make-ord
    (equal (o-first-coeff (make-ord fe fco rst))
           fco))

  (defthm o-first-coeff-when-o-finp
    (implies (and (force (o-p ord))
                  (o-finp ord))
             (equal (o-first-coeff ord) ord)))

  ;; `O-RST'
  (defthm o-rst-tp
    (implies (and (force (o-p ord))
                  (o-infp ord))
             (or (consp (o-rst ord))
                 (natp (o-rst ord))))
    :rule-classes :type-prescription)

  (defthm o-p-of-o-rst
    (implies (force (o-p ord))
             (equal (o-p (o-rst ord))
                    (o-infp ord))))

  (defthm o-rst-of-make-ord
    (equal (o-rst (make-ord fe fco rst))
           rst))

  (defthm o-first-expt-of-o-rst-is-decreasing
    (implies (force (o-p ord))
             (equal (o< (o-first-expt (o-rst ord))
                        (o-first-expt ord))
                    (o-infp ord))))

  ;; `O-P'
  (defthm o-p-cr
    (implies (o-p ord)
             (or (consp ord)
                 (natp ord)))
    :rule-classes :compound-recognizer)

  (defthm natp-implies-o-p
    (implies (natp ord)
             (o-p ord)))

  ;; `O-FINP'
  (defthm o-finp-equals-natp
    (implies (o-p ord)
             (equal (o-finp ord)
                    (natp ord))))

  ;; `MAKE-ORD'
  (defthm make-ord-elim
    (implies (and (force (o-p ord))
                  (o-infp ord))
             (equal (make-ord (o-first-expt ord)
                              (o-first-coeff ord)
                              (o-rst ord))
                    ord))
    :rule-classes :elim)

  (defthm o-p-of-make-ord
    (equal (o-p (make-ord fe fco rst))
           (and (o-p fe)
                (or (o-infp fe)
                    (posp fe))
                (posp fco)
                (o-p rst)
                (o< (o-first-expt rst)
                    fe)))))


;;;; `SYMBOLIC-ORDINALS'
(deflabel symbolic-ordinals-end-label)

(deftheory symbolic-ordinals
  (union-theories
   (set-difference-theories (current-theory 'symbolic-ordinals-end-label)
                            (current-theory 'symbolic-ordinals-begin-label))
   (set-difference-theories '(o<)
                            '(o-first-expt
                              o-first-coeff
                              o-rst
                              o-p
                              o-finp
                              make-ord))))

(in-theory
  (e/d (o<)
       (o-first-expt
        o-first-coeff
        o-rst
        o-p
        o-finp
        make-ord)))
