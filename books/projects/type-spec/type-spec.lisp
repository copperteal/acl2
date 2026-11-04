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


(in-package "TYPE-SPEC")

(include-book "projects/apply/top" :dir :system)

#!ACL2
(encapsulate ()
  (local
    (include-book "std/lists/remove-duplicates" :dir :system))

  (local
    (include-book "std/util/defredundant" :dir :system))

  (make-event
    `(std::defredundant :names (revappend-without-guard
                                rev
                                hons-remove-duplicates1
                                hons-remove-duplicates))))


;;;; `INTERVAL-DESIGNATOR-P'
(defun interval-designator-p (designator type-spec)
; A valid upper or lower bound for a numeric interval compound type specifier as
; described in the Common Lisp HyperSpec:
; https://www.lispworks.com/documentation/HyperSpec/Body/12_af.htm
  (declare (xargs :guard t
                  :type-prescription
                  (booleanp (interval-designator-p designator type-spec))))
  (flet ((type-check (designator type-spec)
; Check that the numeric designator is properly typed
           (case type-spec
             (integer
              (integerp designator))
             (rational
              (rationalp designator))
             (real
              (real/rationalp designator)))))
    (cond
      ((not (member-eq type-spec *compound-real-type-specifier-names*))
       'nil)
      ((symbolp designator)
       (eq designator '*))
      ((consp designator)
       (and (null (cdr designator))
            (type-check (car designator) type-spec)))
      (t
       (type-check designator type-spec)))))


;;;; `ACL2-TYPE-SPEC-P'
(defun acl2-type-spec-p (type-spec)
; Determine if `TYPE-SPEC' is a valid ACL2 type specifier as described on the
; doc page: https://acl2.org/doc/?topic=ACL2____TYPE-SPEC
  (declare (xargs :guard t
                  :type-prescription
                  (booleanp (acl2-type-spec-p type-spec))))
  (cond
    ((symbolp type-spec)
     (and (member-eq type-spec *atomic-type-specifiers*)
          t))
    ((consp type-spec)
     (let ((name (car type-spec))
           (params (cdr type-spec)))
       (and (symbolp name)
            (member-eq name *compound-type-specifier-names*)
            (case name
              ((and or) ; (name . (type1 ... typek))
               (if (consp params)
                   (and (acl2-type-spec-p (car params))
                        (acl2-type-spec-p (cons name (cdr params))))
                   (null params)))
              (complex ; (complex . (type-spec))
               ;; NOTE: `COMPLEX' is disjoint from `REAL'
               (and (consp params)
                    (null (cdr params))
                    (let ((type-spec (car params)))
                      (or (and (symbolp type-spec)
                               (and (member-eq type-spec *atomic-real-subtype-specifiers*)
                                    t))
                          (and (consp type-spec)
                               (symbolp (car type-spec))
                               (member-eq (car type-spec) *compound-real-type-specifier-names*)
                               (acl2-type-spec-p type-spec))))))
              ((integer real rational) ; (name . (i j))
               (and (consp params)
                    (consp (cdr params))
                    (null (cddr params))
                    (and (interval-designator-p (first params) name)
                         (interval-designator-p (second params) name))))
              (member ; (member . (x1 ... xn))
               (eqlable-listp params))
              (mod ; (mod . (i))
               (and (consp params)
                    (null (cdr params))
                    (let ((param (car params)))
                      (and (integerp param)
                           (< 0 param)))))
              (not ; (not . (type-spec))
               (and (consp params)
                    (null (cdr params))
                    (acl2-type-spec-p (car params))))
              (satisfies ; (satisfies . (predicate))
               (and (consp params)
                    (null (cdr params))
                    (let ((predicate (car params)))
                      ;; `WORLD' is inaccessible
                      (acl2::legal-variablep predicate))))
              ((signed-byte unsigned-byte) ; (name . (size))
               (and (consp params)
                    (null (cdr params))
                    (let ((size (car params)))
                      (and (integerp size)
                           (< 0 size)))))
              (string ; (string . (max))
               (and (consp params)
                    (null (cdr params))
                    (let ((max (car params)))
                      (and (integerp max)
                           (<= 0 max)))))))))))

(defthm acl2-type-spec-p-cr
  (implies (acl2-type-spec-p type-spec)
           (or (symbolp type-spec)
               (and (consp type-spec)
                    (true-listp type-spec))))
  :rule-classes :compound-recognizer)

(defthm acl2-type-spec-p-when-atom
  (implies (atom type-spec)
           (iff (acl2-type-spec-p type-spec)
                (member type-spec *atomic-type-specifiers*))))

(defwarrant acl2-type-spec-p)


;;;; `TYPEP$RUNTIME'
(defun typep$runtime (object type-spec)
  (declare (xargs :guard (acl2-type-spec-p type-spec)
                  :type-prescription :none))
  (and (mbt (acl2-type-spec-p type-spec))
       (cond
         ((symbolp type-spec)
          (case type-spec
            (atom
             (atom object))
            (bit
             (bitp object))
            (character
             (characterp object))
            (complex
             (complex/complex-rationalp object))
            (cons
             (consp object))
            (double-float
             (dfp object))
            ((integer signed-byte)
             (integerp object))
            (list
             (listp object))
            ;; If `TYPE-SPEC' is `NIL', vacuously return `NIL'.
            (null
             (null object))
            (number
             (acl2-numberp object))
            (ratio
             (and (rationalp object)
                  (not (integerp object))))
            (rational
             (rationalp object))
            (real
             (real/rationalp object))
            (standard-char
             (and (characterp object)
                  (standard-char-p object)))
            (string
             (stringp object))
            (symbol
             (symbolp object))
            ((t)
             t)
            (unsigned-byte
             (and (integerp object)
                  (<= 0 object)))))
         ((consp type-spec)
          (let ((name (car type-spec))
                (params (cdr type-spec)))
            (case name
              ((and or) ; (name . (type1 ... typek))
               (if (consp params)
                   (let ((bool (typep$runtime object (car params))))
                     (case name
                       (or
                        (or bool
                            (typep$runtime object (cons name (cdr params)))))
                       (and
                        (and bool
                             (typep$runtime object (cons name (cdr params)))))))
                   (case name
                     (or
                      nil)
                     (and
                      t))))
              (complex ; (complex . (type-spec))
               (let ((type-spec (car params)))
                 (and (complex/complex-rationalp object)
                      (typep$runtime (realpart object) type-spec)
                      (typep$runtime (imagpart object) type-spec))))
              ((integer real rational) ; (name . (i j))
               (let ((i (first params))
                     (j (second params)))
                 (and (typep$runtime object name)
                      (cond
                        ((symbolp i)
                         t)
                        ((consp i)
                         (< (car i) object))
                        (t
                         (<= i object)))
                      (cond
                        ((symbolp j)
                         t)
                        ((consp j)
                         (< object (car j)))
                        (t
                         (<= object j))))))
              (member ; (member . (x1 ... xn))
               (member object params))
              (mod ; (mod . (i))
               (and (integerp object)
                    (<= 0 object)
                    (< object (car params))))
              (not ; (not . (type-spec))
               (not (typep$runtime object (car params))))
              (satisfies ; (satisfies . (predicate))
               (apply$ (car params) (list object)))
              ((signed-byte unsigned-byte) ; (name . (size))
               (let ((size (car params)))
                 (case name
                   (signed-byte
                    (signed-byte-p size object))
                   (unsigned-byte
                    (unsigned-byte-p size object)))))
              (string ; (string . (max))
               (and (stringp object)
                    (int= (length object) (car params))))))))))

(defthm typep$runtime-typically-booleanp
  (implies (or (atom type-spec)
               (not (member (car type-spec)
                            '(and or member satisfies))))
           (booleanp (typep$runtime object type-spec)))
  :rule-classes nil)


;;;; `TYPEP$EXPANSION'
(defun typep$expansion (object type-spec)
  (declare (xargs :guard (acl2-type-spec-p type-spec)
                  :type-prescription
                  (or (booleanp (typep$expansion object type-spec))
                      (and (consp (typep$expansion object type-spec))
                           (true-listp (typep$expansion object type-spec))))))
  (and (mbt (acl2-type-spec-p type-spec))
       (if (symbolp type-spec)
           (case type-spec
             (atom
              `(atom ,object))
             (bit
              `(bitp ,object))
             (character
              `(characterp ,object))
             (complex
              `(complex/complex-rationalp ,object))
             (cons
              `(consp ,object))
             (double-float
              `(dfp ,object))
             ((integer signed-byte)
              `(integerp ,object))
             (list
              `(listp ,object))
             (null
              `(null ,object))
             (number
              `(acl2-numberp ,object))
             (ratio
              `(and (rationalp ,object)
                    (not (integerp ,object))))
             (rational
              `(rationalp ,object))
             (real
              `(real/rationalp ,object))
             (standard-char
              `(and (characterp ,object)
                    (standard-char-p ,object)))
             (string
              `(stringp ,object))
             (symbol
              `(symbolp ,object))
             ((t)
              't)
             (unsigned-byte
              `(and (integerp ,object)
                    (<= 0 ,object)))
             (t
              'nil))
           ;; (consp type-spec)
           (let ((name (car type-spec))
                 (params (cdr type-spec)))
             (flet ((flatten (name recognizer)
                      (declare (type symbol name))
                      (if (and (consp recognizer)
                               (eq (car recognizer) name))
                          (cdr recognizer)
                          (list recognizer))))
               (case name
                 ((and or)
                  (cond
                    ;; (name)
                    ((endp params)
                     (case name
                       (or
                        'nil)
                       (and
                        't)))
                    ;; (name . (type))
                    ((endp (cdr params))
                     (typep$expansion object (car params)))
                    ;; (name . (type1 ... typek))
                    (t
                     (acl2::hons-remove-duplicates
                      (append (list name)
                              (flatten name (typep$expansion object (car params)))
                              (flatten name (typep$expansion object (cons name (cdr params)))))))))
                 (complex ; (complex . (type-spec))
                  (let ((type-spec (car params)))
                    (append `(and (complex/complex-rationalp ,object))
                            (flatten 'and (typep$expansion `(realpart ,object) type-spec))
                            (flatten 'and (typep$expansion `(imagpart ,object) type-spec)))))
                 ((integer real rational) ; (name . (i j))
                  (let* ((i (first params))
                         (j (second params))
                         (recognizer (typep$expansion object name))
                         (lower (and (not (symbolp i))
                                     (if (consp i)
                                         `(< ,(car i) ,object)
                                         `(<= ,i ,object))))
                         (upper (and (not (symbolp j))
                                     (if (consp j)
                                         `(< ,object ,(car j))
                                         `(<= ,object ,j)))))
                    (if (or lower upper)
                        `(and ,recognizer
                              ,@(and lower (list lower))
                              ,@(and upper (list upper)))
                        recognizer)))
                 (member ; (member . (x1 ... xn))
                  `(member ,object ',params))
                 (mod ; (mod . (i))
                  `(and (integerp ,object)
                        (<= 0 ,object)
                        (< ,object ,(car params))))
                 (not ; (not . (type-spec))
                  `(not ,(typep$expansion object (car params))))
                 (satisfies ; (satisfies . (predicate))
                  `(apply$ ',(car params) (list ,object)))
                 ((signed-byte unsigned-byte) ; (name . (size))
                  (let ((size (car params)))
                    (case name
                      (signed-byte
                       `(signed-byte-p ,size ,object))
                      (unsigned-byte
                       `(unsigned-byte-p ,size ,object)))))
                 (string ; (string . (max))
                  `(and (stringp ,object)
                        (int= (length ,object) ',(car params))))))))))

(defwarrant typep$expansion)


;;;; `TYPEP$'
(defmacro typep$ (object type-spec)
  (declare (xargs :guard t))
; If `TYPE-SPEC' is a quoted constant and `OBJECT' is not, then we macro expand
; into the appropriate conjunction or disjunction of recognizers applied to
; `OBJECT'.  Otherwise, we place code for runtime checking.
  (if (and (quotep type-spec)
           (acl2-type-spec-p (cadr type-spec)))
      (if (quotep object)
          `(typep$runtime ,object ,type-spec)
; We do a test expansion to see if the result is composite.  If so, we wrap the
; body in a LET, similar to DEFABBREV.
          (let* ((type-spec (cadr type-spec))
                 (expansion (typep$expansion 'object type-spec)))
            (if (and (consp expansion)
                     (member-eq (car expansion) '(and or)))
                `(let ((object ,object))
                   ,expansion)
                (typep$expansion object type-spec))))
      `(typep$runtime ,object ,type-spec)))

(add-macro-fn typep$ typep$runtime)


;;;; Atomic Specifier Rewrite Theorems
(defthm typep$-atom
  (equal (typep$runtime object 'atom)
         (typep$ object 'atom)))

(defthm typep$-bit
  (equal (typep$runtime object 'bit)
         (typep$ object 'bit)))

(defthm typep$-character
  (equal (typep$runtime object 'character)
         (typep$ object 'character)))

(defthm typep$-complex/atomic
  (equal (typep$runtime object 'complex)
         (typep$ object 'complex)))

(defthm typep$-cons
  (equal (typep$runtime object 'cons)
         (typep$ object 'cons)))

(defthm typep$-double-float
  (equal (typep$runtime object 'double-float)
         (typep$ object 'double-float)))

(defthm typep$-integer/atomic
  (equal (typep$runtime object 'integer)
         (typep$ object 'integer)))

(defthm typep$-list
  (equal (typep$runtime object 'list)
         (typep$ object 'list)))

(defthm typep$-nil
  (equal (typep$runtime object 'nil)
         (typep$ object 'nil)))

(defthm typep$-null
  (equal (typep$runtime object 'null)
         (typep$ object 'null)))

(defthm typep$-number
  (equal (typep$runtime object 'number)
         (typep$ object 'number)))

(defthm typep$-ratio
  (equal (typep$runtime object 'ratio)
         (typep$ object 'ratio)))

(defthm typep$-rational/atomic
  (equal (typep$runtime object 'rational)
         (typep$ object 'rational)))

(defthm typep$-real/atomic
  (equal (typep$runtime object 'real)
         (typep$ object 'real)))

(defthm typep$-signed-byte/atomic
  (equal (typep$runtime object 'signed-byte)
         (typep$ object 'signed-byte)))

(defthm typep$-standard-char
  (equal (typep$runtime object 'standard-char)
         (typep$ object 'standard-char)))

(defthm typep$-string/atomic
  (equal (typep$runtime object 'string)
         (typep$ object 'string)))

(defthm typep$-symbol
  (equal (typep$runtime object 'symbol)
         (typep$ object 'symbol)))

(defthm typep$-t
  (equal (typep$runtime object 't)
         (typep$ object 't)))

(defthm typep$-unsigned-byte/atomic
  (equal (typep$runtime object 'unsigned-byte)
         (typep$ object 'unsigned-byte)))


;;;; Compound Specifier Rewrite Theorems
(defthm typep$-and
  (implies (and (consp type-spec)
                (equal (car type-spec) 'and))
           (equal (typep$ object type-spec)
                  (let ((type-specs (cdr type-spec)))
                    (or (null type-specs)
                        (and (typep$ object (car type-specs))
                             (typep$ object (cons 'and (cdr type-specs)))))))))

(defthm typep$-complex/compound
  (implies (and (consp type-spec)
                (equal (car type-spec) 'complex))
           (equal (typep$ object type-spec)
                  (and (acl2-type-spec-p type-spec)
                       (let ((type-spec (cadr type-spec)))
                         (and (complex-rationalp object)
                              (if (consp type-spec)
                                  (member (car type-spec) *compound-real-type-specifier-names*)
                                  (member type-spec *atomic-real-subtype-specifiers*))
                              (typep$ (realpart object) type-spec)
                              (typep$ (imagpart object) type-spec)))))))

(defthm typep$-integer/compound
  (implies (and (consp type-spec)
                (equal (car type-spec) 'integer))
           (equal (typep$ object type-spec)
                  (and (acl2-type-spec-p type-spec)
                       (let ((i (cadr type-spec))
                             (j (caddr type-spec)))
                         (and (integerp object)
                              (interval-designator-p i 'integer)
                              (interval-designator-p j 'integer)
                              (cond
                                ((equal i '*))
                                ((consp i)
                                 (< (car i) object))
                                (t
                                 (<= i object)))
                              (cond
                                ((equal j '*))
                                ((consp j)
                                 (< object (car j)))
                                (t
                                 (<= object j)))))))))

(defthm typep$-member
  (implies (and (consp type-spec)
                (equal (car type-spec) 'member))
           (equal (typep$ object type-spec)
                  (and (eqlable-listp (cdr type-spec))
                       (member object (cdr type-spec))))))

(defthm typep$-mod
  (implies (and (consp type-spec)
                (equal (car type-spec) 'mod))
           (equal (typep$ object type-spec)
                  (and (acl2-type-spec-p type-spec)
                       (let ((i (cadr type-spec)))
                         (and (integerp object)
                              (<= 0 object)
                              (integerp i)
                              (< object i)))))))

(defthm typep$-not
  (implies (and (consp type-spec)
                (equal (car type-spec) 'not))
           (equal (typep$ object type-spec)
                  (and (acl2-type-spec-p type-spec)
                       (let ((type-spec (cadr type-spec)))
                         (and (acl2-type-spec-p type-spec)
                              (not (typep$ object type-spec))))))))

(defthm typep$-or
  (implies (and (consp type-spec)
                (equal (car type-spec) 'or))
           (equal (typep$ object type-spec)
                  (let ((type-specs (cdr type-spec)))
                    (and (consp type-specs)
                         (acl2-type-spec-p (car type-specs))
                         (acl2-type-spec-p (cons 'or (cdr type-specs)))
                         (or (typep$ object (car type-specs))
                             (typep$ object (cons 'or (cdr type-specs)))))))))

(defthm typep$-rational/compound
  (implies (and (consp type-spec)
                (equal (car type-spec) 'rational))
           (equal (typep$ object type-spec)
                  (and (acl2-type-spec-p type-spec)
                       (let ((i (cadr type-spec))
                             (j (caddr type-spec)))
                         (and (rationalp object)
                              (interval-designator-p i 'rational)
                              (interval-designator-p j 'rational)
                              (cond
                                ((equal i '*))
                                ((consp i)
                                 (< (car i) object))
                                (t
                                 (<= i object)))
                              (cond
                                ((equal j '*))
                                ((consp j)
                                 (< object (car j)))
                                (t
                                 (<= object j)))))))))

(defthm typep$-real/compound
  (implies (and (consp type-spec)
                (equal (car type-spec) 'real))
           (equal (typep$ object type-spec)
                  (and (acl2-type-spec-p type-spec)
                       (let ((i (cadr type-spec))
                             (j (caddr type-spec)))
                         (and (real/rationalp object)
                              (interval-designator-p i 'real)
                              (interval-designator-p j 'real)
                              (cond
                                ((equal i '*))
                                ((consp i)
                                 (< (car i) object))
                                (t
                                 (<= i object)))
                              (cond
                                ((equal j '*))
                                ((consp j)
                                 (< object (car j)))
                                (t
                                 (<= object j)))))))))

(defthm typep$-satisfies
  (implies (and (consp type-spec)
                (equal (car type-spec) 'satisfies))
           (equal (typep$ object type-spec)
                  (and (acl2-type-spec-p type-spec)
                       (let ((predicate (cadr type-spec)))
                         (and (symbolp predicate)
                              (apply$ predicate (list object))))))))

(defthm typep$-signed-byte/compound
  (implies (and (consp type-spec)
                (equal (car type-spec) 'signed-byte))
           (equal (typep$ object type-spec)
                  (and (acl2-type-spec-p type-spec)
                       (signed-byte-p (cadr type-spec) object)))))

(defthm typep$-string/compound
  (implies (and (consp type-spec)
                (equal (car type-spec) 'string))
           (equal (typep$ object type-spec)
                  (and (acl2-type-spec-p type-spec)
                       (let ((max (cadr type-spec)))
                         (and (stringp object)
                              (integerp max)
                              (<= 0 max)
                              (equal (length object) max)))))))

(defthm typep$-unsigned-byte/compound
  (implies (and (consp type-spec)
                (equal (car type-spec) 'unsigned-byte))
           (equal (typep$ object type-spec)
                  (and (acl2-type-spec-p type-spec)
                       (let ((i (cadr type-spec)))
                         (and (unsigned-byte-p i object)
                              (< 0 i)))))))

(defthm typep$-is-total
  (implies (not (acl2-type-spec-p type-spec))
           (not (typep$ object type-spec))))


;;;; Epilogue
(in-theory
  (disable interval-designator-p
           acl2-type-spec-p
           typep$runtime
           typep$expansion))

(deftheory theory
  '((:e interval-designator-p)
    (:t interval-designator-p)
    (:e acl2-type-spec-p)
    (:t acl2-type-spec-p)
    acl2-type-spec-p-cr
    acl2-type-spec-p-when-atom
    apply$-warrant-acl2-type-spec-p-necc
    apply$-acl2-type-spec-p
    (:e typep$runtime)
    (:t typep$runtime)
    (:e typep$expansion)
    (:t typep$expansion)
    apply$-warrant-typep$expansion-necc
    apply$-typep$expansion
    typep$-atom
    typep$-bit
    typep$-character
    typep$-complex/atomic
    typep$-cons
    typep$-double-float
    typep$-integer/atomic
    typep$-list
    typep$-nil
    typep$-null
    typep$-number
    typep$-ratio
    typep$-rational/atomic
    typep$-real/atomic
    typep$-signed-byte/atomic
    typep$-standard-char
    typep$-string/atomic
    typep$-symbol
    typep$-t
    typep$-unsigned-byte/atomic
    typep$-and
    typep$-complex/compound
    typep$-integer/compound
    typep$-member
    typep$-mod
    typep$-not
    typep$-or
    typep$-rational/compound
    typep$-real/compound
    typep$-satisfies
    typep$-signed-byte/compound
    typep$-string/compound
    typep$-unsigned-byte/compound
    typep$-is-total))
