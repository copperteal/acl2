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

(include-book "projects/apply/top" :dir :system)


;;;; `INTERVAL-DESIGNATOR-P'
(defun interval-designator-p (designator type-spec)
  (declare (xargs :guard t))
  (flet ((type-check (designator type-spec)
           (case type-spec
             (integer
              (integerp designator))
             (rational
              (rationalp designator))
             (real
              (real/rationalp designator)))))
    (cond
      ((not (member type-spec *compound-real-type-specifier-names*))
       'nil)
      ((symbolp designator)
       (eq designator '*))
      ((consp designator)
       (and (null (cdr designator))
            (type-check (car designator) type-spec)))
      (t
       (type-check designator type-spec)))))

(local
  (thm ; ensure `INTERVAL-DESIGNATOR-P' is known to return a boolean
    (booleanp (interval-designator-p designator type-spec))
    :hints
    (("Goal"
      :in-theory '((:d booleanp)
                   (:t interval-designator-p))))))


;;;; `MEMBERP'
(defun-inline memberp-eq (x list)
  (declare (xargs :guard (and (symbolp x)
                              (true-listp list))))
  (and (member x list :test 'eq)
       t))

(defun-inline memberp-eql (x list)
  (declare (xargs :guard (and (eqlablep x)
                              (true-listp list))))
  (and (member x list :test 'eql)
       t))

(defun-inline memberp-equal (x list)
  (declare (xargs :guard (true-listp list)))
  (and (member x list :test 'equal)
       t))

(defmacro memberp (x list)
  `(memberp-equal ,x ,list))

(add-macro-fn memberp memberp-equal)

(defthm memberp-eq-rw
  (equal (memberp-eq x list)
         (memberp x list)))

(in-theory
  (disable memberp-eq))

(defthm memberp-eql-rw
  (equal (memberp-eql x list)
         (memberp x list)))

(in-theory
  (disable memberp-eql))

(defthm memberp-iff-member
  (iff (memberp x list)
       (member x list))
  :rule-classes
  (:rewrite
   (:forward-chaining :trigger-terms
                      ((member x list))
                      :corollary
                      (implies (memberp x list)
                               (member x list)))))

(in-theory
  (disable memberp-equal))


;;;; `ACL2-TYPE-SPEC-P'
(defun acl2-type-spec-p (type-spec)
  (declare (xargs :guard t))
  (cond
    ((symbolp type-spec)
     (memberp-eq type-spec *atomic-type-specifiers*))
    ((consp type-spec)
     (let ((name (car type-spec))
           (params (cdr type-spec)))
       (and (symbolp name)
            (member name *compound-type-specifier-names* :test 'eq)
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
                               (memberp-eq type-spec *atomic-real-subtype-specifiers*))
                          (and (consp type-spec)
                               (symbolp (car type-spec))
                               (member (car type-spec) *compound-real-type-specifier-names*
                                       :test 'eq)
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
                      (symbolp predicate))))
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

(defwarrant acl2-type-spec-p)

(local
  (thm ; ensure `ACL2-TYPE-SPEC-P' is known to return a boolean
    (booleanp (acl2-type-spec-p type-spec))
    :hints
    (("Goal"
      :in-theory '((:d booleanp)
                   (:t acl2-type-spec-p))))))

(defthm acl2-type-spec-p-cr
  (implies (acl2-type-spec-p type-spec)
           (or (symbolp type-spec)
               (and (consp type-spec)
                    (true-listp type-spec))))
  :rule-classes :compound-recognizer)

(defthm acl2-type-spec-p-when-atom
  (implies (atom type-spec)
           (equal (acl2-type-spec-p type-spec)
                  (memberp type-spec *atomic-type-specifiers*))))


;;;; `TYPEP$RUNTIME'
(defun typep$runtime (object type-spec)
  (declare (xargs :guard (acl2-type-spec-p type-spec)))
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
             (or (consp object)
                 (null object)))
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
                        ((symbolp i))
                        ((consp i)
                         (< (car i) object))
                        (t
                         (<= i object)))
                      (cond
                        ((symbolp j))
                        ((consp j)
                         (< object (car j)))
                        (t
                         (<= object j))))))
              (member ; (member . (x1 ... xn))
               (memberp object params))
              (mod ; (mod . (i))
               (and (integerp object)
                    (<= 0 object)
                    (< object (car params))))
              (not ; (not . (type-spec))
               (not (typep$runtime object (car params))))
              (satisfies ; (satisfies . (predicate))
               (and (apply$ (car params) (list object))
                    t))
              ((signed-byte unsigned-byte) ; (name . (size))
               (let ((size (car params)))
                 (case name
                   (signed-byte
                    (signed-byte-p size object))
                   (unsigned-byte
                    (unsigned-byte-p size object)))))
              (string ; (string . (max))
               (and (stringp object)
                    (equal (length object) (car params))))))))))

(local
  (thm ; ensure `TYPEP$RUNTIME' is known to return a boolean
    (booleanp (typep$runtime object type-spec))
    :hints
    (("Goal"
      :in-theory '((:d booleanp)
                   (:t typep$runtime))))))


;;;; `TYPEP$TRANSFORM'
(defun typep$transform (object type-spec)
  (declare (xargs :guard (acl2-type-spec-p type-spec)))
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
         `(or (consp ,object)
              (null ,object)))
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
                 (if (and (consp recognizer)
                          (eq (car recognizer) name))
                     (cdr recognizer)
                     (list recognizer)))
               (dedup (list)
                 ;; TODO: Flatten nested ANDs/ORs and remove duplicates
                 ;; as `HONS-REMOVE-DUPLICATES' but with `EQUAL' instead
                 ;; of `EQL'.  `DEDUP' runs in quadratic time.
                 (reverse (remove-duplicates-equal (reverse list)))))
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
                (typep$transform object (car params)))
               ;; (name . (type1 ... typek))
               (t
                (dedup
                 (append (list name)
                         (flatten name (typep$transform object (car params)))
                         (flatten name (typep$transform object (cons name (cdr params)))))))))
            (complex ; (complex . (type-spec))
             (let ((type-spec (car params)))
               (append `(and (complex/complex-rationalp ,object))
                       (flatten 'and (typep$transform `(realpart ,object) type-spec))
                       (flatten 'and (typep$transform `(imagpart ,object) type-spec)))))
            ((integer real rational) ; (name . (i j))
             (let* ((i (first params))
                    (j (second params))
                    (recognizer (typep$transform object name))
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
             `(memberp ,object ',params))
            (mod ; (mod . (i))
             `(and (integerp ,object)
                   (<= 0 ,object)
                   (< ,object ,(car params))))
            (not ; (not . (type-spec))
             `(not ,(typep$transform object (car params))))
            (satisfies ; (satisfies . (predicate))
             `(and (apply$ ',(car params) (list ,object))
                   t))
            ((signed-byte unsigned-byte) ; (name . (size))
             (let ((size (car params)))
               (case name
                 (signed-byte
                  `(signed-byte-p ,size ,object))
                 (unsigned-byte
                  `(unsigned-byte-p ,size ,object)))))
            (string ; (string . (max))
             `(and (stringp ,object)
                   (equal (length ,object) ',(car params)))))))))

(defwarrant typep$transform)

(defthm typep$transform-tp
  (or (booleanp (typep$transform object type-spec))
      (and (consp (typep$transform object type-spec))
           (true-listp (typep$transform object type-spec))))
  :rule-classes :type-prescription)


;;;; `TYPEP$'
(defmacro typep$ (object type-spec)
  (declare (xargs :guard t))
  (if (and (consp type-spec)
           (eq (car type-spec) 'quote)
           (consp (cdr type-spec))
           (acl2-type-spec-p (cadr type-spec))
           (null (cddr type-spec)))
      (let* ((type-spec (cadr type-spec))
             (transform (typep$transform 'object type-spec)))
        (if (and (consp transform)
                 (member (car transform) '(and or) :test 'eq))
            `(let ((object ,object))
               ,transform)
            (typep$transform object type-spec)))
      `(typep$runtime ,object ,type-spec)))

(add-macro-fn typep$ typep$runtime)


;;;; Atomic Specifier Rewrite Theorems
(defthm typep$-atom
  (implies (equal type-spec 'atom)
           (equal (typep$ object type-spec)
                  (atom object))))

(defthm typep$-bit
  (implies (equal type-spec 'bit)
           (equal (typep$ object type-spec)
                  (bitp object))))

(defthm typep$-character
  (implies (equal type-spec 'character)
           (equal (typep$ object type-spec)
                  (characterp object))))

(defthm typep$-complex/atomic
  (implies (equal type-spec 'complex)
           (equal (typep$ object type-spec)
                  (complex/complex-rationalp object))))

(defthm typep$-cons
  (implies (equal type-spec 'cons)
           (equal (typep$ object type-spec)
                  (consp object))))

(defthm typep$-double-float
  (implies (equal type-spec 'double-float)
           (equal (typep$ object type-spec)
                  (dfp object))))

(defthm typep$-integer/atomic
  (implies (equal type-spec 'integer)
           (equal (typep$ object type-spec)
                  (integerp object))))

(defthm typep$-list
  (implies (equal type-spec 'list)
           (equal (typep$ object type-spec)
                  (listp object))))

(defthm typep$-nil
  (implies (not type-spec)
           (not (typep$ object type-spec))))

(defthm typep$-null
  (implies (equal type-spec 'null)
           (equal (typep$ object type-spec)
                  (null object))))

(defthm typep$-number
  (implies (equal type-spec 'number)
           (equal (typep$ object type-spec)
                  (acl2-numberp object))))

(defthm typep$-ratio
  (implies (equal type-spec 'ratio)
           (equal (typep$ object type-spec)
                  (and (rationalp object)
                       (not (integerp object))))))

(defthm typep$-rational/atomic
  (implies (equal type-spec 'rational)
           (equal (typep$ object type-spec)
                  (rationalp object))))

(defthm typep$-real/atomic
  (implies (equal type-spec 'real)
           (equal (typep$ object type-spec)
                  (real/rationalp object))))

(defthm typep$-signed-byte/atomic
  (implies (equal type-spec 'signed-byte)
           (equal (typep$ object type-spec)
                  (integerp object))))

(defthm typep$-standard-char
  (implies (equal type-spec 'standard-char)
           (equal (typep$ object type-spec)
                  (standard-char-p object))))

(defthm typep$-string/atomic
  (implies (equal type-spec 'string)
           (equal (typep$ object type-spec)
                  (stringp object))))

(defthm typep$-symbol
  (implies (equal type-spec 'symbol)
           (equal (typep$ object type-spec)
                  (symbolp object))))

(defthm typep$-t
  (implies (equal type-spec t)
           (typep$ object type-spec)))

(defthm typep$-unsigned-byte/atomic
  (implies (equal type-spec 'unsigned-byte)
           (equal (typep$ object type-spec)
                  (and (integerp object)
                       (<= 0 object)))))


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
                (equal (car type-spec) 'complex)
                (force (acl2-type-spec-p type-spec)))
           (equal (typep$ object type-spec)
                  (let ((type-spec (cadr type-spec)))
                    (and (complex-rationalp object)
                         (if (consp type-spec)
                             (memberp (car type-spec) *compound-real-type-specifier-names*)
                             (memberp type-spec *atomic-real-subtype-specifiers*))
                         (typep$ (realpart object) type-spec)
                         (typep$ (imagpart object) type-spec))))))

(defthm typep$-integer/compound
  (implies (and (consp type-spec)
                (equal (car type-spec) 'integer)
                (force (acl2-type-spec-p type-spec)))
           (equal (typep$ object type-spec)
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
                            (<= object j))))))))

(defthm typep$-member
  (implies (and (consp type-spec)
                (equal (car type-spec) 'member))
           (equal (typep$ object type-spec)
                  (and (eqlable-listp (cdr type-spec))
                       (memberp object (cdr type-spec))))))

(defthm typep$-mod
  (implies (and (consp type-spec)
                (equal (car type-spec) 'mod)
                (force (acl2-type-spec-p type-spec)))
           (equal (typep$ object type-spec)
                  (let ((i (cadr type-spec)))
                    (and (integerp object)
                         (<= 0 object)
                         (integerp i)
                         (< object i))))))

(defthm typep$-not
  (implies (and (consp type-spec)
                (equal (car type-spec) 'not)
                (force (acl2-type-spec-p type-spec)))
           (equal (typep$ object type-spec)
                  (let ((type-spec (cadr type-spec)))
                    (and (acl2-type-spec-p type-spec)
                         (not (typep$ object type-spec)))))))

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
                (equal (car type-spec) 'rational)
                (force (acl2-type-spec-p type-spec)))
           (equal (typep$ object type-spec)
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
                            (<= object j))))))))

(defthm typep$-real/compound
  (implies (and (consp type-spec)
                (equal (car type-spec) 'real)
                (force (acl2-type-spec-p type-spec)))
           (equal (typep$ object type-spec)
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
                            (<= object j))))))))

(defthm typep$-satisfies
  (implies (and (consp type-spec)
                (equal (car type-spec) 'satisfies)
                (force (acl2-type-spec-p type-spec)))
           (equal (typep$ object type-spec)
                  (let ((predicate (cadr type-spec)))
                    (and (symbolp predicate)
                         (apply$ predicate (list object))
                         t)))))

(defthm typep$-signed-byte/compound
  (implies (and (consp type-spec)
                (equal (car type-spec) 'signed-byte)
                (force (acl2-type-spec-p type-spec)))
           (equal (typep$ object type-spec)
                  (signed-byte-p (cadr type-spec) object))))

(defthm typep$-string/compound
  (implies (and (consp type-spec)
                (equal (car type-spec) 'string)
                (force (acl2-type-spec-p type-spec)))
           (equal (typep$ object type-spec)
                  (let ((max (cadr type-spec)))
                    (and (stringp object)
                         (integerp max)
                         (<= 0 max)
                         (equal (length object) max))))))

(defthm typep$-unsigned-byte/compound
  (implies (and (consp type-spec)
                (equal (car type-spec) 'unsigned-byte)
                (force (acl2-type-spec-p type-spec)))
           (equal (typep$ object type-spec)
                  (let ((i (cadr type-spec)))
                    (and (unsigned-byte-p i object)
                         (< 0 i))))))

(defthm typep$-is-total
  (implies (not (acl2-type-spec-p type-spec))
           (not (typep$ object type-spec))))


;;;; Epilogue
(in-theory
  (disable interval-designator-p
           acl2-type-spec-p
           typep$runtime
           typep$transform))

(deftheory type-spec-theory
  '((:e interval-designator-p)
    (:t interval-designator-p)
    (:e memberp-eq$inline)
    (:t memberp-eq$inline)
    (:e memberp-eql$inline)
    (:t memberp-eql$inline)
    (:e memberp-equal$inline)
    (:t memberp-equal$inline)
    memberp-eq-rw
    memberp-eql-rw
    memberp-iff-member
    (:e acl2-type-spec-p)
    (:t acl2-type-spec-p)
    apply$-warrant-acl2-type-spec-p-necc
    apply$-acl2-type-spec-p
    acl2-type-spec-p-cr
    acl2-type-spec-p-when-atom
    (:e typep$runtime)
    (:t typep$runtime)
    (:e typep$transform)
    (:t typep$transform)
    apply$-warrant-typep$transform-necc
    apply$-typep$transform
    (:t typep$transform-tp)
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
