
(in-package "ACL2")

(include-book "nat-defuns")

(local
  (include-book "std/basic/nfix" :dir :system))

(defthm natp-of-nfix
  (natp (nfix x)))

(defthm nfix-when-natp
  (implies (natp x)
           (equal (nfix x) x)))

(defthm nat-equiv-implies-equal-nfix-1
  (implies (nat-equiv x x-equiv)
           (equal (nfix x)
                  (nfix x-equiv)))
  :rule-classes (:congruence))

(defthm nfix-under-nat-equiv
  (nat-equiv (nfix x) x)
  :rule-classes (:rewrite :rewrite-quoted-constant))

(in-theory
  (disable natp
           nfix
           nat-equiv))
