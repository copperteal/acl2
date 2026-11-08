
(in-package "ACL2")

(local
  (include-book "std/basic/arith-equiv-defs" :dir :system))

(defun-inline nat-equiv (x y)
  (declare (xargs :normalize nil
                  :guard (and (natp x) (natp y))
                  :verify-guards t))
  (equal (nfix x) (nfix y)))

(defthm nat-equiv-is-an-equivalence
  (and (booleanp (nat-equiv x y))
       (nat-equiv x x)
       (implies (nat-equiv x y)
                (nat-equiv y x))
       (implies (and (nat-equiv x y)
                     (nat-equiv y z))
                (nat-equiv x z)))
  :rule-classes (:equivalence))
