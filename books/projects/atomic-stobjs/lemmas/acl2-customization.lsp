
(ld "vector-c.acl2")
(ld "vector-a.acl2")
(ld "hash-table-c.acl2")
(ld "hash-table-a.acl2")
(set-verify-guards-eagerness 2)
(set-warnings-as-errors t '("double-rewrite" "free") state)
