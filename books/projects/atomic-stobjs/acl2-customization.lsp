(ld "~/acl2-customization.lsp" :ld-missing-input-ok t)

(in-theory
  (current-theory 'ground-zero))

(ld "type-spec.acl2")
(ld "package.lsp")
(set-verify-guards-eagerness 2)
