
(include-book "projects/type-spec/portcullis" :dir :system)
(ld "package.lsp")
(set-match-free-error t)
(set-verify-guards-eagerness 2)
(set-warnings-as-errors t '("double-rewrite" "free") state)
(reset-prehistory)
