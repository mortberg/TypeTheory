((coq-mode
  . ((eval . 
          (progn
            (make-local-variable 'coq-prog-args)
            (if (not (memq 'agda-input features))
                (load "~/code/coq/TypeTheory/agda-input"))
            (set-input-method "Agda")
            (setq coq-prog-args `("-emacs" "-indices-matter" "-type-in-type"
				  "-R" ,(expand-file-name (locate-dominating-file buffer-file-name ".dir-locals.el")) "TypeTheory" )))))))
