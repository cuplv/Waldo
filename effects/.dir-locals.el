(
 (fstar-mode . ((eval . (let ((cur_dir (file-truename (locate-dominating-file default-directory ".dir-locals.el"))))
    (progn
		(setq-local fstar-subp-prover-args (append fstar-subp-prover-args (list 
            "--include" (concat cur_dir "/.."))))
    ))))))
