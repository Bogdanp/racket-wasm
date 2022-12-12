((racket-mode . ((eval . (cl-dolist (s '("opcase" "switch"))
                           (put (intern s) 'racket-indent-function #'defun))))))
