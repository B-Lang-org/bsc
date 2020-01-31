;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; for bsv mode 
(add-to-list 'load-path (concat (getenv "BLUESPEC_HOME") "/util/emacs"))
(load "bsv-mode")

;; for bsv snippets
(setq bsv-snippets-path (concat (getenv "BLUESPEC_HOME") "/util/emacs/bsv-snippets"))
(add-to-list 'load-path bsv-snippets-path)
(load "bsv-snippets")
