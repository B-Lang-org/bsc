;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; File: bsv-snippets (this file is the emacs / elisp commands need to enable)
;; Author: Steve Allen sallen@bluespec.com
;; Aug 1, 2012
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; :NOTE:
;; 
;;   you don't need to change anything here
;;

;; this looks for snippet library, and if it finds, it loads it up
(if (not (string= (locate-library "yasnippet.el") nil))
    (progn
      (load "yasnippet")
      (yas/load-directory bsv-snippets-path)
      (add-hook 'bsv-mode-hook
		'(lambda ()
		   (yas/minor-mode-on)))))

;; with this, when you open a file, say, Foo.bsv, you should see this (or something
;; a lot like it in the bottom status bar
;;
;; --:---   Foo.bsv    Top L1  (BSV yas)
;;
;; you will also see a new menu called "YASnippet", which you can also use :)
;;
;; to test..  open a file "Foo.bsv", type "rule<TAB>" in it and see what happens :)
;; (note if there's more than one possible completion, you'll see a menu to select which 
;; one you want... Try "module<TAB>" to see)
;;
;; - highlighted text can be replaced in line
;;
;; - <TAB> moves up one field
;;
;; - any other direction key breaks you out of completing the snippet..
;;
;; afterwards, it's just text.. Edit it as you want
;;
;; finally, there is a list of all snippets in the file
;;   /prj/qct/esldes/users/c_sallen/utils/bsv-snippets/BsvSnippetSummary.txt
