;; bsv-mode.el --- major mode for editing bsv source in Emacs

;; Copyright (C) 1996-2012  Free Software Foundation, Inc.

;; Verilog Mode Author: Michael McNamara (mac@verilog.com),
;;    Wilson Snyder (wsnyder@wsnyder.org)
;; Please see our web sites:
;;    http://www.verilog.com
;;    http://www.veripool.org
;;
;; Keywords: languages

;; This file is part of GNU Emacs.

;; GNU Emacs is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This mode borrows heavily from the Pascal-mode and the cc-mode of Emacs

;; USAGE
;; =====

;; A major mode for editing BSV HDL source code.  When you have
;; entered BSV mode, you may get more info by pressing C-h m. You
;; may also get online help describing various functions by: C-h f
;; <Name of function you want described>

;; KNOWN BUGS / BUG REPORTS
;; =======================

;; This is beta code and likely has bugs.
;; Please report any issues to the BSC developers, by opening a ticket
;; in the issue database: https://github.com/B-Lang-org/bsc/issues

;; INSTALLING THE MODE
;; ===================

;; An older version of this mode may be already installed as a part of
;; your environment, and one method of updating would be to update
;; your Emacs environment.  Sometimes this is difficult for local
;; political/control reasons, and hence you can always install a
;; private copy (or even a shared copy) which overrides the system
;; default.

;; You can get step by step help in installing this file by going to
;; <http://www.bsv.com/emacs_install.html>

;; The short list of installation instructions are: To set up
;; automatic BSV mode, put this file in your load path, and put
;; the following in code (please un comment it first!) in your
;; .emacs, or in your site's site-load.el

; (autoload 'bsv-mode "bsv-mode" "BSV mode" t )
; (setq auto-mode-alist (cons  '("\\.bsv\\'" . bsv-mode) auto-mode-alist))

;; Be sure to examine at the help for bsv-auto, and the other
;; bsv-auto-* functions for some major coding time savers.
;;
;; If you want to customize BSV mode to fit your needs better,
;; you may add the below lines (the values of the variables presented
;; here are the defaults). Note also that if you use an Emacs that
;; supports custom, it's probably better to use the custom menu to
;; edit these.  If working as a member of a large team these settings
;; should be common across all users (in a site-start file), or set
;; in Local Variables in every file.  Otherwise, different people's
;; AUTO expansion may result different whitespace changes.
;;
; ;; Enable syntax highlighting of **all** languages
; (global-font-lock-mode t)
;
; ;; User customization for BSV mode
; (setq bsv-indent-level             3
;       bsv-indent-level-module      3
;       bsv-indent-level-declaration 3
;       bsv-indent-level-behavioral  3
;       bsv-indent-level-directive   1
;       bsv-case-indent              2
;       bsv-auto-newline             nil
;       bsv-auto-indent-on-newline   t
;       bsv-tab-always-indent        t
;       bsv-auto-endcomments         t
;       bsv-minimum-comment-distance 40
;       bsv-indent-begin-after-if    t
;       bsv-auto-lineup              'declarations
;       bsv-highlight-p1800-keywords nil
;	bsv-linter			 "my_lint_shell_command"
;	)

;; 

;;; History:

;;; Code:

(require 'cl)

;; This variable will always hold the version number of the mode
(defconst bsv-mode-version "725"
  "Version of this BSV mode.")
(defconst bsv-mode-release-date "2011-11-27-GNU"
  "Release date of this BSV mode.")
(defconst bsv-mode-release-emacs t
  "If non-nil, this version of BSV mode was released with Emacs itself.")

(defun bsv-version ()
  "Inform caller of the version of this file."
  (interactive)
  (message "Using bsv-mode version %s" bsv-mode-version))

;; Insure we have certain packages, and deal with it if we don't
;; Be sure to note which Emacs flavor and version added each feature.
(eval-when-compile
  ;; Provide stuff if we are XEmacs
  (when (featurep 'xemacs)
    (condition-case nil
        (require 'easymenu)
      (error nil))
    (condition-case nil
        (require 'regexp-opt)
      (error nil))
    ;; Bug in 19.28 through 19.30 skeleton.el, not provided.
    (condition-case nil
        (load "skeleton")
      (error nil))
    (condition-case nil
        (if (fboundp 'when)
            nil ;; fab
          (defmacro when (cond &rest body)
            (list 'if cond (cons 'progn body))))
      (error nil))
    (condition-case nil
        (if (fboundp 'unless)
            nil ;; fab
          (defmacro unless (cond &rest body)
            (cons 'if (cons cond (cons nil body)))))
      (error nil))
    (condition-case nil
        (if (fboundp 'store-match-data)
            nil ;; fab
          (defmacro store-match-data (&rest args) nil))
      (error nil))
    (condition-case nil
        (if (fboundp 'char-before)
            nil ;; great
          (defmacro char-before (&rest body)
            (char-after (1- (point)))))
      (error nil))
    (condition-case nil
        (if (fboundp 'when)
            nil ;; fab
          (defsubst point-at-bol (&optional N)
            (save-excursion (beginning-of-line N) (point))))
      (error nil))
    (condition-case nil
        (if (fboundp 'when)
            nil ;; fab
          (defsubst point-at-eol (&optional N)
            (save-excursion (end-of-line N) (point))))
      (error nil))
    (condition-case nil
        (require 'custom)
      (error nil))
    (condition-case nil
        (if (fboundp 'match-string-no-properties)
            nil ;; great
          (defsubst match-string-no-properties (num &optional string)
            "Return string of text matched by last search, without text properties.
NUM specifies which parenthesized expression in the last regexp.
 Value is nil if NUMth pair didn't match, or there were less than NUM pairs.
Zero means the entire text matched by the whole regexp or whole string.
STRING should be given if the last search was by `string-match' on STRING."
            (if (match-beginning num)
                (if string
                    (let ((result
                           (substring string
				      (match-beginning num) (match-end num))))
                      (set-text-properties 0 (length result) nil result)
                      result)
                  (buffer-substring-no-properties (match-beginning num)
                                                  (match-end num)
                                                  (current-buffer)))))
	  )
      (error nil))
    (if (and (featurep 'custom) (fboundp 'custom-declare-variable))
        nil ;; We've got what we needed
      ;; We have the old custom-library, hack around it!
      (defmacro defgroup (&rest args)  nil)
      (defmacro customize (&rest args)
        (message
	 "Sorry, Customize is not available with this version of Emacs"))
      (defmacro defcustom (var value doc &rest args)
        `(defvar ,var ,value ,doc))
      )
    (if (fboundp 'defface)
        nil				; great!
      (defmacro defface (var values doc &rest args)
        `(make-face ,var))
      )

    (if (and (featurep 'custom) (fboundp 'customize-group))
        nil ;; We've got what we needed
      ;; We have an intermediate custom-library, hack around it!
      (defmacro customize-group (var &rest args)
        `(customize ,var))
      )

    (unless (boundp 'inhibit-point-motion-hooks)
      (defvar inhibit-point-motion-hooks nil))
    (unless (boundp 'deactivate-mark)
      (defvar deactivate-mark nil))
    )
  ;;
  ;; OK, do this stuff if we are NOT XEmacs:
  (unless (featurep 'xemacs)
    (unless (fboundp 'region-active-p)
      (defmacro region-active-p ()
	`(and transient-mark-mode mark-active))))
  )

;; Provide a regular expression optimization routine, using regexp-opt
;; if provided by the user's elisp libraries
(eval-and-compile
  ;; The below were disabled when GNU Emacs 22 was released;
  ;; perhaps some still need to be there to support Emacs 21.
  (if (featurep 'xemacs)
      (if (fboundp 'regexp-opt)
          ;; regexp-opt is defined, does it take 3 or 2 arguments?
          (if (fboundp 'function-max-args)
              (let ((args (function-max-args `regexp-opt)))
                (cond
                 ((eq args 3) ;; It takes 3
                  (condition-case nil	; Hide this defun from emacses
					;with just a two input regexp
                      (defun bsv-regexp-opt (a b)
                        "Deal with differing number of required arguments for  `regexp-opt'.
         Call 'regexp-opt' on A and B."
                        (regexp-opt a b 't))
                    (error nil))
                  )
                 ((eq args 2) ;; It takes 2
                  (defun bsv-regexp-opt (a b)
                    "Call 'regexp-opt' on A and B."
                    (regexp-opt a b))
                  )
                 (t nil)))
            ;; We can't tell; assume it takes 2
            (defun bsv-regexp-opt (a b)
              "Call 'regexp-opt' on A and B."
              (regexp-opt a b))
            )
        ;; There is no regexp-opt, provide our own
        (defun bsv-regexp-opt (strings &optional paren shy)
          (let ((open (if paren "\\(" "")) (close (if paren "\\)" "")))
            (concat open (mapconcat 'regexp-quote strings "\\|") close)))
        )
    ;; Emacs.
    (defalias 'bsv-regexp-opt 'regexp-opt)))

(eval-and-compile
  ;; Both xemacs and emacs
  (condition-case nil
      (require 'diff) ;; diff-command and diff-switches
    (error nil))
  (condition-case nil
      (require 'compile) ;; compilation-error-regexp-alist-alist
    (error nil))
  (condition-case nil
      (unless (fboundp 'buffer-chars-modified-tick)  ;; Emacs 22 added
	(defmacro buffer-chars-modified-tick () (buffer-modified-tick)))
    (error nil))
  ;; Added in Emacs 24.1
  (condition-case nil
      (unless (fboundp 'prog-mode)
	(define-derived-mode prog-mode fundamental-mode "Prog"))
    (error nil)))

(eval-when-compile
  (defun bsv-regexp-words (a)
    "Call 'regexp-opt' with word delimiters for the words A."
    (concat "\\<" (bsv-regexp-opt a t) "\\>")))
(defun bsv-regexp-words (a)
  "Call 'regexp-opt' with word delimiters for the words A."
  ;; The FAQ references this function, so user LISP sometimes calls it
  (concat "\\<" (bsv-regexp-opt a t) "\\>"))

(defun bsv-easy-menu-filter (menu)
  "Filter `easy-menu-define' MENU to support new features."
  (cond ((not (featurep 'xemacs))
	 menu) ;; GNU Emacs - passthru
	;; XEmacs doesn't support :help.  Strip it.
	;; Recursively filter the a submenu
	((listp menu)
	 (mapcar 'bsv-easy-menu-filter menu))
	;; Look for [:help "blah"] and remove
	((vectorp menu)
	 (let ((i 0) (out []))
	   (while (< i (length menu))
	     (if (equal `:help (aref menu i))
		 (setq i (+ 2 i))
	       (setq out (vconcat out (vector (aref menu i)))
		     i (1+ i))))
	   out))
	(t menu))) ;; Default - ok
;;(bsv-easy-menu-filter
;;  `("BSV" ("MA" ["SAA" nil :help "Help SAA"] ["SAB" nil :help "Help SAA"])
;;     "----" ["MB" nil :help "Help MB"]))

(defun bsv-define-abbrev (table name expansion &optional hook)
  "Filter `define-abbrev' TABLE NAME EXPANSION and call HOOK.
Provides SYSTEM-FLAG in newer Emacs."
  (condition-case nil
      (define-abbrev table name expansion hook 0 t)
    (error
     (define-abbrev table name expansion hook))))

(defun bsv-customize ()
  "Customize variables and other settings used by BSV-Mode."
  (interactive)
  (customize-group 'bsv-mode))

(defun bsv-font-customize ()
  "Customize fonts used by BSV-Mode."
  (interactive)
  (if (fboundp 'customize-apropos)
      (customize-apropos "font-lock-*" 'faces)))

(defun bsv-booleanp (value)
  "Return t if VALUE is boolean.
This implements GNU Emacs 22.1's `booleanp' function in earlier Emacs.
This function may be removed when Emacs 21 is no longer supported."
  (or (equal value t) (equal value nil)))

(defun bsv-insert-last-command-event ()
  "Insert the `last-command-event'."
  (insert (if (featurep 'xemacs)
	      ;; XEmacs 21.5 doesn't like last-command-event
	      last-command-char
	    ;; And GNU Emacs 22 has obsoleted last-command-char
	    last-command-event)))

(defvar bsv-no-change-functions nil
  "True if `after-change-functions' is disabled.
Use of `syntax-ppss' may break, as ppss's cache may get corrupted.")

(defvar bsv-in-hooks nil
  "True when within a `bsv-run-hooks' block.")

(defmacro bsv-run-hooks (&rest hooks)
  "Run each hook in HOOKS using `run-hooks'.
Set `bsv-in-hooks' during this time, to assist AUTO caches."
  `(let ((bsv-in-hooks t))
     (run-hooks ,@hooks)))

(defun bsv-syntax-ppss (&optional pos)
  (when bsv-no-change-functions
    (if bsv-in-hooks
	(bsv-scan-cache-flush)
      ;; else don't let the AUTO code itself get away with flushing the cache,
      ;; as that'll make things very slow
      (backtrace)
      (error "%s: Internal problem; use of syntax-ppss when cache may be corrupt"
	     (bsv-point-text))))
  (if (fboundp 'syntax-ppss)
      (syntax-ppss pos)
    (parse-partial-sexp (point-min) (or pos (point)))))

(defgroup bsv-mode nil
  "Facilitates easy editing of BSV source text."
  :version "22.2"
  :group 'languages)

; (defgroup bsv-mode-fonts nil
;   "Facilitates easy customization fonts used in BSV source text"
;   :link '(customize-apropos "font-lock-*" 'faces)
;  :group 'bsv-mode)

(defgroup bsv-mode-indent nil
  "Customize indentation and highlighting of BSV source text."
  :group 'bsv-mode)

(defgroup bsv-mode-actions nil
  "Customize actions on BSV source text."
  :group 'bsv-mode)

(defgroup bsv-mode-auto nil
  "Customize AUTO actions when expanding BSV source text."
  :group 'bsv-mode)

(defvar bsv-debug nil
  "If set, enable debug messages for `bsv-mode' internals.")

(defcustom bsv-linter
  "echo 'No bsv-linter set, see \"M-x describe-variable bsv-linter\"'"
  "*Unix program and arguments to call to run a lint checker on BSV source.
Depending on the `bsv-set-compile-command', this may be invoked when
you type \\[compile].  When the compile completes, \\[next-error] will take
you to the next lint error."
  :type 'string
  :group 'bsv-mode-actions)
;; We don't mark it safe, as it's used as a shell command

(defcustom bsv-coverage
  "echo 'No bsv-coverage set, see \"M-x describe-variable bsv-coverage\"'"
  "*Program and arguments to use to annotate for coverage BSV source.
Depending on the `bsv-set-compile-command', this may be invoked when
you type \\[compile].  When the compile completes, \\[next-error] will take
you to the next lint error."
  :type 'string
  :group 'bsv-mode-actions)
;; We don't mark it safe, as it's used as a shell command

(defcustom bsv-simulator "bsc -sim "
  "*Program and arguments to use to interpret bsv source."
  :type 'string
  :group 'bsv-mode-actions)
;; We don't mark it safe, as it's used as a shell command

(defcustom bsv-compiler  "bsc -verilog "
  "*Program and arguments to use to compile bsv source."
  :type 'string
  :group 'bsv-mode-actions)
;; We don't mark it safe, as it's used as a shell command

(defcustom bsv-preprocessor
  ;; Very few tools give preprocessed output, so we'll default to BSV-Perl
  "vppreproc __FLAGS__ __FILE__"
  "*Program and arguments to use to preprocess BSV source.
This is invoked with `bsv-preprocess', and depending on the
`bsv-set-compile-command', may also be invoked when you type
\\[compile].  When the compile completes, \\[next-error] will
take you to the next lint error."
  :type 'string
  :group 'bsv-mode-actions)
;; We don't mark it safe, as it's used as a shell command

(defvar bsv-preprocess-history nil
  "History for `bsv-preprocess'.")

(defvar bsv-tool 'bsv-compiler)

(defcustom bsv-highlight-translate-off nil
  "*Non-nil means background-highlight code excluded from translation.
That is, all code between \"// synopsys translate_off\" and
\"// synopsys translate_on\" is highlighted using a different background color
\(face `bsv-font-lock-translate-off-face').

Note: This will slow down on-the-fly fontification (and thus editing).

Note: Activate the new setting in a BSV buffer by re-fontifying it (menu
entry \"Fontify Buffer\").  XEmacs: turn off and on font locking."
  :type 'boolean
  :group 'bsv-mode-indent)
;; Note we don't use :safe, as that would break on Emacsen before 22.0.
(put 'bsv-highlight-translate-off 'safe-local-variable 'bsv-booleanp)

(defcustom bsv-auto-lineup 'declarations
  "*Type of statements to lineup across multiple lines.
If 'all' is selected, then all line ups described below are done.

If 'declaration', then just declarations are lined up with any
preceding declarations, taking into account widths and the like,
so or example the code:
 	reg [31:0] a;
 	reg b;
would become
 	reg [31:0] a;
 	reg        b;

If 'assignment', then assignments are lined up with any preceding
assignments, so for example the code
	a_long_variable <= b + c;
	d = e + f;
would become
	a_long_variable <= b + c;
	d                = e + f;

In order to speed up editing, large blocks of statements are lined up
only when a \\[bsv-pretty-expr] is typed; and large blocks of declarations
are lineup only when \\[bsv-pretty-declarations] is typed."

  :type '(radio (const :tag "Line up Assignments and Declarations" all)
		(const :tag "Line up Assignment statements" assignments )
		(const :tag "Line up Declarations" declarations)
		(function :tag "Other"))
  :group 'bsv-mode-indent )

(defcustom bsv-indent-level 3
  "*Indentation of BSV statements with respect to containing block."
  :group 'bsv-mode-indent
  :type 'integer)
(put 'bsv-indent-level 'safe-local-variable 'integerp)

(defcustom bsv-indent-level-module 3
  "*Indentation of Module level BSV statements (eg always, initial).
Set to 0 to get initial and always statements lined up on the left side of
your screen."
  :group 'bsv-mode-indent
  :type 'integer)
(put 'bsv-indent-level-module 'safe-local-variable 'integerp)

(defcustom bsv-indent-level-declaration 3
  "*Indentation of declarations with respect to containing block.
Set to 0 to get them list right under containing block."
  :group 'bsv-mode-indent
  :type 'integer)
(put 'bsv-indent-level-declaration 'safe-local-variable 'integerp)

(defcustom bsv-indent-declaration-macros nil
  "*How to treat macro expansions in a declaration.
If nil, indent as:
	input [31:0] a;
	input        `CP;
	output       c;
If non nil, treat as:
	input [31:0] a;
	input `CP    ;
	output       c;"
  :group 'bsv-mode-indent
  :type 'boolean)
(put 'bsv-indent-declaration-macros 'safe-local-variable 'bsv-booleanp)

(defcustom bsv-indent-lists t
  "*How to treat indenting items in a list.
If t (the default), indent as:
	always @( posedge a or
	          reset ) begin

If nil, treat as:
	always @( posedge a or
	   reset ) begin"
  :group 'bsv-mode-indent
  :type 'boolean)
(put 'bsv-indent-lists 'safe-local-variable 'bsv-booleanp)

(defcustom bsv-indent-level-behavioral 3
  "*Absolute indentation of first begin in a task or function block.
Set to 0 to get such code to start at the left side of the screen."
  :group 'bsv-mode-indent
  :type 'integer)
(put 'bsv-indent-level-behavioral 'safe-local-variable 'integerp)

(defcustom bsv-indent-level-directive 1
  "*Indentation to add to each level of `ifdef declarations.
Set to 0 to have all directives start at the left side of the screen."
  :group 'bsv-mode-indent
  :type 'integer)
(put 'bsv-indent-level-directive 'safe-local-variable 'integerp)

(defcustom bsv-cexp-indent 2
  "*Indentation of BSV statements split across lines."
  :group 'bsv-mode-indent
  :type 'integer)
(put 'bsv-cexp-indent 'safe-local-variable 'integerp)

(defcustom bsv-case-indent 2
  "*Indentation for case statements."
  :group 'bsv-mode-indent
  :type 'integer)
(put 'bsv-case-indent 'safe-local-variable 'integerp)

(defcustom bsv-auto-newline nil
  "*True means automatically newline after semicolons."
  :group 'bsv-mode-indent
  :type 'boolean)
(put 'bsv-auto-newline 'safe-local-variable 'bsv-booleanp)

(defcustom bsv-auto-indent-on-newline t
  "*True means automatically indent line after newline."
  :group 'bsv-mode-indent
  :type 'boolean)
(put 'bsv-auto-indent-on-newline 'safe-local-variable 'bsv-booleanp)

(defcustom bsv-tab-always-indent t
  "*True means TAB should always re-indent the current line.
A nil value means TAB will only reindent when at the beginning of the line."
  :group 'bsv-mode-indent
  :type 'boolean)
(put 'bsv-tab-always-indent 'safe-local-variable 'bsv-booleanp)

(defcustom bsv-tab-to-comment nil
  "*True means TAB moves to the right hand column in preparation for a comment."
  :group 'bsv-mode-actions
  :type 'boolean)
(put 'bsv-tab-to-comment 'safe-local-variable 'bsv-booleanp)

(defcustom bsv-indent-begin-after-if t
  "*If true, indent begin statements following if, else, while, for and repeat.
Otherwise, line them up."
  :group 'bsv-mode-indent
  :type 'boolean)
(put 'bsv-indent-begin-after-if 'safe-local-variable 'bsv-booleanp)


(defcustom bsv-align-ifelse nil
  "*If true, align `else' under matching `if'.
Otherwise else is lined up with first character on line holding matching if."
  :group 'bsv-mode-indent
  :type 'boolean)
(put 'bsv-align-ifelse 'safe-local-variable 'bsv-booleanp)

(defcustom bsv-minimum-comment-distance 10
  "*Minimum distance (in lines) between begin and end required before a comment.
Setting this variable to zero results in every end acquiring a comment; the
default avoids too many redundant comments in tight quarters."
  :group 'bsv-mode-indent
  :type 'integer)
(put 'bsv-minimum-comment-distance 'safe-local-variable 'integerp)

(defcustom bsv-highlight-p1800-keywords nil
  "*True means highlight words newly reserved by IEEE-1800.
These will appear in `bsv-font-lock-p1800-face' in order to gently
suggest changing where these words are used as variables to something else.
A nil value means highlight these words as appropriate for the SystemBSV
IEEE-1800 standard.  Note that changing this will require restarting Emacs
to see the effect as font color choices are cached by Emacs."
  :group 'bsv-mode-indent
  :type 'boolean)
(put 'bsv-highlight-p1800-keywords 'safe-local-variable 'bsv-booleanp)

(defcustom bsv-highlight-grouping-keywords nil
  "*True means highlight grouping keywords 'begin' and 'end' more dramatically.
If false, these words are in the `font-lock-type-face'; if True then they are in
`bsv-font-lock-ams-face'.  Some find that special highlighting on these
grouping constructs allow the structure of the code to be understood at a glance."
  :group 'bsv-mode-indent
  :type 'boolean)
(put 'bsv-highlight-grouping-keywords 'safe-local-variable 'bsv-booleanp)

(defcustom bsv-highlight-modules nil
  "*True means highlight module statements for `bsv-load-file-at-point'.
When true, mousing over module names will allow jumping to the
module definition.  If false, this is not supported.  Setting
this is experimental, and may lead to bad performance."
  :group 'bsv-mode-indent
  :type 'boolean)
(put 'bsv-highlight-modules 'safe-local-variable 'bsv-booleanp)

(defcustom bsv-highlight-includes t
  "*True means highlight module statements for `bsv-load-file-at-point'.
When true, mousing over include file names will allow jumping to the
file referenced.  If false, this is not supported."
  :group 'bsv-mode-indent
  :type 'boolean)
(put 'bsv-highlight-includes 'safe-local-variable 'bsv-booleanp)

(defcustom bsv-auto-declare-nettype nil
  "*Non-nil specifies the data type to use with `bsv-auto-input' etc.
Set this to \"wire\" if the BSV code uses \"`default_nettype
none\".  Note using `default_nettype none isn't recommended practice; this
mode is experimental."
  :version "24.1"
  :group 'bsv-mode-actions
  :type 'boolean)
(put 'bsv-auto-declare-nettype 'safe-local-variable `stringp)

(defcustom bsv-auto-wire-type nil
  "*Non-nil specifies the data type to use with `bsv-auto-wire' etc.
Set this to \"logic\" for SystemBSV code, or use `bsv-auto-logic'."
  :version "24.1"
  :group 'bsv-mode-actions
  :type 'boolean)
(put 'bsv-auto-wire-type 'safe-local-variable `stringp)

(defcustom bsv-auto-endcomments t
  "*True means insert a comment /* ... */ after 'end's.
The name of the function or case will be set between the braces."
  :group 'bsv-mode-actions
  :type 'boolean)
(put 'bsv-auto-endcomments 'safe-local-variable 'bsv-booleanp)

(defcustom bsv-auto-delete-trailing-whitespace nil
  "*True means to `delete-trailing-whitespace' in `bsv-auto'."
  :version "24.1"
  :group 'bsv-mode-actions
  :type 'boolean)
(put 'bsv-auto-delete-trailing-whitespace 'safe-local-variable 'bsv-booleanp)

(defcustom bsv-auto-ignore-concat nil
  "*True means ignore signals in {...} concatenations for AUTOWIRE etc.
This will exclude signals referenced as pin connections in {...}
from AUTOWIRE, AUTOOUTPUT and friends.  This flag should be set
for backward compatibility only and not set in new designs; it
may be removed in future versions."
  :group 'bsv-mode-actions
  :type 'boolean)
(put 'bsv-auto-ignore-concat 'safe-local-variable 'bsv-booleanp)

(defcustom bsv-auto-read-includes nil
  "*True means to automatically read includes before AUTOs.
This will do a `bsv-read-defines' and `bsv-read-includes' before
each AUTO expansion.  This makes it easier to embed defines and includes,
but can result in very slow reading times if there are many or large
include files."
  :group 'bsv-mode-actions
  :type 'boolean)
(put 'bsv-auto-read-includes 'safe-local-variable 'bsv-booleanp)

(defcustom bsv-auto-save-policy nil
  "*Non-nil indicates action to take when saving a BSV buffer with AUTOs.
A value of `force' will always do a \\[bsv-auto] automatically if
needed on every save.  A value of `detect' will do \\[bsv-auto]
automatically when it thinks necessary.  A value of `ask' will query the
user when it thinks updating is needed.

You should not rely on the 'ask or 'detect policies, they are safeguards
only.  They do not detect when AUTOINSTs need to be updated because a
sub-module's port list has changed."
  :group 'bsv-mode-actions
  :type '(choice (const nil) (const ask) (const detect) (const force)))

(defcustom bsv-auto-star-expand t
  "*Non-nil indicates to expand a SystemBSV .* instance ports.
They will be expanded in the same way as if there was a AUTOINST in the
instantiation.  See also `bsv-auto-star' and `bsv-auto-star-save'."
  :group 'bsv-mode-actions
  :type 'boolean)
(put 'bsv-auto-star-expand 'safe-local-variable 'bsv-booleanp)

(defcustom bsv-auto-star-save nil
  "*Non-nil indicates to save to disk SystemBSV .* instance expansions.
A nil value indicates direct connections will be removed before saving.
Only meaningful to those created due to `bsv-auto-star-expand' being set.

Instead of setting this, you may want to use /*AUTOINST*/, which will
always be saved."
  :group 'bsv-mode-actions
  :type 'boolean)
(put 'bsv-auto-star-save 'safe-local-variable 'bsv-booleanp)

(defvar bsv-auto-update-tick nil
  "Modification tick at which autos were last performed.")

(defvar bsv-auto-last-file-locals nil
  "Text from file-local-variables during last evaluation.")

(defvar bsv-diff-function 'bsv-diff-report
  "*Function to run when `bsv-diff-auto' detects differences.
Function takes three arguments, the original buffer, the
difference buffer, and the point in original buffer with the
first difference.")

;;; Compile support
(require 'compile)
(defvar bsv-error-regexp-added nil)

(defvar bsv-error-regexp-emacs-alist
  '(
    (bsc-xl-1a
     "Error: \"\\([A-Za-z0-9\._/]+\\)\", line \\([0-9]+\\)" 1 2 )
    (bsc-xl-1b
     "Warning: \"\\([A-Za-z0-9\._/]+\\)\", line \\([0-9]+\\)" 1 2 )
    (bsc-xl-1c
     "Error: \"\\([A-Za-z0-9\._/]+\\)\", line \\([0-9]+\\), column \\([0-9]+\\)" 1 2 3)
    (bsc-xl-1d
     "Warning: \"\\([A-Za-z0-9\._/]+\\)\", line \\([0-9]+\\), column \\([0-9]+\\)" 1 2 3)
    (verilog-xl-1
     "\\(Error\\|Warning\\)!.*\n?.*\"\\([^\"]+\\)\", \\([0-9]+\\)" 2 3)
    (verilog-xl-2
     "([WE][0-9A-Z]+)[ \t]+\\([^ \t\n,]+\\)[, \t]+\\(line[ \t]+\\)?\\([0-9]+\\):.*$" 1 3)
    (verilog-IES
     ".*\\*[WE],[0-9A-Z]+\\(\[[0-9A-Z_,]+\]\\)? (\\([^ \t,]+\\),\\([0-9]+\\)" 2 3)
    (verilog-surefire-1
     "[^\n]*\\[\\([^:]+\\):\\([0-9]+\\)\\]" 1 2)
    (verilog-surefire-2
     "\\(WARNING\\|ERROR\\|INFO\\)[^:]*: \\([^,]+\\),\\s-+\\(line \\)?\\([0-9]+\\):" 2 4 )
    (verilog-verbose
     "\
\\([a-zA-Z]?:?[^:( \t\n]+\\)[:(][ \t]*\\([0-9]+\\)\\([) \t]\\|\
:\\([^0-9\n]\\|\\([0-9]+:\\)\\)\\)" 1 2 5)
    (verilog-xsim
     "\\(Error\\|Warning\\).*in file (\\([^ \t]+\\) at line *\\([0-9]+\\))" 2 3)
    (verilog-vcs-1
     "\\(Error\\|Warning\\):[^(]*(\\([^ \t]+\\) line *\\([0-9]+\\))" 2 3)
    (verilog-vcs-2
     "Warning:.*(port.*(\\([^ \t]+\\) line \\([0-9]+\\))" 1 2)
    (verilog-vcs-3
     "\\(Error\\|Warning\\):[\n.]*\\([^ \t]+\\) *\\([0-9]+\\):" 2 3)
    (verilog-vcs-4
     "syntax error:.*\n\\([^ \t]+\\) *\\([0-9]+\\):" 1 2)
    (verilog-verilator
     "%?\\(Error\\|Warning\\)\\(-[^:]+\\|\\):[\n ]*\\([^ \t:]+\\):\\([0-9]+\\):" 3 4)
    (verilog-leda
     "^In file \\([^ \t]+\\)[ \t]+line[ \t]+\\([0-9]+\\):\n[^\n]*\n[^\n]*\n\\(Warning\\|Error\\|Failure\\)[^\n]*" 1 2)
    )
  "List of regexps for BSV compilers.
See `compilation-error-regexp-alist' for the formatting.  For Emacs 22+.")

(defvar bsv-error-regexp-xemacs-alist
  ;; Emacs form is '((v-tool "re" 1 2) ...)
  ;; XEmacs form is '(bsv ("re" 1 2) ...)
  ;; So we can just map from Emacs to XEmacs
  (cons 'bsv (mapcar 'cdr bsv-error-regexp-emacs-alist))
  "List of regexps for BSV compilers.
See `compilation-error-regexp-alist-alist' for the formatting.  For XEmacs.")

(defvar bsv-error-font-lock-keywords
  '(
    ;; bsv-xl-1
    ("\\(Error\\|Warning\\)!.*\n?.*\"\\([^\"]+\\)\", \\([0-9]+\\)" 2 bold t)
    ("\\(Error\\|Warning\\)!.*\n?.*\"\\([^\"]+\\)\", \\([0-9]+\\)" 2 bold t)
    ;; bsv-xl-2
    ("([WE][0-9A-Z]+)[ \t]+\\([^ \t\n,]+\\)[, \t]+\\(line[ \t]+\\)?\\([0-9]+\\):.*$" 1 bold t)
    ("([WE][0-9A-Z]+)[ \t]+\\([^ \t\n,]+\\)[, \t]+\\(line[ \t]+\\)?\\([0-9]+\\):.*$" 3 bold t)
    ;; bsv-IES (nc-bsv)
    (".*\\*[WE],[0-9A-Z]+\\(\[[0-9A-Z_,]+\]\\)? (\\([^ \t,]+\\),\\([0-9]+\\)|" 2 bold t)
    (".*\\*[WE],[0-9A-Z]+\\(\[[0-9A-Z_,]+\]\\)? (\\([^ \t,]+\\),\\([0-9]+\\)|" 3 bold t)
    ;; bsv-surefire-1
    ("[^\n]*\\[\\([^:]+\\):\\([0-9]+\\)\\]" 1 bold t)
    ("[^\n]*\\[\\([^:]+\\):\\([0-9]+\\)\\]" 2 bold t)
    ;; bsv-surefire-2
    ("\\(WARNING\\|ERROR\\|INFO\\): \\([^,]+\\), line \\([0-9]+\\):" 2 bold t)
    ("\\(WARNING\\|ERROR\\|INFO\\): \\([^,]+\\), line \\([0-9]+\\):" 3 bold t)
    ;; bsv-verbose
    ("\
\\([a-zA-Z]?:?[^:( \t\n]+\\)[:(][ \t]*\\([0-9]+\\)\\([) \t]\\|\
:\\([^0-9\n]\\|\\([0-9]+:\\)\\)\\)" 1 bold t)
    ("\
\\([a-zA-Z]?:?[^:( \t\n]+\\)[:(][ \t]*\\([0-9]+\\)\\([) \t]\\|\
:\\([^0-9\n]\\|\\([0-9]+:\\)\\)\\)" 1 bold t)
    ;; bsv-vcs-1
    ("\\(Error\\|Warning\\):[^(]*(\\([^ \t]+\\) line *\\([0-9]+\\))" 2 bold t)
    ("\\(Error\\|Warning\\):[^(]*(\\([^ \t]+\\) line *\\([0-9]+\\))" 3 bold t)
    ;; bsv-vcs-2
    ("Warning:.*(port.*(\\([^ \t]+\\) line \\([0-9]+\\))" 1 bold t)
    ("Warning:.*(port.*(\\([^ \t]+\\) line \\([0-9]+\\))" 1 bold t)
    ;; bsv-vcs-3
    ("\\(Error\\|Warning\\):[\n.]*\\([^ \t]+\\) *\\([0-9]+\\):" 2 bold t)
    ("\\(Error\\|Warning\\):[\n.]*\\([^ \t]+\\) *\\([0-9]+\\):" 3 bold t)
    ;; bsv-vcs-4
    ("syntax error:.*\n\\([^ \t]+\\) *\\([0-9]+\\):" 1 bold t)
    ("syntax error:.*\n\\([^ \t]+\\) *\\([0-9]+\\):" 2 bold t)
    ;; bsv-verilator
    (".*%?\\(Error\\|Warning\\)\\(-[^:]+\\|\\):[\n ]*\\([^ \t:]+\\):\\([0-9]+\\):" 3 bold t)
    (".*%?\\(Error\\|Warning\\)\\(-[^:]+\\|\\):[\n ]*\\([^ \t:]+\\):\\([0-9]+\\):" 4 bold t)
    ;; bsv-leda
    ("^In file \\([^ \t]+\\)[ \t]+line[ \t]+\\([0-9]+\\):\n[^\n]*\n[^\n]*\n\\(Warning\\|Error\\|Failure\\)[^\n]*" 1 bold t)
    ("^In file \\([^ \t]+\\)[ \t]+line[ \t]+\\([0-9]+\\):\n[^\n]*\n[^\n]*\n\\(Warning\\|Error\\|Failure\\)[^\n]*" 2 bold t)
    )
  "*Keywords to also highlight in BSV *compilation* buffers.
Only used in XEmacs; GNU Emacs uses `bsv-error-regexp-emacs-alist'.")

(defcustom bsv-library-flags '("")
  "*List of standard BSV arguments to use for /*AUTOINST*/.
These arguments are used to find files for `bsv-auto', and match
the flags accepted by a standard BSV-XL simulator.

    -f filename     Reads more `bsv-library-flags' from the filename.
    +incdir+dir     Adds the directory to `bsv-library-directories'.
    -Idir           Adds the directory to `bsv-library-directories'.
    -y dir          Adds the directory to `bsv-library-directories'.
    +libext+.v      Adds the extensions to `bsv-library-extensions'.
    -v filename     Adds the filename to `bsv-library-files'.

    filename        Adds the filename to `bsv-library-files'.
                    This is not recommended, -v is a better choice.

You might want these defined in each file; put at the *END* of your file
something like:

    // Local Variables:
    // bsv-library-flags:(\"-y dir -y otherdir\")
    // End:

bsv-mode attempts to detect changes to this local variable, but they
are only insured to be correct when the file is first visited.  Thus if you
have problems, use \\[find-alternate-file] RET to have these take effect.

See also the variables mentioned above."
  :group 'bsv-mode-auto
  :type '(repeat string))
(put 'bsv-library-flags 'safe-local-variable 'listp)

(defcustom bsv-library-directories '(".")
  "*List of directories when looking for files for /*AUTOINST*/.
The directory may be relative to the current file, or absolute.
Environment variables are also expanded in the directory names.
Having at least the current directory is a good idea.

You might want these defined in each file; put at the *END* of your file
something like:

    // Local Variables:
    // bsv-library-directories:(\".\" \"subdir\" \"subdir2\")
    // End:

bsv-mode attempts to detect changes to this local variable, but they
are only insured to be correct when the file is first visited.  Thus if you
have problems, use \\[find-alternate-file] RET to have these take effect.

See also `bsv-library-flags', `bsv-library-files'
and `bsv-library-extensions'."
  :group 'bsv-mode-auto
  :type '(repeat file))
(put 'bsv-library-directories 'safe-local-variable 'listp)

(defcustom bsv-library-files '()
  "*List of files to search for modules.
AUTOINST will use this when it needs to resolve a module name.
This is a complete path, usually to a technology file with many standard
cells defined in it.

You might want these defined in each file; put at the *END* of your file
something like:

    // Local Variables:
    // bsv-library-files:(\"/some/path/technology.v\" \"/some/path/tech2.v\")
    // End:

bsv-mode attempts to detect changes to this local variable, but they
are only insured to be correct when the file is first visited.  Thus if you
have problems, use \\[find-alternate-file] RET to have these take effect.

See also `bsv-library-flags', `bsv-library-directories'."
  :group 'bsv-mode-auto
  :type '(repeat directory))
(put 'bsv-library-files 'safe-local-variable 'listp)

(defcustom bsv-library-extensions '(".v" ".sv")
  "*List of extensions to use when looking for files for /*AUTOINST*/.
See also `bsv-library-flags', `bsv-library-directories'."
  :type '(repeat string)
  :group 'bsv-mode-auto)
(put 'bsv-library-extensions 'safe-local-variable 'listp)

(defcustom bsv-active-low-regexp nil
  "*If set, treat signals matching this regexp as active low.
This is used for AUTORESET and AUTOTIEOFF.  For proper behavior,
you will probably also need `bsv-auto-reset-widths' set."
  :group 'bsv-mode-auto
  :type 'string)
(put 'bsv-active-low-regexp 'safe-local-variable 'stringp)

(defcustom bsv-auto-sense-include-inputs nil
  "*If true, AUTOSENSE should include all inputs.
If nil, only inputs that are NOT output signals in the same block are
included."
  :group 'bsv-mode-auto
  :type 'boolean)
(put 'bsv-auto-sense-include-inputs 'safe-local-variable 'bsv-booleanp)

(defcustom bsv-auto-sense-defines-constant nil
  "*If true, AUTOSENSE should assume all defines represent constants.
When true, the defines will not be included in sensitivity lists.  To
maintain compatibility with other sites, this should be set at the bottom
of each BSV file that requires it, rather than being set globally."
  :group 'bsv-mode-auto
  :type 'boolean)
(put 'bsv-auto-sense-defines-constant 'safe-local-variable 'bsv-booleanp)

(defcustom bsv-auto-reset-blocking-in-non t
  "*If true, AUTORESET will reset those signals which were
assigned with blocking assignments (=) even in a block with
non-blocking assignments (<=).

If nil, all blocking assigned signals are ignored when any
non-blocking assignment is in the AUTORESET block.  This allows
blocking assignments to be used for temporary values and not have
those temporaries reset.  See example in `bsv-auto-reset'."
  :version "24.1"
  :type 'boolean
  :group 'bsv-mode-auto)
(put 'bsv-auto-reset-blocking-in-non 'safe-local-variable 'bsv-booleanp)

(defcustom bsv-auto-reset-widths t
  "*If true, AUTORESET should determine the width of signals.
This is then used to set the width of the zero (32'h0 for example).  This
is required by some lint tools that aren't smart enough to ignore widths of
the constant zero.  This may result in ugly code when parameters determine
the MSB or LSB of a signal inside an AUTORESET."
  :type 'boolean
  :group 'bsv-mode-auto)
(put 'bsv-auto-reset-widths 'safe-local-variable 'bsv-booleanp)

(defcustom bsv-assignment-delay ""
  "*Text used for delays in delayed assignments.  Add a trailing space if set."
  :group 'bsv-mode-auto
  :type 'string)
(put 'bsv-assignment-delay 'safe-local-variable 'stringp)

(defcustom bsv-auto-arg-sort nil
  "*If set, AUTOARG signal names will be sorted, not in declaration order.
Declaration order is advantageous with order based instantiations
and is the default for backward compatibility.  Sorted order
reduces changes when declarations are moved around in a file, and
it's bad practice to rely on order based instantiations anyhow.

See also `bsv-auto-inst-sort'."
  :group 'bsv-mode-auto
  :type 'boolean)
(put 'bsv-auto-arg-sort 'safe-local-variable 'bsv-booleanp)

(defcustom bsv-auto-inst-dot-name nil
  "*If true, when creating ports with AUTOINST, use .name syntax.
This will use \".port\" instead of \".port(port)\" when possible.
This is only legal in SystemBSV files, and will confuse older
simulators.  Setting `bsv-auto-inst-vector' to nil may also
be desirable to increase how often .name will be used."
  :group 'bsv-mode-auto
  :type 'boolean)
(put 'bsv-auto-inst-dot-name 'safe-local-variable 'bsv-booleanp)

(defcustom bsv-auto-inst-param-value nil
  "*If set, AUTOINST will replace parameters with the parameter value.
If nil, leave parameters as symbolic names.

Parameters must be in BSV 2001 format #(...), and if a parameter is not
listed as such there (as when the default value is acceptable), it will not
be replaced, and will remain symbolic.

For example, imagine a submodule uses parameters to declare the size of its
inputs.  This is then used by a upper module:

	module InstModule (o,i);
	   parameter WIDTH;
	   input [WIDTH-1:0] i;
	endmodule

	module ExampInst;
	   InstModule
 	     #(PARAM(10))
	    instName
	     (/*AUTOINST*/
	      .i 	(i[PARAM-1:0]));

Note even though PARAM=10, the AUTOINST has left the parameter as a
symbolic name.  If `bsv-auto-inst-param-value' is set, this will
instead expand to:

	module ExampInst;
	   InstModule
 	     #(PARAM(10))
	    instName
	     (/*AUTOINST*/
	      .i 	(i[9:0]));"
  :group 'bsv-mode-auto
  :type 'boolean)
(put 'bsv-auto-inst-param-value 'safe-local-variable 'bsv-booleanp)

(defcustom bsv-auto-inst-sort nil
  "*If set, AUTOINST signal names will be sorted, not in declaration order.
Also affects AUTOINSTPARAM.  Declaration order is the default for
backward compatibility, and as some teams prefer signals that are
declared together to remain together.  Sorted order reduces
changes when declarations are moved around in a file.

See also `bsv-auto-arg-sort'."
  :version "24.1"
  :group 'bsv-mode-auto
  :type 'boolean)
(put 'bsv-auto-inst-sort 'safe-local-variable 'bsv-booleanp)

(defcustom bsv-auto-inst-vector t
  "*If true, when creating default ports with AUTOINST, use bus subscripts.
If nil, skip the subscript when it matches the entire bus as declared in
the module (AUTOWIRE signals always are subscripted, you must manually
declare the wire to have the subscripts removed.)  Setting this to nil may
speed up some simulators, but is less general and harder to read, so avoid."
  :group 'bsv-mode-auto
  :type 'boolean)
(put 'bsv-auto-inst-vector 'safe-local-variable 'bsv-booleanp)

(defcustom bsv-auto-inst-template-numbers nil
  "*If true, when creating templated ports with AUTOINST, add a comment.

If t, the comment will add the line number of the template that
was used for that port declaration.  This setting is suggested
only for debugging use, as regular use may cause a large numbers
of merge conflicts.

If 'lhs', the comment will show the left hand side of the
AUTO_TEMPLATE rule that is matched.  This is less precise than
numbering (t) when multiple rules have the same pin name, but
won't merge conflict."
  :group 'bsv-mode-auto
  :type '(choice (const nil) (const t) (const lhs)))
(put 'bsv-auto-inst-template-numbers 'safe-local-variable
     '(lambda (x) (memq x '(nil t lhs))))

(defcustom bsv-auto-inst-column 40
  "*Indent-to column number for net name part of AUTOINST created pin."
  :group 'bsv-mode-indent
  :type 'integer)
(put 'bsv-auto-inst-column 'safe-local-variable 'integerp)

(defcustom bsv-auto-input-ignore-regexp nil
  "*If set, when creating AUTOINPUT list, ignore signals matching this regexp.
See the \\[bsv-faq] for examples on using this."
  :group 'bsv-mode-auto
  :type 'string)
(put 'bsv-auto-input-ignore-regexp 'safe-local-variable 'stringp)

(defcustom bsv-auto-inout-ignore-regexp nil
  "*If set, when creating AUTOINOUT list, ignore signals matching this regexp.
See the \\[bsv-faq] for examples on using this."
  :group 'bsv-mode-auto
  :type 'string)
(put 'bsv-auto-inout-ignore-regexp 'safe-local-variable 'stringp)

(defcustom bsv-auto-output-ignore-regexp nil
  "*If set, when creating AUTOOUTPUT list, ignore signals matching this regexp.
See the \\[bsv-faq] for examples on using this."
  :group 'bsv-mode-auto
  :type 'string)
(put 'bsv-auto-output-ignore-regexp 'safe-local-variable 'stringp)

(defcustom bsv-auto-tieoff-declaration "wire"
  "*Data type used for the declaration for AUTOTIEOFF.  If \"wire\" then
create a wire, if \"assign\" create an assignment, else the data type for
variable creation."
  :version "24.1"
  :group 'bsv-mode-auto
  :type 'string)
(put 'bsv-auto-tieoff-declaration 'safe-local-variable 'stringp)

(defcustom bsv-auto-tieoff-ignore-regexp nil
  "*If set, when creating AUTOTIEOFF list, ignore signals matching this regexp.
See the \\[bsv-faq] for examples on using this."
  :group 'bsv-mode-auto
  :type 'string)
(put 'bsv-auto-tieoff-ignore-regexp 'safe-local-variable 'stringp)

(defcustom bsv-auto-unused-ignore-regexp nil
  "*If set, when creating AUTOUNUSED list, ignore signals matching this regexp.
See the \\[bsv-faq] for examples on using this."
  :group 'bsv-mode-auto
  :type 'string)
(put 'bsv-auto-unused-ignore-regexp 'safe-local-variable 'stringp)

(defcustom bsv-typedef-regexp nil
  "*If non-nil, regular expression that matches BSV-2001 typedef names.
For example, \"_t$\" matches typedefs named with _t, as in the C language."
  :group 'bsv-mode-auto
  :type 'string)
(put 'bsv-typedef-regexp 'safe-local-variable 'stringp)

(defcustom bsv-mode-hook   'bsv-set-compile-command
  "*Hook run after BSV mode is loaded."
  :type 'hook
  :group 'bsv-mode)

(defcustom bsv-auto-hook nil
  "*Hook run after `bsv-mode' updates AUTOs."
  :group 'bsv-mode-auto
  :type 'hook)

(defcustom bsv-before-auto-hook nil
  "*Hook run before `bsv-mode' updates AUTOs."
  :group 'bsv-mode-auto
  :type 'hook)

(defcustom bsv-delete-auto-hook nil
  "*Hook run after `bsv-mode' deletes AUTOs."
  :group 'bsv-mode-auto
  :type 'hook)

(defcustom bsv-before-delete-auto-hook nil
  "*Hook run before `bsv-mode' deletes AUTOs."
  :group 'bsv-mode-auto
  :type 'hook)

(defcustom bsv-getopt-flags-hook nil
  "*Hook run after `bsv-getopt-flags' determines the BSV option lists."
  :group 'bsv-mode-auto
  :type 'hook)

(defcustom bsv-before-getopt-flags-hook nil
  "*Hook run before `bsv-getopt-flags' determines the BSV option lists."
  :group 'bsv-mode-auto
  :type 'hook)

(defvar bsv-imenu-generic-expression
  '((nil "^\\s-*\\(\\(m\\(odule\\|acromodule\\)\\)\\|primitive\\)\\s-+\\([a-zA-Z0-9_.:]+\\)" 4)
    ("*Vars*" "^\\s-*\\(reg\\|wire\\)\\s-+\\(\\|\\[[^]]+\\]\\s-+\\)\\([A-Za-z0-9_]+\\)" 3))
  "Imenu expression for BSV mode.  See `imenu-generic-expression'.")

;;
;; provide a bsv-header function.
;; Customization variables:
;;
(defvar bsv-date-scientific-format nil
  "*If non-nil, dates are written in scientific format (e.g.  1997/09/17).
If nil, in European format (e.g.  17.09.1997).  The brain-dead American
format (e.g.  09/17/1997) is not supported.")

(defvar bsv-company nil
  "*Default name of Company for BSV header.
If set will become buffer local.")
(make-variable-buffer-local 'bsv-company)

(defvar bsv-project nil
  "*Default name of Project for BSV header.
If set will become buffer local.")
(make-variable-buffer-local 'bsv-project)

(defvar bsv-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map ";"        'electric-bsv-semi)
    (define-key map [(control 59)]    'electric-bsv-semi-with-comment)
    (define-key map ":"        'electric-bsv-colon)
    ;;(define-key map "="        'electric-bsv-equal)
    (define-key map "\`"       'electric-bsv-tick)
;;    (define-key map "\t"       'electric-bsv-tab)
    (define-key map "\t"       'bsv-complete-or-indent-command)
    (define-key map "\r"       'electric-bsv-terminate-line)
    ;; backspace/delete key bindings
    (define-key map [backspace]    'backward-delete-char-untabify)
    (unless (boundp 'delete-key-deletes-forward) ; XEmacs variable
      (define-key map [delete]       'delete-char)
      (define-key map [(meta delete)] 'kill-word))
    (define-key map "\M-\C-b"  'electric-bsv-backward-sexp)
    (define-key map "\M-\C-f"  'electric-bsv-forward-sexp)
    (define-key map "\M-\r"    `electric-bsv-terminate-and-indent)
    (define-key map "\M-\t"    'bsv-complete-word)
    (define-key map "\M-?"     'bsv-show-completions)
    ;; Note \C-c and letter are reserved for users
    (define-key map "\C-c\`"   'bsv-lint-off)
    (define-key map "\C-c\*"   'bsv-delete-auto-star-implicit)
    (define-key map "\C-c\?"   'bsv-diff-auto)
    (define-key map "\C-c\C-r" 'bsv-label-be)
    (define-key map "\C-c\C-i" 'bsv-pretty-declarations)
    (define-key map "\C-c="    'bsv-pretty-expr)
    (define-key map "\M-*"     'bsv-star-comment)
    (define-key map "\C-c\C-c" 'bsv-comment-region)
    (define-key map "\C-c\C-u" 'bsv-uncomment-region)
    (when (featurep 'xemacs)
      (define-key map [(meta control h)] 'bsv-mark-defun)
      (define-key map "\M-\C-a"  'bsv-beg-of-defun)
      (define-key map "\M-\C-e"  'bsv-end-of-defun))
    (define-key map "\C-c\C-d" 'bsv-goto-defun)
    (define-key map "\C-c\C-k" 'bsv-delete-auto)
    (define-key map "\C-c\C-a" 'bsv-auto)
    (define-key map "\C-c\C-s" 'bsv-auto-save-compile)
    (define-key map "\C-c\C-p" 'bsv-preprocess)
    (define-key map "\C-c\C-z" 'bsv-inject-auto)
    (define-key map "\C-c\C-e" 'bsv-expand-vector)
    (define-key map "\C-c\C-h" 'bsv-header)
    (define-key map "\C-c\C-c" 'bsv-add-comment-bar)
    (define-key map "\C-l" 'bsv-recenter-and-font-lock-fontify-buffer)
    map)
  "Keymap used in BSV mode.")

;; menus
(easy-menu-define
  bsv-menu bsv-mode-map "Menu for BSV mode"
  (bsv-easy-menu-filter
   '("BSV"
     ("Choose Compilation Action"
      ["None"
       (progn
	 (setq bsv-tool nil)
	 (bsv-set-compile-command))
       :style radio
       :selected (equal bsv-tool nil)
       :help "When invoking compilation, use compile-command"]
      ["Lint"
       (progn
	 (setq bsv-tool 'bsv-linter)
	 (bsv-set-compile-command))
       :style radio
       :selected (equal bsv-tool `bsv-linter)
       :help "When invoking compilation, use lint checker"]
      ["Coverage"
       (progn
	 (setq bsv-tool 'bsv-coverage)
	 (bsv-set-compile-command))
       :style radio
       :selected (equal bsv-tool `bsv-coverage)
       :help "When invoking compilation, annotate for coverage"]
      ["Simulator"
       (progn
	 (setq bsv-tool 'bsv-simulator)
	 (bsv-set-compile-command))
       :style radio
       :selected (equal bsv-tool `bsv-simulator)
       :help "When invoking compilation, interpret BSV source"]
      ["Compiler"
       (progn
	 (setq bsv-tool 'bsv-compiler)
	 (bsv-set-compile-command))
       :style radio
       :selected (equal bsv-tool `bsv-compiler)
       :help "When invoking compilation, compile BSV source"]
      ["Preprocessor"
       (progn
	 (setq bsv-tool 'bsv-preprocessor)
	 (bsv-set-compile-command))
       :style radio
       :selected (equal bsv-tool `bsv-preprocessor)
       :help "When invoking compilation, preprocess BSV source, see also `bsv-preprocess'"]
      )
     ("Move"
      ["Beginning of function"		bsv-beg-of-defun
       :keys "C-M-a"
       :help		"Move backward to the beginning of the current function or procedure"]
      ["End of function"		bsv-end-of-defun
       :keys "C-M-e"
       :help		"Move forward to the end of the current function or procedure"]
      ["Mark function"			bsv-mark-defun
       :keys "C-M-h"
       :help		"Mark the current BSV function or procedure"]
      ["Goto function/module"		bsv-goto-defun
       :help		"Move to specified BSV module/task/function"]
      ["Move to beginning of block"	electric-bsv-backward-sexp
       :help		"Move backward over one balanced expression"]
      ["Move to end of block"		electric-bsv-forward-sexp
       :help		"Move forward over one balanced expression"]
      )
     ("Comments"
      ["Comment Region"			bsv-comment-region
       :help		"Put marked area into a comment"]
      ["UnComment Region"		bsv-uncomment-region
       :help		"Uncomment an area commented with Comment Region"]
      ["Multi-line comment insert"	bsv-star-comment
       :help		"Insert BSV /* */ comment at point"]
      ["Lint error to comment"		bsv-lint-off
       :help		"Convert a BSV linter warning line into a disable statement"]
      )
     "----"
     ["Compile"				compile
      :help		"Perform compilation-action (above) on the current buffer"]
     ["AUTO, Save, Compile"		bsv-auto-save-compile
      :help		"Recompute AUTOs, save buffer, and compile"]
     ["Next Compile Error"		next-error
      :help		"Visit next compilation error message and corresponding source code"]
     ["Ignore Lint Warning at point"	bsv-lint-off
      :help		"Convert a BSV linter warning line into a disable statement"]
     "----"
     ["Line up declarations around point"	bsv-pretty-declarations
      :help		"Line up declarations around point"]
     ["Line up equations around point"		bsv-pretty-expr
      :help		"Line up expressions around point"]
     ["Redo/insert comments on every end"	bsv-label-be
      :help		"Label matching begin ... end statements"]
     ["Expand [x:y] vector line"	bsv-expand-vector
      :help		"Take a signal vector on the current line and expand it to multiple lines"]
     ["Insert begin-end block"		bsv-insert-block
      :help		"Insert begin ... end"]
     ["Complete word"			bsv-complete-word
      :help		"Complete word at point"]
     "----"
     ["Recompute AUTOs"			bsv-auto
      :help		"Expand AUTO meta-comment statements"]
     ["Kill AUTOs"			bsv-delete-auto
      :help		"Remove AUTO expansions"]
     ["Diff AUTOs"			bsv-diff-auto
      :help		"Show differences in AUTO expansions"]
     ["Inject AUTOs"			bsv-inject-auto
      :help		"Inject AUTOs into legacy non-AUTO buffer"]
     ("AUTO Help..."
      ["AUTO General"			(describe-function 'bsv-auto)
       :help		"Help introduction on AUTOs"]
      ["AUTO Library Flags"		(describe-variable 'bsv-library-flags)
       :help		"Help on bsv-library-flags"]
      ["AUTO Library Path"		(describe-variable 'bsv-library-directories)
       :help		"Help on bsv-library-directories"]
      ["AUTO Library Files"		(describe-variable 'bsv-library-files)
       :help		"Help on bsv-library-files"]
      ["AUTO Library Extensions"	(describe-variable 'bsv-library-extensions)
       :help		"Help on bsv-library-extensions"]
      ["AUTO `define Reading"		(describe-function 'bsv-read-defines)
       :help		"Help on reading `defines"]
      ["AUTO `include Reading"		(describe-function 'bsv-read-includes)
       :help		"Help on parsing `includes"]
      ["AUTOARG"			(describe-function 'bsv-auto-arg)
       :help		"Help on AUTOARG - declaring module port list"]
      ["AUTOASCIIENUM"			(describe-function 'bsv-auto-ascii-enum)
       :help		"Help on AUTOASCIIENUM - creating ASCII for enumerations"]
      ["AUTOINOUTCOMP"			(describe-function 'bsv-auto-inout-comp)
       :help		"Help on AUTOINOUTCOMP - copying complemented i/o from another file"]
      ["AUTOINOUTIN"			(describe-function 'bsv-auto-inout-in)
       :help		"Help on AUTOINOUTCOMP - copying i/o from another file as all inputs"]
      ["AUTOINOUTMODULE"		(describe-function 'bsv-auto-inout-module)
       :help		"Help on AUTOINOUTMODULE - copying i/o from another file"]
      ["AUTOINSERTLISP"			(describe-function 'bsv-auto-insert-lisp)
       :help		"Help on AUTOINSERTLISP - insert text from a lisp function"]
      ["AUTOINOUT"			(describe-function 'bsv-auto-inout)
       :help		"Help on AUTOINOUT - adding inouts from cells"]
      ["AUTOINPUT"			(describe-function 'bsv-auto-input)
       :help		"Help on AUTOINPUT - adding inputs from cells"]
      ["AUTOINST"			(describe-function 'bsv-auto-inst)
       :help		"Help on AUTOINST - adding pins for cells"]
      ["AUTOINST (.*)"			(describe-function 'bsv-auto-star)
       :help		"Help on expanding BSV-2001 .* pins"]
      ["AUTOINSTPARAM"			(describe-function 'bsv-auto-inst-param)
       :help		"Help on AUTOINSTPARAM - adding parameter pins to cells"]
      ["AUTOLOGIC"			(describe-function 'bsv-auto-logic)
       :help		"Help on AUTOLOGIC - declaring logic signals"]
      ["AUTOOUTPUT"			(describe-function 'bsv-auto-output)
       :help		"Help on AUTOOUTPUT - adding outputs from cells"]
      ["AUTOOUTPUTEVERY"		(describe-function 'bsv-auto-output-every)
       :help		"Help on AUTOOUTPUTEVERY - adding outputs of all signals"]
      ["AUTOREG"			(describe-function 'bsv-auto-reg)
       :help		"Help on AUTOREG - declaring registers for non-wires"]
      ["AUTOREGINPUT"			(describe-function 'bsv-auto-reg-input)
       :help		"Help on AUTOREGINPUT - declaring inputs for non-wires"]
      ["AUTORESET"			(describe-function 'bsv-auto-reset)
       :help		"Help on AUTORESET - resetting always blocks"]
      ["AUTOSENSE"			(describe-function 'bsv-auto-sense)
       :help		"Help on AUTOSENSE - sensitivity lists for always blocks"]
      ["AUTOTIEOFF"			(describe-function 'bsv-auto-tieoff)
       :help		"Help on AUTOTIEOFF - tying off unused outputs"]
      ["AUTOUNUSED"			(describe-function 'bsv-auto-unused)
       :help		"Help on AUTOUNUSED - terminating unused inputs"]
      ["AUTOWIRE"			(describe-function 'bsv-auto-wire)
       :help		"Help on AUTOWIRE - declaring wires for cells"]
      )
     "----"
     ["Version and FAQ"			bsv-faq
      :help		"Show the current version, and where to get the FAQ etc"]
     ["Customize BSV Mode..."	bsv-customize
      :help		"Customize variables and other settings used by BSV-Mode"]
     ["Customize BSV Fonts & Colors"	bsv-font-customize
      :help		"Customize fonts used by BSV-Mode."])))

(easy-menu-define
  bsv-stmt-menu bsv-mode-map "Menu for statement templates in BSV."
  (bsv-easy-menu-filter
   '("Statements"
     ["Header"		bsv-sk-header
      :help		"Insert a header block at the top of file"]
     ["Comment"		bsv-sk-comment
      :help		"Insert a comment block"]
     "----"
     ["Module"		bsv-sk-module
      :help		"Insert a module .. (/*AUTOARG*/);.. endmodule block"]
     ["OVM Class"	bsv-sk-ovm-class
      :help		"Insert an OVM class block"]
     ["UVM Class"	bsv-sk-uvm-class
      :help		"Insert an UVM class block"]
     ["Primitive"	bsv-sk-primitive
      :help		"Insert a primitive .. (.. );.. endprimitive block"]
     "----"
     ["Input"		bsv-sk-input
      :help		"Insert an input declaration"]
     ["Output"		bsv-sk-output
      :help		"Insert an output declaration"]
     ["Inout"		bsv-sk-inout
      :help		"Insert an inout declaration"]
     ["Wire"		bsv-sk-wire
      :help		"Insert a wire declaration"]
     ["Reg"		bsv-sk-reg
      :help		"Insert a register declaration"]
     ["Define thing under point as a register" bsv-sk-define-signal
      :help		"Define signal under point as a register at the top of the module"]
     "----"
     ["Initial"		bsv-sk-initial
      :help		"Insert an initial begin .. end block"]
     ["Always"		bsv-sk-always
      :help		"Insert an always @(AS) begin .. end block"]
     ["Function"	bsv-sk-function
      :help		"Insert a function .. begin .. end endfunction block"]
     ["Task"		bsv-sk-task
      :help		"Insert a task .. begin .. end endtask block"]
     ["Specify"		bsv-sk-specify
      :help		"Insert a specify .. endspecify block"]
     ["Generate"	bsv-sk-generate
      :help		"Insert a generate .. endgenerate block"]
     "----"
     ["Begin"		bsv-sk-begin
      :help		"Insert a begin .. end block"]
     ["If"		bsv-sk-if
      :help		"Insert an if (..) begin .. end block"]
     ["(if) else"	bsv-sk-else-if
      :help		"Insert an else if (..) begin .. end block"]
     ["For"		bsv-sk-for
      :help		"Insert a for (...) begin .. end block"]
     ["While"		bsv-sk-while
      :help		"Insert a while (...) begin .. end block"]
     ["Fork"		bsv-sk-fork
      :help		"Insert a fork begin .. end .. join block"]
     ["Repeat"		bsv-sk-repeat
      :help		"Insert a repeat (..) begin .. end block"]
     ["Case"		bsv-sk-case
      :help		"Insert a case block, prompting for details"]
     ["Casex"		bsv-sk-casex
      :help		"Insert a casex (...) item: begin.. end endcase block"]
     ["Casez"		bsv-sk-casez
      :help		"Insert a casez (...) item: begin.. end endcase block"])))

(defvar bsv-mode-abbrev-table nil
  "Abbrev table in use in bsv-mode buffers.")

(define-abbrev-table 'bsv-mode-abbrev-table ())
(bsv-define-abbrev bsv-mode-abbrev-table "class" "" 'bsv-sk-ovm-class)
(bsv-define-abbrev bsv-mode-abbrev-table "always" "" 'bsv-sk-always)
(bsv-define-abbrev bsv-mode-abbrev-table "begin" nil `bsv-sk-begin)
(bsv-define-abbrev bsv-mode-abbrev-table "case" "" `bsv-sk-case)
(bsv-define-abbrev bsv-mode-abbrev-table "for" "" `bsv-sk-for)
(bsv-define-abbrev bsv-mode-abbrev-table "generate" "" `bsv-sk-generate)
(bsv-define-abbrev bsv-mode-abbrev-table "initial" "" `bsv-sk-initial)
(bsv-define-abbrev bsv-mode-abbrev-table "fork" "" `bsv-sk-fork)
(bsv-define-abbrev bsv-mode-abbrev-table "module" "" `bsv-sk-module)
(bsv-define-abbrev bsv-mode-abbrev-table "primitive" "" `bsv-sk-primitive)
(bsv-define-abbrev bsv-mode-abbrev-table "repeat" "" `bsv-sk-repeat)
(bsv-define-abbrev bsv-mode-abbrev-table "specify" "" `bsv-sk-specify)
(bsv-define-abbrev bsv-mode-abbrev-table "task" "" `bsv-sk-task)
(bsv-define-abbrev bsv-mode-abbrev-table "while" "" `bsv-sk-while)
(bsv-define-abbrev bsv-mode-abbrev-table "casex" "" `bsv-sk-casex)
(bsv-define-abbrev bsv-mode-abbrev-table "casez" "" `bsv-sk-casez)
(bsv-define-abbrev bsv-mode-abbrev-table "if" "" `bsv-sk-if)
(bsv-define-abbrev bsv-mode-abbrev-table "else if" "" `bsv-sk-else-if)
(bsv-define-abbrev bsv-mode-abbrev-table "assign" "" `bsv-sk-assign)
(bsv-define-abbrev bsv-mode-abbrev-table "function" "" `bsv-sk-function)
(bsv-define-abbrev bsv-mode-abbrev-table "input" "" `bsv-sk-input)
(bsv-define-abbrev bsv-mode-abbrev-table "output" "" `bsv-sk-output)
(bsv-define-abbrev bsv-mode-abbrev-table "inout" "" `bsv-sk-inout)
(bsv-define-abbrev bsv-mode-abbrev-table "wire" "" `bsv-sk-wire)
(bsv-define-abbrev bsv-mode-abbrev-table "reg" "" `bsv-sk-reg)

;;
;;  Macros
;;

(defsubst bsv-within-string ()
  (nth 3 (parse-partial-sexp (point-at-bol) (point))))

(defsubst bsv-string-replace-matches (from-string to-string fixedcase literal string)
  "Replace occurrences of FROM-STRING with TO-STRING.
FIXEDCASE and LITERAL as in `replace-match`.  STRING is what to replace.
The case (bsv-string-replace-matches \"o\" \"oo\" nil nil \"foobar\")
will break, as the o's continuously replace.  xa -> x works ok though."
  ;; Hopefully soon to a emacs built-in
  ;; Also note \ in the replacement prevent multiple replacements; IE
  ;;   (bsv-string-replace-matches "@" "\\\\([0-9]+\\\\)" nil nil "wire@_@")
  ;;   Gives "wire\([0-9]+\)_@" not "wire\([0-9]+\)_\([0-9]+\)"
  (let ((start 0))
    (while (string-match from-string string start)
      (setq string (replace-match to-string fixedcase literal string)
	    start (min (length string) (+ (match-beginning 0) (length to-string)))))
    string))

(defsubst bsv-string-remove-spaces (string)
  "Remove spaces surrounding STRING."
  (save-match-data
    (setq string (bsv-string-replace-matches "^\\s-+" "" nil nil string))
    (setq string (bsv-string-replace-matches "\\s-+$" "" nil nil string))
    string))

(defsubst bsv-re-search-forward (REGEXP BOUND NOERROR)
  ; checkdoc-params: (REGEXP BOUND NOERROR)
  "Like `re-search-forward', but skips over match in comments or strings."
  (let ((mdata '(nil nil)))  ;; So match-end will return nil if no matches found
    (while (and
	    (re-search-forward REGEXP BOUND NOERROR)
	    (setq mdata (match-data))
	    (and (bsv-skip-forward-comment-or-string)
		 (progn
		   (setq mdata '(nil nil))
		   (if BOUND
		       (< (point) BOUND)
		     t)))))
    (store-match-data mdata)
    (match-end 0)))

(defsubst bsv-re-search-backward (REGEXP BOUND NOERROR)
  ; checkdoc-params: (REGEXP BOUND NOERROR)
  "Like `re-search-backward', but skips over match in comments or strings."
  (let ((mdata '(nil nil)))  ;; So match-end will return nil if no matches found
    (while (and
	    (re-search-backward REGEXP BOUND NOERROR)
	    (setq mdata (match-data))
	    (and (bsv-skip-backward-comment-or-string)
		 (progn
		   (setq mdata '(nil nil))
		   (if BOUND
		       (> (point) BOUND)
		     t)))))
    (store-match-data mdata)
    (match-end 0)))

(defsubst bsv-re-search-forward-quick (regexp bound noerror)
  "Like `bsv-re-search-forward', including use of REGEXP BOUND and NOERROR,
but trashes match data and is faster for REGEXP that doesn't match often.
This uses `bsv-scan' and text properties to ignore comments,
so there may be a large up front penalty for the first search."
  (let (pt)
    (while (and (not pt)
		(re-search-forward regexp bound noerror))
      (if (bsv-inside-comment-or-string-p)
	  (re-search-forward "[/\"\n]" nil t) ;; Only way a comment or quote can end
	(setq pt (match-end 0))))
    pt))

(defsubst bsv-re-search-backward-quick (regexp bound noerror)
  ; checkdoc-params: (REGEXP BOUND NOERROR)
  "Like `bsv-re-search-backward', including use of REGEXP BOUND and NOERROR,
but trashes match data and is faster for REGEXP that doesn't match often.
This uses `bsv-scan' and text properties to ignore comments,
so there may be a large up front penalty for the first search."
  (let (pt)
    (while (and (not pt)
		(re-search-backward regexp bound noerror))
      (if (bsv-inside-comment-or-string-p)
	  (re-search-backward "[/\"]" nil t) ;; Only way a comment or quote can begin
	(setq pt (match-beginning 0))))
    pt))

(defsubst bsv-re-search-forward-substr (substr regexp bound noerror)
  "Like `re-search-forward', but first search for SUBSTR constant.
Then searched for the normal REGEXP (which contains SUBSTR), with given
BOUND and NOERROR.  The REGEXP must fit within a single line.
This speeds up complicated regexp matches."
  ;; Problem with overlap: search-forward BAR then FOOBARBAZ won't match.
  ;; thus require matches to be on one line, and use beginning-of-line.
  (let (done)
    (while (and (not done)
		(search-forward substr bound noerror))
      (save-excursion
	(beginning-of-line)
	(setq done (re-search-forward regexp (point-at-eol) noerror)))
      (unless (and (<= (match-beginning 0) (point))
		   (>= (match-end 0) (point)))
	(setq done nil)))
    (when done (goto-char done))
    done))
;;(bsv-re-search-forward-substr "-end" "get-end-of" nil t) ;;-end (test bait)

(defsubst bsv-re-search-backward-substr (substr regexp bound noerror)
  "Like `re-search-backward', but first search for SUBSTR constant.
Then searched for the normal REGEXP (which contains SUBSTR), with given
BOUND and NOERROR.  The REGEXP must fit within a single line.
This speeds up complicated regexp matches."
  ;; Problem with overlap: search-backward BAR then FOOBARBAZ won't match.
  ;; thus require matches to be on one line, and use beginning-of-line.
  (let (done)
    (while (and (not done)
		(search-backward substr bound noerror))
      (save-excursion
	(end-of-line)
	(setq done (re-search-backward regexp (point-at-bol) noerror)))
      (unless (and (<= (match-beginning 0) (point))
		   (>= (match-end 0) (point)))
	(setq done nil)))
    (when done (goto-char done))
    done))
;;(bsv-re-search-backward-substr "-end" "get-end-of" nil t) ;;-end (test bait)

(defun bsv-delete-trailing-whitespace ()
  "Delete trailing spaces or tabs, but not newlines nor linefeeds."
  ;; Similar to `delete-trailing-whitespace' but that's not present in XEmacs
  (save-excursion
    (goto-char (point-min))
    (while (re-search-forward "[ \t]+$" nil t)  ;; Not syntactic WS as no formfeed
      (replace-match "" nil nil))))

(defvar compile-command)

;; compilation program
(defun bsv-set-compile-command ()
  "Function to compute shell command to compile BSV.

This reads `bsv-tool' and sets `compile-command'.  This specifies the
program that executes when you type \\[compile] or
\\[bsv-auto-save-compile].

By default `bsv-tool' uses a Makefile if one exists in the
current directory.  If not, it is set to the `bsv-linter',
`bsv-compiler', `bsv-coverage', `bsv-preprocessor',
or `bsv-simulator' variables, as selected with the BSV ->
\"Choose Compilation Action\" menu.

You should set `bsv-tool' or the other variables to the path and
arguments for your BSV simulator.  For example:
    \"vcs -p123 -O\"
or a string like:
    \"(cd /tmp; surecov %s)\".

In the former case, the path to the current buffer is concat'ed to the
value of `bsv-tool'; in the later, the path to the current buffer is
substituted for the %s.

Where __FLAGS__ appears in the string `bsv-current-flags'
will be substituted.

Where __FILE__ appears in the string, the variable
`buffer-file-name' of the current buffer, without the directory
portion, will be substituted."
  (interactive)
  (cond
   ((or (file-exists-p "makefile")	;If there is a makefile, use it
	(file-exists-p "Makefile"))
    (set (make-local-variable 'compile-command) "make "))
   (t
    (set (make-local-variable 'compile-command)
	 (if bsv-tool
	     (if (string-match "%s" (eval bsv-tool))
		 (format (eval bsv-tool) (or buffer-file-name ""))
	       (concat (eval bsv-tool) " " (or buffer-file-name "")))
	   ""))))
  (bsv-modify-compile-command))

(defun bsv-expand-command (command)
  "Replace meta-information in COMMAND and return it.
Where __FLAGS__ appears in the string `bsv-current-flags'
will be substituted.  Where __FILE__ appears in the string, the
current buffer's file-name, without the directory portion, will
be substituted."
  (setq command	(bsv-string-replace-matches
		 ;; Note \\b only works if under bsv syntax table
		 "\\b__FLAGS__\\b" (bsv-current-flags)
		 t t command))
  (setq command	(bsv-string-replace-matches
		 "\\b__FILE__\\b" (file-name-nondirectory
				   (or (buffer-file-name) ""))
		 t t command))
  command)

(defun bsv-modify-compile-command ()
  "Update `compile-command' using `bsv-expand-command'."
  (when (and
	 (stringp compile-command)
	 (string-match "\\b\\(__FLAGS__\\|__FILE__\\)\\b" compile-command))
    (set (make-local-variable 'compile-command)
	 (bsv-expand-command compile-command))))

(if (featurep 'xemacs)
    ;; Following code only gets called from compilation-mode-hook on XEmacs to add error handling.
    (defun bsv-error-regexp-add-xemacs ()
      "Teach XEmacs about bsv errors.
Called by `compilation-mode-hook'.  This allows \\[next-error] to
find the errors."
      (interactive)
      (if (boundp 'compilation-error-regexp-systems-alist)
	  (if (and
	       (not (equal compilation-error-regexp-systems-list 'all))
	       (not (member compilation-error-regexp-systems-list 'bsv)))
	      (push 'bsv compilation-error-regexp-systems-list)))
      (if (boundp 'compilation-error-regexp-alist-alist)
	  (if (not (assoc 'bsv compilation-error-regexp-alist-alist))
	      (setcdr compilation-error-regexp-alist-alist
		      (cons bsv-error-regexp-xemacs-alist
			    (cdr compilation-error-regexp-alist-alist)))))
      (if (boundp 'compilation-font-lock-keywords)
	  (progn
	    (set (make-local-variable 'compilation-font-lock-keywords)
		 bsv-error-font-lock-keywords)
	    (font-lock-set-defaults)))
      ;; Need to re-run compilation-error-regexp builder
      (if (fboundp 'compilation-build-compilation-error-regexp-alist)
	  (compilation-build-compilation-error-regexp-alist))
      ))

(defvar bsv-error-regexp-add-didit nil)
(defvar bsv-error-regexp nil)
(setq bsv-error-regexp-add-didit nil
 bsv-error-regexp
  '(
       ; Bluespec compiler
    ;;    ("\\(Error\\|Warning\\):.*\n?.*\"\\([^\"]+\\)\",line \\([0-9]+\\)" 2 3)
    ("Error: \"\\([A-Za-z0-9\._/]+\\)\", line \\([0-9]+\\)" 1 2 )
    ("Warning: \"\\([A-Za-z0-9\._/]+\\)\", line \\([0-9]+\\)" 1 2 )
    ("Error: \"\\([A-Za-z0-9\._/]+\\)\", line \\([0-9]+\\), column \\([0-9]+\\)" 1 2 3)
    ("Warning: \"\\([A-Za-z0-9\._/]+\\)\", line \\([0-9]+\\), column \\([0-9]+\\)" 1 2 3)))

(if (< emacs-major-version 24)

    (progn
      (defun bsv-error-regexp-add-emacs ()
	"Add the messages to the `compilation-error-regexp-alist'.
Called by `compilation-mode-hook'.  This allows \\[next-error] to find the errors."
	(progn
	  (setq-default compilation-error-regexp-alist
			(append 
			 bsv-error-regexp
			 nil ;; (default-value 'compilation-error-regexp-alist)
			 ))
	  ))

      (if (not bsv-error-regexp-add-didit)
	  (progn
	    (setq bsv-error-regexp-add-didit t)
	    (setq-default compilation-error-regexp-alist
			  (append 
			   bsv-error-regexp
			   nil ;; (default-value 'compilation-error-regexp-alist)
			   ))
	    ;; Could be buffer local at this point; maybe also in let; change all three
	    (setq compilation-error-regexp-alist (default-value 'compilation-error-regexp-alist))
	    (set (make-local-variable 'compilation-error-regexp-alist)
		 (default-value 'compilation-error-regexp-alist))
	    ))
      )

  ;; Following code only gets called from compilation-mode-hook on Emacs to add error handling.
  (defun bsv-error-regexp-add-emacs ()
    "Tell Emacs compile that we are BSV.
Called by `compilation-mode-hook'.  This allows \\[next-error] to
find the errors."
    (interactive)
    (if (boundp 'compilation-error-regexp-alist-alist)
	(progn
	  (if (not (assoc 'bsv-xl-1 compilation-error-regexp-alist-alist))
	      (mapcar
	       (lambda (item)
		 (push (car item) compilation-error-regexp-alist)
		 (push item compilation-error-regexp-alist-alist)
		 )
	       bsv-error-regexp-emacs-alist)))))
)

(if (featurep 'xemacs) (add-hook 'compilation-mode-hook 'bsv-error-regexp-add-xemacs))
(if (featurep 'emacs) (add-hook 'compilation-mode-hook 'bsv-error-regexp-add-emacs))

(defconst bsv-directive-re
  (eval-when-compile
    (bsv-regexp-words
     '(
   "`case" "`default" "`define" "`else" "`elsif" "`endfor" "`endif"
   "`endprotect" "`endswitch" "`endwhile" "`for" "`format" "`if" "`ifdef"
   "`ifndef" "`include" "`let" "`protect" "`switch" "`timescale"
   "`time_scale" "`undef" "`while" ))))

(defconst bsv-directive-re-1
  (concat "[ \t]*"  bsv-directive-re))

(defconst bsv-directive-begin
  "\\<`\\(for\\|i\\(f\\|fdef\\|fndef\\)\\|switch\\|while\\)\\>")

(defconst bsv-directive-middle
  "\\<`\\(else\\|elsif\\|default\\|case\\)\\>")

(defconst bsv-directive-end
  "`\\(endfor\\|endif\\|endswitch\\|endwhile\\)\\>")

(defconst bsv-ovm-begin-re
  (eval-when-compile
    (bsv-regexp-opt
     '(
       "`ovm_component_utils_begin"
       "`ovm_component_param_utils_begin"
       "`ovm_field_utils_begin"
       "`ovm_object_utils_begin"
       "`ovm_object_param_utils_begin"
       "`ovm_sequence_utils_begin"
       "`ovm_sequencer_utils_begin"
       ) nil )))

(defconst bsv-ovm-end-re
  (eval-when-compile
    (bsv-regexp-opt
     '(
       "`ovm_component_utils_end"
       "`ovm_field_utils_end"
       "`ovm_object_utils_end"
       "`ovm_sequence_utils_end"
       "`ovm_sequencer_utils_end"
       ) nil )))

(defconst bsv-uvm-begin-re
  (eval-when-compile
    (bsv-regexp-opt
     '(
       "`uvm_component_utils_begin"
       "`uvm_component_param_utils_begin"
       "`uvm_field_utils_begin"
       "`uvm_object_utils_begin"
       "`uvm_object_param_utils_begin"
       "`uvm_sequence_utils_begin"
       "`uvm_sequencer_utils_begin"
       ) nil )))

(defconst bsv-uvm-end-re
  (eval-when-compile
    (bsv-regexp-opt
     '(
       "`uvm_component_utils_end"
       "`uvm_field_utils_end"
       "`uvm_object_utils_end"
       "`uvm_sequence_utils_end"
       "`uvm_sequencer_utils_end"
       ) nil )))

(defconst bsv-vmm-begin-re
  (eval-when-compile
    (bsv-regexp-opt
     '(
       "`vmm_data_member_begin"
       "`vmm_env_member_begin"
       "`vmm_scenario_member_begin"
       "`vmm_subenv_member_begin"
       "`vmm_xactor_member_begin"
       ) nil ) ) )

(defconst bsv-vmm-end-re
  (eval-when-compile
    (bsv-regexp-opt
     '(
       "`vmm_data_member_end"
       "`vmm_env_member_end"
       "`vmm_scenario_member_end"
       "`vmm_subenv_member_end"
       "`vmm_xactor_member_end"
       ) nil ) ) )

(defconst bsv-vmm-statement-re
  (eval-when-compile
    (bsv-regexp-opt
     '(
;;       "`vmm_xactor_member_enum_array"
       "`vmm_\\(data\\|env\\|scenario\\|subenv\\|xactor\\)_member_\\(scalar\\|string\\|enum\\|vmm_data\\|channel\\|xactor\\|subenv\\|user_defined\\)\\(_array\\)?"
;;       "`vmm_xactor_member_scalar_array"
;;       "`vmm_xactor_member_scalar"
       ) nil )))

(defconst bsv-ovm-statement-re
  (eval-when-compile
    (bsv-regexp-opt
     '(
       ;; Statements
       "`DUT_ERROR"
       "`MESSAGE"
       "`dut_error"
       "`message"
       "`ovm_analysis_imp_decl"
       "`ovm_blocking_get_imp_decl"
       "`ovm_blocking_get_peek_imp_decl"
       "`ovm_blocking_master_imp_decl"
       "`ovm_blocking_peek_imp_decl"
       "`ovm_blocking_put_imp_decl"
       "`ovm_blocking_slave_imp_decl"
       "`ovm_blocking_transport_imp_decl"
       "`ovm_component_registry"
       "`ovm_component_registry_param"
       "`ovm_component_utils"
       "`ovm_create"
       "`ovm_create_seq"
       "`ovm_declare_sequence_lib"
       "`ovm_do"
       "`ovm_do_seq"
       "`ovm_do_seq_with"
       "`ovm_do_with"
       "`ovm_error"
       "`ovm_fatal"
       "`ovm_field_aa_int_byte"
       "`ovm_field_aa_int_byte_unsigned"
       "`ovm_field_aa_int_int"
       "`ovm_field_aa_int_int_unsigned"
       "`ovm_field_aa_int_integer"
       "`ovm_field_aa_int_integer_unsigned"
       "`ovm_field_aa_int_key"
       "`ovm_field_aa_int_longint"
       "`ovm_field_aa_int_longint_unsigned"
       "`ovm_field_aa_int_shortint"
       "`ovm_field_aa_int_shortint_unsigned"
       "`ovm_field_aa_int_string"
       "`ovm_field_aa_object_int"
       "`ovm_field_aa_object_string"
       "`ovm_field_aa_string_int"
       "`ovm_field_aa_string_string"
       "`ovm_field_array_int"
       "`ovm_field_array_object"
       "`ovm_field_array_string"
       "`ovm_field_enum"
       "`ovm_field_event"
       "`ovm_field_int"
       "`ovm_field_object"
       "`ovm_field_queue_int"
       "`ovm_field_queue_object"
       "`ovm_field_queue_string"
       "`ovm_field_sarray_int"
       "`ovm_field_string"
       "`ovm_field_utils"
       "`ovm_file"
       "`ovm_get_imp_decl"
       "`ovm_get_peek_imp_decl"
       "`ovm_info"
       "`ovm_info1"
       "`ovm_info2"
       "`ovm_info3"
       "`ovm_info4"
       "`ovm_line"
       "`ovm_master_imp_decl"
       "`ovm_msg_detail"
       "`ovm_non_blocking_transport_imp_decl"
       "`ovm_nonblocking_get_imp_decl"
       "`ovm_nonblocking_get_peek_imp_decl"
       "`ovm_nonblocking_master_imp_decl"
       "`ovm_nonblocking_peek_imp_decl"
       "`ovm_nonblocking_put_imp_decl"
       "`ovm_nonblocking_slave_imp_decl"
       "`ovm_object_registry"
       "`ovm_object_registry_param"
       "`ovm_object_utils"
       "`ovm_peek_imp_decl"
       "`ovm_phase_func_decl"
       "`ovm_phase_task_decl"
       "`ovm_print_aa_int_object"
       "`ovm_print_aa_string_int"
       "`ovm_print_aa_string_object"
       "`ovm_print_aa_string_string"
       "`ovm_print_array_int"
       "`ovm_print_array_object"
       "`ovm_print_array_string"
       "`ovm_print_object_queue"
       "`ovm_print_queue_int"
       "`ovm_print_string_queue"
       "`ovm_put_imp_decl"
       "`ovm_rand_send"
       "`ovm_rand_send_with"
       "`ovm_send"
       "`ovm_sequence_utils"
       "`ovm_slave_imp_decl"
       "`ovm_transport_imp_decl"
       "`ovm_update_sequence_lib"
       "`ovm_update_sequence_lib_and_item"
       "`ovm_warning"
       "`static_dut_error"
       "`static_message") nil )))

(defconst bsv-uvm-statement-re
  (eval-when-compile
    (bsv-regexp-opt
     '(
       ;; Statements
       "`uvm_analysis_imp_decl"
       "`uvm_blocking_get_imp_decl"
       "`uvm_blocking_get_peek_imp_decl"
       "`uvm_blocking_master_imp_decl"
       "`uvm_blocking_peek_imp_decl"
       "`uvm_blocking_put_imp_decl"
       "`uvm_blocking_slave_imp_decl"
       "`uvm_blocking_transport_imp_decl"
       "`uvm_component_param_utils"
       "`uvm_component_registry"
       "`uvm_component_registry_param"
       "`uvm_component_utils"
       "`uvm_create"
       "`uvm_create_on"
       "`uvm_create_seq"		;; Undocumented in 1.1
       "`uvm_declare_p_sequencer"
       "`uvm_declare_sequence_lib"	;; Deprecated in 1.1
       "`uvm_do"
       "`uvm_do_callbacks"
       "`uvm_do_callbacks_exit_on"
       "`uvm_do_obj_callbacks"
       "`uvm_do_obj_callbacks_exit_on"
       "`uvm_do_on"
       "`uvm_do_on_pri"
       "`uvm_do_on_pri_with"
       "`uvm_do_on_with"
       "`uvm_do_pri"
       "`uvm_do_pri_with"
       "`uvm_do_seq"			;; Undocumented in 1.1
       "`uvm_do_seq_with"		;; Undocumented in 1.1
       "`uvm_do_with"
       "`uvm_error"
       "`uvm_error_context"
       "`uvm_fatal"
       "`uvm_fatal_context"
       "`uvm_field_aa_int_byte"
       "`uvm_field_aa_int_byte_unsigned"
       "`uvm_field_aa_int_enum"
       "`uvm_field_aa_int_int"
       "`uvm_field_aa_int_int_unsigned"
       "`uvm_field_aa_int_integer"
       "`uvm_field_aa_int_integer_unsigned"
       "`uvm_field_aa_int_key"
       "`uvm_field_aa_int_longint"
       "`uvm_field_aa_int_longint_unsigned"
       "`uvm_field_aa_int_shortint"
       "`uvm_field_aa_int_shortint_unsigned"
       "`uvm_field_aa_int_string"
       "`uvm_field_aa_object_int"
       "`uvm_field_aa_object_string"
       "`uvm_field_aa_string_int"
       "`uvm_field_aa_string_string"
       "`uvm_field_array_enum"
       "`uvm_field_array_int"
       "`uvm_field_array_object"
       "`uvm_field_array_string"
       "`uvm_field_enum"
       "`uvm_field_event"
       "`uvm_field_int"
       "`uvm_field_object"
       "`uvm_field_queue_enum"
       "`uvm_field_queue_int"
       "`uvm_field_queue_object"
       "`uvm_field_queue_string"
       "`uvm_field_real"
       "`uvm_field_sarray_enum"
       "`uvm_field_sarray_int"
       "`uvm_field_sarray_object"
       "`uvm_field_sarray_string"
       "`uvm_field_string"
       "`uvm_field_utils"
       "`uvm_file"		;; Undocumented in 1.1, use `__FILE__
       "`uvm_get_imp_decl"
       "`uvm_get_peek_imp_decl"
       "`uvm_info"
       "`uvm_info_context"
       "`uvm_line"		;; Undocumented in 1.1, use `__LINE__
       "`uvm_master_imp_decl"
       "`uvm_non_blocking_transport_imp_decl"	;; Deprecated in 1.1
       "`uvm_nonblocking_get_imp_decl"
       "`uvm_nonblocking_get_peek_imp_decl"
       "`uvm_nonblocking_master_imp_decl"
       "`uvm_nonblocking_peek_imp_decl"
       "`uvm_nonblocking_put_imp_decl"
       "`uvm_nonblocking_slave_imp_decl"
       "`uvm_nonblocking_transport_imp_decl"
       "`uvm_object_param_utils"
       "`uvm_object_registry"
       "`uvm_object_registry_param"	;; Undocumented in 1.1
       "`uvm_object_utils"
       "`uvm_pack_array"
       "`uvm_pack_arrayN"
       "`uvm_pack_enum"
       "`uvm_pack_enumN"
       "`uvm_pack_int"
       "`uvm_pack_intN"
       "`uvm_pack_queue"
       "`uvm_pack_queueN"
       "`uvm_pack_real"
       "`uvm_pack_sarray"
       "`uvm_pack_sarrayN"
       "`uvm_pack_string"
       "`uvm_peek_imp_decl"
       "`uvm_put_imp_decl"
       "`uvm_rand_send"
       "`uvm_rand_send_pri"
       "`uvm_rand_send_pri_with"
       "`uvm_rand_send_with"
       "`uvm_record_attribute"
       "`uvm_record_field"
       "`uvm_register_cb"
       "`uvm_send"
       "`uvm_send_pri"
       "`uvm_sequence_utils"		;; Deprecated in 1.1
       "`uvm_set_super_type"
       "`uvm_slave_imp_decl"
       "`uvm_transport_imp_decl"
       "`uvm_unpack_array"
       "`uvm_unpack_arrayN"
       "`uvm_unpack_enum"
       "`uvm_unpack_enumN"
       "`uvm_unpack_int"
       "`uvm_unpack_intN"
       "`uvm_unpack_queue"
       "`uvm_unpack_queueN"
       "`uvm_unpack_real"
       "`uvm_unpack_sarray"
       "`uvm_unpack_sarrayN"
       "`uvm_unpack_string"
       "`uvm_update_sequence_lib"		;; Deprecated in 1.1
       "`uvm_update_sequence_lib_and_item"	;; Deprecated in 1.1
       "`uvm_warning"
       "`uvm_warning_context") nil )))


;;
;; Regular expressions used to calculate indent, etc.
;;
(defconst bsv-symbol-re      "\\<[a-zA-Z_][a-zA-Z_0-9.]*\\>")
;; Want to match
;; aa :
;; aa,bb :
;; a[34:32] :
;; a,
;;   b :
(defconst bsv-assignment-operator-re
  (eval-when-compile
     (bsv-regexp-opt
      `(
	;; blocking assignment_operator
	"=" "+=" "-=" "*=" "/=" "%=" "&=" "|=" "^=" "<<=" ">>=" "<<<=" ">>>="
	;; non blocking assignment operator
	"<="
	;; comparison
	"==" "!=" "===" "!===" "<=" ">=" "==\?" "!=\?"
	;; event_trigger
	"->" "->>"
	;; property_expr
	"|->" "|=>"
	;; Is this a legal bsv operator?
	":="
	) 't
      )))
(defconst bsv-assignment-operation-re
  (concat
;     "\\(^\\s-*[A-Za-z0-9_]+\\(\\[\\([A-Za-z0-9_]+\\)\\]\\)*\\s-*\\)"
;     "\\(^\\s-*[^=<>+-*/%&|^:\\s-]+[^=<>+-*/%&|^\n]*?\\)"
     "\\(^.*?\\)" "\\B" bsv-assignment-operator-re "\\B" ))

(defconst bsv-label-re (concat bsv-symbol-re "\\s-*:\\s-*"))
(defconst bsv-property-re
  (concat "\\(" bsv-label-re "\\)?"
	  "\\(\\(assert\\|assume\\|cover\\)\\>\\s-+\\<property\\>\\)\\|\\(assert\\)"))
	  ;;  "\\(assert\\|assume\\|cover\\)\\s-+property\\>"

(defconst bsv-no-indent-begin-re
  "\\<\\(if\\|else\\|while\\|for\\|repeat\\|always\\|always_comb\\|always_ff\\|always_latch\\)\\>")

(defconst bsv-ends-re
  ;; Parenthesis indicate type of keyword found
  (concat
   "\\(\\<else\\>\\)\\|"		; 1
   "\\(\\<if\\>\\)\\|"			; 2
   "\\(\\<assert\\>\\)\\|"              ; 3
   "\\(\\<end\\>\\)\\|"			; 3.1
   "\\(\\<endcase\\>\\)\\|"		; 4
   "\\(\\<endfunction\\>\\)\\|"		; 5
   "\\(\\<endtask\\>\\)\\|"		; 6
   "\\(\\<endspecify\\>\\)\\|"		; 7
   "\\(\\<endtable\\>\\)\\|"		; 8
   "\\(\\<endgenerate\\>\\)\\|"         ; 9
   "\\(\\<join\\(_any\\|_none\\)?\\>\\)\\|" ; 10
   "\\(\\<endclass\\>\\)\\|"            ; 11
   "\\(\\<endgroup\\>\\)\\|"            ; 12
   ;; BSV
   "\\(\\<endinterface\\>\\)\\|"
   "\\(\\<endmethod\\>\\)\\|"
   "\\(\\<endrule\\>\\)\\|"
   "\\(\\<endaction\\>\\)\\|"
   ;; VMM
   "\\(\\<`vmm_data_member_end\\>\\)\\|"
   "\\(\\<`vmm_env_member_end\\>\\)\\|"
   "\\(\\<`vmm_scenario_member_end\\>\\)\\|"
   "\\(\\<`vmm_subenv_member_end\\>\\)\\|"
   "\\(\\<`vmm_xactor_member_end\\>\\)\\|"
   ;; OVM
   "\\(\\<`ovm_component_utils_end\\>\\)\\|"
   "\\(\\<`ovm_field_utils_end\\>\\)\\|"
   "\\(\\<`ovm_object_utils_end\\>\\)\\|"
   "\\(\\<`ovm_sequence_utils_end\\>\\)\\|"
   "\\(\\<`ovm_sequencer_utils_end\\>\\)"
   ;; UVM
   "\\(\\<`uvm_component_utils_end\\>\\)\\|"
   "\\(\\<`uvm_field_utils_end\\>\\)\\|"
   "\\(\\<`uvm_object_utils_end\\>\\)\\|"
   "\\(\\<`uvm_sequence_utils_end\\>\\)\\|"
   "\\(\\<`uvm_sequencer_utils_end\\>\\)"
   ))

(defconst bsv-auto-end-comment-lines-re
  ;; Matches to names in this list cause auto-end-commenting
  (concat "\\("
	  bsv-directive-re "\\)\\|\\("
	  (eval-when-compile
	    (bsv-regexp-words
	     `( "begin"
		"else"
		"end"
		"endcase"
		"endclass"
		"endclocking"
		"endgroup"
		"endfunction"
		"endmodule"
		"endprogram"
		"endprimitive"
		"endinterface"
		"endpackage"
		"endsequence"
		"endspecify"
		"endtable"
		"endtask"
		"join"
		"join_any"
		"join_none"
		"module"
		"macromodule"
		"primitive"
		"interface"
		"package"
		"endinterface"
		"endmethod"
		"endrule"
		"endaction")))
	  "\\)"))

;;; NOTE: bsv-leap-to-head expects that bsv-end-block-re and
;;; bsv-end-block-ordered-re matches exactly the same strings.
(defconst bsv-end-block-ordered-re
  ;; Parenthesis indicate type of keyword found
  (concat "\\(\\<endcase\\>\\)\\|" ; 1
	  "\\(\\<end\\>\\)\\|"     ; 2
	  "\\(\\<end"              ; 3, but not used
	  "\\("                    ; 4, but not used
	  "\\(function\\)\\|"      ; 5
	  "\\(task\\)\\|"          ; 6
	  "\\(module\\)\\|"        ; 7
	  "\\(primitive\\)\\|"     ; 8
	  "\\(interface\\)\\|"     ; 9
	  "\\(package\\)\\|"       ; 10
	  "\\(class\\)\\|"         ; 11
          "\\(group\\)\\|"         ; 12
          "\\(program\\)\\|"	   ; 13
          "\\(sequence\\)\\|"	   ; 14
	  "\\(clocking\\)\\|"      ; 15
	  "\\)\\>\\)"))
(defconst bsv-end-block-re
  (eval-when-compile
    (bsv-regexp-words

     `("end"  ;; closes begin
       "endcase" ;; closes any of case, casex casez or randcase
       "join" "join_any" "join_none" ;; closes fork
       "endclass"
       "endtable"
       "endspecify"
       "endfunction"
       "endgenerate"
       "endmethod"
       "endrule"
       "endaction"
       "endtask"
       "endgroup"
       "endproperty"
       "endinterface"
       "endpackage"
       "endprogram"
       "endsequence"
       "endclocking"
       ;; OVM
       "`ovm_component_utils_end"
       "`ovm_field_utils_end"
       "`ovm_object_utils_end"
       "`ovm_sequence_utils_end"
       "`ovm_sequencer_utils_end"
       ;; UVM
       "`uvm_component_utils_end"
       "`uvm_field_utils_end"
       "`uvm_object_utils_end"
       "`uvm_sequence_utils_end"
       "`uvm_sequencer_utils_end"
       ;; VMM
       "`vmm_data_member_end"
       "`vmm_env_member_end"
       "`vmm_scenario_member_end"
       "`vmm_subenv_member_end"
       "`vmm_xactor_member_end"
       ))))


(defconst bsv-endcomment-reason-re
  ;; Parenthesis indicate type of keyword found
  (concat
   "\\(\\<begin\\>\\)\\|"		         ; 1
   "\\(\\<else\\>\\)\\|"		         ; 2
   "\\(\\<end\\>\\s-+\\<else\\>\\)\\|"	         ; 3
   "\\(\\<always_comb\\>\\(\[ \t\]*@\\)?\\)\\|"  ; 4
   "\\(\\<always_ff\\>\\(\[ \t\]*@\\)?\\)\\|"    ; 5
   "\\(\\<always_latch\\>\\(\[ \t\]*@\\)?\\)\\|" ; 6
   "\\(\\<fork\\>\\)\\|"			 ; 7
   "\\(\\<always\\>\\(\[ \t\]*@\\)?\\)\\|"
   "\\(\\<if\\>\\)\\|"
   bsv-property-re "\\|"
   "\\(\\(" bsv-label-re "\\)?\\<assert\\>\\)\\|"
   "\\(\\<clocking\\>\\)\\|"
   "\\(\\<task\\>\\)\\|"
   "\\(\\<function\\>\\)\\|"
   "\\(\\<initial\\>\\)\\|"
   "\\(\\<interface\\>\\)\\|"
   "\\(\\<package\\>\\)\\|"
   "\\(\\<final\\>\\)\\|"
   "\\(@\\)\\|"
   "\\(\\<while\\>\\)\\|"
   "\\(\\<for\\(ever\\|each\\)?\\>\\)\\|"
   "\\(\\<repeat\\>\\)\\|\\(\\<wait\\>\\)\\|"
   "#"))

(defconst bsv-named-block-re  "begin[ \t]*:")

;; These words begin a block which can occur inside a module which should be indented,
;; and closed with the respective word from the end-block list

(defconst bsv-beg-block-re
  (eval-when-compile
    (bsv-regexp-words
     `("begin"
       "case" "casex" "casez" "randcase"
       "clocking"
       "generate"
       "method"
       "rule"
       "action"
       "fork"
       "function"
       "property"
       "specify"
       "table"
       "task"
       ;; OVM
       "`ovm_component_utils_begin"
       "`ovm_component_param_utils_begin"
       "`ovm_field_utils_begin"
       "`ovm_object_utils_begin"
       "`ovm_object_param_utils_begin"
       "`ovm_sequence_utils_begin"
       "`ovm_sequencer_utils_begin"
       ;; UVM
       "`uvm_component_utils_begin"
       "`uvm_component_param_utils_begin"
       "`uvm_field_utils_begin"
       "`uvm_object_utils_begin"
       "`uvm_object_param_utils_begin"
       "`uvm_sequence_utils_begin"
       "`uvm_sequencer_utils_begin"
       ;; VMM
       "`vmm_data_member_begin"
       "`vmm_env_member_begin"
       "`vmm_scenario_member_begin"
       "`vmm_subenv_member_begin"
       "`vmm_xactor_member_begin"
       ))))
;; These are the same words, in a specific order in the regular
;; expression so that matching will work nicely for
;; bsv-forward-sexp and bsv-calc-indent
(defconst bsv-beg-block-re-ordered
  ( concat "\\(\\<begin\\>\\)"		;1
	   "\\|\\(\\<randcase\\>\\|\\(\\<unique\\s-+\\|priority\\s-+\\)?case[xz]?\\>\\)" ; 2,3
	   "\\|\\(\\(\\<disable\\>\\s-+\\|\\<wait\\>\\s-+\\)?fork\\>\\)" ;4,5
	   "\\|\\(\\<class\\>\\)"		;6
	   "\\|\\(\\<table\\>\\)"		;7
	   "\\|\\(\\<specify\\>\\)"		;8
	   "\\|\\(\\<function\\>\\)"		;9
	   "\\|\\(\\(\\(\\<virtual\\>\\s-+\\)\\|\\(\\<protected\\>\\s-+\\)\\)*\\<function\\>\\)"	;10
	   "\\|\\(\\<task\\>\\)"		;14
	   "\\|\\(\\(\\(\\<virtual\\>\\s-+\\)\\|\\(\\<protected\\>\\s-+\\)\\)*\\<task\\>\\)"	;15
	   "\\|\\(\\<generate\\>\\)"		;18
	   "\\|\\(\\<covergroup\\>\\)"	;16 20
	   "\\|\\(\\(\\(\\<cover\\>\\s-+\\)\\|\\(\\<assert\\>\\s-+\\)\\)*\\<property\\>\\)"	;17 21
	   "\\|\\(\\<\\(rand\\)?sequence\\>\\)" ;21 25
	   "\\|\\(\\<clocking\\>\\)"          ;22 27
	   "\\|\\(\\<`[ou]vm_[a-z_]+_begin\\>\\)" ;28
           "\\|\\(\\<`vmm_[a-z_]+_member_begin\\>\\)"
	   "\\|\\(\\<method\\>\\)"
	   "\\|\\(\\<rule\\>\\)"
	   "\\|\\(\\<action\\>\\)"
	   ;;

	   ))

(defconst bsv-end-block-ordered-rry
  [ "\\(\\<begin\\>\\)\\|\\(\\<end\\>\\)\\|\\(\\<endcase\\>\\)\\|\\(\\<join\\(_any\\|_none\\)?\\>\\)"
    "\\(\\<randcase\\>\\|\\<case[xz]?\\>\\)\\|\\(\\<endcase\\>\\)"
    "\\(\\<fork\\>\\)\\|\\(\\<join\\(_any\\|_none\\)?\\>\\)"
    "\\(\\<class\\>\\)\\|\\(\\<endclass\\>\\)"
    "\\(\\<table\\>\\)\\|\\(\\<endtable\\>\\)"
    "\\(\\<specify\\>\\)\\|\\(\\<endspecify\\>\\)"
    "\\(\\<function\\>\\)\\|\\(\\<endfunction\\>\\)"
    "\\(\\<generate\\>\\)\\|\\(\\<endgenerate\\>\\)"
    "\\(\\<task\\>\\)\\|\\(\\<endtask\\>\\)"
    "\\(\\<covergroup\\>\\)\\|\\(\\<endgroup\\>\\)"
    "\\(\\<property\\>\\)\\|\\(\\<endproperty\\>\\)"
    "\\(\\<\\(rand\\)?sequence\\>\\)\\|\\(\\<endsequence\\>\\)"
    "\\(\\<clocking\\>\\)\\|\\(\\<endclocking\\>\\)"
    "\\(\\<method\\>\\)\\|\\(\\<endmethod\\>\\)"
    "\\(\\<rule\\>\\)\\|\\(\\<endrule\\>\\)"
    "\\(\\<action\\>\\)\\|\\(\\<endaction\\>\\)"
    ] )

(defconst bsv-nameable-item-re
  (eval-when-compile
    (bsv-regexp-words
     `("begin"
       "fork"
       "join" "join_any" "join_none"
       "end"
       "endcase"
       "endconfig"
       "endclass"
       "endclocking"
       "endfunction"
       "endgenerate"
       "endmethod"
       "endrule"
       "endaction"
       "endmodule"
       "endprimitive"
       "endinterface"
       "endpackage"
       "endspecify"
       "endtable"
       "endtask" )
     )))

(defconst bsv-declaration-opener
  (eval-when-compile
    (bsv-regexp-words
     `("module" "begin" "task" "function"))))

(defconst bsv-declaration-prefix-re
  (eval-when-compile
    (bsv-regexp-words
     `(
       ;; port direction
       "inout" "input" "output" "ref"
       ;; changeableness
       "const" "static" "protected" "local"
       ;; parameters
       "localparam" "parameterx" "var"
       ;; type creation
       "typedef"
       ))))
(defconst bsv-declaration-core-re
  (eval-when-compile
    (bsv-regexp-words
     `(
       ;; port direction (by themselves)
       "inout" "input" "output"
       ;; integer_atom_type
       "byte" "shortint" "int" "longint" "integer" "time"
       ;; integer_vector_type
       "bit" "logic" "reg"
       ;; non_integer_type
       "shortreal" "real" "realtime"
       ;; net_type
       "supply0" "supply1" "tri" "triand" "trior" "trireg" "tri0" "tri1" "uwire" "wire" "wand" "wor"
       ;; misc
       "string" "event" "chandle" "virtual" "enum" "genvar"
       "struct" "union"
       ;; builtin classes
       "mailbox" "semaphore"
       ))))
(defconst bsv-declaration-re
  (concat "\\(" bsv-declaration-prefix-re "\\s-*\\)?" bsv-declaration-core-re))
(defconst bsv-range-re "\\(\\[[^]]*\\]\\s-*\\)+")
(defconst bsv-optional-signed-re "\\s-*\\(signed\\)?")
(defconst bsv-optional-signed-range-re
  (concat
   "\\s-*\\(\\<\\(reg\\|wire\\)\\>\\s-*\\)?\\(\\<signed\\>\\s-*\\)?\\(" bsv-range-re "\\)?"))
(defconst bsv-macroexp-re "`\\sw+")

(defconst bsv-delay-re "#\\s-*\\(\\([0-9_]+\\('s?[hdxbo][0-9a-fA-F_xz]+\\)?\\)\\|\\(([^()]*)\\)\\|\\(\\sw+\\)\\)")
(defconst bsv-declaration-re-2-no-macro
  (concat "\\s-*" bsv-declaration-re
	  "\\s-*\\(\\(" bsv-optional-signed-range-re "\\)\\|\\(" bsv-delay-re "\\)"
	  "\\)?"))
(defconst bsv-declaration-re-2-macro
  (concat "\\s-*" bsv-declaration-re
	  "\\s-*\\(\\(" bsv-optional-signed-range-re "\\)\\|\\(" bsv-delay-re "\\)"
	  "\\|\\(" bsv-macroexp-re "\\)"
	  "\\)?"))
(defconst bsv-declaration-re-1-macro
  (concat "^" bsv-declaration-re-2-macro))

(defconst bsv-declaration-re-1-no-macro (concat "^" bsv-declaration-re-2-no-macro))

(defconst bsv-defun-re
  (eval-when-compile (bsv-regexp-words `("macromodule" "module" "class" "program" "interface" "package" "primitive" "config"))))
(defconst bsv-end-defun-re
  (eval-when-compile (bsv-regexp-words `("endmodule" "endclass" "endprogram" "endinterface" "endpackage" "endprimitive" "endconfig"))))
(defconst bsv-zero-indent-re
  (concat bsv-defun-re "\\|" bsv-end-defun-re))
(defconst bsv-inst-comment-re
  (eval-when-compile (bsv-regexp-words `("Outputs" "Inouts" "Inputs" "Interfaces" "Interfaced"))))

(defconst bsv-behavioral-block-beg-re
  (eval-when-compile (bsv-regexp-words `("initial" "final" "always" "always_comb" "always_latch" "always_ff"
					     "function" "task"))))
(defconst bsv-coverpoint-re "\\w+\\s*:\\s*\\(coverpoint\\|cross\\constraint\\)"  )
(defconst bsv-indent-re
  (eval-when-compile
    (bsv-regexp-words
     `(
       "{"
       "always" "always_latch" "always_ff" "always_comb"
       "begin" "end"
;       "unique" "priority"
       "case" "casex" "casez" "randcase" "endcase"
       "class" "endclass"
       "clocking" "endclocking"
       "config" "endconfig"
       "covergroup" "endgroup"
       "fork" "join" "join_any" "join_none"
       "function" "endfunction"
       "final"
       "generate" "endgenerate"
       "method" "endmethod"
       "rule" "endrule"
       "action" "endaction"
       "initial"
       "interface" "endinterface"
       "module" "macromodule" "endmodule"
       "package" "endpackage"
       "primitive" "endprimitive"
       "program" "endprogram"
       "property" "endproperty"
       "sequence" "randsequence" "endsequence"
       "specify" "endspecify"
       "table" "endtable"
       "task" "endtask"
       "virtual"
       "`case"
       "`default"
       "`define" "`undef"
       "`if" "`ifdef" "`ifndef" "`else" "`elsif" "`endif"
       "`while" "`endwhile"
       "`for" "`endfor"
       "`format"
       "`include"
       "`let"
       "`protect" "`endprotect"
       "`switch" "`endswitch"
       "`timescale"
       "`time_scale"
       ;; OVM Begin tokens
       "`ovm_component_utils_begin"
       "`ovm_component_param_utils_begin"
       "`ovm_field_utils_begin"
       "`ovm_object_utils_begin"
       "`ovm_object_param_utils_begin"
       "`ovm_sequence_utils_begin"
       "`ovm_sequencer_utils_begin"
       ;; OVM End tokens
       "`ovm_component_utils_end"
       "`ovm_field_utils_end"
       "`ovm_object_utils_end"
       "`ovm_sequence_utils_end"
       "`ovm_sequencer_utils_end"
       ;; UVM Begin tokens
       "`uvm_component_utils_begin"
       "`uvm_component_param_utils_begin"
       "`uvm_field_utils_begin"
       "`uvm_object_utils_begin"
       "`uvm_object_param_utils_begin"
       "`uvm_sequence_utils_begin"
       "`uvm_sequencer_utils_begin"
       ;; UVM End tokens
       "`uvm_component_utils_end"	;; Typo in spec, it's not uvm_component_end
       "`uvm_field_utils_end"
       "`uvm_object_utils_end"
       "`uvm_sequence_utils_end"
       "`uvm_sequencer_utils_end"
       ;; VMM Begin tokens
       "`vmm_data_member_begin"
       "`vmm_env_member_begin"
       "`vmm_scenario_member_begin"
       "`vmm_subenv_member_begin"
       "`vmm_xactor_member_begin"
       ;; VMM End tokens
       "`vmm_data_member_end"
       "`vmm_env_member_end"
       "`vmm_scenario_member_end"
       "`vmm_subenv_member_end"
       "`vmm_xactor_member_end"
       ))))

(defconst bsv-defun-level-not-generate-re
  (eval-when-compile
    (bsv-regexp-words
     `( "module" "macromodule" "primitive" "class" "program"
	"interface" "package" "config"))))

(defconst bsv-defun-level-re
  (eval-when-compile
    (bsv-regexp-words
     (append
      `( "module" "macromodule" "primitive" "class" "program"
	 "interface" "package" "config")
      `( "initial" "final" "always" "always_comb" "always_ff"
	 "always_latch" "endtask" "endfunction" )))))

(defconst bsv-defun-level-generate-only-re
  (eval-when-compile
    (bsv-regexp-words
     `( "initial" "final" "always" "always_comb" "always_ff"
	"always_latch" "endtask" "endfunction"))))

(defconst bsv-cpp-level-re
  (eval-when-compile
    (bsv-regexp-words
     `(
       "endmodule" "endprimitive" "endinterface" "endpackage" "endprogram" "endclass"
       ))))
(defconst bsv-disable-fork-re "\\(disable\\|wait\\)\\s-+fork\\>")
(defconst bsv-extended-case-re "\\(unique\\s-+\\|priority\\s-+\\)?case[xz]?")
(defconst bsv-extended-complete-re
  (concat "\\(\\<extern\\s-+\\|\\<\\(\\<pure\\>\\s-+\\)?virtual\\s-+\\|\\<protected\\s-+\\)*\\(\\<function\\>\\|\\<task\\>\\)"
	  "\\|\\(\\<typedef\\>\\s-+\\)*\\(\\<struct\\>\\|\\<union\\>\\|\\<class\\>\\)"
	  "\\|\\(\\<import\\>\\s-+\\)?\"DPI-C\"\\s-+\\(function\\>\\|task\\>\\)"
	  "\\|" bsv-extended-case-re ))
(defconst bsv-basic-complete-re
  (eval-when-compile
    (bsv-regexp-words
     `(
       "always" "assign" "always_latch" "always_ff" "always_comb" "constraint"
       "import" "initial" "final" "module" "macromodule" "repeat" "randcase" "while"
       "if" "for" "forever" "foreach" "else" "parameterx" "do" "localparam" "assert"
       ))))
(defconst bsv-complete-reg
  (concat
   bsv-extended-complete-re
   "\\|"
   bsv-basic-complete-re))

(defconst bsv-end-statement-re
  (concat "\\(" bsv-beg-block-re "\\)\\|\\("
	  bsv-end-block-re "\\)"))

(defconst bsv-endcase-re
  (concat bsv-extended-case-re "\\|"
	  "\\(endcase\\)\\|"
	  bsv-defun-re
	  ))

(defconst bsv-exclude-str-start "/* -----\\/----- EXCLUDED -----\\/-----"
  "String used to mark beginning of excluded text.")
(defconst bsv-exclude-str-end " -----/\\----- EXCLUDED -----/\\----- */"
  "String used to mark end of excluded text.")
(defconst bsv-preprocessor-re
  (eval-when-compile
    (bsv-regexp-words
     `(
       "`define" "`include" "`ifdef" "`ifndef" "`if" "`endif" "`else"
       ))))

(defconst bsv-keywords
  '( "`case" "`default" "`define" "`else" "`endfor" "`endif"
     "`endprotect" "`endswitch" "`endwhile" "`for" "`format" "`if" "`ifdef"
     "`ifndef" "`include" "`let" "`protect" "`switch" "`timescale"
     "`time_scale" "`undef" "`while"

     "method" "endmethod" "rule" "endrule" "action" "endaction"
     "seq" "endseq" "par" "endpar" "rules" "endrules"
     "provisos" "return" "parameterx" "deriving"
     "typeclass" "endtypeclass" "instance" "endinstance" 

     "after" "alias" "always" "always_comb" "always_ff" "always_latch" "and"
     "assert" "assign" "assume" "automatic" "before" "begin" "bind"
     "bins" "binsof" "bit" "break" "buf" "bufif0" "bufif1" "byte"
     "case" "casex" "casez" "cell" "chandle" "class" "clocking" "cmos"
     "config" "const" "constraint" "context" "continue" "cover"
     "covergroup" "coverpoint" "cross" "deassign" "default" "defparam"
     "design" "disable" "dist" "do" "edge" "else" "end" "endcase"
     "endclass" "endclocking" "endconfig" "endfunction" "endgenerate"
     "endgroup" "endinterface" "endmodule" "endpackage" "endprimitive"
     "endprogram" "endproperty" "endspecify" "endsequence" "endtable"
     "endtask" "enum" "event" "expect" "export" "extends" "extern"
     "final" "first_match" "for" "force" "foreach" "forever" "fork"
     "forkjoin" "function" "generate" "genvar" "highz0" "highz1" "if"
     "iff" "ifnone" "ignore_bins" "illegal_bins" "import" "incdir"
     "include" "initial" "inout" "input" "inside" "instance" "int"
     "integer" "interface" "intersect" "join" "join_any" "join_none"
     "large" "liblist" "library" "local" "localparam" "logic"
     "longint" "macromodule" "mailbox" "matches" "medium" "modport" "module"
     "nand" "negedge" "new" "nmos" "nor" "noshowcancelled" "not"
     "notif0" "notif1" "null" "or" "output" "package" "packed"
     "parameterx" "pmos" "posedge" "primitive" "priority" "program"
     "property" "protected" "pull0" "pull1" "pulldown" "pullup"
     "pulsestyle_onevent" "pulsestyle_ondetect" "pure" "rand" "randc"
     "randcase" "randsequence" "rcmos" "real" "realtime" "ref" "reg"
     "release" "repeat" "return" "rnmos" "rpmos" "rtran" "rtranif0"
     "rtranif1" "scalared" "semaphore" "sequence" "shortint" "shortreal"
     "showcancelled" "signed" "small" "solve" "specify" "specparam"
     "static" "string" "strong0" "strong1" "struct" "super" "supply0"
     "supply1" "table" "tagged" "task" "this" "throughout" "time"
     "timeprecision" "timeunit" "tran" "tranif0" "tranif1" "tri"
     "tri0" "tri1" "triand" "trior" "trireg" "type" "typedef" "union"
     "unique" "unsigned" "use" "uwire" "var" "vectored" "virtual" "void"
     "wait" "wait_order" "wand" "weak0" "weak1" "while" "wildcard"
     "wire" "with" "within" "wor" "xnor" "xor"
     ;; 1800-2009
     "accept_on" "checker" "endchecker" "eventually" "global" "implies"
     "let" "nexttime" "reject_on" "restrict" "s_always" "s_eventually"
     "s_nexttime" "s_until" "s_until_with" "strong" "sync_accept_on"
     "sync_reject_on" "unique0" "until" "until_with" "untyped" "weak"
 )
 "List of BSV keywords.")

(defconst bsv-comment-start-regexp "//\\|/\\*"
  "Dual comment value for `comment-start-regexp'.")

(defvar bsv-mode-syntax-table
  (let ((table (make-syntax-table)))
    ;; Populate the syntax TABLE.
    (modify-syntax-entry ?\\ "\\" table)
    (modify-syntax-entry ?+ "." table)
    (modify-syntax-entry ?- "." table)
    (modify-syntax-entry ?= "." table)
    (modify-syntax-entry ?% "." table)
    (modify-syntax-entry ?< "." table)
    (modify-syntax-entry ?> "." table)
    (modify-syntax-entry ?& "." table)
    (modify-syntax-entry ?| "." table)
    (modify-syntax-entry ?` "w" table)
    (modify-syntax-entry ?_ "w" table)
    (modify-syntax-entry ?\' "." table)

    ;; Set up TABLE to handle block and line style comments.
    (if (featurep 'xemacs)
	(progn
	  ;; XEmacs (formerly Lucid) has the best implementation
	  (modify-syntax-entry ?/  ". 1456" table)
	  (modify-syntax-entry ?*  ". 23"   table)
	  (modify-syntax-entry ?\n "> b"    table))
      ;; Emacs does things differently, but we can work with it
      (modify-syntax-entry ?/  ". 124b" table)
      (modify-syntax-entry ?*  ". 23"   table)
      (modify-syntax-entry ?\n "> b"    table))
    table)
  "Syntax table used in BSV mode buffers.")

(defvar bsv-font-lock-keywords nil
  "Default highlighting for BSV mode.")

(defvar bsv-font-lock-keywords-1 nil
  "Subdued level highlighting for BSV mode.")

(defvar bsv-font-lock-keywords-2 nil
  "Medium level highlighting for BSV mode.
See also `bsv-font-lock-extra-types'.")

(defvar bsv-font-lock-keywords-3 nil
  "Gaudy level highlighting for BSV mode.
See also `bsv-font-lock-extra-types'.")
(defvar  bsv-font-lock-translate-off-face
  'bsv-font-lock-translate-off-face
  "Font to use for translated off regions.")
(defface bsv-font-lock-translate-off-face
  '((((class color)
      (background light))
     (:background "gray90" :italic t ))
    (((class color)
      (background dark))
     (:background "gray10" :italic t ))
    (((class grayscale) (background light))
     (:foreground "DimGray" :italic t))
    (((class grayscale) (background dark))
     (:foreground "LightGray" :italic t))
    (t (:italis t)))
  "Font lock mode face used to background highlight translate-off regions."
  :group 'font-lock-highlighting-faces)

(defvar bsv-font-lock-p1800-face
  'bsv-font-lock-p1800-face
  "Font to use for p1800 keywords.")
(defface bsv-font-lock-p1800-face
  '((((class color)
      (background light))
     (:foreground "DarkOrange3" :bold t ))
    (((class color)
      (background dark))
     (:foreground "orange1" :bold t ))
    (t (:italic t)))
  "Font lock mode face used to highlight P1800 keywords."
  :group 'font-lock-highlighting-faces)

(defvar bsv-font-lock-ams-face
  'bsv-font-lock-ams-face
  "Font to use for Analog/Mixed Signal keywords.")
(defface bsv-font-lock-ams-face
  '((((class color)
      (background light))
     (:foreground "Purple" :bold t ))
    (((class color)
      (background dark))
     (:foreground "orange1" :bold t ))
    (t (:italic t)))
  "Font lock mode face used to highlight AMS keywords."
  :group 'font-lock-highlighting-faces)

(defvar bsv-font-grouping-keywords-face
  'bsv-font-lock-grouping-keywords-face
  "Font to use for BSV Grouping Keywords (such as begin..end).")
(defface bsv-font-lock-grouping-keywords-face
  '((((class color)
      (background light))
     (:foreground "red4" :bold t ))
    (((class color)
      (background dark))
     (:foreground "red4" :bold t ))
    (t (:italic t)))
  "Font lock mode face used to highlight bsv grouping keywords."
  :group 'font-lock-highlighting-faces)

(let* ((bsv-type-font-keywords
	(eval-when-compile
	  (bsv-regexp-opt
	   '(
	     "and" "bit" "buf" "bufif0" "bufif1" "cmos" "defparam"
	     "event" "genvar" "inout" "input" "integer" "localparam"
	     "logic" "mailbox" "nand" "nmos" "not" "notif0" "notif1" "or"
	     "output" "parameterx" "pmos" "pull0" "pull1" "pulldown" "pullup"
	     "rcmos" "real" "realtime" "reg" "rnmos" "rpmos" "rtran"
	     "rtranif0" "rtranif1" "semaphore" "signed" "struct" "supply"
	     "supply0" "supply1" "time" "tran" "tranif0" "tranif1"
	     "tri" "tri0" "tri1" "triand" "trior" "trireg" "typedef"
	     "uwire" "vectored" "wand" "wire" "wor" "xnor" "xor"
	     ) nil  )))
       (bsv-type-types
	(eval-when-compile
	  (bsv-regexp-opt
	   '(
	     "enum"
	     ) nil )))
       (bsv-pragma-keywords
	(eval-when-compile
	  (bsv-regexp-opt
	   '("surefire" "synopsys" "rtl_synthesis" "verilint" "leda" "0in") nil
	    )))
       (bsv-attr-keywords
	(eval-when-compile
	  (bsv-regexp-opt
	   '("synthesize" "noinline" "always_enabled" "always_ready" "preempts"
	     "parameter"
	     "no_implicit_conditions" "fire_when_enabled" 
	     "clocked_by" "reset_by"
	     "aggressive_implicit_conditions" "options") nil
	    )))
       (bsv-1800-2005-keywords
	(eval-when-compile
	  (bsv-regexp-opt
	   '("alias" "assert" "assume" "automatic" "before" "bind"
	     "bins" "binsof" "break" "byte" "cell" "chandle" "class"
	     "clocking" "config" "const" "constraint" "context" "continue"
	     "cover" "covergroup" "coverpoint" "cross" "deassign" "design"
	     "dist" "do" "edge" "endclass" "endclocking" "endconfig"
	     "endgroup" "endprogram" "endproperty" "endsequence" "enum"
	     "expect" "export" "extends" "extern" "first_match" "foreach"
	     "forkjoin" "genvar" "highz0" "highz1" "ifnone" "ignore_bins"
	     "illegal_bins" "import" "incdir" "include" "inside" "instance"
	     "int" "intersect" "large" "liblist" "library" "local" "longint"
	     "matches" "medium" "modport" "new" "noshowcancelled" "null"
	     "packed" "program" "property" "protected" "pull0" "pull1"
	     "pulsestyle_onevent" "pulsestyle_ondetect" "pure" "rand" "randc"
	     "randcase" "randsequence" "ref" "release" "return" "scalared"
	     "sequence" "shortint" "shortreal" "showcancelled" "small" "solve"
	     "specparam" "static" "string" "strong0" "strong1" "struct"
	     "super" "tagged" "this" "throughout" "timeprecision" "timeunit"
	     "type" "union" "unsigned" "use" "var" "virtual" "void"
	     "wait_order" "weak0" "weak1" "wildcard" "with" "within"
	     ) nil )))

       (bsv-1800-2009-keywords
	(eval-when-compile
	  (bsv-regexp-opt
	   '("accept_on" "checker" "endchecker" "eventually" "global"
	     "implies" "let" "nexttime" "reject_on" "restrict" "s_always"
	     "s_eventually" "s_nexttime" "s_until" "s_until_with" "strong"
	     "sync_accept_on" "sync_reject_on" "unique0" "until"
	     "until_with" "untyped" "weak" ) nil )))

       (bsv-ams-keywords
	(eval-when-compile
	  (bsv-regexp-opt
	   '("above" "abs" "absdelay" "acos" "acosh" "ac_stim"
	     "aliasparam" "analog" "analysis" "asin" "asinh" "atan" "atan2" "atanh"
	     "branch" "ceil" "connectmodule" "connectrules" "cos" "cosh" "ddt"
	     "ddx" "discipline" "driver_update" "enddiscipline" "endconnectrules"
	     "endnature" "endparamset" "exclude" "exp" "final_step" "flicker_noise"
	     "floor" "flow" "from" "ground" "hypot" "idt" "idtmod" "inf"
	     "initial_step" "laplace_nd" "laplace_np" "laplace_zd" "laplace_zp"
	     "last_crossing" "limexp" "ln" "log" "max" "min" "nature"
	     "net_resolution" "noise_table" "paramset" "potential" "pow" "sin"
	     "sinh" "slew" "sqrt" "tan" "tanh" "timer" "transition" "white_noise"
	     "wreal" "zi_nd" "zi_np" "zi_zd" ) nil )))

       (bsv-font-keywords
	(eval-when-compile
	  (bsv-regexp-opt
	   '(
	     "assign" "case" "casex" "casez" "randcase" "deassign"
	     "default" "disable" "else" "endcase" "endfunction"
	     "endgenerate" "endinterface" "endmodule" "endprimitive"
	     "endspecify" "endtable" "endtask" "final" "for" "force" "return" "break"
	     "continue" "forever" "fork" "function" "generate" "if" "iff" "initial"
	     "interface" "join" "join_any" "join_none" "macromodule" "module" "negedge"
	     "package" "endpackage" "always" "always_comb" "always_ff"
	     "always_latch" "posedge" "primitive" "priority" "release"
	     "repeat" "specify" "table" "task" "unique" "wait" "while"
	     "class" "program" "endclass" "endprogram"
	     "method" "endmethod" "rule" "endrule" "action" "endaction"
	     "seq" "endseq" "par" "endpar" "rules" "endrules" 
	     "let" "begin" "end" "import" "type" "matches" "tagged" "union"
;;	     "Eq" "Bits" "Bounded" "FShow" 
	     "typedef" "enum" "struct"
	     "provisos" "return" "parameterx" "deriving"
	     "typeclass" "endtypeclass" "instance" "endinstance"
	     ) nil  )))

       (bsv-font-grouping-keywords
	(eval-when-compile
	  (bsv-regexp-opt
	   '( "begin" "end" ) nil  ))))

  (setq bsv-font-lock-keywords
	(list
	 ;; Fontify all builtin keywords
	 (concat "\\<\\(" bsv-font-keywords "\\|"
		       ;; And user/system tasks and functions
              "\\$[a-zA-Z][a-zA-Z0-9_\\$]*"
              "\\)\\>")
	 ;; Fontify all types
	 (if bsv-highlight-grouping-keywords
	     (cons (concat "\\<\\(" bsv-font-grouping-keywords "\\)\\>")
		   'bsv-font-lock-ams-face)
	   (cons (concat "\\<\\(" bsv-font-grouping-keywords "\\)\\>")
		 'font-lock-type-face))
	 (cons (concat "\\<\\(" bsv-type-font-keywords "\\)\\>")
          'font-lock-type-face)
	 ;; Fontify IEEE-1800-2005 keywords appropriately
	 (if bsv-highlight-p1800-keywords
	     (cons (concat "\\<\\(" bsv-1800-2005-keywords "\\)\\>")
		   'bsv-font-lock-p1800-face)
	   (cons (concat "\\<\\(" bsv-1800-2005-keywords "\\)\\>")
		 'font-lock-type-face))
	 ;; Fontify IEEE-1800-2009 keywords appropriately
	 (if bsv-highlight-p1800-keywords
	     (cons (concat "\\<\\(" bsv-1800-2009-keywords "\\)\\>")
		   'bsv-font-lock-p1800-face)
	   (cons (concat "\\<\\(" bsv-1800-2009-keywords "\\)\\>")
		 'font-lock-type-face))
	 ;; Fontify BSV-AMS keywords
;;	 (cons (concat "\\<\\(" bsv-ams-keywords "\\)\\>")
;;	       'bsv-font-lock-ams-face)
	 ))

  (setq bsv-font-lock-keywords-1
	(append bsv-font-lock-keywords
		(list
		 ;; Fontify module definitions
		 (list
		  "\\<\\(\\(macro\\)?module\\|primitive\\|class\\|program\\|interface\\|package\\|task\\)\\>\\s-*\\(\\sw+\\)"
		  '(1 font-lock-keyword-face)
		  '(3 font-lock-function-name-face 'prepend))
		 ;; Fontify function definitions
		 (list
		  (concat "\\<function\\>\\s-+\\(integer\\|real\\(time\\)?\\|time\\)\\s-+\\([a-z]+\\sw+\\)" )
		       '(1 font-lock-keyword-face)
		       '(3 font-lock-constant-face prepend))
		 '("\\<function\\>\\s-+\\(\\[[^]]+\\]\\)\\s-+\\([a-z]+\\sw+\\)"
		   (1 font-lock-keyword-face)
		   (2 font-lock-constant-face append))
		 '("\\<function\\>\\s-+\\([a-z]+\\sw+\\)"
		   1 'font-lock-constant-face append))))

  (setq bsv-font-lock-keywords-2
	(append bsv-font-lock-keywords-1
		(list
		 (cons (concat "\\<\\(" bsv-type-types "\\)\\>") 
		       'font-lock-type-face)
		 ;; Fontify bsv attributes
		 (cons (concat "\\<\\(" bsv-attr-keywords "\\)\\>")
		       'font-lock-constant-face)
		 ;; Fontify pragmas
		 (concat "\\(//\\s-*" bsv-pragma-keywords "\\s-.*\\)")
		 ;; Fontify escaped names
		 '("\\(\\\\\\S-*\\s-\\)"  0 font-lock-function-name-face)
;		 '("\\(//\\s-*synthesize\\)"  0 font-lock-constant-face)
		 ;; Fontify macro definitions/ uses
		 '("`\\s-*[A-Za-z][A-Za-z0-9_]*" 0 (if (boundp 'font-lock-preprocessor-face)
						       'font-lock-preprocessor-face
						     'font-lock-type-face))
		 ;; Fontify delays/numbers
;;		 '("\\(@\\)\\|\\(#\\s-*\\(\\(\[0-9_.\]+\\('s?[hdxbo][0-9a-fA-F_xz]*\\)?\\)\\|\\(([^()]+)\\|\\sw+\\)\\)\\)"
;;		   0 font-lock-type-face append)
		 ;; Fontify instantiation names
		 '("[^A-Za-z0-9_.]+\\([A-Za-z][A-Za-z0-9_]*\\)\\s-*(" 1 font-lock-function-name-face)
		 '("<-[^A-Za-z0-9_.]+\\([A-Za-z][A-Za-z0-9_]*\\)\\s-*;" 1 font-lock-function-name-face)
		 '("(+\\([A-Za-z][A-Za-z0-9_]*\\)\\s-*(" 1 font-lock-function-name-face)
		 '("rule\\s-+\\([A-Za-z][A-Za-z0-9_]*\\)\\s-+" 1 font-lock-function-name-face)
		 '("rule\\s-+\\([A-Za-z][A-Za-z0-9_]*\\);" 1 font-lock-function-name-face)
		 '("[^A-Za-z0-9_.]+\\([A-Z]+[A-Za-z0-9_]*\\)" 1 font-lock-type-face)
		 )))

  (setq bsv-font-lock-keywords-3
	(append bsv-font-lock-keywords-2
		(when bsv-highlight-translate-off
		  (list
		   ;; Fontify things in translate off regions
		   '(bsv-match-translate-off
		     (0 'bsv-font-lock-translate-off-face prepend))
		   )))))

;;
;; Buffer state preservation

(defmacro bsv-save-buffer-state (&rest body)
  "Execute BODY forms, saving state around insignificant change.
Changes in text properties like `face' or `syntax-table' are
considered insignificant.  This macro allows text properties to
be changed, even in a read-only buffer.

A change is considered significant if it affects the buffer text
in any way that isn't completely restored again.  Any
user-visible changes to the buffer must not be within a
`bsv-save-buffer-state'."
  ;; From c-save-buffer-state
  `(let* ((modified (buffer-modified-p))
	  (buffer-undo-list t)
	  (inhibit-read-only t)
	  (inhibit-point-motion-hooks t)
	  (bsv-no-change-functions t)
	  before-change-functions
	  after-change-functions
	  deactivate-mark
	  buffer-file-name ; Prevent primitives checking
	  buffer-file-truename)	; for file modification
     (unwind-protect
	 (progn ,@body)
       (and (not modified)
	    (buffer-modified-p)
	    (set-buffer-modified-p nil)))))

(defmacro bsv-save-no-change-functions (&rest body)
  "Execute BODY forms, disabling all change hooks in BODY.
For insignificant changes, see instead `bsv-save-buffer-state'."
  `(let* ((inhibit-point-motion-hooks t)
	  (bsv-no-change-functions t)
	  before-change-functions
	  after-change-functions)
     (progn ,@body)))

;;
;; Comment detection and caching

(defvar bsv-scan-cache-preserving nil
  "If set, the specified buffer's comment properties are static.
Buffer changes will be ignored.  See `bsv-inside-comment-or-string-p'
and `bsv-scan'.")

(defvar bsv-scan-cache-tick nil
  "Modification tick at which `bsv-scan' was last completed.")
(make-variable-buffer-local 'bsv-scan-cache-tick)

(defun bsv-scan-cache-flush ()
  "Flush the `bsv-scan' cache."
  (setq bsv-scan-cache-tick nil))

(defun bsv-scan-cache-ok-p ()
  "Return t iff the scan cache is up to date."
  (or (and bsv-scan-cache-preserving
	   (eq bsv-scan-cache-preserving (current-buffer))
	   bsv-scan-cache-tick)
      (equal bsv-scan-cache-tick (buffer-chars-modified-tick))))

(defmacro bsv-save-scan-cache (&rest body)
  "Execute the BODY forms, allowing scan cache preservation within BODY.
This requires that insertions must use `bsv-insert'."
  ;; If the buffer is out of date, trash it, as we'll not check later the tick
  ;; Note this must work properly if there's multiple layers of calls
  ;; to bsv-save-scan-cache even with differing ticks.
  `(progn
     (unless (bsv-scan-cache-ok-p)  ;; Must be before let
       (setq bsv-scan-cache-tick nil))
     (let* ((bsv-scan-cache-preserving (current-buffer)))
       (progn ,@body))))

(defun bsv-scan-region (beg end)
  "Parse between BEG and END for `bsv-inside-comment-or-string-p'.
This creates v-cmts properties where comments are in force."
  ;; Why properties and not overlays?  Overlays have much slower non O(1)
  ;; lookup times.
  ;; This function is warm - called on every bsv-insert
  (save-excursion
    (save-match-data
      (bsv-save-buffer-state
       (let (pt)
	 (goto-char beg)
	 (while (< (point) end)
	   (cond ((looking-at "//")
		  (setq pt (point))
		  (or (search-forward "\n" end t)
		      (goto-char end))
		  ;; "1+": The leading // or /* itself isn't considered as
		  ;; being "inside" the comment, so that a (search-backward)
		  ;; that lands at the start of the // won't mis-indicate
		  ;; it's inside a comment.  Also otherwise it would be
		  ;; hard to find a commented out /*AS*/ vs one that isn't
		  (put-text-property (1+ pt) (point) 'v-cmts t))
		 ((looking-at "/\\*")
		  (setq pt (point))
		  (or (search-forward "*/" end t)
		      ;; No error - let later code indicate it so we can
		      ;; use inside functions on-the-fly
		      ;;(error "%s: Unmatched /* */, at char %d"
		      ;;       (bsv-point-text) (point))
		      (goto-char end))
		  (put-text-property (1+ pt) (point) 'v-cmts t))
		 ((looking-at "\"")
		  (setq pt (point))
		  (or (re-search-forward "[^\\]\"" end t)	;; don't forward-char first, since we look for a non backslash first
		      ;; No error - let later code indicate it so we can
		      (goto-char end))
		  (put-text-property (1+ pt) (point) 'v-cmts t))
		 (t
		  (forward-char 1)
		  (if (re-search-forward "[/\"]" end t)
		      (backward-char 1)
		    (goto-char end))))))))))

(defun bsv-scan ()
  "Parse the buffer, marking all comments with properties.
Also assumes any text inserted since `bsv-scan-cache-tick'
either is ok to parse as a non-comment, or `bsv-insert' was used."
  ;; See also `bsv-scan-debug' and `bsv-scan-and-debug'
  (unless (bsv-scan-cache-ok-p)
    (save-excursion
      (bsv-save-buffer-state
	(when bsv-debug
	  (message "Scanning %s cache=%s cachetick=%S tick=%S" (current-buffer)
		   bsv-scan-cache-preserving bsv-scan-cache-tick
		   (buffer-chars-modified-tick)))
	(remove-text-properties (point-min) (point-max) '(v-cmts nil))
	(bsv-scan-region (point-min) (point-max))
	(setq bsv-scan-cache-tick (buffer-chars-modified-tick))
	(when bsv-debug (message "Scanning... done"))))))

(defun bsv-scan-debug ()
  "For debugging, show with display face results of `bsv-scan'."
  (font-lock-mode 0)
  ;;(if dbg (setq dbg (concat dbg (format "bsv-scan-debug\n"))))
  (save-excursion
    (goto-char (point-min))
    (remove-text-properties (point-min) (point-max) '(face nil))
    (while (not (eobp))
      (cond ((get-text-property (point) 'v-cmts)
	     (put-text-property (point) (1+ (point)) `face 'underline)
	     ;;(if dbg (setq dbg (concat dbg (format "  v-cmts at %S\n" (point)))))
	     (forward-char 1))
	    (t
	     (goto-char (or (next-property-change (point)) (point-max))))))))

(defun bsv-scan-and-debug ()
  "For debugging, run `bsv-scan' and `bsv-scan-debug'."
  (let (bsv-scan-cache-preserving
	bsv-scan-cache-tick)
    (goto-char (point-min))
    (bsv-scan)
    (bsv-scan-debug)))

(defun bsv-inside-comment-or-string-p (&optional pos)
  "Check if optional point POS is inside a comment.
This may require a slow pre-parse of the buffer with `bsv-scan'
to establish comment properties on all text."
  ;; This function is very hot
  (bsv-scan)
  (if pos
      (and (>= pos (point-min))
	   (get-text-property pos 'v-cmts))
    (get-text-property (point) 'v-cmts)))

(defun bsv-insert (&rest stuff)
  "Insert STUFF arguments, tracking for `bsv-inside-comment-or-string-p'.
Any insert that includes a comment must have the entire commente
inserted using a single call to `bsv-insert'."
  (let ((pt (point)))
    (while stuff
      (insert (car stuff))
      (setq stuff (cdr stuff)))
    (bsv-scan-region pt (point))))

;; More searching

(defun bsv-declaration-end ()
  (search-forward ";"))

(defun bsv-point-text (&optional pointnum)
  "Return text describing where POINTNUM or current point is (for errors).
Use filename, if current buffer being edited shorten to just buffer name."
  (concat (or (and (equal (window-buffer (selected-window)) (current-buffer))
		   (buffer-name))
	      buffer-file-name
	      (buffer-name))
	  ":" (int-to-string (1+ (count-lines (point-min) (or pointnum (point)))))))

(defun electric-bsv-backward-sexp ()
  "Move backward over one balanced expression."
  (interactive)
  ;; before that see if we are in a comment
  (bsv-backward-sexp))

(defun electric-bsv-forward-sexp ()
  "Move forward over one balanced expression."
  (interactive)
  ;; before that see if we are in a comment
  (bsv-forward-sexp))

;;;used by hs-minor-mode
(defun bsv-forward-sexp-function (arg)
  (if (< arg 0)
      (bsv-backward-sexp)
    (bsv-forward-sexp)))


(defun bsv-backward-sexp ()
  (let ((reg)
	(elsec 1)
	(found nil)
	(st (point)))
    (if (not (looking-at "\\<"))
	(forward-word -1))
    (cond
     ((bsv-skip-backward-comment-or-string))
     ((looking-at "\\<else\\>")
      (setq reg (concat
		 bsv-end-block-re
		 "\\|\\(\\<else\\>\\)"
		 "\\|\\(\\<if\\>\\)"))
      (while (and (not found)
		  (bsv-re-search-backward reg nil 'move))
	(cond
	 ((match-end 1) ; matched bsv-end-block-re
	; try to leap back to matching outward block by striding across
	; indent level changing tokens then immediately
	; previous line governs indentation.
	  (bsv-leap-to-head))
	 ((match-end 2) ; else, we're in deep
	  (setq elsec (1+ elsec)))
	 ((match-end 3) ; found it
	  (setq elsec (1- elsec))
	  (if (= 0 elsec)
	      ;; Now previous line describes syntax
	      (setq found 't))))))
     ((looking-at bsv-end-block-re)
      (bsv-leap-to-head))
     ((looking-at "\\(endmodule\\>\\)\\|\\(\\<endprimitive\\>\\)\\|\\(\\<endclass\\>\\)\\|\\(\\<endprogram\\>\\)\\|\\(\\<endinterface\\>\\)\\|\\(\\<endpackage\\>\\)")
      (cond
       ((match-end 1)
	(bsv-re-search-backward "\\<\\(macro\\)?module\\>" nil 'move))
       ((match-end 2)
	(bsv-re-search-backward "\\<primitive\\>" nil 'move))
       ((match-end 3)
	(bsv-re-search-backward "\\<class\\>" nil 'move))
       ((match-end 4)
	(bsv-re-search-backward "\\<program\\>" nil 'move))
       ((match-end 5)
	(bsv-re-search-backward "\\<interface\\>" nil 'move))
       ((match-end 6)
	(bsv-re-search-backward "\\<package\\>" nil 'move))
       (t
	(goto-char st)
	(backward-sexp 1))))
     (t
      (goto-char st)
      (backward-sexp)))))

(defun bsv-forward-sexp ()
  (let ((reg)
	(md 2)
	(st (point))
	(nest 'yes))
    (if (not (looking-at "\\<"))
	(forward-word -1))
    (cond
     ((bsv-skip-forward-comment-or-string)
      (bsv-forward-syntactic-ws))
     ((looking-at bsv-beg-block-re-ordered)
      (cond
       ((match-end 1);
	;; Search forward for matching end
	(setq reg "\\(\\<begin\\>\\)\\|\\(\\<end\\>\\)" ))
       ((match-end 2)
	;; Search forward for matching endcase
	(setq reg "\\(\\<randcase\\>\\|\\(\\<unique\\>\\s-+\\|\\<priority\\>\\s-+\\)?\\<case[xz]?\\>[^:]\\)\\|\\(\\<endcase\\>\\)" )
	(setq md 3) ;; ender is third item in regexp
	)
       ((match-end 4)
	;; might be "disable fork" or "wait fork"
	(let
	    (here)
	  (if (or
	       (looking-at bsv-disable-fork-re)
	       (and (looking-at "fork")
		    (progn
		      (setq here (point)) ;; sometimes a fork is just a fork
		      (forward-word -1)
		      (looking-at bsv-disable-fork-re))))
	      (progn ;; it is a disable fork; ignore it
		(goto-char (match-end 0))
		(forward-word 1)
		(setq reg nil))
	    (progn ;; it is a nice simple fork
	      (goto-char here)   ;; return from looking for "disable fork"
	      ;; Search forward for matching join
	      (setq reg "\\(\\<fork\\>\\)\\|\\(\\<join\\(_any\\|_none\\)?\\>\\)" )))))
       ((match-end 6)
	;; Search forward for matching endclass
	(setq reg "\\(\\<class\\>\\)\\|\\(\\<endclass\\>\\)" ))

       ((match-end 7)
	;; Search forward for matching endtable
	(setq reg "\\<endtable\\>" )
	(setq nest 'no))
      ((match-end 8)
       ;; Search forward for matching endspecify
       (setq reg "\\(\\<specify\\>\\)\\|\\(\\<endspecify\\>\\)" ))
      ((match-end 9)
       ;; Search forward for matching endfunction
       (setq reg "\\<endfunction\\>" )
       (setq nest 'no))
      ((match-end 10)
       ;; Search forward for matching endfunction
       (setq reg "\\<endfunction\\>" )
       (setq nest 'no))
      ((match-end 14)
       ;; Search forward for matching endtask
       (setq reg "\\<endtask\\>" )
       (setq nest 'no))
      ((match-end 15)
       ;; Search forward for matching endtask
       (setq reg "\\<endtask\\>" )
       (setq nest 'no))
      ((match-end 19)
       ;; Search forward for matching endgenerate
       (setq reg "\\(\\<generate\\>\\)\\|\\(\\<endgenerate\\>\\)" ))
      ((match-end 20)
       ;; Search forward for matching endgroup
       (setq reg "\\(\\<covergroup\\>\\)\\|\\(\\<endgroup\\>\\)" ))
      ((match-end 21)
       ;; Search forward for matching endproperty
       (setq reg "\\(\\<property\\>\\)\\|\\(\\<endproperty\\>\\)" ))
      ((match-end 25)
       ;; Search forward for matching endsequence
       (setq reg "\\(\\<\\(rand\\)?sequence\\>\\)\\|\\(\\<endsequence\\>\\)" )
       (setq md 3)) ; 3 to get to endsequence in the reg above
      ((match-end 27)
       ;; Search forward for matching endclocking
       (setq reg "\\(\\<clocking\\>\\)\\|\\(\\<endclocking\\>\\)" )))
      (if (and reg
	       (forward-word 1))
	  (catch 'skip
	    (if (eq nest 'yes)
		(let ((depth 1)
		      here)
		  (while (bsv-re-search-forward reg nil 'move)
		    (cond
		     ((match-end md) ; a closer in regular expression, so we are climbing out
		      (setq depth (1- depth))
		      (if (= 0 depth) ; we are out!
			  (throw 'skip 1)))
		     ((match-end 1) ; an opener in the r-e, so we are in deeper now
		      (setq here (point)) ; remember where we started
		      (goto-char (match-beginning 1))
		      (cond
		       ((if (or
			     (looking-at bsv-disable-fork-re)
			     (and (looking-at "fork")
				  (progn
				    (forward-word -1)
				    (looking-at bsv-disable-fork-re))))
			    (progn ;; it is a disable fork; another false alarm
			      (goto-char (match-end 0)))
			  (progn ;; it is a simple fork (or has nothing to do with fork)
			    (goto-char here)
			    (setq depth (1+ depth))))))))))
	      (if (bsv-re-search-forward reg nil 'move)
		  (throw 'skip 1))))))

     ((looking-at (concat
		   "\\(\\<\\(macro\\)?module\\>\\)\\|"
		   "\\(\\<primitive\\>\\)\\|"
		   "\\(\\<class\\>\\)\\|"
		   "\\(\\<program\\>\\)\\|"
		   "\\(\\<interface\\>\\)\\|"
		   "\\(\\<package\\>\\)"))
      (cond
       ((match-end 1)
	(bsv-re-search-forward "\\<endmodule\\>" nil 'move))
       ((match-end 2)
	(bsv-re-search-forward "\\<endprimitive\\>" nil 'move))
       ((match-end 3)
	(bsv-re-search-forward "\\<endclass\\>" nil 'move))
       ((match-end 4)
	(bsv-re-search-forward "\\<endprogram\\>" nil 'move))
       ((match-end 5)
	(bsv-re-search-forward "\\<endinterface\\>" nil 'move))
       ((match-end 6)
	(bsv-re-search-forward "\\<endpackage\\>" nil 'move))
       (t
	(goto-char st)
	(if (= (following-char) ?\) )
	    (forward-char 1)
	  (forward-sexp 1)))))
     (t
      (goto-char st)
      (if (= (following-char) ?\) )
	  (forward-char 1)
	(forward-sexp 1))))))

(defun bsv-declaration-beg ()
  (bsv-re-search-backward bsv-declaration-re (bobp) t))

;;
;;
;;  Mode
;;
(defvar bsv-which-tool 1)
;;;###autoload
(define-derived-mode bsv-mode prog-mode "BSV"
  "Major mode for editing BSV code.
\\<bsv-mode-map>
See \\[describe-function] bsv-auto (\\[bsv-auto]) for details on how
AUTOs can improve coding efficiency.

Use \\[bsv-faq] for a pointer to frequently asked questions.

NEWLINE, TAB indents for BSV code.
Delete converts tabs to spaces as it moves back.

Supports highlighting.

Turning on BSV mode calls the value of the variable `bsv-mode-hook'
with no args, if that value is non-nil.

Variables controlling indentation/edit style:

 variable `bsv-indent-level'      (default 3)
   Indentation of BSV statements with respect to containing block.
 `bsv-indent-level-module'        (default 3)
   Absolute indentation of Module level BSV statements.
   Set to 0 to get initial and always statements lined up
   on the left side of your screen.
 `bsv-indent-level-declaration'   (default 3)
   Indentation of declarations with respect to containing block.
   Set to 0 to get them list right under containing block.
 `bsv-indent-level-behavioral'    (default 3)
   Indentation of first begin in a task or function block
   Set to 0 to get such code to lined up underneath the task or
   function keyword.
 `bsv-indent-level-directive'     (default 1)
   Indentation of `ifdef/`endif blocks.
 `bsv-cexp-indent'              (default 1)
   Indentation of BSV statements broken across lines i.e.:
      if (a)
        begin
 `bsv-case-indent'              (default 2)
   Indentation for case statements.
 `bsv-auto-newline'             (default nil)
   Non-nil means automatically newline after semicolons and the punctuation
   mark after an end.
 `bsv-auto-indent-on-newline'   (default t)
   Non-nil means automatically indent line after newline.
 `bsv-tab-always-indent'        (default t)
   Non-nil means TAB in BSV mode should always reindent the current line,
   regardless of where in the line point is when the TAB command is used.
 `bsv-indent-begin-after-if'    (default t)
   Non-nil means to indent begin statements following a preceding
   if, else, while, for and repeat statements, if any.  Otherwise,
   the begin is lined up with the preceding token.  If t, you get:
      if (a)
         begin // amount of indent based on `bsv-cexp-indent'
   otherwise you get:
      if (a)
      begin
 `bsv-auto-endcomments'         (default t)
   Non-nil means a comment /* ... */ is set after the ends which ends
   cases, tasks, functions and modules.
   The type and name of the object will be set between the braces.
 `bsv-minimum-comment-distance' (default 10)
   Minimum distance (in lines) between begin and end required before a comment
   will be inserted.  Setting this variable to zero results in every
   end acquiring a comment; the default avoids too many redundant
   comments in tight quarters.
 `bsv-auto-lineup'              (default 'declarations)
   List of contexts where auto lineup of code should be done.

Variables controlling other actions:

 `bsv-linter'                   (default surelint)
   Unix program to call to run the lint checker.  This is the default
   command for \\[compile-command] and \\[bsv-auto-save-compile].

See \\[customize] for the complete list of variables.

AUTO expansion functions are, in part:

    \\[bsv-auto]  Expand AUTO statements.
    \\[bsv-delete-auto]  Remove the AUTOs.
    \\[bsv-inject-auto]  Insert AUTOs for the first time.

Some other functions are:

    \\[bsv-complete-word]    Complete word with appropriate possibilities.
    \\[bsv-mark-defun]  Mark function.
    \\[bsv-beg-of-defun]  Move to beginning of current function.
    \\[bsv-end-of-defun]  Move to end of current function.
    \\[bsv-label-be]  Label matching begin ... end, fork ... join, etc statements.

    \\[bsv-comment-region]  Put marked area in a comment.
    \\[bsv-uncomment-region]  Uncomment an area commented with \\[bsv-comment-region].
    \\[bsv-insert-block]  Insert begin ... end.
    \\[bsv-star-comment]    Insert /* ... */.

    \\[bsv-sk-always]  Insert an always @(AS) begin .. end block.
    \\[bsv-sk-begin]  Insert a begin .. end block.
    \\[bsv-sk-case]  Insert a case block, prompting for details.
    \\[bsv-sk-for]  Insert a for (...) begin .. end block, prompting for details.
    \\[bsv-sk-generate]  Insert a generate .. endgenerate block.
    \\[bsv-sk-header]  Insert a header block at the top of file.
    \\[bsv-sk-initial]  Insert an initial begin .. end block.
    \\[bsv-sk-fork]  Insert a fork begin .. end .. join block.
    \\[bsv-sk-module]  Insert a module .. (/*AUTOARG*/);.. endmodule block.
    \\[bsv-sk-ovm-class]  Insert an OVM Class block.
    \\[bsv-sk-uvm-class]  Insert an UVM Class block.
    \\[bsv-sk-primitive]  Insert a primitive .. (.. );.. endprimitive block.
    \\[bsv-sk-repeat]  Insert a repeat (..) begin .. end block.
    \\[bsv-sk-specify]  Insert a specify .. endspecify block.
    \\[bsv-sk-task]  Insert a task .. begin .. end endtask block.
    \\[bsv-sk-while]  Insert a while (...) begin .. end block, prompting for details.
    \\[bsv-sk-casex]  Insert a casex (...) item: begin.. end endcase block, prompting for details.
    \\[bsv-sk-casez]  Insert a casez (...) item: begin.. end endcase block, prompting for details.
    \\[bsv-sk-if]  Insert an if (..) begin .. end block.
    \\[bsv-sk-else-if]  Insert an else if (..) begin .. end block.
    \\[bsv-sk-comment]  Insert a comment block.
    \\[bsv-sk-assign]  Insert an assign .. = ..; statement.
    \\[bsv-sk-function]  Insert a function .. begin .. end endfunction block.
    \\[bsv-sk-input]  Insert an input declaration, prompting for details.
    \\[bsv-sk-output]  Insert an output declaration, prompting for details.
    \\[bsv-sk-state-machine]  Insert a state machine definition, prompting for details.
    \\[bsv-sk-inout]  Insert an inout declaration, prompting for details.
    \\[bsv-sk-wire]  Insert a wire declaration, prompting for details.
    \\[bsv-sk-reg]  Insert a register declaration, prompting for details.
    \\[bsv-sk-define-signal]  Define signal under point as a register at the top of the module.

All key bindings can be seen in a BSV-buffer with \\[describe-bindings].
Key bindings specific to `bsv-mode-map' are:

\\{bsv-mode-map}"
  :abbrev-table bsv-mode-abbrev-table
  (set (make-local-variable 'beginning-of-defun-function)
       'bsv-beg-of-defun)
  (set (make-local-variable 'end-of-defun-function)
       'bsv-end-of-defun)
  (set-syntax-table bsv-mode-syntax-table)
  (set (make-local-variable 'indent-line-function)
       #'bsv-indent-line)
  (setq comment-indent-function 'bsv-comment-indent)
  (set (make-local-variable 'parse-sexp-ignore-comments) nil)
  (set (make-local-variable 'comment-start) "// ")
  (set (make-local-variable 'comment-end) "")
  (set (make-local-variable 'comment-start-skip) "/\\*+ *\\|// *")
  (set (make-local-variable 'comment-multi-line) nil)
  ;; Set up for compilation
  (setq bsv-which-tool 1)
  (setq bsv-tool 'bsv-compiler)
  (bsv-set-compile-command)
  (when (boundp 'hack-local-variables-hook)  ;; Also modify any file-local-variables
    (add-hook 'hack-local-variables-hook 'bsv-modify-compile-command t))

  ;; Setting up menus
  (when (featurep 'xemacs)
    (easy-menu-add bsv-stmt-menu)
    (easy-menu-add bsv-menu)
    (setq mode-popup-menu (cons "BSV Mode" bsv-stmt-menu)))

  ;; Stuff for GNU Emacs
  (set (make-local-variable 'font-lock-defaults)
       `((bsv-font-lock-keywords bsv-font-lock-keywords-1
                                     bsv-font-lock-keywords-2
                                     bsv-font-lock-keywords-3)
         nil nil nil
	 ,(if (functionp 'syntax-ppss)
	      ;; bsv-beg-of-defun uses syntax-ppss, and syntax-ppss uses
	      ;; font-lock-beginning-of-syntax-function, so
	      ;; font-lock-beginning-of-syntax-function, can't use
              ;; bsv-beg-of-defun.
	      nil
	    'bsv-beg-of-defun)))
  ;;------------------------------------------------------------
  ;; now hook in 'bsv-highlight-include-files (eldo-mode.el&spice-mode.el)
  ;; all buffer local:
  (unless noninteractive  ;; Else can't see the result, and change hooks are slow
    (when (featurep 'xemacs)
      (make-local-hook 'font-lock-mode-hook)
      (make-local-hook 'font-lock-after-fontify-buffer-hook); doesn't exist in Emacs
      (make-local-hook 'after-change-functions))
    (add-hook 'font-lock-mode-hook 'bsv-highlight-buffer t t)
    (add-hook 'font-lock-after-fontify-buffer-hook 'bsv-highlight-buffer t t) ; not in Emacs
    (add-hook 'after-change-functions 'bsv-highlight-region t t))

  ;; Tell imenu how to handle BSV.
  (set (make-local-variable 'imenu-generic-expression)
       bsv-imenu-generic-expression)
  ;; Tell which-func-modes that imenu knows about bsv
  (when (boundp 'which-func-modes) 
        (when (eq (type-of which-func-modes) 'cons)
             (add-to-list 'which-func-modes 'bsv-mode)))
  ;; hideshow support
  (when (boundp 'hs-special-modes-alist)
    (unless (assq 'bsv-mode hs-special-modes-alist)
      (setq hs-special-modes-alist
	    (cons '(bsv-mode-mode  "\\<begin\\>" "\\<end\\>" nil
				       bsv-forward-sexp-function)
		  hs-special-modes-alist))))

  ;; Stuff for autos
  (add-hook 'write-contents-hooks 'bsv-auto-save-check nil 'local)
  ;; bsv-mode-hook call added by define-derived-mode
  )


;;
;;  Electric functions
;;
(defun electric-bsv-terminate-line (&optional arg)
  "Terminate line and indent next line.
With optional ARG, remove existing end of line comments."
  (interactive)
  ;; before that see if we are in a comment
  (let ((state (save-excursion (bsv-syntax-ppss))))
    (cond
     ((nth 7 state)			; Inside // comment
      (if (eolp)
	  (progn
	    (delete-horizontal-space)
	    (newline))
	(progn
	  (newline)
	  (insert "// ")
	  (beginning-of-line)))
      (bsv-indent-line))
     ((nth 4 state)			; Inside any comment (hence /**/)
      (newline)
      (bsv-more-comment))
     ((eolp)
      (newline)
      (if bsv-auto-indent-on-newline
	  (bsv-indent-line)))
     ;; ((eolp)
     ;;   ;; First, check if current line should be indented
     ;;   (if (save-excursion
     ;;         (delete-horizontal-space)
     ;; 	     (beginning-of-line)
     ;; 	     (skip-chars-forward " \t")
     ;; 	     (if (looking-at bsv-auto-end-comment-lines-re)
     ;; 		 (let ((indent-str (bsv-indent-line)))
     ;; 		   ;; Maybe we should set some endcomments
     ;; 		   (if bsv-auto-endcomments
     ;; 		       (bsv-set-auto-endcomments indent-str arg))
     ;; 		   (end-of-line)
     ;; 		   (delete-horizontal-space)
     ;; 		   (if arg
     ;; 		       ()
     ;; 		     (newline))
     ;; 		   nil)
     ;; 	       (progn
     ;; 		 (end-of-line)
     ;; 		 (delete-horizontal-space)
     ;; 		 't)))
     ;; 	   ;; see if we should line up assignments
     ;; 	   (progn
     ;; 	     (if (or (eq 'all bsv-auto-lineup)
     ;; 		     (eq 'assignments bsv-auto-lineup))
     ;; 		 (bsv-pretty-expr t "\\(<\\|:\\)?=" ))
     ;; 	     (newline))
     ;; 	 (forward-line 1))
     ;;   ;; Indent next line
     ;;   (if bsv-auto-indent-on-newline
     ;; 	   (bsv-indent-line)))
     (t
      (newline)))))

(defun electric-bsv-terminate-and-indent ()
  "Insert a newline and indent for the next statement."
  (interactive)
  (electric-bsv-terminate-line 1))

(defun electric-bsv-semi ()
  "Insert `;' character and reindent the line."
  (interactive)
  (bsv-insert-last-command-event)

  (if (or (bsv-in-comment-or-string-p)
	  (bsv-in-escaped-name-p))
      ()
    (save-excursion
      (beginning-of-line)
      (bsv-forward-ws&directives)
      (bsv-indent-line-conservative))
    (if (and bsv-auto-newline
	     (not (bsv-parenthesis-depth)))
	(electric-bsv-terminate-line))))

(defun electric-bsv-semi-with-comment ()
  "Insert `;' character, reindent the line and indent for comment."
  (interactive)
  (insert "\;")
  (save-excursion
    (beginning-of-line)
    (bsv-indent-line))
  (indent-for-comment))

(defun electric-bsv-colon ()
  "Insert `:' and do all indentations except line indent on this line."
  (interactive)
  (bsv-insert-last-command-event)
  ;; Do nothing if within string.
  (if (or
       (bsv-within-string)
       (not (bsv-in-case-region-p)))
      ()
    (save-excursion
      (let ((p (point))
	    (lim (progn (bsv-beg-of-statement) (point))))
	(goto-char p)
	(bsv-backward-case-item lim)
	(bsv-indent-line)))
;;    (let ((bsv-tab-always-indent nil))
;;      (bsv-indent-line))
    ))

;;(defun electric-bsv-equal ()
;;  "Insert `=', and do indentation if within block."
;;  (interactive)
;;  (bsv-insert-last-command-event)
;; Could auto line up expressions, but not yet
;;  (if (eq (car (bsv-calculate-indent)) 'block)
;;      (let ((bsv-tab-always-indent nil))
;;	(bsv-indent-command)))
;;  )

(defun electric-bsv-tick ()
  "Insert back-tick, and indent to column 0 if this is a CPP directive."
  (interactive)
  (bsv-insert-last-command-event)
  (save-excursion
    (if (bsv-in-directive-p)
        (bsv-indent-line))))

(defun electric-bsv-tab ()
  "Function called when TAB is pressed in BSV mode."
  (interactive)
  ;; If bsv-tab-always-indent, indent the beginning of the line.
  (cond
   ;; The region is active, indent it.
   ((and (region-active-p)
	 (not (eq (region-beginning) (region-end))))
    (indent-region (region-beginning) (region-end) nil))
   ((or bsv-tab-always-indent
	(save-excursion
	  (skip-chars-backward " \t")
	  (bolp)))
    (let* ((oldpnt (point))
	   (boi-point
	    (save-excursion
	      (beginning-of-line)
	      (skip-chars-forward " \t")
	      (bsv-indent-line)
	      (back-to-indentation)
	      (point))))
      (if (< (point) boi-point)
	  (back-to-indentation)
	(cond ((not bsv-tab-to-comment))
	      ((not (eolp))
	       (end-of-line))
	      (t
	       (indent-for-comment)
	       (when (and (eolp) (= oldpnt (point)))
					; kill existing comment
		 (beginning-of-line)
		 (re-search-forward comment-start-skip oldpnt 'move)
		 (goto-char (match-beginning 0))
		 (skip-chars-backward " \t")
		 (kill-region (point) oldpnt)))))))
   (t (progn (insert "\t")))))



;;
;; Interactive functions
;;

(defun bsv-indent-buffer ()
  "Indent-region the entire buffer as BSV code.
To call this from the command line, see \\[bsv-batch-indent]."
  (interactive)
  (bsv-mode)
  (indent-region (point-min) (point-max) nil))

(defun bsv-insert-block ()
  "Insert BSV begin ... end; block in the code with right indentation."
  (interactive)
  (bsv-indent-line)
  (insert "begin")
  (electric-bsv-terminate-line)
  (save-excursion
    (electric-bsv-terminate-line)
    (insert "end")
    (beginning-of-line)
    (bsv-indent-line)))

(defun bsv-star-comment ()
  "Insert BSV star comment at point."
  (interactive)
  (bsv-indent-line)
  (insert "/*")
  (save-excursion
    (newline)
    (insert " */"))
  (newline)
  (insert " * "))

(defun bsv-insert-1 (fmt max)
  "Use format string FMT to insert integers 0 to MAX - 1.
Inserts one integer per line, at the current column.  Stops early
if it reaches the end of the buffer."
  (let ((col (current-column))
        (n 0))
    (save-excursion
      (while (< n max)
        (insert (format fmt n))
        (forward-line 1)
        ;; Note that this function does not bother to check for lines
        ;; shorter than col.
        (if (eobp)
            (setq n max)
          (setq n (1+ n))
          (move-to-column col))))))

(defun bsv-insert-indices (max)
  "Insert a set of indices into a rectangle.
The upper left corner is defined by point.  Indices begin with 0
and extend to the MAX - 1.  If no prefix arg is given, the user
is prompted for a value.  The indices are surrounded by square
brackets \[].  For example, the following code with the point
located after the first 'a' gives:

    a = b                           a[  0] = b
    a = b                           a[  1] = b
    a = b                           a[  2] = b
    a = b                           a[  3] = b
    a = b   ==> insert-indices ==>  a[  4] = b
    a = b                           a[  5] = b
    a = b                           a[  6] = b
    a = b                           a[  7] = b
    a = b                           a[  8] = b"

  (interactive "NMAX: ")
  (bsv-insert-1 "[%3d]" max))

(defun bsv-generate-numbers (max)
  "Insert a set of generated numbers into a rectangle.
The upper left corner is defined by point.  The numbers are padded to three
digits, starting with 000 and extending to (MAX - 1).  If no prefix argument
is supplied, then the user is prompted for the MAX number.  Consider the
following code fragment:

    buf buf                             buf buf000
    buf buf                             buf buf001
    buf buf                             buf buf002
    buf buf                             buf buf003
    buf buf   ==> generate-numbers ==>  buf buf004
    buf buf                             buf buf005
    buf buf                             buf buf006
    buf buf                             buf buf007
    buf buf                             buf buf008"

  (interactive "NMAX: ")
  (bsv-insert-1 "%3.3d" max))

(defun bsv-mark-defun ()
  "Mark the current BSV function (or procedure).
This puts the mark at the end, and point at the beginning."
  (interactive)
  (if (featurep 'xemacs)
      (progn
	(push-mark (point))
	(bsv-end-of-defun)
	(push-mark (point))
	(bsv-beg-of-defun)
	(if (fboundp 'zmacs-activate-region)
	    (zmacs-activate-region)))
    (mark-defun)))

(defun bsv-comment-region (start end)
  ; checkdoc-params: (start end)
  "Put the region into a BSV comment.
The comments that are in this area are \"deformed\":
`*)' becomes `!(*' and `}' becomes `!{'.
These deformed comments are returned to normal if you use
\\[bsv-uncomment-region] to undo the commenting.

The commented area starts with `bsv-exclude-str-start', and ends with
`bsv-exclude-str-end'.  But if you change these variables,
\\[bsv-uncomment-region] won't recognize the comments."
  (interactive "r")
  (save-excursion
    ;; Insert start and endcomments
    (goto-char end)
    (if (and (save-excursion (skip-chars-forward " \t") (eolp))
	     (not (save-excursion (skip-chars-backward " \t") (bolp))))
	(forward-line 1)
      (beginning-of-line))
    (insert bsv-exclude-str-end)
    (setq end (point))
    (newline)
    (goto-char start)
    (beginning-of-line)
    (insert bsv-exclude-str-start)
    (newline)
    ;; Replace end-comments within commented area
    (goto-char end)
    (save-excursion
      (while (re-search-backward "\\*/" start t)
	(replace-match "*-/" t t)))
    (save-excursion
      (let ((s+1 (1+ start)))
	(while (re-search-backward "/\\*" s+1 t)
	  (replace-match "/-*" t t))))))

(defun bsv-uncomment-region ()
  "Uncomment a commented area; change deformed comments back to normal.
This command does nothing if the pointer is not in a commented
area.  See also `bsv-comment-region'."
  (interactive)
  (save-excursion
    (let ((start (point))
	  (end (point)))
      ;; Find the boundaries of the comment
      (save-excursion
	(setq start (progn (search-backward bsv-exclude-str-start nil t)
			   (point)))
	(setq end (progn (search-forward bsv-exclude-str-end nil t)
			 (point))))
      ;; Check if we're really inside a comment
      (if (or (equal start (point)) (<= end (point)))
	  (message "Not standing within commented area.")
	(progn
	  ;; Remove endcomment
	  (goto-char end)
	  (beginning-of-line)
	  (let ((pos (point)))
	    (end-of-line)
	    (delete-region pos (1+ (point))))
	  ;; Change comments back to normal
	  (save-excursion
	    (while (re-search-backward "\\*-/" start t)
	      (replace-match "*/" t t)))
	  (save-excursion
	    (while (re-search-backward "/-\\*" start t)
	      (replace-match "/*" t t)))
	  ;; Remove start comment
	  (goto-char start)
	  (beginning-of-line)
	  (let ((pos (point)))
	    (end-of-line)
	    (delete-region pos (1+ (point)))))))))

(defun bsv-beg-of-defun ()
  "Move backward to the beginning of the current function or procedure."
  (interactive)
  (bsv-re-search-backward bsv-defun-re nil 'move))

(defun bsv-beg-of-defun-quick ()
  "Move backward to the beginning of the current function or procedure.
Uses `bsv-scan' cache."
  (interactive)
  (bsv-re-search-backward-quick bsv-defun-re nil 'move))

(defun bsv-end-of-defun ()
  "Move forward to the end of the current function or procedure."
  (interactive)
  (bsv-re-search-forward bsv-end-defun-re nil 'move))

(defun bsv-get-beg-of-defun (&optional warn)
  (save-excursion
    (cond ((bsv-re-search-forward-quick bsv-defun-re nil t)
	   (point))
	  (t
	   (error "%s: Can't find module beginning" (bsv-point-text))
	   (point-max)))))
(defun bsv-get-end-of-defun (&optional warn)
  (save-excursion
    (cond ((bsv-re-search-forward-quick bsv-end-defun-re nil t)
	   (point))
	  (t
	   (error "%s: Can't find endmodule" (bsv-point-text))
	   (point-max)))))

(defun bsv-label-be (&optional arg)
  "Label matching begin ... end, fork ... join and case ... endcase statements.
With ARG, first kill any existing labels."
  (interactive)
  (let ((cnt 0)
	(oldpos (point))
	(b (progn
	     (bsv-beg-of-defun)
	     (point-marker)))
	(e (progn
	     (bsv-end-of-defun)
	     (point-marker))))
    (goto-char (marker-position b))
    (if (> (- e b) 200)
	(message  "Relabeling module..."))
    (while (and
	    (> (marker-position e) (point))
	    (bsv-re-search-forward
	     (concat
	      "\\<end\\(\\(function\\)\\|\\(task\\)\\|\\(module\\)\\|\\(primitive\\)\\|\\(interface\\)\\|\\(package\\)\\|\\(case\\)\\)?\\>"
	      "\\|\\(`endif\\)\\|\\(`else\\)")
	     nil 'move))
      (goto-char (match-beginning 0))
      (let ((indent-str (bsv-indent-line)))
	(bsv-set-auto-endcomments indent-str 't)
	(end-of-line)
	(delete-horizontal-space))
      (setq cnt (1+ cnt))
      (if (= 9 (% cnt 10))
	  (message "%d..." cnt)))
    (goto-char oldpos)
    (if (or
	 (> (- e b) 200)
	 (> cnt 20))
	(message  "%d lines auto commented" cnt))))

(defun bsv-beg-of-statement ()
  "Move backward to beginning of statement."
  (interactive)
  ;; Move back token by token until we see the end
  ;; of some earlier line.
  (let (h)
    (while
	;; If the current point does not begin a new
	;; statement, as in the character ahead of us is a ';', or SOF
	;; or the string after us unambiguously starts a statement,
	;; or the token before us unambiguously ends a statement,
	;; then move back a token and test again.
	(not (or
          ;; stop if beginning of buffer
	      (bolp)
          ;; stop if we find a ;
	      (= (preceding-char) ?\;)
          ;; stop if we see a named coverpoint
	      (looking-at "\\w+\\W*:\\W*\\(coverpoint\\|cross\\|constraint\\)")
          ;; keep going if we are in the middle of a word
	      (not (or (looking-at "\\<") (forward-word -1)))
          ;; stop if we see an assertion (perhaps labeled)
	      (and
	       (looking-at "\\(\\<\\(assert\\|assume\\|cover\\)\\>\\s-+\\<property\\>\\)\\|\\(\\<assert\\>\\)")
	       (progn
             (setq h (point))
             (save-excursion
               (bsv-backward-token)
               (if (looking-at bsv-label-re)
                   (setq h (point))))
             (goto-char h)))
          ;; stop if we see a complete reg, perhaps an extended one
	      (and
           (looking-at bsv-complete-reg)
           (let* ((p (point)))
             (while (and (looking-at bsv-extended-complete-re)
                         (progn (setq p (point))
                                (bsv-backward-token)
                                (/= p (point)))))
             (goto-char p)))
          ;; stop if we see a complete reg (previous found extended ones)
	      (looking-at bsv-basic-complete-re)
          ;; stop if previous token is an ender
	      (save-excursion
            (bsv-backward-token)
            (or
             (looking-at bsv-end-block-re)
             (looking-at bsv-preprocessor-re))))) ;; end of test
    (bsv-backward-syntactic-ws)
    (bsv-backward-token))
    ;; Now point is where the previous line ended.
    (bsv-forward-syntactic-ws)))

(defun bsv-beg-of-statement-1 ()
  "Move backward to beginning of statement."
  (interactive)
  (if (bsv-in-comment-p)
      (bsv-backward-syntactic-ws))
  (let ((pt (point)))
    (catch 'done
      (while (not (looking-at bsv-complete-reg))
        (setq pt (point))
        (bsv-backward-syntactic-ws)
        (if (or (bolp)
                (= (preceding-char) ?\;)
		(save-excursion
		  (bsv-backward-token)
		  (looking-at bsv-ends-re)))
            (progn
              (goto-char pt)
              (throw 'done t))
          (bsv-backward-token))))
    (bsv-forward-syntactic-ws)))
;
;    (while (and
;            (not (looking-at bsv-complete-reg))
;            (not (bolp))
;            (not (= (preceding-char) ?\;)))
;      (bsv-backward-token)
;      (bsv-backward-syntactic-ws)
;      (setq pt (point)))
;    (goto-char pt)
; ;(bsv-forward-syntactic-ws)

(defun bsv-end-of-statement ()
  "Move forward to end of current statement."
  (interactive)
  (let ((nest 0) pos)
    (cond
     ((bsv-in-directive-p)
      (forward-line 1)
      (backward-char 1))

     ((looking-at bsv-beg-block-re)
      (bsv-forward-sexp))

     ((equal (char-after) ?\})
      (forward-char))

      ;; Skip to end of statement
     ((condition-case nil
       (setq pos
             (catch 'found
               (while t
                 (forward-sexp 1)
                 (bsv-skip-forward-comment-or-string)
                 (if (eolp)
                     (forward-line 1))
                 (cond ((looking-at "[ \t]*;")
                        (skip-chars-forward "^;")
                        (forward-char 1)
                        (throw 'found (point)))
                       ((save-excursion
                          (forward-sexp -1)
                          (looking-at bsv-beg-block-re))
                        (goto-char (match-beginning 0))
                        (throw 'found nil))
                       ((looking-at "[ \t]*)")
                        (throw 'found (point)))
                       ((eobp)
                        (throw 'found (point)))
                       )))

             )
       (error nil))
      (if (not pos)
          ;; Skip a whole block
          (catch 'found
            (while t
              (bsv-re-search-forward bsv-end-statement-re nil 'move)
              (setq nest (if (match-end 1)
                             (1+ nest)
                           (1- nest)))
              (cond ((eobp)
                     (throw 'found (point)))
                    ((= 0 nest)
                     (throw 'found (bsv-end-of-statement))))))
        pos)))))

(defun bsv-in-case-region-p ()
  "Return true if in a case region.
More specifically, point @ in the line foo : @ begin"
  (interactive)
  (save-excursion
    (if (and
	 (progn (bsv-forward-syntactic-ws)
		(looking-at "\\<begin\\>"))
	 (progn (bsv-backward-syntactic-ws)
		(= (preceding-char) ?\:)))
	(catch 'found
	  (let ((nest 1))
	    (while t
	      (bsv-re-search-backward
	       (concat "\\(\\<module\\>\\)\\|\\(\\<randcase\\>\\|\\<case[xz]?\\>[^:]\\)\\|"
		       "\\(\\<endcase\\>\\)\\>")
	       nil 'move)
	      (cond
	       ((match-end 3)
		(setq nest (1+ nest)))
	       ((match-end 2)
		(if (= nest 1)
		(throw 'found 1))
		(setq nest (1- nest)))
	       (t
		(throw 'found (= nest 0)))))))
      nil)))

(defun bsv-backward-up-list (arg)
  "Like `backward-up-list', but deal with comments."
  (let ((parse-sexp-ignore-comments t))
    (backward-up-list arg)))

(defun bsv-forward-sexp-cmt (arg)
  "Call `forward-sexp', inside comments."
  (let ((parse-sexp-ignore-comments nil))
    (forward-sexp arg)))

(defun bsv-forward-sexp-ign-cmt (arg)
  "Call `forward-sexp', ignoring comments."
  (let ((parse-sexp-ignore-comments t))
    (forward-sexp arg)))

(defun bsv-in-struct-region-p ()
  "Return true if in a struct region.
More specifically, in a list after a struct|union keyword."
  (interactive)
  (save-excursion
    (let* ((state (bsv-syntax-ppss))
	   (depth (nth 0 state)))
      (if depth
	  (progn (bsv-backward-up-list depth)
		 (bsv-beg-of-statement)
		 (looking-at "\\<typedef\\>?\\s-*\\<struct\\|union\\>"))))))

(defun bsv-in-generate-region-p ()
  "Return true if in a generate region.
More specifically, after a generate and before an endgenerate."
  (interactive)
  (let ((nest 1))
    (save-excursion
      (catch 'done
	(while (and
		(/= nest 0)
		(bsv-re-search-backward
		 "\\<\\(module\\)\\|\\(generate\\)\\|\\(endgenerate\\)\\>" nil 'move)
		(cond
		 ((match-end 1) ; module - we have crawled out
		  (throw 'done 1))
		 ((match-end 2) ; generate
		  (setq nest (1- nest)))
		 ((match-end 3) ; endgenerate
		  (setq nest (1+ nest))))))))
    (= nest 0) )) ; return nest

(defun bsv-in-fork-region-p ()
  "Return true if between a fork and join."
  (interactive)
  (let ((lim (save-excursion (bsv-beg-of-defun)  (point)))
	(nest 1))
    (save-excursion
      (while (and
	      (/= nest 0)
	      (bsv-re-search-backward "\\<\\(fork\\)\\|\\(join\\(_any\\|_none\\)?\\)\\>" lim 'move)
	      (cond
	       ((match-end 1) ; fork
		(setq nest (1- nest)))
	       ((match-end 2) ; join
		(setq nest (1+ nest)))))))
    (= nest 0) )) ; return nest

(defun bsv-backward-case-item (lim)
  "Skip backward to nearest enclosing case item.
Limit search to point LIM."
  (interactive)
  (let ((str 'nil)
	(lim1
	 (progn
	   (save-excursion
	     (bsv-re-search-backward bsv-endcomment-reason-re
					 lim 'move)
	     (point)))))
    ;; Try to find the real :
    (if (save-excursion (search-backward ":" lim1 t))
	(let ((colon 0)
	      b e )
	  (while
	      (and
	       (< colon 1)
	       (bsv-re-search-backward "\\(\\[\\)\\|\\(\\]\\)\\|\\(:\\)"
					   lim1 'move))
	    (cond
	     ((match-end 1) ;; [
	      (setq colon (1+ colon))
	      (if (>= colon 0)
		  (error "%s: unbalanced [" (bsv-point-text))))
	     ((match-end 2) ;; ]
	      (setq colon (1- colon)))

	     ((match-end 3) ;; :
	      (setq colon (1+ colon)))))
	  ;; Skip back to beginning of case item
	  (skip-chars-backward "\t ")
	  (bsv-skip-backward-comment-or-string)
	  (setq e (point))
	  (setq b
		(progn
		  (if
		      (bsv-re-search-backward
		       "\\<\\(case[zx]?\\)\\>\\|;\\|\\<end\\>" nil 'move)
		      (progn
			(cond
			 ((match-end 1)
			  (goto-char (match-end 1))
			  (bsv-forward-ws&directives)
			  (if (looking-at "(")
			      (progn
				(forward-sexp)
				(bsv-forward-ws&directives)))
			  (point))
			 (t
			  (goto-char (match-end 0))
			  (bsv-forward-ws&directives)
			  (point))))
		    (error "Malformed case item"))))
	  (setq str (buffer-substring b e))
	  (if
	      (setq e
		    (string-match
		     "[ \t]*\\(\\(\n\\)\\|\\(//\\)\\|\\(/\\*\\)\\)" str))
	      (setq str (concat (substring str 0 e) "...")))
	  str)
      'nil)))


;;
;; Other functions
;;

(defun bsv-kill-existing-comment ()
  "Kill auto comment on this line."
  (save-excursion
    (let* (
	   (e (progn
		(end-of-line)
		(point)))
	   (b (progn
		(beginning-of-line)
		(search-forward "//" e t))))
      (if b
	  (delete-region (- b 2) e)))))

(defconst bsv-directive-nest-re
  (concat "\\(`else\\>\\)\\|"
	  "\\(`endif\\>\\)\\|"
	  "\\(`if\\>\\)\\|"
	  "\\(`ifdef\\>\\)\\|"
	  "\\(`ifndef\\>\\)\\|"
	  "\\(`elsif\\>\\)"))
(defun bsv-set-auto-endcomments (indent-str kill-existing-comment)
  "Add ending comment with given INDENT-STR.
With KILL-EXISTING-COMMENT, remove what was there before.
Insert `// case: 7 ' or `// NAME ' on this line if appropriate.
Insert `// case expr ' if this line ends a case block.
Insert `// ifdef FOO ' if this line ends code conditional on FOO.
Insert `// NAME ' if this line ends a function, task, module,
primitive or interface named NAME."
  (save-excursion
    (cond
     ((eq indent-str 0) nil)
     (; Comment close preprocessor directives
      (and
       (looking-at "\\(`endif\\)\\|\\(`else\\)")
       (or  kill-existing-comment
	    (not (save-excursion
		   (end-of-line)
		   (search-backward "//" (point-at-bol) t)))))
      (let ((nest 1) b e
	    m
	    (else (if (match-end 2) "!" " ")))
	(end-of-line)
	(if kill-existing-comment
	    (bsv-kill-existing-comment))
	(delete-horizontal-space)
	(save-excursion
	  (backward-sexp 1)
	  (while (and (/= nest 0)
		      (bsv-re-search-backward bsv-directive-nest-re nil 'move))
	    (cond
	     ((match-end 1) ; `else
	      (if (= nest 1)
		  (setq else "!")))
	     ((match-end 2) ; `endif
	      (setq nest (1+ nest)))
	     ((match-end 3) ; `if
	      (setq nest (1- nest)))
	     ((match-end 4) ; `ifdef
	      (setq nest (1- nest)))
	     ((match-end 5) ; `ifndef
	      (setq nest (1- nest)))
	     ((match-end 6) ; `elsif
	      (if (= nest 1)
		  (progn
		    (setq else "!")
		    (setq nest 0))))))
	  (if (match-end 0)
	      (setq
	       m (buffer-substring
		  (match-beginning 0)
		  (match-end 0))
	       b (progn
		   (skip-chars-forward "^ \t")
		   (bsv-forward-syntactic-ws)
		   (point))
	       e (progn
		   (skip-chars-forward "a-zA-Z0-9_")
		   (point)))))
	(if b
	    (if (> (count-lines (point) b) bsv-minimum-comment-distance)
		(insert (concat " // " else m " " (buffer-substring b e))))
	  (progn
	    (insert " // unmatched `else, `elsif or `endif")
	    (ding 't)))))

     (; Comment close case/class/function/task/module and named block
      (and (looking-at "\\<end")
	   (or kill-existing-comment
	       (not (save-excursion
		      (end-of-line)
		      (search-backward "//" (point-at-bol) t)))))
      (let ((type (car indent-str)))
	(unless (eq type 'declaration)
	  (unless (looking-at (concat "\\(" bsv-end-block-ordered-re "\\)[ \t]*:")) ;; ignore named ends
	    (if (looking-at bsv-end-block-ordered-re)
	      (cond
	       (;- This is a case block; search back for the start of this case
		(match-end 1) ;; of bsv-end-block-ordered-re

		(let ((err 't)
		      (str "UNMATCHED!!"))
		  (save-excursion
		    (bsv-leap-to-head)
		    (cond
		     ((looking-at "\\<randcase\\>")
		      (setq str "randcase")
		      (setq err nil))
		     ((looking-at "\\(\\(unique\\s-+\\|priority\\s-+\\)?case[xz]?\\)")
		      (goto-char (match-end 0))
		      (setq str (concat (match-string 0) " " (bsv-get-expr)))
		      (setq err nil))
		     ))
		  (end-of-line)
		  (if kill-existing-comment
		      (bsv-kill-existing-comment))
		  (delete-horizontal-space)
		  (insert (concat " // " str ))
		  (if err (ding 't))))

	       (;- This is a begin..end block
		(match-end 2) ;; of bsv-end-block-ordered-re
		(let ((str " // UNMATCHED !!")
		      (err 't)
		      (here (point))
		      there
		      cntx)
		  (save-excursion
		    (bsv-leap-to-head)
		    (setq there (point))
		    (if (not (match-end 0))
			(progn
			  (goto-char here)
			  (end-of-line)
			  (if kill-existing-comment
			      (bsv-kill-existing-comment))
			  (delete-horizontal-space)
			  (insert str)
			  (ding 't))
		      (let ((lim
			     (save-excursion (bsv-beg-of-defun) (point)))
			    (here (point)))
			(cond
			 (;-- handle named block differently
			  (looking-at bsv-named-block-re)
			  (search-forward ":")
			  (setq there (point))
			  (setq str (bsv-get-expr))
			  (setq err nil)
			  (setq str (concat " // block: " str )))

			 ((bsv-in-case-region-p) ;-- handle case item differently
			  (goto-char here)
			  (setq str (bsv-backward-case-item lim))
			  (setq there (point))
			  (setq err nil)
			  (setq str (concat " // case: " str )))

			 (;- try to find "reason" for this begin
			  (cond
			   (;
			    (eq here (progn
				    ;;   (bsv-backward-token)
				       (bsv-beg-of-statement)
				       (point)))
			    (setq err nil)
			    (setq str ""))
			   ((looking-at bsv-endcomment-reason-re)
			    (setq there (match-end 0))
			    (setq cntx (concat (match-string 0) " "))
			    (cond
			     (;- begin
			      (match-end 1)
			      (setq err nil)
			      (save-excursion
				(if (and (bsv-continued-line)
					 (looking-at "\\<repeat\\>\\|\\<wait\\>\\|\\<always\\>"))
				    (progn
				      (goto-char (match-end 0))
				      (setq there (point))
				      (setq str
					    (concat " // " (match-string 0) " " (bsv-get-expr))))
				  (setq str ""))))

			     (;- else
			      (match-end 2)
			      (let ((nest 0)
				    ( reg "\\(\\<begin\\>\\)\\|\\(\\<end\\>\\)\\|\\(\\<if\\>\\)\\|\\(assert\\)"))
				(catch 'skip
				  (while (bsv-re-search-backward reg nil 'move)
				    (cond
				     ((match-end 1) ; begin
				      (setq nest (1- nest)))
				     ((match-end 2)                       ; end
				      (setq nest (1+ nest)))
				     ((match-end 3)
				      (if (= 0 nest)
					  (progn
					    (goto-char (match-end 0))
					    (setq there (point))
					    (setq err nil)
					    (setq str (bsv-get-expr))
					    (setq str (concat " // else: !if" str ))
					    (throw 'skip 1))))
				     ((match-end 4)
				      (if (= 0 nest)
					  (progn
					    (goto-char (match-end 0))
					    (setq there (point))
					    (setq err nil)
					    (setq str (bsv-get-expr))
					    (setq str (concat " // else: !assert " str ))
					    (throw 'skip 1)))))))))
			     (;- end else
			      (match-end 3)
			      (goto-char there)
			      (let ((nest 0)
				    (reg "\\(\\<begin\\>\\)\\|\\(\\<end\\>\\)\\|\\(\\<if\\>\\)\\|\\(assert\\)"))
				(catch 'skip
				  (while (bsv-re-search-backward reg nil 'move)
				    (cond
				     ((match-end 1) ; begin
				      (setq nest (1- nest)))
				     ((match-end 2)                       ; end
				      (setq nest (1+ nest)))
				     ((match-end 3)
				      (if (= 0 nest)
					  (progn
					    (goto-char (match-end 0))
					    (setq there (point))
					    (setq err nil)
					    (setq str (bsv-get-expr))
					    (setq str (concat " // else: !if" str ))
					    (throw 'skip 1))))
				     ((match-end 4)
				      (if (= 0 nest)
					  (progn
					    (goto-char (match-end 0))
					    (setq there (point))
					    (setq err nil)
					    (setq str (bsv-get-expr))
					    (setq str (concat " // else: !assert " str ))
					    (throw 'skip 1)))))))))

			     (; always_comb, always_ff, always_latch
			      (or (match-end 4) (match-end 5) (match-end 6))
			      (goto-char (match-end 0))
			      (setq there (point))
			      (setq err nil)
			      (setq str (concat " // " cntx )))

			     (;- task/function/initial et cetera
			      t
			      (match-end 0)
			      (goto-char (match-end 0))
			      (setq there (point))
			      (setq err nil)
			      (setq str (concat " // " cntx (bsv-get-expr))))

			     (;-- otherwise...
			      (setq str " // auto-endcomment confused "))))

			   ((and
			     (bsv-in-case-region-p) ;-- handle case item differently
			     (progn
			       (setq there (point))
			       (goto-char here)
			       (setq str (bsv-backward-case-item lim))))
			    (setq err nil)
			    (setq str (concat " // case: " str )))

			   ((bsv-in-fork-region-p)
			    (setq err nil)
			    (setq str " // fork branch" ))

			   ((looking-at "\\<end\\>")
			    ;; HERE
			    (forward-word 1)
			    (bsv-forward-syntactic-ws)
			    (setq err nil)
			    (setq str (bsv-get-expr))
			    (setq str (concat " // " cntx str )))

			   ))))
		      (goto-char here)
		      (end-of-line)
		      (if kill-existing-comment
			  (bsv-kill-existing-comment))
		      (delete-horizontal-space)
		      (if (or err
			      (> (count-lines here there) bsv-minimum-comment-distance))
			  (insert str))
		      (if err (ding 't))
		      ))))
	       (;- this is endclass, which can be nested
		(match-end 11) ;; of bsv-end-block-ordered-re
		;;(goto-char there)
		(let ((nest 0)
		      (reg "\\<\\(class\\)\\|\\(endclass\\)\\|\\(package\\|primitive\\|\\(macro\\)?module\\)\\>")
		      string)
		  (save-excursion
		    (catch 'skip
		      (while (bsv-re-search-backward reg nil 'move)
			(cond
			 ((match-end 3)	; endclass
			  (ding 't)
			  (setq string "unmatched endclass")
			  (throw 'skip 1))

			 ((match-end 2)	; endclass
			  (setq nest (1+ nest)))

			 ((match-end 1) ; class
			  (setq nest (1- nest))
			  (if (< nest 0)
			      (progn
				(goto-char (match-end 0))
				(let (b e)
				  (setq b (progn
					    (skip-chars-forward "^ \t")
					    (bsv-forward-ws&directives)
					    (point))
					e (progn
					    (skip-chars-forward "a-zA-Z0-9_")
					    (point)))
				  (setq string (buffer-substring b e)))
				(throw 'skip 1))))
			 ))))
		  (end-of-line)
		  (insert (concat " // " string ))))

	       (;- this is end{function,generate,task,module,primitive,table,generate}
		;- which can not be nested.
		t
		(let (string reg (name-re nil))
		  (end-of-line)
		  (if kill-existing-comment
		      (save-match-data
		       (bsv-kill-existing-comment)))
		  (delete-horizontal-space)
		  (backward-sexp)
		  (cond
		   ((match-end 5) ;; of bsv-end-block-ordered-re
		    (setq reg "\\(\\<function\\>\\)\\|\\(\\<\\(endfunction\\|task\\|\\(macro\\)?module\\|primitive\\)\\>\\)")
		    (setq name-re "\\w+\\s-*(")
		    )
		   ((match-end 6) ;; of bsv-end-block-ordered-re
		    (setq reg "\\(\\<task\\>\\)\\|\\(\\<\\(endtask\\|function\\|\\(macro\\)?module\\|primitive\\)\\>\\)"))
		   ((match-end 7) ;; of bsv-end-block-ordered-re
		    (setq reg "\\(\\<\\(macro\\)?module\\>\\)\\|\\<endmodule\\>"))
		   ((match-end 8) ;; of bsv-end-block-ordered-re
		    (setq reg "\\(\\<primitive\\>\\)\\|\\(\\<\\(endprimitive\\|package\\|interface\\|\\(macro\\)?module\\)\\>\\)"))
		   ((match-end 9) ;; of bsv-end-block-ordered-re
		    (setq reg "\\(\\<interface\\>\\)\\|\\(\\<\\(endinterface\\|package\\|primitive\\|\\(macro\\)?module\\)\\>\\)"))
		   ((match-end 10) ;; of bsv-end-block-ordered-re
		    (setq reg "\\(\\<package\\>\\)\\|\\(\\<\\(endpackage\\|primitive\\|interface\\|\\(macro\\)?module\\)\\>\\)"))
		   ((match-end 11) ;; of bsv-end-block-ordered-re
		    (setq reg "\\(\\<class\\>\\)\\|\\(\\<\\(endclass\\|primitive\\|interface\\|\\(macro\\)?module\\)\\>\\)"))
		   ((match-end 12) ;; of bsv-end-block-ordered-re
		    (setq reg "\\(\\<covergroup\\>\\)\\|\\(\\<\\(endcovergroup\\|primitive\\|interface\\|\\(macro\\)?module\\)\\>\\)"))
		   ((match-end 13) ;; of bsv-end-block-ordered-re
		    (setq reg "\\(\\<program\\>\\)\\|\\(\\<\\(endprogram\\|primitive\\|interface\\|\\(macro\\)?module\\)\\>\\)"))
		   ((match-end 14) ;; of bsv-end-block-ordered-re
		    (setq reg "\\(\\<\\(rand\\)?sequence\\>\\)\\|\\(\\<\\(endsequence\\|primitive\\|interface\\|\\(macro\\)?module\\)\\>\\)"))
		   ((match-end 15) ;; of bsv-end-block-ordered-re
		    (setq reg "\\(\\<clocking\\>\\)\\|\\<endclocking\\>"))

		   (t (error "Problem in bsv-set-auto-endcomments")))
		  (let (b e)
		    (save-excursion
		      (bsv-re-search-backward reg nil 'move)
		      (cond
		       ((match-end 1)
			(setq b (progn
				  (skip-chars-forward "^ \t")
				  (bsv-forward-ws&directives)
				  (if (looking-at "static\\|automatic")
				      (progn
					(goto-char (match-end 0))
					(bsv-forward-ws&directives)))
				  (if (and name-re (bsv-re-search-forward name-re nil 'move))
				      (progn
					(goto-char (match-beginning 0))
					(bsv-forward-ws&directives)))
				  (point))
			      e (progn
				  (skip-chars-forward "a-zA-Z0-9_")
				  (point)))
			(setq string (buffer-substring b e)))
		       (t
			(ding 't)
			(setq string "unmatched end(function|task|module|primitive|interface|package|class|clocking)")))))
		  (end-of-line)
		  (insert (concat " // " string )))
		))))))))))

(defun bsv-get-expr()
  "Grab expression at point, e.g, case ( a | b & (c ^d))."
  (let* ((b (progn
	      (bsv-forward-syntactic-ws)
	      (skip-chars-forward " \t")
	      (point)))
	 (e (let ((par 1))
	      (cond
	       ((looking-at "@")
		(forward-char 1)
		(bsv-forward-syntactic-ws)
		(if (looking-at "(")
		    (progn
		      (forward-char 1)
		      (while (and (/= par 0)
				  (bsv-re-search-forward "\\((\\)\\|\\()\\)" nil 'move))
			(cond
			 ((match-end 1)
			  (setq par (1+ par)))
			 ((match-end 2)
			  (setq par (1- par)))))))
		(point))
	       ((looking-at "(")
		(forward-char 1)
		(while (and (/= par 0)
			    (bsv-re-search-forward "\\((\\)\\|\\()\\)" nil 'move))
		  (cond
		   ((match-end 1)
		    (setq par (1+ par)))
		   ((match-end 2)
		    (setq par (1- par)))))
		(point))
	       ((looking-at "\\[")
		(forward-char 1)
		(while (and (/= par 0)
			    (bsv-re-search-forward "\\(\\[\\)\\|\\(\\]\\)" nil 'move))
		  (cond
		   ((match-end 1)
		    (setq par (1+ par)))
		   ((match-end 2)
		    (setq par (1- par)))))
		(bsv-forward-syntactic-ws)
		(skip-chars-forward "^ \t\n\f")
		(point))
	       ((looking-at "/[/\\*]")
		b)
	       ('t
		(skip-chars-forward "^: \t\n\f")
		(point)))))
	 (str (buffer-substring b e)))
    (if (setq e (string-match "[ \t]*\\(\\(\n\\)\\|\\(//\\)\\|\\(/\\*\\)\\)" str))
	(setq str (concat (substring str 0 e) "...")))
    str))

(defun bsv-expand-vector ()
  "Take a signal vector on the current line and expand it to multiple lines.
Useful for creating tri's and other expanded fields."
  (interactive)
  (bsv-expand-vector-internal "[" "]"))

(defun bsv-expand-vector-internal (bra ket)
  "Given BRA, the start brace and KET, the end brace, expand one line into many lines."
  (save-excursion
    (forward-line 0)
    (let ((signal-string (buffer-substring (point)
					   (progn
					     (end-of-line) (point)))))
      (if (string-match
	   (concat "\\(.*\\)"
		   (regexp-quote bra)
		   "\\([0-9]*\\)\\(:[0-9]*\\|\\)\\(::[0-9---]*\\|\\)"
		   (regexp-quote ket)
		   "\\(.*\\)$") signal-string)
	  (let* ((sig-head (match-string 1 signal-string))
		 (vec-start (string-to-number (match-string 2 signal-string)))
		 (vec-end (if (= (match-beginning 3) (match-end 3))
			      vec-start
			    (string-to-number
			     (substring signal-string (1+ (match-beginning 3))
					(match-end 3)))))
		 (vec-range
		  (if (= (match-beginning 4) (match-end 4))
		      1
		    (string-to-number
		     (substring signal-string (+ 2 (match-beginning 4))
				(match-end 4)))))
		 (sig-tail (match-string 5 signal-string))
		 vec)
	    ;; Decode vectors
	    (setq vec nil)
	    (if (< vec-range 0)
		(let ((tmp vec-start))
		  (setq vec-start vec-end
			vec-end tmp
			vec-range (- vec-range))))
	    (if (< vec-end vec-start)
		(while (<= vec-end vec-start)
		  (setq vec (append vec (list vec-start)))
		  (setq vec-start (- vec-start vec-range)))
	      (while (<= vec-start vec-end)
		(setq vec (append vec (list vec-start)))
		(setq vec-start (+ vec-start vec-range))))
	    ;;
	    ;; Delete current line
	    (delete-region (point) (progn (forward-line 0) (point)))
	    ;;
	    ;; Expand vector
	    (while vec
	      (insert (concat sig-head bra
			      (int-to-string (car vec)) ket sig-tail "\n"))
	      (setq vec (cdr vec)))
	    (delete-char -1)
	    ;;
	    )))))

(defun bsv-strip-comments ()
  "Strip all comments from the BSV code."
  (interactive)
  (goto-char (point-min))
  (while (re-search-forward "//" nil t)
    (if (bsv-within-string)
	(re-search-forward "\"" nil t)
      (if (bsv-in-star-comment-p)
	  (re-search-forward "\*/" nil t)
	(let ((bpt (- (point) 2)))
	  (end-of-line)
	  (delete-region bpt (point))))))
    ;;
  (goto-char (point-min))
  (while (re-search-forward "/\\*" nil t)
    (if (bsv-within-string)
	(re-search-forward "\"" nil t)
      (let ((bpt (- (point) 2)))
	(re-search-forward "\\*/")
	(delete-region bpt (point))))))

(defun bsv-one-line ()
  "Convert structural BSV instances to occupy one line."
  (interactive)
  (goto-char (point-min))
  (while (re-search-forward "\\([^;]\\)[ \t]*\n[ \t]*" nil t)
	(replace-match "\\1 " nil nil)))

(defun bsv-linter-name ()
  "Return name of linter, either surelint or verilint."
  (let ((compile-word1 (bsv-string-replace-matches "\\s .*$" "" nil nil
						       compile-command))
	(lint-word1    (bsv-string-replace-matches "\\s .*$" "" nil nil
						       bsv-linter)))
    (cond ((equal compile-word1 "surelint") `surelint)
	  ((equal compile-word1 "verilint") `verilint)
	  ((equal lint-word1 "surelint")    `surelint)
	  ((equal lint-word1 "verilint")    `verilint)
	  (t `surelint))))  ;; back compatibility

(defun bsv-lint-off ()
  "Convert a BSV linter warning line into a disable statement.
For example:
	pci_bfm_null.v, line  46: Unused input: pci_rst_
becomes a comment for the appropriate tool.

The first word of the `compile-command' or `bsv-linter'
variables is used to determine which product is being used.

See \\[bsv-surelint-off] and \\[bsv-verilint-off]."
  (interactive)
  (let ((linter (bsv-linter-name)))
    (cond ((equal linter `surelint)
	   (bsv-surelint-off))
	  ((equal linter `verilint)
	   (bsv-verilint-off))
	  (t (error "Linter name not set")))))

(defvar compilation-last-buffer)
(defvar next-error-last-buffer)

(defun bsv-surelint-off ()
  "Convert a SureLint warning line into a disable statement.
Run from BSV source window; assumes there is a *compile* buffer
with point set appropriately.

For example:
	WARNING [STD-UDDONX]: xx.v, line 8: output out is never assigned.
becomes:
	// surefire lint_line_off UDDONX"
  (interactive)
  (let ((buff (if (boundp 'next-error-last-buffer)
                  next-error-last-buffer
                compilation-last-buffer)))
    (when (buffer-live-p buff)
      (save-excursion
        (switch-to-buffer buff)
        (beginning-of-line)
        (when
            (looking-at "\\(INFO\\|WARNING\\|ERROR\\) \\[[^-]+-\\([^]]+\\)\\]: \\([^,]+\\), line \\([0-9]+\\): \\(.*\\)$")
          (let* ((code (match-string 2))
                 (file (match-string 3))
                 (line (match-string 4))
                 (buffer (get-file-buffer file))
                 dir filename)
            (unless buffer
              (progn
                (setq buffer
                      (and (file-exists-p file)
                           (find-file-noselect file)))
                (or buffer
                    (let* ((pop-up-windows t))
                      (let ((name (expand-file-name
                                   (read-file-name
                                    (format "Find this error in: (default %s) "
                                            file)
                                    dir file t))))
                        (if (file-directory-p name)
                            (setq name (expand-file-name filename name)))
                        (setq buffer
                              (and (file-exists-p name)
                                   (find-file-noselect name))))))))
            (switch-to-buffer buffer)
            (goto-char (point-min))
            (forward-line (- (string-to-number line)))
            (end-of-line)
            (catch 'already
              (cond
               ((bsv-in-slash-comment-p)
                (re-search-backward "//")
                (cond
                 ((looking-at "// surefire lint_off_line ")
                  (goto-char (match-end 0))
                  (let ((lim (point-at-eol)))
                    (if (re-search-forward code lim 'move)
                        (throw 'already t)
                      (insert (concat " " code)))))
                 (t
                  )))
               ((bsv-in-star-comment-p)
                (re-search-backward "/\*")
                (insert (format " // surefire lint_off_line %6s" code )))
               (t
                (insert (format " // surefire lint_off_line %6s" code ))
                )))))))))

(defun bsv-verilint-off ()
  "Convert a Verilint warning line into a disable statement.

For example:
	(W240)  pci_bfm_null.v, line  46: Unused input: pci_rst_
becomes:
	//Verilint 240 off // WARNING: Unused input"
  (interactive)
  (save-excursion
    (beginning-of-line)
    (when (looking-at "\\(.*\\)([WE]\\([0-9A-Z]+\\)).*,\\s +line\\s +[0-9]+:\\s +\\([^:\n]+\\):?.*$")
      (replace-match (format
		      ;; %3s makes numbers 1-999 line up nicely
		      "\\1//Verilint %3s off // WARNING: \\3"
		      (match-string 2)))
      (beginning-of-line)
      (bsv-indent-line))))

(defun bsv-auto-save-compile ()
  "Update automatics with \\[bsv-auto], save the buffer, and compile."
  (interactive)
  (bsv-auto)	; Always do it for safety
  (save-buffer)
  (compile compile-command))

(defun bsv-preprocess (&optional command filename)
  "Preprocess the buffer, similar to `compile', but leave output in BSV-Mode.
Takes optional COMMAND or defaults to `bsv-preprocessor', and
FILENAME or defaults to `buffer-file-name`."
  (interactive
   (list
    (let ((default (bsv-expand-command bsv-preprocessor)))
      (set (make-local-variable `bsv-preprocessor)
	   (read-from-minibuffer "Run Preprocessor (like this): "
				 default nil nil
				 'bsv-preprocess-history default)))))
  (unless command (setq command (bsv-expand-command bsv-preprocessor)))
  (let* ((fontlocked (and (boundp 'font-lock-mode) font-lock-mode))
	 (dir (file-name-directory (or filename buffer-file-name)))
	 (file (file-name-nondirectory (or filename buffer-file-name)))
	 (cmd (concat "cd " dir "; " command " " file)))
    (with-output-to-temp-buffer "*BSV-Preprocessed*"
      (with-current-buffer (get-buffer "*BSV-Preprocessed*")
	(insert (concat "// " cmd "\n"))
	(shell-command cmd "*BSV-Preprocessed*")
	(bsv-mode)
	;; Without this force, it takes a few idle seconds
	;; to get the color, which is very jarring
	(when fontlocked (font-lock-fontify-buffer))))))


;;
;; Batch
;;

(defmacro bsv-batch-error-wrapper (&rest body)
  "Execute BODY and add error prefix to any errors found.
This lets programs calling batch mode to easily extract error messages."
  `(condition-case err
       (progn ,@body)
     (error
      (error "%%Error: %s%s" (error-message-string err)
	     (if (featurep 'xemacs) "\n" "")))))  ;; XEmacs forgets to add a newline

(defun bsv-batch-execute-func (funref &optional no-save)
  "Internal processing of a batch command, running FUNREF on all command arguments.
Save the result unless optional NO-SAVE is t."
  (bsv-batch-error-wrapper
   ;; Setting global variables like that is *VERY NASTY* !!!  --Stef
   ;; However, this function is called only when Emacs is being used as
   ;; a standalone language instead of as an editor, so we'll live.
   ;;
   ;; General globals needed
   (setq make-backup-files nil)
   (setq-default make-backup-files nil)
   (setq enable-local-variables t)
   (setq enable-local-eval t)
   ;; Make sure any sub-files we read get proper mode
   (setq-default major-mode 'bsv-mode)
   ;; Ditto files already read in
   (mapc (lambda (buf)
	   (when (buffer-file-name buf)
	     (with-current-buffer buf
	       (bsv-mode))))
	 (buffer-list))
   ;; Process the files
   (mapcar (lambda (buf)
	     (when (buffer-file-name buf)
	       (save-excursion
		 (if (not (file-exists-p (buffer-file-name buf)))
		     (error
		      (concat "File not found: " (buffer-file-name buf))))
		 (message (concat "Processing " (buffer-file-name buf)))
		 (set-buffer buf)
		 (funcall funref)
		 (unless no-save (save-buffer)))))
	   (buffer-list))))

(defun bsv-batch-auto ()
  "For use with --batch, perform automatic expansions as a stand-alone tool.
This sets up the appropriate BSV mode environment, updates automatics
with \\[bsv-auto] on all command-line files, and saves the buffers.
For proper results, multiple filenames need to be passed on the command
line in bottom-up order."
  (unless noninteractive
    (error "Use bsv-batch-auto only with --batch"))  ;; Otherwise we'd mess up buffer modes
  (bsv-batch-execute-func `bsv-auto))

(defun bsv-batch-delete-auto ()
  "For use with --batch, perform automatic deletion as a stand-alone tool.
This sets up the appropriate BSV mode environment, deletes automatics
with \\[bsv-delete-auto] on all command-line files, and saves the buffers."
  (unless noninteractive
    (error "Use bsv-batch-delete-auto only with --batch"))  ;; Otherwise we'd mess up buffer modes
  (bsv-batch-execute-func `bsv-delete-auto))

(defun bsv-batch-diff-auto ()
  "For use with --batch, perform automatic differences as a stand-alone tool.
This sets up the appropriate BSV mode environment, expand automatics
with \\[bsv-diff-auto] on all command-line files, and reports an error
if any differences are observed.  This is appropriate for adding to regressions
to insure automatics are always properly maintained."
  (unless noninteractive
    (error "Use bsv-batch-diff-auto only with --batch"))  ;; Otherwise we'd mess up buffer modes
  (bsv-batch-execute-func `bsv-diff-auto t))

(defun bsv-batch-inject-auto ()
  "For use with --batch, perform automatic injection as a stand-alone tool.
This sets up the appropriate BSV mode environment, injects new automatics
with \\[bsv-inject-auto] on all command-line files, and saves the buffers.
For proper results, multiple filenames need to be passed on the command
line in bottom-up order."
  (unless noninteractive
    (error "Use bsv-batch-inject-auto only with --batch"))  ;; Otherwise we'd mess up buffer modes
  (bsv-batch-execute-func `bsv-inject-auto))

(defun bsv-batch-indent ()
  "For use with --batch, reindent an a entire file as a stand-alone tool.
This sets up the appropriate BSV mode environment, calls
\\[bsv-indent-buffer] on all command-line files, and saves the buffers."
  (unless noninteractive
    (error "Use bsv-batch-indent only with --batch"))  ;; Otherwise we'd mess up buffer modes
  (bsv-batch-execute-func `bsv-indent-buffer))


;;
;; Indentation
;;
(defconst bsv-indent-alist
  '((block       . (+ ind bsv-indent-level))
    (case        . (+ ind bsv-case-indent))
    (cparenexp   . (+ ind bsv-indent-level))
    (cexp        . (+ ind bsv-cexp-indent))
    (defun       . bsv-indent-level-module)
    (declaration . bsv-indent-level-declaration)
    (directive   . (bsv-calculate-indent-directive))
    (tf          . bsv-indent-level)
    (behavioral  . (+ bsv-indent-level-behavioral bsv-indent-level-module))
    (statement   . ind)
    (cpp         . 0)
    (comment     . (bsv-comment-indent))
    (unknown     . 3)
    (string      . 0)))

(defun bsv-continued-line-1 (lim)
  "Return true if this is a continued line.
Set point to where line starts.  Limit search to point LIM."
  (let ((continued 't))
    (if (eq 0 (forward-line -1))
	(progn
	  (end-of-line)
	  (bsv-backward-ws&directives lim)
	  (if (bobp)
	      (setq continued nil)
	    (setq continued (bsv-backward-token))))
      (setq continued nil))
    continued))

(defun bsv-calculate-indent ()
  "Calculate the indent of the current BSV line.
Examine previous lines.  Once a line is found that is definitive as to the
type of the current line, return that lines' indent level and its type.
Return a list of two elements: (INDENT-TYPE INDENT-LEVEL)."
  (save-excursion
    (let* ((starting_position (point))
	   (par 0)
	   (begin (looking-at "[ \t]*begin\\>"))
	   (lim (save-excursion (bsv-re-search-backward "\\(\\<begin\\>\\)\\|\\(\\<module\\>\\)" nil t)))
	   (type (catch 'nesting
		   ;; Keep working backwards until we can figure out
		   ;; what type of statement this is.
		   ;; Basically we need to figure out
		   ;; 1) if this is a continuation of the previous line;
		   ;; 2) are we in a block scope (begin..end)

		   ;; if we are in a comment, done.
		   (if (bsv-in-star-comment-p)
		       (throw 'nesting 'comment))

		   ;; if we have a directive, done.
		   (if (save-excursion (beginning-of-line)
				       (and (looking-at bsv-directive-re-1)
					    (not (or (looking-at "[ \t]*`[ou]vm_")
                                 (looking-at "[ \t]*`vmm_")))))
		       (throw 'nesting 'directive))
           ;; indent structs as if there were module level
           (if (bsv-in-struct-p)
               (throw 'nesting 'block))

	   ;; if we are in a parenthesized list, and the user likes to indent these, return.
	   ;; unless we are in the newfangled coverpoint or constraint blocks
	   (if (and
                bsv-indent-lists
                (bsv-in-paren)
                (not (bsv-in-coverage-p))
                )
	       (progn (setq par 1)
                      (throw 'nesting 'block)))

	   ;; See if we are continuing a previous line
	   (while t
	     ;; trap out if we crawl off the top of the buffer
	     (if (bobp) (throw 'nesting 'cpp))

	     (if (bsv-continued-line-1 lim)
		 (let ((sp (point)))
		   (if (and
			(not (looking-at bsv-complete-reg))
			(bsv-continued-line-1 lim))
		       (progn (goto-char sp)
			      (throw 'nesting 'cexp))

		     (goto-char sp))

		   (if (and begin
			    (not bsv-indent-begin-after-if)
			    (looking-at bsv-no-indent-begin-re))
		       (progn
			 (beginning-of-line)
			 (skip-chars-forward " \t")
			 (throw 'nesting 'statement))
		     (progn
		       (throw 'nesting 'cexp))))
	       ;; not a continued line
	       (goto-char starting_position))

	     (if (looking-at "\\<else\\>")
		 ;; search back for governing if, striding across begin..end pairs
		 ;; appropriately
		 (let ((elsec 1))
		   (while (bsv-re-search-backward bsv-ends-re nil 'move)
		     (cond
		      ((match-end 1) ; else, we're in deep
		       (setq elsec (1+ elsec)))
		      ((match-end 2) ; if
		       (setq elsec (1- elsec))
		       (if (= 0 elsec)
			   (if bsv-align-ifelse
			       (throw 'nesting 'statement)
			     (progn ;; back up to first word on this line
			       (beginning-of-line)
			       (bsv-forward-syntactic-ws)
			       (throw 'nesting 'statement)))))
		      ((match-end 3) ; assert block
		       (setq elsec (1- elsec))
		       (bsv-beg-of-statement) ;; doesn't get to beginning
		       (if (looking-at bsv-property-re)
			   (throw 'nesting 'statement) ; We don't need an endproperty for these
			 (throw 'nesting 'block)	;We still need a endproperty
			 ))
		      (t ; endblock
					; try to leap back to matching outward block by striding across
					; indent level changing tokens then immediately
					; previous line governs indentation.
		       (let (( reg) (nest 1))
			 ;;	 bsv-ends =>  else|if|end|join(_any|_none|)|endcase|endclass|endtable|endspecify|endfunction|endtask|endgenerate|endgroup
			 (cond
			  ((match-end 4) ; end
			   ;; Search back for matching begin
			   (setq reg "\\(\\<begin\\>\\)\\|\\(\\<end\\>\\)" ))
			  ((match-end 5) ; endcase
			   ;; Search back for matching case
			   (setq reg "\\(\\<randcase\\>\\|\\<case[xz]?\\>[^:]\\)\\|\\(\\<endcase\\>\\)" ))
			  ((match-end 6) ; endfunction
			   ;; Search back for matching function
			   (setq reg "\\(\\<function\\>\\)\\|\\(\\<endfunction\\>\\)" ))
			  ((match-end 7) ; endtask
			   ;; Search back for matching task
			   (setq reg "\\(\\<task\\>\\)\\|\\(\\<endtask\\>\\)" ))
			  ((match-end 8) ; endspecify
			   ;; Search back for matching specify
			   (setq reg "\\(\\<specify\\>\\)\\|\\(\\<endspecify\\>\\)" ))
			  ((match-end 9) ; endtable
			   ;; Search back for matching table
			   (setq reg "\\(\\<table\\>\\)\\|\\(\\<endtable\\>\\)" ))
			  ((match-end 10) ; endgenerate
			   ;; Search back for matching generate
			   (setq reg "\\(\\<generate\\>\\)\\|\\(\\<endgenerate\\>\\)" ))
			  ((match-end 11) ; joins
			   ;; Search back for matching fork
			   (setq reg "\\(\\<fork\\>\\)\\|\\(\\<join\\(_any\\|none\\)?\\>\\)" ))
			  ((match-end 12) ; class
			   ;; Search back for matching class
			   (setq reg "\\(\\<class\\>\\)\\|\\(\\<endclass\\>\\)" ))
			  ((match-end 13) ; covergroup
			   ;; Search back for matching covergroup
			   (setq reg "\\(\\<covergroup\\>\\)\\|\\(\\<endgroup\\>\\)" )))
			 (catch 'skip
			   (while (bsv-re-search-backward reg nil 'move)
			     (cond
			      ((match-end 1) ; begin
			       (setq nest (1- nest))
			       (if (= 0 nest)
				   (throw 'skip 1)))
			      ((match-end 2) ; end
			       (setq nest (1+ nest)))))
			   )))))))
	     (throw 'nesting (bsv-calc-1)))
	   );; catch nesting
		 );; type
	   )
      ;; Return type of block and indent level.
      (if (not type)
	  (setq type 'cpp))
      (if (> par 0)			; Unclosed Parenthesis
	  (list 'cparenexp par)
	(cond
	  ((eq type 'case)
	   (list type (bsv-case-indent-level)))
	  ((eq type 'statement)
	   (list type (current-column)))
	  ((eq type 'defun)
	   (list type 0))
	  (t
	   (list type (bsv-current-indent-level))))))))

(defun bsv-wai ()
  "Show matching nesting block for debugging."
  (interactive)
  (save-excursion
    (let* ((type (bsv-calc-1))
	   depth)
      ;; Return type of block and indent level.
      (if (not type)
	  (setq type 'cpp))
      (if (and
	   bsv-indent-lists
	   (not(or (bsv-in-coverage-p)
               (bsv-in-struct-p)))
	   (bsv-in-paren))
	  (setq depth 1)
	(cond
	  ((eq type 'case)
	   (setq depth (bsv-case-indent-level)))
	  ((eq type 'statement)
	   (setq depth (current-column)))
	  ((eq type 'defun)
	   (setq depth 0))
	  (t
	   (setq depth (bsv-current-indent-level)))))
      (message "You are at nesting %s depth %d" type depth))))

(defun bsv-calc-1 ()
  (catch 'nesting
    (let ((re (concat "\\({\\|}\\|" bsv-indent-re "\\)")))
      (while (bsv-re-search-backward re nil 'move)
	(catch 'continue
	  (cond
	   ((equal (char-after) ?\{)
	    (if (bsv-at-constraint-p)
		(throw 'nesting 'block)))

	   ((equal (char-after) ?\})
	    (let ((there (bsv-at-close-constraint-p)))
	      (if there ;; we are at the } that closes a constraint.  Find the { that opens it
		  (progn
		    (forward-char 1)
		    (backward-list 1)
		    (bsv-beg-of-statement)))))

	   ((looking-at bsv-beg-block-re-ordered)
	    (cond
	     ((match-end 2)  ; *sigh* could be "unique case" or "priority casex"
	      (let ((here (point)))
		(bsv-beg-of-statement)
		(if (looking-at bsv-extended-case-re)
		    (throw 'nesting 'case)
		  (goto-char here)))
	      (throw 'nesting 'case))

	     ((match-end 4)  ; *sigh* could be "disable fork"
	      (let ((here (point)))
		(bsv-beg-of-statement)
		(if (looking-at bsv-disable-fork-re)
		    t ; this is a normal statement
		  (progn ; or is fork, starts a new block
		    (goto-char here)
		    (throw 'nesting 'block)))))

	     ((match-end 27)  ; *sigh* might be a clocking declaration
	      (let ((here (point)))
		(if (bsv-in-paren)
		    t ; this is a normal statement
		  (progn ; or is fork, starts a new block
		    (goto-char here)
		    (throw 'nesting 'block)))))

	     ;; need to consider typedef struct here...
	     ((looking-at "\\<class\\|struct\\|function\\|task\\>")
					; *sigh* These words have an optional prefix:
					; extern {virtual|protected}? function a();
	                                ; typedef class foo;
					; and we don't want to confuse this with
					; function a();
	                                ; property
					; ...
					; endfunction
	      (bsv-beg-of-statement)
	      (if (looking-at bsv-beg-block-re-ordered)
		  (throw 'nesting 'block)
		(throw 'nesting 'defun)))

	     ((looking-at "\\<property\\>")
					; *sigh*
					;    {assert|assume|cover} property (); are complete
	                                ;   and could also be labeled: - foo: assert property
					; but
                                        ;    property ID () ... needs end_property
	      (bsv-beg-of-statement)
	      (if (looking-at bsv-property-re)
		  (throw 'continue 'statement) ; We don't need an endproperty for these
		(throw 'nesting 'block)	;We still need a endproperty
		))

	     (t              (throw 'nesting 'block))))

	   ((looking-at bsv-end-block-re)
	    (bsv-leap-to-head)
	    (if (bsv-in-case-region-p)
		(progn
		  (bsv-leap-to-case-head)
		  (if (looking-at bsv-extended-case-re)
		      (throw 'nesting 'case)))))

	   ((looking-at bsv-defun-level-re)
	    (if (looking-at bsv-defun-level-generate-only-re)
		(if (bsv-in-generate-region-p)
		    (throw 'continue 'foo)  ; always block in a generate - keep looking
		  (throw 'nesting 'defun))
	      (throw 'nesting 'defun)))

	   ((looking-at bsv-cpp-level-re)
	    (throw 'nesting 'cpp))

	   ((bobp)
	    (throw 'nesting 'cpp)))))

      (throw 'nesting 'cpp))))

(defun bsv-calculate-indent-directive ()
  "Return indentation level for directive.
For speed, the searcher looks at the last directive, not the indent
of the appropriate enclosing block."
  (let ((base -1)	;; Indent of the line that determines our indentation
	(ind 0))        ;; Relative offset caused by other directives (like `endif on same line as `else)
    ;; Start at current location, scan back for another directive

    (save-excursion
      (beginning-of-line)
      (while (and (< base 0)
		  (bsv-re-search-backward bsv-directive-re nil t))
	(cond ((save-excursion (skip-chars-backward " \t") (bolp))
	       (setq base (current-indentation))))
	(cond ((and (looking-at bsv-directive-end) (< base 0))  ;; Only matters when not at BOL
	       (setq ind (- ind bsv-indent-level-directive)))
	      ((and (looking-at bsv-directive-middle) (>= base 0))  ;; Only matters when at BOL
	       (setq ind (+ ind bsv-indent-level-directive)))
	      ((looking-at bsv-directive-begin)
	       (setq ind (+ ind bsv-indent-level-directive)))))
      ;; Adjust indent to starting indent of critical line
      (setq ind (max 0 (+ ind base))))

    (save-excursion
      (beginning-of-line)
      (skip-chars-forward " \t")
      (cond ((or (looking-at bsv-directive-middle)
		 (looking-at bsv-directive-end))
	     (setq ind (max 0 (- ind bsv-indent-level-directive))))))
   ind))

(defun bsv-leap-to-case-head ()
  (let ((nest 1))
    (while (/= 0 nest)
      (bsv-re-search-backward
       (concat
	"\\(\\<randcase\\>\\|\\(\\<unique\\s-+\\|priority\\s-+\\)?\\<case[xz]?\\>\\)"
	"\\|\\(\\<endcase\\>\\)" )
       nil 'move)
      (cond
       ((match-end 1)
	(let ((here (point)))
	  (bsv-beg-of-statement)
	  (unless (looking-at bsv-extended-case-re)
	    (goto-char here)))
	(setq nest (1- nest)))
       ((match-end 3)
	(setq nest (1+ nest)))
       ((bobp)
	(ding 't)
	(setq nest 0))))))

(defun bsv-leap-to-head ()
  "Move point to the head of this block.
Jump from end to matching begin, from endcase to matching case, and so on."
  (let ((reg nil)
	snest
	(nesting 'yes)
	(nest 1))
    (cond
     ((looking-at "\\<end\\>")
      ;; 1: Search back for matching begin
      (setq reg (concat "\\(\\<begin\\>\\)\\|\\(\\<end\\>\\)\\|"
			"\\(\\<endcase\\>\\)\\|\\(\\<join\\(_any\\|_none\\)?\\>\\)" )))
     ((looking-at "\\<endtask\\>")
      ;; 2: Search back for matching task
      (setq reg "\\(\\<task\\>\\)\\|\\(\\(\\(\\<virtual\\>\\s-+\\)\\|\\(\\<protected\\>\\s-+\\)\\)+\\<task\\>\\)")
      (setq nesting 'no))
     ((looking-at "\\<endcase\\>")
      (catch 'nesting
	(bsv-leap-to-case-head) )
      (setq reg nil) ; to force skip
      )

     ((looking-at "\\<join\\(_any\\|_none\\)?\\>")
      ;; 4: Search back for matching fork
      (setq reg "\\(\\<fork\\>\\)\\|\\(\\<join\\(_any\\|_none\\)?\\>\\)" ))
     ((looking-at "\\<endclass\\>")
      ;; 5: Search back for matching class
      (setq reg "\\(\\<class\\>\\)\\|\\(\\<endclass\\>\\)" ))
     ((looking-at "\\<endtable\\>")
      ;; 6: Search back for matching table
      (setq reg "\\(\\<table\\>\\)\\|\\(\\<endtable\\>\\)" ))
     ((looking-at "\\<endspecify\\>")
      ;; 7: Search back for matching specify
      (setq reg "\\(\\<specify\\>\\)\\|\\(\\<endspecify\\>\\)" ))
     ((looking-at "\\<endfunction\\>")
      ;; 8: Search back for matching function
      (setq reg "\\(\\<function\\>\\)\\|\\(\\(\\(\\<virtual\\>\\s-+\\)\\|\\(\\<protected\\>\\s-+\\)\\)+\\<function\\>\\)")
      (setq nesting 'no))
      ;;(setq reg "\\(\\<function\\>\\)\\|\\(\\<endfunction\\>\\)" ))
     ((looking-at "\\<endgenerate\\>")
      ;; 8: Search back for matching generate
      (setq reg "\\(\\<generate\\>\\)\\|\\(\\<endgenerate\\>\\)" ))
     ((looking-at "\\<endgroup\\>")
      ;; 10: Search back for matching covergroup
      (setq reg "\\(\\<covergroup\\>\\)\\|\\(\\<endgroup\\>\\)" ))
     ((looking-at "\\<endproperty\\>")
      ;; 11: Search back for matching property
      (setq reg "\\(\\<property\\>\\)\\|\\(\\<endproperty\\>\\)" ))
     ((looking-at bsv-uvm-end-re)
      ;; 12: Search back for matching sequence
      (setq reg (concat "\\(" bsv-uvm-begin-re "\\|" bsv-uvm-end-re "\\)")))
     ((looking-at bsv-ovm-end-re)
      ;; 12: Search back for matching sequence
      (setq reg (concat "\\(" bsv-ovm-begin-re "\\|" bsv-ovm-end-re "\\)")))
     ((looking-at bsv-vmm-end-re)
      ;; 12: Search back for matching sequence
      (setq reg (concat "\\(" bsv-vmm-begin-re "\\|" bsv-vmm-end-re "\\)")))
     ((looking-at "\\<endinterface\\>")
      ;; 12: Search back for matching interface
      (setq reg "\\(\\<interface\\>\\)\\|\\(\\<endinterface\\>\\)" ))
     ((looking-at "\\<endsequence\\>")
      ;; 12: Search back for matching sequence
      (setq reg "\\(\\<\\(rand\\)?sequence\\>\\)\\|\\(\\<endsequence\\>\\)" ))
     ((looking-at "\\<endclocking\\>")
      ;; 12: Search back for matching clocking
      (setq reg "\\(\\<clocking\\)\\|\\(\\<endclocking\\>\\)" )))
    (if reg
	(catch 'skip
	  (if (eq nesting 'yes)
	      (let (sreg)
		(while (bsv-re-search-backward reg nil 'move)
		  (cond
		   ((match-end 1) ; begin
		    (if (looking-at "fork")
			(let ((here (point)))
			  (bsv-beg-of-statement)
			  (unless (looking-at bsv-disable-fork-re)
			    (goto-char here)
			    (setq nest (1- nest))))
		      (setq nest (1- nest)))
		    (if (= 0 nest)
			;; Now previous line describes syntax
			(throw 'skip 1))
		    (if (and snest
			     (= snest nest))
			(setq reg sreg)))
		   ((match-end 2) ; end
		    (setq nest (1+ nest)))
		   ((match-end 3)
		    ;; endcase, jump to case
		    (setq snest nest)
		    (setq nest (1+ nest))
		    (setq sreg reg)
		    (setq reg "\\(\\<randcase\\>\\|\\<case[xz]?\\>[^:]\\)\\|\\(\\<endcase\\>\\)" ))
		   ((match-end 4)
		    ;; join, jump to fork
		    (setq snest nest)
		    (setq nest (1+ nest))
		    (setq sreg reg)
		    (setq reg "\\(\\<fork\\>\\)\\|\\(\\<join\\(_any\\|_none\\)?\\>\\)" ))
		   )))
	    ;no nesting
	    (if (and
		 (bsv-re-search-backward reg nil 'move)
		 (match-end 1)) ; task -> could be virtual and/or protected
		(progn
		  (bsv-beg-of-statement)
		  (throw 'skip 1))
	      (throw 'skip 1)))))))

(defun bsv-continued-line ()
  "Return true if this is a continued line.
Set point to where line starts."
  (let ((continued 't))
    (if (eq 0 (forward-line -1))
	(progn
	  (end-of-line)
	  (bsv-backward-ws&directives)
	  (if (bobp)
	      (setq continued nil)
	    (while (and continued
			(save-excursion
			  (skip-chars-backward " \t")
			  (not (bolp))))
	    (setq continued (bsv-backward-token)))))
      (setq continued nil))
    continued))

(defun bsv-backward-token ()
  "Step backward token, returning true if this is a continued line."
  (interactive)
  (bsv-backward-syntactic-ws)
  (cond
   ((bolp)
    nil)
   (;-- Anything ending in a ; is complete
    (= (preceding-char) ?\;)
    nil)
   (; If a "}" is prefixed by a ";", then this is a complete statement
    ; i.e.: constraint foo { a = b; }
    (= (preceding-char) ?\})
    (progn
      (backward-char)
      (not(bsv-at-close-constraint-p))))
   (;-- constraint foo { a = b }
    ;   is a complete statement. *sigh*
    (= (preceding-char) ?\{)
    (progn
      (backward-char)
      (not (bsv-at-constraint-p))))
   (;" string "
    (= (preceding-char) ?\")
    (backward-char)
    (bsv-skip-backward-comment-or-string)
    nil)

   (; [3:4]
    (= (preceding-char) ?\])
    (backward-char)
    (bsv-backward-open-bracket)
    t)

   (;-- Could be 'case (foo)' or 'always @(bar)' which is complete
    ;   also could be simply '@(foo)'
    ;   or foo u1 #(a=8)
    ;            (b, ... which ISN'T complete
    ;;;; Do we need this???
    (= (preceding-char) ?\))
    (progn
      (backward-char)
      (bsv-backward-up-list 1)
      (bsv-backward-syntactic-ws)
      (let ((back (point)))
	(forward-word -1)
	(cond
	 ;;XX
	 ((looking-at "\\<\\(always\\(_latch\\|_ff\\|_comb\\)?\\|case\\(\\|[xz]\\)\\|for\\(\\|each\\|ever\\)\\|i\\(f\\|nitial\\)\\|repeat\\|while\\)\\>")
	  (not (looking-at "\\<randcase\\>\\|\\<case[xz]?\\>[^:]")))
	 ((looking-at bsv-uvm-statement-re)
	  nil)
	 ((looking-at bsv-uvm-begin-re)
	  t)
	 ((looking-at bsv-uvm-end-re)
	  t)
	 ((looking-at bsv-ovm-statement-re)
	  nil)
	 ((looking-at bsv-ovm-begin-re)
	  t)
	 ((looking-at bsv-ovm-end-re)
	  t)
     ;; JBA find VMM macros
     ((looking-at bsv-vmm-statement-re)
      nil )
     ((looking-at bsv-vmm-begin-re)
      t)
     ((looking-at bsv-vmm-end-re)
      nil)
     ;; JBA trying to catch macro lines with no ; at end
     ((looking-at "\\<`")
      nil)
	 (t
	  (goto-char back)
	  (cond
	   ((= (preceding-char) ?\@)
	    (backward-char)
	    (save-excursion
	      (bsv-backward-token)
	      (not (looking-at "\\<\\(always\\(_latch\\|_ff\\|_comb\\)?\\|initial\\|while\\)\\>"))))
	   ((= (preceding-char) ?\#)
	    (backward-char))
	   (t t)))))))

   (;-- any of begin|initial|while are complete statements; 'begin : foo' is also complete
    t
    (forward-word -1)
    (while (= (preceding-char) ?\_)
      (forward-word -1))
    (cond
     ((looking-at "\\<else\\>")
      t)
     ((looking-at bsv-behavioral-block-beg-re)
      t)
     ((looking-at bsv-indent-re)
      nil)
     (t
      (let
	  ((back (point)))
	(bsv-backward-syntactic-ws)
	(cond
	 ((= (preceding-char) ?\:)
	  (backward-char)
	  (bsv-backward-syntactic-ws)
	  (backward-sexp)
	  (if (looking-at bsv-nameable-item-re )
	      nil
	    t))
	 ((= (preceding-char) ?\#)
	  (backward-char)
	  t)
	 ((= (preceding-char) ?\`)
	  (backward-char)
	  t)

	 (t
	  (goto-char back)
	  t))))))))

(defun bsv-backward-syntactic-ws ()
  "Move backwards putting point after first non-whitespace non-comment."
  (bsv-skip-backward-comments)
  (forward-comment (- (buffer-size))))

(defun bsv-backward-syntactic-ws-quick ()
  "As with `bsv-backward-syntactic-ws' but uses `bsv-scan' cache."
  (while (cond ((bobp)
		nil) ; Done
	       ((> (skip-syntax-backward " ") 0)
		t)
	       ((eq (preceding-char) ?\n)  ;; \n's terminate // so aren't space syntax
		(forward-char -1)
		t)
	       ((or (bsv-inside-comment-or-string-p (1- (point)))
		    (bsv-inside-comment-or-string-p (point)))
		(re-search-backward "[/\"]" nil t) ;; Only way a comment or quote can begin
		t))))

(defun bsv-forward-syntactic-ws ()
  (bsv-skip-forward-comment-p)
  (forward-comment (buffer-size)))

(defun bsv-backward-ws&directives (&optional bound)
  "Backward skip over syntactic whitespace and compiler directives for Emacs 19.
Optional BOUND limits search."
  (save-restriction
    (let* ((bound (or bound (point-min)))
	   (here bound)
	   (p nil) )
      (if (< bound (point))
	  (progn
	    (let ((state (save-excursion (bsv-syntax-ppss))))
	      (cond
	       ((nth 7 state) ;; in // comment
		(bsv-re-search-backward "//" nil 'move)
                (skip-chars-backward "/"))
	       ((nth 4 state) ;; in /* */ comment
		(bsv-re-search-backward "/\*" nil 'move))))
	    (narrow-to-region bound (point))
	    (while (/= here (point))
	      (setq here (point))
	      (bsv-skip-backward-comments)
	      (setq p
		    (save-excursion
		      (beginning-of-line)
		      (cond
		       ((and bsv-highlight-translate-off
			     (bsv-within-translate-off))
			(bsv-back-to-start-translate-off (point-min)))
		       ((looking-at bsv-directive-re-1)
			(point))
		       (t
			nil))))
	      (if p (goto-char p))))))))

(defun bsv-forward-ws&directives (&optional bound)
  "Forward skip over syntactic whitespace and compiler directives for Emacs 19.
Optional BOUND limits search."
  (save-restriction
    (let* ((bound (or bound (point-max)))
	   (here bound)
	   jump)
      (if (> bound (point))
	  (progn
	    (let ((state (save-excursion (bsv-syntax-ppss))))
	      (cond
	       ((nth 7 state) ;; in // comment
		(end-of-line)
		(forward-char 1)
		(skip-chars-forward " \t\n\f")
		)
	       ((nth 4 state) ;; in /* */ comment
		(bsv-re-search-forward "\*\/\\s-*" nil 'move))))
	    (narrow-to-region (point) bound)
	    (while (/= here (point))
	      (setq here (point)
		    jump nil)
	      (forward-comment (buffer-size))
	      (and (looking-at "\\s-*(\\*.*\\*)\\s-*") ;; Attribute
		   (goto-char (match-end 0)))
	      (save-excursion
		(beginning-of-line)
		(if (looking-at bsv-directive-re-1)
		    (setq jump t)))
	      (if jump
		  (beginning-of-line 2))))))))

(defun bsv-in-comment-p ()
 "Return true if in a star or // comment."
 (let ((state (save-excursion (bsv-syntax-ppss))))
   (or (nth 4 state) (nth 7 state))))

(defun bsv-in-star-comment-p ()
 "Return true if in a star comment."
 (let ((state (save-excursion (bsv-syntax-ppss))))
   (and
    (nth 4 state)			; t if in a comment of style a // or b /**/
	(not
	 (nth 7 state)			; t if in a comment of style b /**/
	 ))))

(defun bsv-in-slash-comment-p ()
 "Return true if in a slash comment."
 (let ((state (save-excursion (bsv-syntax-ppss))))
   (nth 7 state)))

(defun bsv-in-comment-or-string-p ()
 "Return true if in a string or comment."
 (let ((state (save-excursion (bsv-syntax-ppss))))
   (or (nth 3 state) (nth 4 state) (nth 7 state)))) ; Inside string or comment)

(defun bsv-in-attribute-p ()
 "Return true if point is in an attribute (* [] attribute *)."
 (save-match-data
   (save-excursion
     (bsv-re-search-backward "\\((\\*\\)\\|\\(\\*)\\)" nil 'move)
     (numberp (match-beginning 1)))))

(defun bsv-in-parameter-p ()
 "Return true if point is in a parameter assignment #( p1=1, p2=5)."
 (save-match-data
   (save-excursion
     (bsv-re-search-backward "\\(#(\\)\\|\\()\\)" nil 'move)
     (numberp (match-beginning 1)))))

(defun bsv-in-escaped-name-p ()
 "Return true if in an escaped name."
 (save-excursion
   (backward-char)
   (skip-chars-backward "^ \t\n\f")
   (if (equal (char-after (point) ) ?\\ )
       t
     nil)))
(defun bsv-in-directive-p ()
 "Return true if in a directive."
 (save-excursion
   (beginning-of-line)
   (looking-at bsv-directive-re-1)))

(defun bsv-in-parenthesis-p ()
 "Return true if in a ( ) expression (but not { } or [ ])."
 (save-match-data
   (save-excursion
     (bsv-re-search-backward "\\((\\)\\|\\()\\)" nil 'move)
     (numberp (match-beginning 1)))))

(defun bsv-in-paren ()
 "Return true if in a parenthetical expression.
May cache result using `bsv-syntax-ppss'."
 (let ((state (save-excursion (bsv-syntax-ppss))))
   (> (nth 0 state) 0 )))

(defun bsv-in-paren-quick ()
 "Return true if in a parenthetical expression.
Always starts from point-min, to allow inserts with hooks disabled."
 ;; The -quick refers to its use alongside the other -quick functions,
 ;; not that it's likely to be faster than bsv-in-paren.
 (let ((state (save-excursion (parse-partial-sexp (point-min) (point)))))
   (> (nth 0 state) 0 )))

(defun bsv-in-struct-p ()
 "Return true if in a struct declaration."
 (interactive)
 (save-excursion
   (if (bsv-in-paren)
       (progn
	 (bsv-backward-up-list 1)
	 (bsv-at-struct-p)
	 )
     nil)))

(defun bsv-in-coverage-p ()
 "Return true if in a constraint or coverpoint expression."
 (interactive)
 (save-excursion
   (if (bsv-in-paren)
       (progn
	 (bsv-backward-up-list 1)
	 (bsv-at-constraint-p)
	 )
     nil)))
(defun bsv-at-close-constraint-p ()
  "If at the } that closes a constraint or covergroup, return true."
  (if (and
       (equal (char-after) ?\})
       (bsv-in-paren))

      (save-excursion
	(bsv-backward-ws&directives)
	(if (equal (char-before) ?\;)
	    (point)
	  nil))))

(defun bsv-at-constraint-p ()
  "If at the { of a constraint or coverpoint definition, return true, moving point to constraint."
  (if (save-excursion
	(and
	 (equal (char-after) ?\{)
	 (forward-list)
	 (progn (backward-char 1)
		(bsv-backward-ws&directives)
		(equal (char-before) ?\;))))
      ;; maybe
      (bsv-re-search-backward "\\<constraint\\|coverpoint\\|cross\\>" nil 'move)
    ;; not
    nil))

(defun bsv-at-struct-p ()
  "If at the { of a struct, return true, moving point to struct."
  (save-excursion
    (if (and (equal (char-after) ?\{)
             (bsv-backward-token))
        (looking-at "\\<struct\\|union\\|packed\\|\\(un\\)?signed\\>")
      nil)))

(defun bsv-parenthesis-depth ()
 "Return non zero if in parenthetical-expression."
 (save-excursion (nth 1 (bsv-syntax-ppss))))


(defun bsv-skip-forward-comment-or-string ()
 "Return true if in a string or comment."
 (let ((state (save-excursion (bsv-syntax-ppss))))
   (cond
    ((nth 3 state)			;Inside string
     (search-forward "\"")
     t)
    ((nth 7 state)			;Inside // comment
     (forward-line 1)
     t)
    ((nth 4 state)			;Inside any comment (hence /**/)
     (search-forward "*/"))
    (t
     nil))))

(defun bsv-skip-backward-comment-or-string ()
 "Return true if in a string or comment."
 (let ((state (save-excursion (bsv-syntax-ppss))))
   (cond
    ((nth 3 state)			;Inside string
     (search-backward "\"")
     t)
    ((nth 7 state)			;Inside // comment
     (search-backward "//")
     (skip-chars-backward "/")
     t)
    ((nth 4 state)			;Inside /* */ comment
     (search-backward "/*")
     t)
    (t
     nil))))

(defun bsv-skip-backward-comments ()
 "Return true if a comment was skipped."
 (let ((more t))
   (while more
     (setq more
	   (let ((state (save-excursion (bsv-syntax-ppss))))
	     (cond
	      ((nth 7 state)			;Inside // comment
	       (search-backward "//")
	       (skip-chars-backward "/")
	       (skip-chars-backward " \t\n\f")
	       t)
	      ((nth 4 state)			;Inside /* */ comment
	       (search-backward "/*")
	       (skip-chars-backward " \t\n\f")
	       t)
	      ((and (not (bobp))
		    (= (char-before) ?\/)
		    (= (char-before (1- (point))) ?\*))
	       (goto-char (- (point) 2))
	       t) ;; Let nth 4 state handle the rest
	      ((and (not (bobp))
		    (= (char-before) ?\))
		    (= (char-before (1- (point))) ?\*))
	       (goto-char (- (point) 2))
	       (if (search-backward "(*" nil t)
		   (progn
		     (skip-chars-backward " \t\n\f")
		     t)
		 (progn
		   (goto-char (+ (point) 2))
		   nil)))
	      (t
	       (/= (skip-chars-backward " \t\n\f") 0))))))))

(defun bsv-skip-forward-comment-p ()
  "If in comment, move to end and return true."
  (let* (h
	 (state (save-excursion (bsv-syntax-ppss)))
	 (skip (cond
		((nth 3 state)		;Inside string
		 t)
		((nth 7 state)		;Inside // comment
		 (end-of-line)
		 (forward-char 1)
		 t)
		((nth 4 state)		;Inside /* comment
		 (search-forward "*/")
		 t)
		((bsv-in-attribute-p)  ;Inside (* attribute
		 (search-forward "*)" nil t)
		 t)
		(t nil))))
    (skip-chars-forward " \t\n\f")
    (while
	(cond
	 ((looking-at "\\/\\*")
	  (progn
	    (setq h (point))
	    (goto-char (match-end 0))
	    (if (search-forward "*/" nil t)
		(progn
		  (skip-chars-forward " \t\n\f")
		  (setq skip 't))
	      (progn
		(goto-char h)
		nil))))
	 ((looking-at "(\\*")
	  (progn
	    (setq h (point))
	    (goto-char (match-end 0))
	    (if (search-forward "*)" nil t)
		(progn
		  (skip-chars-forward " \t\n\f")
		  (setq skip 't))
	      (progn
		(goto-char h)
		nil))))
	 (t nil)))
    skip))

(defun bsv-indent-line-relative ()
  "Cheap version of indent line.
Only look at a few lines to determine indent level."
  (interactive)
  (let ((indent-str)
	(sp (point)))
    (if (looking-at "^[ \t]*$")
	(cond  ;- A blank line; No need to be too smart.
	 ((bobp)
	  (setq indent-str (list 'cpp 0)))
	 ((bsv-continued-line)
	  (let ((sp1 (point)))
	    (if (bsv-continued-line)
		(progn
		  (goto-char sp)
		  (setq indent-str
			(list 'statement (bsv-current-indent-level))))
	      (goto-char sp1)
	      (setq indent-str (list 'block (bsv-current-indent-level)))))
	  (goto-char sp))
	 ((goto-char sp)
	  (setq indent-str (bsv-calculate-indent))))
      (progn (skip-chars-forward " \t")
	     (setq indent-str (bsv-calculate-indent))))
    (bsv-do-indent indent-str)))

;; (defun bsv-indent-line ()
;;   "Indent for special part of code."
;;   (bsv-do-indent (bsv-calculate-indent)))

(defun bsv-do-indent (indent-str)
  (let ((type (car indent-str))
	(ind (car (cdr indent-str))))
    (cond
     (; handle continued exp
      (eq type 'cexp)
      (let ((here (point)))
	(bsv-backward-syntactic-ws)
	(cond
	 ((or
	   (= (preceding-char) ?\,)
	   (= (preceding-char) ?\])
	   (save-excursion
	     (bsv-beg-of-statement-1)
	     (looking-at bsv-declaration-re)))
	  (let* ( fst
		  (val
		   (save-excursion
		     (backward-char 1)
		     (bsv-beg-of-statement-1)
		     (setq fst (point))
		     (if (looking-at bsv-declaration-re)
			 (progn ;; we have multiple words
			   (goto-char (match-end 0))
			   (skip-chars-forward " \t")
			   (cond
			    ((and bsv-indent-declaration-macros
				  (= (following-char) ?\`))
			     (progn
			       (forward-char 1)
			       (forward-word 1)
			       (skip-chars-forward " \t")))
			    ((= (following-char) ?\[)
			     (progn
			       (forward-char 1)
			       (bsv-backward-up-list -1)
			       (skip-chars-forward " \t"))))
			   (current-column))
		       (progn
			 (goto-char fst)
			 (+ (current-column) bsv-cexp-indent))))))
	    (goto-char here)
	    (indent-line-to val)
	    (if (and (not bsv-indent-lists)
		     (bsv-in-paren))
		(bsv-pretty-declarations))
	    ))
	 ((= (preceding-char) ?\) )
	  (goto-char here)
	  (let ((val (eval (cdr (assoc type bsv-indent-alist)))))
	    (indent-line-to val)))
	 (t
	  (goto-char here)
	  (let ((val))
	    (bsv-beg-of-statement-1)
	    (if (and (< (point) here)
		     (bsv-re-search-forward "=[ \\t]*" here 'move))
		(setq val (current-column))
	      (setq val (eval (cdr (assoc type bsv-indent-alist)))))
	    (goto-char here)
	    (indent-line-to val))))))

     (; handle inside parenthetical expressions
      (eq type 'cparenexp)
      (let* ( here
	      (val (save-excursion
		     (bsv-backward-up-list 1)
		     (forward-char 1)
             (if bsv-indent-lists
                 (skip-chars-forward " \t")
               (bsv-forward-syntactic-ws))
             (setq here (point))
             (current-column)))

	      (decl (save-excursion
		      (goto-char here)
		      (bsv-forward-syntactic-ws)
		      (setq here (point))
		      (looking-at bsv-declaration-re))))
        (indent-line-to val)
        (if decl
            (bsv-pretty-declarations))))

     (;-- Handle the ends
      (or
       (looking-at bsv-end-block-re )
       (bsv-at-close-constraint-p))
      (let ((val (if (eq type 'statement)
		     (- ind bsv-indent-level)
		   ind)))
	(indent-line-to val)))

     (;-- Case -- maybe line 'em up
      (and (eq type 'case) (not (looking-at "^[ \t]*$")))
      (progn
	(cond
	 ((looking-at "\\<endcase\\>")
	  (indent-line-to ind))
	 (t
	  (let ((val (eval (cdr (assoc type bsv-indent-alist)))))
	    (indent-line-to val))))))

     (;-- defun
      (and (eq type 'defun)
	   (looking-at bsv-zero-indent-re))
      (indent-line-to 0))

     (;-- declaration
      (and (or
	    (eq type 'defun)
	    (eq type 'block))
	   (looking-at bsv-declaration-re))
      (bsv-indent-declaration ind))

     (;-- Everything else
      t
      (let ((val (eval (cdr (assoc type bsv-indent-alist)))))
	(indent-line-to val))))

    (if (looking-at "[ \t]+$")
	(skip-chars-forward " \t"))
    indent-str				; Return indent data
    ))

(defun bsv-current-indent-level ()
  "Return the indent-level of the current statement."
  (save-excursion
    (let (par-pos)
      (beginning-of-line)
      (setq par-pos (bsv-parenthesis-depth))
      (while par-pos
	(goto-char par-pos)
	(beginning-of-line)
	(setq par-pos (bsv-parenthesis-depth)))
      (skip-chars-forward " \t")
      (current-column))))

(defun bsv-case-indent-level ()
  "Return the indent-level of the current statement.
Do not count named blocks or case-statements."
  (save-excursion
    (skip-chars-forward " \t")
    (cond
     ((looking-at bsv-named-block-re)
      (current-column))
     ((and (not (looking-at bsv-extended-case-re))
	   (looking-at "^[^:;]+[ \t]*:"))
      (bsv-re-search-forward ":" nil t)
      (skip-chars-forward " \t")
      (current-column))
     (t
      (current-column)))))

(defun bsv-indent-comment ()
  "Indent current line as comment."
  (let* ((stcol
	  (cond
	   ((bsv-in-star-comment-p)
	    (save-excursion
	      (re-search-backward "/\\*" nil t)
	      (1+(current-column))))
	   (comment-column
	     comment-column )
	   (t
	    (save-excursion
	      (re-search-backward "//" nil t)
	      (current-column))))))
    (indent-line-to stcol)
    stcol))

(defun bsv-more-comment ()
  "Make more comment lines like the previous."
  (let* ((star 0)
	 (stcol
	  (cond
	   ((bsv-in-star-comment-p)
	    (save-excursion
	      (setq star 1)
	      (re-search-backward "/\\*" nil t)
	      (1+(current-column))))
	   (comment-column
	    comment-column )
	   (t
	    (save-excursion
	      (re-search-backward "//" nil t)
	      (current-column))))))
    (progn
      (indent-to stcol)
      (if (and star
	       (save-excursion
		 (forward-line -1)
		 (skip-chars-forward " \t")
		 (looking-at "\*")))
	  (insert "* ")))))

(defun bsv-comment-indent (&optional arg)
  "Return the column number the line should be indented to.
ARG is ignored, for `comment-indent-function' compatibility."
  (cond
   ((bsv-in-star-comment-p)
    (save-excursion
      (re-search-backward "/\\*" nil t)
      (1+(current-column))))
   ( comment-column
     comment-column )
   (t
    (save-excursion
      (re-search-backward "//" nil t)
      (current-column)))))

;;

(defun bsv-pretty-declarations (&optional quiet)
  "Line up declarations around point.
Be verbose about progress unless optional QUIET set."
  (interactive)
  (let* ((m1 (make-marker))
         (e (point))
	 el
         r
	 (here (point))
         ind
         start
         startpos
         end
         endpos
         base-ind
         )
    (save-excursion
      (if (progn
;          (bsv-beg-of-statement-1)
          (beginning-of-line)
          (bsv-forward-syntactic-ws)
          (and (not (bsv-in-directive-p))    ;; could have `define input foo
               (looking-at bsv-declaration-re)))
	  (progn
	    (if (bsv-parenthesis-depth)
		;; in an argument list or parameter block
		(setq el (bsv-backward-up-list -1)
		      start (progn
			      (goto-char e)
			      (bsv-backward-up-list 1)
			      (forward-line) ;; ignore ( input foo,
			      (bsv-re-search-forward bsv-declaration-re el 'move)
			      (goto-char (match-beginning 0))
			      (skip-chars-backward " \t")
			      (point))
		      startpos (set-marker (make-marker) start)
		      end (progn
			    (goto-char start)
			    (bsv-backward-up-list -1)
			    (forward-char -1)
			    (bsv-backward-syntactic-ws)
			    (point))
		      endpos (set-marker (make-marker) end)
		      base-ind (progn
				 (goto-char start)
                 (forward-char 1)
                 (skip-chars-forward " \t")
                 (current-column))
		      )
	      ;; in a declaration block (not in argument list)
	      (setq
	       start (progn
		       (bsv-beg-of-statement-1)
		       (while (and (looking-at bsv-declaration-re)
				   (not (bobp)))
			 (skip-chars-backward " \t")
			 (setq e (point))
			 (beginning-of-line)
			 (bsv-backward-syntactic-ws)
			 (backward-char)
			 (bsv-beg-of-statement-1))
		       e)
	       startpos (set-marker (make-marker) start)
	       end (progn
		     (goto-char here)
		     (bsv-end-of-statement)
		     (setq e (point))	;Might be on last line
		     (bsv-forward-syntactic-ws)
		     (while (looking-at bsv-declaration-re)
		       (bsv-end-of-statement)
		       (setq e (point))
		       (bsv-forward-syntactic-ws))
		     e)
	       endpos (set-marker (make-marker) end)
	       base-ind (progn
			  (goto-char start)
			  (bsv-do-indent (bsv-calculate-indent))
			  (bsv-forward-ws&directives)
			  (current-column))))
	    ;; OK, start and end are set
	    (goto-char (marker-position startpos))
	    (if (and (not quiet)
		     (> (- end start) 100))
		(message "Lining up declarations..(please stand by)"))
	    ;; Get the beginning of line indent first
	    (while (progn (setq e (marker-position endpos))
			  (< (point) e))
	      (cond
	       ((save-excursion (skip-chars-backward " \t")
				(bolp))
		 (bsv-forward-ws&directives)
		 (indent-line-to base-ind)
		 (bsv-forward-ws&directives)
		 (if (< (point) e)
		     (bsv-re-search-forward "[ \t\n\f]" e 'move)))
	       (t
		(just-one-space)
		(bsv-re-search-forward "[ \t\n\f]" e 'move)))
	      ;;(forward-line)
	      )
	    ;; Now find biggest prefix
	    (setq ind (bsv-get-lineup-indent (marker-position startpos) endpos))
	    ;; Now indent each line.
	    (goto-char (marker-position startpos))
	    (while (progn (setq e (marker-position endpos))
			  (setq r (- e (point)))
			  (> r 0))
	      (setq e (point))
	      (unless quiet (message "%d" r))
          ;;(bsv-do-indent (bsv-calculate-indent)))
	      (bsv-forward-ws&directives)
	      (cond
	       ((or (and bsv-indent-declaration-macros
			 (looking-at bsv-declaration-re-2-macro))
		    (looking-at bsv-declaration-re-2-no-macro))
		(let ((p (match-end 0)))
		  (set-marker m1 p)
		  (if (bsv-re-search-forward "[[#`]" p 'move)
		      (progn
			(forward-char -1)
			(just-one-space)
			(goto-char (marker-position m1))
			(just-one-space)
			(indent-to ind))
		    (progn
		      (just-one-space)
		      (indent-to ind)))))
	       ((bsv-continued-line-1 (marker-position startpos))
		(goto-char e)
		(indent-line-to ind))
	       ((bsv-in-struct-p)
		;; could have a declaration of a user defined item
		(goto-char e)
		(bsv-end-of-statement))
	       (t		; Must be comment or white space
		(goto-char e)
		(bsv-forward-ws&directives)
		(forward-line -1)))
	      (forward-line 1))
	    (unless quiet (message "")))))))

(defun bsv-pretty-expr (&optional quiet myre)
  "Line up expressions around point, optionally QUIET with regexp MYRE ignored."
  (interactive)
  (if (not (bsv-in-comment-or-string-p))
      (save-excursion
	(let ((rexp (concat "^\\s-*" bsv-complete-reg)))
	  (beginning-of-line)
	  (if (and (not (looking-at rexp ))
		   (looking-at bsv-assignment-operation-re)
		   (save-excursion
		     (goto-char (match-end 2))
		     (and (not (bsv-in-attribute-p))
			  (not (bsv-in-parameter-p))
			  (not (bsv-in-comment-or-string-p)))))
	      (let* ((here (point))
		     (e) (r)
		     (start
		      (progn
			(beginning-of-line)
			(setq e (point))
			(bsv-backward-syntactic-ws)
			(beginning-of-line)
			(while (and (not (looking-at rexp ))
				    (looking-at bsv-assignment-operation-re)
				    (not (bobp))
				    )
			  (setq e (point))
			  (bsv-backward-syntactic-ws)
			  (beginning-of-line)
			  ) ;Ack, need to grok `define
			e))
		     (end
		      (progn
			(goto-char here)
			(end-of-line)
			(setq e (point))	;Might be on last line
			(bsv-forward-syntactic-ws)
			(beginning-of-line)
			(while (and
				(not (looking-at rexp ))
				(looking-at bsv-assignment-operation-re)
				(progn
				  (end-of-line)
				  (not (eq e (point)))))
			  (setq e (point))
			  (bsv-forward-syntactic-ws)
			  (beginning-of-line)
			  )
			e))
		     (endpos (set-marker (make-marker) end))
		     (ind)
		     )
		(goto-char start)
		(bsv-do-indent (bsv-calculate-indent))
		(if (and (not quiet)
			 (> (- end start) 100))
		    (message "Lining up expressions..(please stand by)"))

		;; Set indent to minimum throughout region
		(while (< (point) (marker-position endpos))
		  (beginning-of-line)
		  (bsv-just-one-space bsv-assignment-operation-re)
		  (beginning-of-line)
		  (bsv-do-indent (bsv-calculate-indent))
		  (end-of-line)
		  (bsv-forward-syntactic-ws)
		  )

		;; Now find biggest prefix
		(setq ind (bsv-get-lineup-indent-2 bsv-assignment-operation-re start endpos))

		;; Now indent each line.
		(goto-char start)
		(while (progn (setq e (marker-position endpos))
			      (setq r (- e (point)))
			      (> r 0))
		  (setq e (point))
		  (if (not quiet) (message "%d" r))
		  (cond
		   ((looking-at bsv-assignment-operation-re)
		    (goto-char (match-beginning 2))
		    (if (not (or (bsv-in-parenthesis-p) ;; leave attributes and comparisons alone
				 (bsv-in-coverage-p)))
			(if (eq (char-after) ?=)
			    (indent-to (1+ ind))	; line up the = of the <= with surrounding =
			  (indent-to ind)
			  ))
		    )
		   ((bsv-continued-line-1 start)
		    (goto-char e)
		    (indent-line-to ind))
		   (t		; Must be comment or white space
		    (goto-char e)
		    (bsv-forward-ws&directives)
		    (forward-line -1))
		   )
		  (forward-line 1))
		(unless quiet (message ""))
            ))))))

(defun bsv-just-one-space (myre)
  "Remove extra spaces around regular expression MYRE."
  (interactive)
  (if (and (not(looking-at bsv-complete-reg))
	   (looking-at myre))
      (let ((p1 (match-end 1))
	    (p2 (match-end 2)))
	(progn
	  (goto-char p2)
	  (just-one-space)
	  (goto-char p1)
	  (just-one-space)))))

(defun bsv-indent-declaration (baseind)
  "Indent current lines as declaration.
Line up the variable names based on previous declaration's indentation.
BASEIND is the base indent to offset everything."
  (interactive)
  (let ((pos (point-marker))
	(lim (save-excursion
	       ;; (bsv-re-search-backward bsv-declaration-opener nil 'move)
	       (bsv-re-search-backward "\\(\\<begin\\>\\)\\|\\(\\<module\\>\\)\\|\\(\\<task\\>\\)" nil 'move)
	       (point)))
	(ind)
	(val)
	(m1 (make-marker)))
    (setq val
	  (+ baseind (eval (cdr (assoc 'declaration bsv-indent-alist)))))
    (indent-line-to val)

    ;; Use previous declaration (in this module) as template.
    (if (or (eq 'all bsv-auto-lineup)
	    (eq 'declarations bsv-auto-lineup))
	(if (bsv-re-search-backward
	     (or (and bsv-indent-declaration-macros
		      bsv-declaration-re-1-macro)
		 bsv-declaration-re-1-no-macro) lim t)
	    (progn
	      (goto-char (match-end 0))
	      (skip-chars-forward " \t")
	      (setq ind (current-column))
	      (goto-char pos)
	      (setq val
		    (+ baseind
		       (eval (cdr (assoc 'declaration bsv-indent-alist)))))
	      (indent-line-to val)
	      (if (and bsv-indent-declaration-macros
		       (looking-at bsv-declaration-re-2-macro))
		  (let ((p (match-end 0)))
		    (set-marker m1 p)
		    (if (bsv-re-search-forward "[[#`]" p 'move)
			(progn
			  (forward-char -1)
			  (just-one-space)
			  (goto-char (marker-position m1))
			  (just-one-space)
			  (indent-to ind))
		      (if (/= (current-column) ind)
			  (progn
			    (just-one-space)
			    (indent-to ind)))))
		(if (looking-at bsv-declaration-re-2-no-macro)
		    (let ((p (match-end 0)))
		      (set-marker m1 p)
		      (if (bsv-re-search-forward "[[`#]" p 'move)
			  (progn
			    (forward-char -1)
			    (just-one-space)
			    (goto-char (marker-position m1))
			    (just-one-space)
			    (indent-to ind))
			(if (/= (current-column) ind)
			    (progn
			      (just-one-space)
			      (indent-to ind))))))))))
    (goto-char pos)))

(defun bsv-get-lineup-indent (b edpos)
  "Return the indent level that will line up several lines within the region.
Region is defined by B and EDPOS."
  (save-excursion
    (let ((ind 0) e)
      (goto-char b)
      ;; Get rightmost position
      (while (progn (setq e (marker-position edpos))
		    (< (point) e))
	(if (bsv-re-search-forward
	     (or (and bsv-indent-declaration-macros
		      bsv-declaration-re-1-macro)
		 bsv-declaration-re-1-no-macro) e 'move)
	    (progn
	      (goto-char (match-end 0))
	      (bsv-backward-syntactic-ws)
	      (if (> (current-column) ind)
		  (setq ind (current-column)))
	      (goto-char (match-end 0)))))
      (if (> ind 0)
	  (1+ ind)
	;; No lineup-string found
	(goto-char b)
	(end-of-line)
	(bsv-backward-syntactic-ws)
	;;(skip-chars-backward " \t")
	(1+ (current-column))))))

(defun bsv-get-lineup-indent-2 (myre b edpos)
  "Return the indent level that will line up several lines within the region."
  (save-excursion
    (let ((ind 0) e)
      (goto-char b)
      ;; Get rightmost position
      (while (progn (setq e (marker-position edpos))
		    (< (point) e))
	(if (and (bsv-re-search-forward myre e 'move)
		 (not (bsv-in-attribute-p))) ;; skip attribute exprs
	    (progn
	      (goto-char (match-beginning 2))
	      (bsv-backward-syntactic-ws)
	      (if (> (current-column) ind)
		  (setq ind (current-column)))
	      (goto-char (match-end 0)))
	  ))
      (if (> ind 0)
	  (1+ ind)
	;; No lineup-string found
	(goto-char b)
	(end-of-line)
	(skip-chars-backward " \t")
	(1+ (current-column))))))

(defun bsv-comment-depth (type val)
  "A useful mode debugging aide.  TYPE and VAL are comments for insertion."
  (save-excursion
    (let
	((b (prog2
		(beginning-of-line)
		(point-marker)
	      (end-of-line)))
	 (e (point-marker)))
      (if (re-search-backward " /\\* \[#-\]# \[a-zA-Z\]+ \[0-9\]+ ## \\*/" b t)
	  (progn
	    (replace-match " /* -#  ## */")
	    (end-of-line))
	(progn
	  (end-of-line)
	  (insert " /* ##  ## */"))))
    (backward-char 6)
    (insert
     (format "%s %d" type val))))

;; 
;;
;; Completion
;;
(defvar bsv-str nil)
(defvar bsv-all nil)
(defvar bsv-pred nil)
(defvar bsv-buffer-to-use nil)
(defvar bsv-flag nil)
(defvar bsv-toggle-completions nil
  "*True means \\<bsv-mode-map>\\[bsv-complete-word] should try all possible completions one by one.
Repeated use of \\[bsv-complete-word] will show you all of them.
Normally, when there is more than one possible completion,
it displays a list of all possible completions.")


(defvar bsv-type-keywords
  '(
    "and" "buf" "bufif0" "bufif1" "cmos" "defparam" "inout" "input"
    "integer" "localparam" "logic" "mailbox" "nand" "nmos" "nor" "not" "notif0"
    "notif1" "or" "output" "parameterx" "pmos" "pull0" "pull1" "pulldown" "pullup"
    "rcmos" "real" "realtime" "reg" "rnmos" "rpmos" "rtran" "rtranif0"
    "rtranif1" "semaphore" "time" "tran" "tranif0" "tranif1" "tri" "tri0" "tri1"
    "triand" "trior" "trireg" "wand" "wire" "wor" "xnor" "xor"
    )
  "*Keywords for types used when completing a word in a declaration or parmlist.
\(integer, real, reg...)")

(defvar bsv-cpp-keywords
  '("module" "macromodule" "primitive" "timescale" "define" "ifdef" "ifndef" "else"
    "endif")
  "*Keywords to complete when at first word of a line in declarative scope.
\(initial, always, begin, assign...)
The procedures and variables defined within the BSV program
will be completed at runtime and should not be added to this list.")

(defvar bsv-defun-keywords
  (append
   '(
     "always" "always_comb" "always_ff" "always_latch" "assign"
     "begin" "end" "generate" "endgenerate" "module" "endmodule"
     "specify" "endspecify" "function" "endfunction" "initial" "final"
     "task" "endtask" "primitive" "endprimitive"
     )
   bsv-type-keywords)
  "*Keywords to complete when at first word of a line in declarative scope.
\(initial, always, begin, assign...)
The procedures and variables defined within the BSV program
will be completed at runtime and should not be added to this list.")

(defvar bsv-block-keywords
  '(
    "begin" "break" "case" "continue" "else" "end" "endfunction"
    "endgenerate" "endinterface" "endpackage" "endspecify" "endtask"
    "for" "fork" "if" "join" "join_any" "join_none" "repeat" "return"
    "while")
  "*Keywords to complete when at first word of a line in behavioral scope.
\(begin, if, then, else, for, fork...)
The procedures and variables defined within the BSV program
will be completed at runtime and should not be added to this list.")

(defvar bsv-tf-keywords
  '("begin" "break" "fork" "join" "join_any" "join_none" "case" "end" "endtask" "endfunction" "if" "else" "for" "while" "repeat")
  "*Keywords to complete when at first word of a line in a task or function.
\(begin, if, then, else, for, fork.)
The procedures and variables defined within the BSV program
will be completed at runtime and should not be added to this list.")

(defvar bsv-case-keywords
  '("begin" "fork" "join" "join_any" "join_none" "case" "end" "endcase" "if" "else" "for" "repeat")
  "*Keywords to complete when at first word of a line in case scope.
\(begin, if, then, else, for, fork...)
The procedures and variables defined within the BSV program
will be completed at runtime and should not be added to this list.")

(defvar bsv-separator-keywords
  '("else" "then" "begin")
  "*Keywords to complete when NOT standing at the first word of a statement.
\(else, then, begin...)
Variables and function names defined within the BSV program
will be completed at runtime and should not be added to this list.")

(defvar bsv-gate-ios
  ;; All these have an implied {"input"...} at the end
  '(("and"	"output")
    ("buf"	"output")
    ("bufif0"	"output")
    ("bufif1"	"output")
    ("cmos"	"output")
    ("nand"	"output")
    ("nmos"	"output")
    ("nor"	"output")
    ("not"	"output")
    ("notif0"	"output")
    ("notif1"	"output")
    ("or"	"output")
    ("pmos"	"output")
    ("pulldown"	"output")
    ("pullup"	"output")
    ("rcmos"	"output")
    ("rnmos"	"output")
    ("rpmos"	"output")
    ("rtran"	"inout" "inout")
    ("rtranif0"	"inout" "inout")
    ("rtranif1"	"inout" "inout")
    ("tran"	"inout" "inout")
    ("tranif0"	"inout" "inout")
    ("tranif1"	"inout" "inout")
    ("xnor"	"output")
    ("xor"	"output"))
  "*Map of direction for each positional argument to each gate primitive.")

(defvar bsv-gate-keywords (mapcar `car bsv-gate-ios)
  "*Keywords for gate primitives.")

(defun bsv-string-diff (str1 str2)
  "Return index of first letter where STR1 and STR2 differs."
  (catch 'done
    (let ((diff 0))
      (while t
	(if (or (> (1+ diff) (length str1))
		(> (1+ diff) (length str2)))
	    (throw 'done diff))
	(or (equal (aref str1 diff) (aref str2 diff))
	    (throw 'done diff))
	(setq diff (1+ diff))))))

;; Calculate all possible completions for functions if argument is `function',
;; completions for procedures if argument is `procedure' or both functions and
;; procedures otherwise.

(defun bsv-func-completion (type)
  "Build regular expression for module/task/function names.
TYPE is 'module, 'tf for task or function, or t if unknown."
  (if (string= bsv-str "")
      (setq bsv-str "[a-zA-Z_]"))
  (let ((bsv-str (concat (cond
			     ((eq type 'module) "\\<\\(module\\)\\s +")
			     ((eq type 'tf) "\\<\\(task\\|function\\)\\s +")
			     (t "\\<\\(task\\|function\\|module\\)\\s +"))
			    "\\<\\(" bsv-str "[a-zA-Z0-9_.]*\\)\\>"))
	match)

    (if (not (looking-at bsv-defun-re))
	(bsv-re-search-backward bsv-defun-re nil t))
    (forward-char 1)

    ;; Search through all reachable functions
    (goto-char (point-min))
    (while (bsv-re-search-forward bsv-str (point-max) t)
      (progn (setq match (buffer-substring (match-beginning 2)
					   (match-end 2)))
	     (if (or (null bsv-pred)
		     (funcall bsv-pred match))
		 (setq bsv-all (cons match bsv-all)))))
    (if (match-beginning 0)
	(goto-char (match-beginning 0)))))

(defun bsv-get-completion-decl (end)
  "Macro for searching through current declaration (var, type or const)
for matches of `str' and adding the occurrence tp `all' through point END."
  (let ((re (or (and bsv-indent-declaration-macros
		     bsv-declaration-re-2-macro)
		bsv-declaration-re-2-no-macro))
	decl-end match)
    ;; Traverse lines
    (while (and (< (point) end)
		(bsv-re-search-forward re end t))
      ;; Traverse current line
      (setq decl-end (save-excursion (bsv-declaration-end)))
      (while (and (bsv-re-search-forward bsv-symbol-re decl-end t)
		  (not (match-end 1)))
	(setq match (buffer-substring (match-beginning 0) (match-end 0)))
	(if (string-match (concat "\\<" bsv-str) match)
	    (if (or (null bsv-pred)
		    (funcall bsv-pred match))
		(setq bsv-all (cons match bsv-all)))))
      (forward-line 1)))
  bsv-all)

(defun bsv-type-completion ()
  "Calculate all possible completions for types."
  (let ((start (point))
	goon)
    ;; Search for all reachable type declarations
    (while (or (bsv-beg-of-defun)
	       (setq goon (not goon)))
      (save-excursion
	(if (and (< start (prog1 (save-excursion (bsv-end-of-defun)
						 (point))
			    (forward-char 1)))
		 (bsv-re-search-forward
		  "\\<type\\>\\|\\<\\(begin\\|function\\|procedure\\)\\>"
		  start t)
		 (not (match-end 1)))
	    ;; Check current type declaration
	    (bsv-get-completion-decl start))))))

(defun bsv-var-completion ()
  "Calculate all possible completions for variables (or constants)."
  (let ((start (point)))
    ;; Search for all reachable var declarations
    (bsv-beg-of-defun)
    (save-excursion
      ;; Check var declarations
      (bsv-get-completion-decl start))))

(defun bsv-keyword-completion (keyword-list)
  "Give list of all possible completions of keywords in KEYWORD-LIST."
  (mapcar (lambda (s)
	    (if (string-match (concat "\\<" bsv-str) s)
		(if (or (null bsv-pred)
			(funcall bsv-pred s))
		    (setq bsv-all (cons s bsv-all)))))
	  keyword-list))


(defun bsv-completion (bsv-str bsv-pred bsv-flag)
  "Function passed to `completing-read', `try-completion' or `all-completions'.
Called to get completion on BSV-STR.  If BSV-PRED is non-nil, it
must be a function to be called for every match to check if this should
really be a match.  If BSV-FLAG is t, the function returns a list of
all possible completions.  If BSV-FLAG is nil it returns a string,
the longest possible completion, or t if BSV-STR is an exact match.
If BSV-FLAG is 'lambda, the function returns t if BSV-STR is an
exact match, nil otherwise."
  (save-excursion
    (let ((bsv-all nil))
      ;; Set buffer to use for searching labels. This should be set
      ;; within functions which use bsv-completions
      (set-buffer bsv-buffer-to-use)

      ;; Determine what should be completed
      (let ((state (car (bsv-calculate-indent))))
	(cond ((eq state 'defun)
	       (save-excursion (bsv-var-completion))
	       (bsv-func-completion 'module)
	       (bsv-keyword-completion bsv-defun-keywords))

	      ((eq state 'behavioral)
	       (save-excursion (bsv-var-completion))
	       (bsv-func-completion 'module)
	       (bsv-keyword-completion bsv-defun-keywords))

	      ((eq state 'block)
	       (save-excursion (bsv-var-completion))
	       (bsv-func-completion 'tf)
	       (bsv-keyword-completion bsv-block-keywords))

	      ((eq state 'case)
	       (save-excursion (bsv-var-completion))
	       (bsv-func-completion 'tf)
	       (bsv-keyword-completion bsv-case-keywords))

	      ((eq state 'tf)
	       (save-excursion (bsv-var-completion))
	       (bsv-func-completion 'tf)
	       (bsv-keyword-completion bsv-tf-keywords))

	      ((eq state 'cpp)
	       (save-excursion (bsv-var-completion))
	       (bsv-keyword-completion bsv-cpp-keywords))

	      ((eq state 'cparenexp)
	       (save-excursion (bsv-var-completion)))

	      (t;--Anywhere else
	       (save-excursion (bsv-var-completion))
	       (bsv-func-completion 'both)
	       (bsv-keyword-completion bsv-separator-keywords))))

      ;; Now we have built a list of all matches. Give response to caller
      (bsv-completion-response))))

(defun bsv-completion-response ()
  (cond ((or (equal bsv-flag 'lambda) (null bsv-flag))
	 ;; This was not called by all-completions
	 (if (null bsv-all)
	     ;; Return nil if there was no matching label
	     nil
	   ;; Get longest string common in the labels
	   (let* ((elm (cdr bsv-all))
		  (match (car bsv-all))
		  (min (length match))
		  tmp)
	     (if (string= match bsv-str)
		 ;; Return t if first match was an exact match
		 (setq match t)
	       (while (not (null elm))
		 ;; Find longest common string
		 (if (< (setq tmp (bsv-string-diff match (car elm))) min)
		     (progn
		       (setq min tmp)
		       (setq match (substring match 0 min))))
		 ;; Terminate with match=t if this is an exact match
		 (if (string= (car elm) bsv-str)
		     (progn
		       (setq match t)
		       (setq elm nil))
		   (setq elm (cdr elm)))))
	     ;; If this is a test just for exact match, return nil ot t
	     (if (and (equal bsv-flag 'lambda) (not (equal match 't)))
		 nil
	       match))))
	;; If flag is t, this was called by all-completions. Return
	;; list of all possible completions
	(bsv-flag
	 bsv-all)))

(defvar bsv-last-word-numb 0)
(defvar bsv-last-word-shown nil)
(defvar bsv-last-completions nil)

(defun bsv-complete-word ()
  "Complete word at current point.
\(See also `bsv-toggle-completions', `bsv-type-keywords',
and `bsv-separator-keywords'.)"
  (interactive)
  (let* ((b (save-excursion (skip-chars-backward "a-zA-Z0-9_") (point)))
	 (e (save-excursion (skip-chars-forward "a-zA-Z0-9_") (point)))
	 (bsv-str (buffer-substring b e))
	 ;; The following variable is used in bsv-completion
	 (bsv-buffer-to-use (current-buffer))
	 (allcomp (if (and bsv-toggle-completions
			   (string= bsv-last-word-shown bsv-str))
		      bsv-last-completions
		    (all-completions bsv-str 'bsv-completion)))
	 (match (if bsv-toggle-completions
		    "" (try-completion
			bsv-str (mapcar (lambda (elm)
					      (cons elm 0)) allcomp)))))
    ;; Delete old string
    (delete-region b e)

    ;; Toggle-completions inserts whole labels
    (if bsv-toggle-completions
	(progn
	  ;; Update entry number in list
	  (setq bsv-last-completions allcomp
		bsv-last-word-numb
		(if (>= bsv-last-word-numb (1- (length allcomp)))
		    0
		  (1+ bsv-last-word-numb)))
	  (setq bsv-last-word-shown (elt allcomp bsv-last-word-numb))
	  ;; Display next match or same string if no match was found
	  (if (not (null allcomp))
	      (insert "" bsv-last-word-shown)
	    (insert "" bsv-str)
	    (message "(No match)")))
      ;; The other form of completion does not necessarily do that.

      ;; Insert match if found, or the original string if no match
      (if (or (null match) (equal match 't))
	  (progn (insert "" bsv-str)
		 (message "(No match)"))
	(insert "" match))
      ;; Give message about current status of completion
      (cond ((equal match 't)
	     (if (not (null (cdr allcomp)))
		 (message "(Complete but not unique)")
	       (message "(Sole completion)")))
	    ;; Display buffer if the current completion didn't help
	    ;; on completing the label.
	    ((and (not (null (cdr allcomp))) (= (length bsv-str)
						(length match)))
	     (with-output-to-temp-buffer "*Completions*"
	       (display-completion-list allcomp))
	     ;; Wait for a key press. Then delete *Completion*  window
	     (momentary-string-display "" (point))
	     (delete-window (get-buffer-window (get-buffer "*Completions*")))
	     )))))

(defun bsv-show-completions ()
  "Show all possible completions at current point."
  (interactive)
  (let* ((b (save-excursion (skip-chars-backward "a-zA-Z0-9_") (point)))
	 (e (save-excursion (skip-chars-forward "a-zA-Z0-9_") (point)))
	 (bsv-str (buffer-substring b e))
	 ;; The following variable is used in bsv-completion
	 (bsv-buffer-to-use (current-buffer))
	 (allcomp (if (and bsv-toggle-completions
			   (string= bsv-last-word-shown bsv-str))
		      bsv-last-completions
		    (all-completions bsv-str 'bsv-completion))))
    ;; Show possible completions in a temporary buffer.
    (with-output-to-temp-buffer "*Completions*"
      (display-completion-list allcomp))
    ;; Wait for a key press. Then delete *Completion*  window
    (momentary-string-display "" (point))
    (delete-window (get-buffer-window (get-buffer "*Completions*")))))


(defun bsv-get-default-symbol ()
  "Return symbol around current point as a string."
  (save-excursion
    (buffer-substring (progn
			(skip-chars-backward " \t")
			(skip-chars-backward "a-zA-Z0-9_")
			(point))
		      (progn
			(skip-chars-forward "a-zA-Z0-9_")
			(point)))))

(defun bsv-build-defun-re (str &optional arg)
  "Return function/task/module starting with STR as regular expression.
With optional second ARG non-nil, STR is the complete name of the instruction."
  (if arg
      (concat "^\\(function\\|task\\|module\\)[ \t]+\\(" str "\\)\\>")
    (concat "^\\(function\\|task\\|module\\)[ \t]+\\(" str "[a-zA-Z0-9_]*\\)\\>")))

(defun bsv-comp-defun (bsv-str bsv-pred bsv-flag)
  "Function passed to `completing-read', `try-completion' or `all-completions'.
Returns a completion on any function name based on BSV-STR prefix.  If
BSV-PRED is non-nil, it must be a function to be called for every match
to check if this should really be a match.  If BSV-FLAG is t, the
function returns a list of all possible completions.  If it is nil it
returns a string, the longest possible completion, or t if BSV-STR is
an exact match.  If BSV-FLAG is 'lambda, the function returns t if
BSV-STR is an exact match, nil otherwise."
  (save-excursion
    (let ((bsv-all nil)
	  match)

      ;; Set buffer to use for searching labels. This should be set
      ;; within functions which use bsv-completions
      (set-buffer bsv-buffer-to-use)

      (let ((bsv-str bsv-str))
	;; Build regular expression for functions
	(if (string= bsv-str "")
	    (setq bsv-str (bsv-build-defun-re "[a-zA-Z_]"))
	  (setq bsv-str (bsv-build-defun-re bsv-str)))
	(goto-char (point-min))

	;; Build a list of all possible completions
	(while (bsv-re-search-forward bsv-str nil t)
	  (setq match (buffer-substring (match-beginning 2) (match-end 2)))
	  (if (or (null bsv-pred)
		  (funcall bsv-pred match))
	      (setq bsv-all (cons match bsv-all)))))

      ;; Now we have built a list of all matches. Give response to caller
      (bsv-completion-response))))

(defun bsv-goto-defun ()
  "Move to specified BSV module/interface/task/function.
The default is a name found in the buffer around point.
If search fails, other files are checked based on
`bsv-library-flags'."
  (interactive)
  (let* ((default (bsv-get-default-symbol))
	 ;; The following variable is used in bsv-comp-function
	 (bsv-buffer-to-use (current-buffer))
	 (label (if (not (string= default ""))
		    ;; Do completion with default
		    (completing-read (concat "Goto-Label: (default "
					     default ") ")
				     'bsv-comp-defun nil nil "")
		  ;; There is no default value. Complete without it
		  (completing-read "Goto-Label: "
				   'bsv-comp-defun nil nil "")))
	 pt)
    ;; Make sure library paths are correct, in case need to resolve module
    (bsv-auto-reeval-locals)
    (bsv-getopt-flags)
    ;; If there was no response on prompt, use default value
    (if (string= label "")
	(setq label default))
    ;; Goto right place in buffer if label is not an empty string
    (or (string= label "")
	(progn
	  (save-excursion
	    (goto-char (point-min))
	    (setq pt
		  (re-search-forward (bsv-build-defun-re label t) nil t)))
	  (when pt
	    (goto-char pt)
	    (beginning-of-line))
	  pt)
	(bsv-goto-defun-file label))))

;; Eliminate compile warning
(defvar occur-pos-list)

(defun bsv-showscopes ()
  "List all scopes in this module."
  (interactive)
  (let ((buffer (current-buffer))
	(linenum 1)
	(nlines 0)
	(first 1)
	(prevpos (point-min))
        (final-context-start (make-marker))
	(regexp "\\(module\\s-+\\w+\\s-*(\\)\\|\\(\\w+\\s-+\\w+\\s-*(\\)"))
    (with-output-to-temp-buffer "*Occur*"
      (save-excursion
	(message (format "Searching for %s ..." regexp))
	;; Find next match, but give up if prev match was at end of buffer.
	(while (and (not (= prevpos (point-max)))
		    (bsv-re-search-forward regexp nil t))
	  (goto-char (match-beginning 0))
	  (beginning-of-line)
	  (save-match-data
            (setq linenum (+ linenum (count-lines prevpos (point)))))
	  (setq prevpos (point))
	  (goto-char (match-end 0))
	  (let* ((start (save-excursion
			  (goto-char (match-beginning 0))
			  (forward-line (if (< nlines 0) nlines (- nlines)))
			  (point)))
		 (end (save-excursion
			(goto-char (match-end 0))
			(if (> nlines 0)
			    (forward-line (1+ nlines))
			    (forward-line 1))
			(point)))
		 (tag (format "%3d" linenum))
		 (empty (make-string (length tag) ?\ ))
		 tem)
	    (save-excursion
	      (setq tem (make-marker))
	      (set-marker tem (point))
	      (set-buffer standard-output)
	      (setq occur-pos-list (cons tem occur-pos-list))
	      (or first (zerop nlines)
		  (insert "--------\n"))
	      (setq first nil)
	      (insert-buffer-substring buffer start end)
	      (backward-char (- end start))
	      (setq tem (if (< nlines 0) (- nlines) nlines))
	      (while (> tem 0)
		(insert empty ?:)
		(forward-line 1)
		(setq tem (1- tem)))
	      (let ((this-linenum linenum))
		(set-marker final-context-start
			    (+ (point) (- (match-end 0) (match-beginning 0))))
		(while (< (point) final-context-start)
		  (if (null tag)
		      (setq tag (format "%3d" this-linenum)))
		  (insert tag ?:)))))))
      (set-buffer-modified-p nil))))


;; Highlight helper functions
(defconst bsv-directive-regexp "\\(translate\\|coverage\\|lint\\)_")
(defun bsv-within-translate-off ()
  "Return point if within translate-off region, else nil."
  (and (save-excursion
	 (re-search-backward
	  (concat "//\\s-*.*\\s-*" bsv-directive-regexp "\\(on\\|off\\)\\>")
	  nil t))
       (equal "off" (match-string 2))
       (point)))

(defun bsv-start-translate-off (limit)
  "Return point before translate-off directive if before LIMIT, else nil."
  (when (re-search-forward
	  (concat "//\\s-*.*\\s-*" bsv-directive-regexp "off\\>")
	  limit t)
    (match-beginning 0)))

(defun bsv-back-to-start-translate-off (limit)
  "Return point before translate-off directive if before LIMIT, else nil."
  (when (re-search-backward
	  (concat "//\\s-*.*\\s-*" bsv-directive-regexp "off\\>")
	  limit t)
    (match-beginning 0)))

(defun bsv-end-translate-off (limit)
  "Return point after translate-on directive if before LIMIT, else nil."

  (re-search-forward (concat
		      "//\\s-*.*\\s-*" bsv-directive-regexp "on\\>") limit t))

(defun bsv-match-translate-off (limit)
  "Match a translate-off block, setting `match-data' and returning t, else nil.
Bound search by LIMIT."
  (when (< (point) limit)
    (let ((start (or (bsv-within-translate-off)
		     (bsv-start-translate-off limit)))
	  (case-fold-search t))
      (when start
	(let ((end (or (bsv-end-translate-off limit) limit)))
	  (set-match-data (list start end))
	  (goto-char end))))))

(defun bsv-font-lock-match-item (limit)
  "Match, and move over, any declaration item after point.
Bound search by LIMIT.  Adapted from
`font-lock-match-c-style-declaration-item-and-skip-to-next'."
  (condition-case nil
      (save-restriction
	(narrow-to-region (point-min) limit)
	;; match item
	(when (looking-at "\\s-*\\([a-zA-Z]\\w*\\)")
	  (save-match-data
	    (goto-char (match-end 1))
	    ;; move to next item
	    (if (looking-at "\\(\\s-*,\\)")
		(goto-char (match-end 1))
	      (end-of-line) t))))
    (error nil)))


;; Added by Subbu Meiyappan for Header

(defun bsv-header ()
  "Insert a standard BSV file header.
See also `bsv-sk-header' for an alternative format."
  (interactive)
  (let ((start (point)))
  (insert "\
//-----------------------------------------------------------------------------
// Title         : <title>
// Project       : <project>
//-----------------------------------------------------------------------------
// File          : <filename>
// Author        : <author>
// Created       : <credate>
// Last modified : <moddate>
//-----------------------------------------------------------------------------
// Description :
// <description>
//-----------------------------------------------------------------------------
// Copyright (c) <copydate> by <company> This model is the confidential and
// proprietary property of <company> and the possession or use of this
// file requires a written license from <company>.
//------------------------------------------------------------------------------
// Modification history :
// <modhist>
//-----------------------------------------------------------------------------

")
    (goto-char start)
    (search-forward "<filename>")
    (replace-match (buffer-name) t t)
    (search-forward "<author>") (replace-match "" t t)
    (insert (user-full-name))
    (insert "  <" (user-login-name) "@" (system-name) ">")
    (search-forward "<credate>") (replace-match "" t t)
    (bsv-insert-date)
    (search-forward "<moddate>") (replace-match "" t t)
    (bsv-insert-date)
    (search-forward "<copydate>") (replace-match "" t t)
    (bsv-insert-year)
    (search-forward "<modhist>") (replace-match "" t t)
    (bsv-insert-date)
    (insert " : created")
    (goto-char start)
    (let (string)
      (setq string (read-string "title: "))
      (search-forward "<title>")
      (replace-match string t t)
      (setq string (read-string "project: " bsv-project))
      (setq bsv-project string)
      (search-forward "<project>")
      (replace-match string t t)
      (setq string (read-string "Company: " bsv-company))
      (setq bsv-company string)
      (search-forward "<company>")
      (replace-match string t t)
      (search-forward "<company>")
      (replace-match string t t)
      (search-forward "<company>")
      (replace-match string t t)
      (search-backward "<description>")
      (replace-match "" t t))))

;; bsv-header Uses the bsv-insert-date function

(defun bsv-insert-date ()
  "Insert date from the system."
  (interactive)
  (if bsv-date-scientific-format
      (insert (format-time-string "%Y/%m/%d"))
    (insert (format-time-string "%d.%m.%Y"))))

(defun bsv-insert-year ()
  "Insert year from the system."
  (interactive)
  (insert (format-time-string "%Y")))


;;
;; Signal list parsing
;;

;; Elements of a signal list
(defsubst bsv-sig-new (name bits comment mem enum signed type multidim modport)
  (list name bits comment mem enum signed type multidim modport))
(defsubst bsv-sig-name (sig)
  (car sig))
(defsubst bsv-sig-bits (sig)
  (nth 1 sig))
(defsubst bsv-sig-comment (sig)
  (nth 2 sig))
(defsubst bsv-sig-memory (sig)
  (nth 3 sig))
(defsubst bsv-sig-enum (sig)
  (nth 4 sig))
(defsubst bsv-sig-signed (sig)
  (nth 5 sig))
(defsubst bsv-sig-type (sig)
  (nth 6 sig))
(defsubst bsv-sig-multidim (sig)
  (nth 7 sig))
(defsubst bsv-sig-multidim-string (sig)
  (if (bsv-sig-multidim sig)
      (let ((str "") (args (bsv-sig-multidim sig)))
	(while args
	  (setq str (concat str (car args)))
	  (setq args (cdr args)))
	str)))
(defsubst bsv-sig-modport (sig)
  (nth 8 sig))
(defsubst bsv-sig-width (sig)
  (bsv-make-width-expression (bsv-sig-bits sig)))

(defsubst bsv-alw-new (outputs-del outputs-imm temps inputs)
  (list outputs-del outputs-imm temps inputs))
(defsubst bsv-alw-get-outputs-delayed (sigs)
  (nth 0 sigs))
(defsubst bsv-alw-get-outputs-immediate (sigs)
  (nth 1 sigs))
(defsubst bsv-alw-get-temps (sigs)
  (nth 2 sigs))
(defsubst bsv-alw-get-inputs (sigs)
  (nth 3 sigs))
(defsubst bsv-alw-get-uses-delayed (sigs)
  (nth 0 sigs))

(defsubst bsv-modi-new (name fob pt type)
  (vector name fob pt type))
(defsubst bsv-modi-name (modi)
  (aref modi 0))
(defsubst bsv-modi-file-or-buffer (modi)
  (aref modi 1))
(defsubst bsv-modi-get-point (modi)
  (aref modi 2))
(defsubst bsv-modi-get-type (modi) ;; "module" or "interface"
  (aref modi 3))
(defsubst bsv-modi-get-decls (modi)
  (bsv-modi-cache-results modi 'bsv-read-decls))
(defsubst bsv-modi-get-sub-decls (modi)
  (bsv-modi-cache-results modi 'bsv-read-sub-decls))

;; Signal reading for given module
;; Note these all take modi's - as returned from bsv-modi-current
(defsubst bsv-decls-new (out inout in vars unuseds assigns consts gparams interfaces)
  (vector out inout in vars unuseds assigns consts gparams interfaces))
(defsubst bsv-decls-get-outputs (decls)
  (aref decls 0))
(defsubst bsv-decls-get-inouts (decls)
  (aref decls 1))
(defsubst bsv-decls-get-inputs (decls)
  (aref decls 2))
(defsubst bsv-decls-get-vars (decls)
  (aref decls 3))
;;(defsubst bsv-decls-get-unused (decls)
;;  (aref decls 4))
(defsubst bsv-decls-get-assigns (decls)
  (aref decls 5))
(defsubst bsv-decls-get-consts (decls)
  (aref decls 6))
(defsubst bsv-decls-get-gparams (decls)
  (aref decls 7))
(defsubst bsv-decls-get-interfaces (decls)
  (aref decls 8))

(defsubst bsv-subdecls-new (out inout in intf intfd)
  (vector out inout in intf intfd))
(defsubst bsv-subdecls-get-outputs (subdecls)
  (aref subdecls 0))
(defsubst bsv-subdecls-get-inouts (subdecls)
  (aref subdecls 1))
(defsubst bsv-subdecls-get-inputs (subdecls)
  (aref subdecls 2))
(defsubst bsv-subdecls-get-interfaces (subdecls)
  (aref subdecls 3))
(defsubst bsv-subdecls-get-interfaced (subdecls)
  (aref subdecls 4))

(defun bsv-signals-not-in (in-list not-list)
  "Return list of signals in IN-LIST that aren't also in NOT-LIST.
Also remove any duplicates in IN-LIST.
Signals must be in standard (base vector) form."
  ;; This function is hot, so implemented as O(1)
  (cond ((eval-when-compile (fboundp 'make-hash-table))
	 (let ((ht (make-hash-table :test 'equal :rehash-size 4.0))
	       out-list)
	   (while not-list
	     (puthash (car (car not-list)) t ht)
	     (setq not-list (cdr not-list)))
	   (while in-list
	     (when (not (gethash (car (car in-list)) ht))
	       (setq out-list (cons (car in-list) out-list))
	       (puthash (car (car in-list)) t ht))
	     (setq in-list (cdr in-list)))
	   (nreverse out-list)))
	;; Slower Fallback if no hash tables (pre Emacs 21.1/XEmacs 21.4)
	(t
	 (let (out-list)
	   (while in-list
	     (if (not (or (assoc (car (car in-list)) not-list)
			  (assoc (car (car in-list)) out-list)))
		 (setq out-list (cons (car in-list) out-list)))
	     (setq in-list (cdr in-list)))
	   (nreverse out-list)))))
;;(bsv-signals-not-in '(("A" "") ("B" "") ("DEL" "[2:3]")) '(("DEL" "") ("EXT" "")))

(defun bsv-signals-memory (in-list)
  "Return list of signals in IN-LIST that are memorized (multidimensional)."
  (let (out-list)
    (while in-list
      (if (nth 3 (car in-list))
	  (setq out-list (cons (car in-list) out-list)))
      (setq in-list (cdr in-list)))
    out-list))
;;(bsv-signals-memory '(("A" nil nil "[3:0]")) '(("B" nil nil nil)))

(defun bsv-signals-sort-compare (a b)
  "Compare signal A and B for sorting."
  (string< (car a) (car b)))

(defun bsv-signals-not-params (in-list)
  "Return list of signals in IN-LIST that aren't parameters or numeric constants."
  (let (out-list)
    (while in-list
      (unless (boundp (intern (concat "vh-" (car (car in-list)))))
	(setq out-list (cons (car in-list) out-list)))
      (setq in-list (cdr in-list)))
    (nreverse out-list)))

(defun bsv-signals-combine-bus (in-list)
  "Return a list of signals in IN-LIST, with buses combined.
Duplicate signals are also removed.  For example A[2] and A[1] become A[2:1]."
  (let (combo buswarn
	out-list
	sig highbit lowbit		; Temp information about current signal
	sv-name sv-highbit sv-lowbit	; Details about signal we are forming
	sv-comment sv-memory sv-enum sv-signed sv-type sv-multidim sv-busstring
	sv-modport
	bus)
    ;; Shove signals so duplicated signals will be adjacent
    (setq in-list (sort in-list `bsv-signals-sort-compare))
    (while in-list
      (setq sig (car in-list))
      ;; No current signal; form from existing details
      (unless sv-name
	(setq sv-name    (bsv-sig-name sig)
	      sv-highbit nil
	      sv-busstring nil
	      sv-comment (bsv-sig-comment sig)
	      sv-memory  (bsv-sig-memory sig)
	      sv-enum    (bsv-sig-enum sig)
	      sv-signed  (bsv-sig-signed sig)
	      sv-type    (bsv-sig-type sig)
	      sv-multidim (bsv-sig-multidim sig)
	      sv-modport  (bsv-sig-modport sig)
	      combo ""
	      buswarn ""))
      ;; Extract bus details
      (setq bus (bsv-sig-bits sig))
      (setq bus (and bus (bsv-simplify-range-expression bus)))
      (cond ((and bus
		  (or (and (string-match "\\[\\([0-9]+\\):\\([0-9]+\\)\\]" bus)
			   (setq highbit (string-to-number (match-string 1 bus))
				 lowbit  (string-to-number
					  (match-string 2 bus))))
		      (and (string-match "\\[\\([0-9]+\\)\\]" bus)
			   (setq highbit (string-to-number (match-string 1 bus))
				 lowbit  highbit))))
	     ;; Combine bits in bus
	     (if sv-highbit
		 (setq sv-highbit (max highbit sv-highbit)
		       sv-lowbit  (min lowbit  sv-lowbit))
	       (setq sv-highbit highbit
		     sv-lowbit  lowbit)))
	    (bus
	     ;; String, probably something like `preproc:0
	     (setq sv-busstring bus)))
      ;; Peek ahead to next signal
      (setq in-list (cdr in-list))
      (setq sig (car in-list))
      (cond ((and sig (equal sv-name (bsv-sig-name sig)))
	     ;; Combine with this signal
	     (when (and sv-busstring
			(not (equal sv-busstring (bsv-sig-bits sig))))
	       (when nil  ;; Debugging
		 (message (concat "Warning, can't merge into single bus "
				  sv-name bus
				  ", the AUTOs may be wrong")))
	       (setq buswarn ", Couldn't Merge"))
	     (if (bsv-sig-comment sig) (setq combo ", ..."))
	     (setq sv-memory (or sv-memory (bsv-sig-memory sig))
		   sv-enum   (or sv-enum   (bsv-sig-enum sig))
		   sv-signed (or sv-signed (bsv-sig-signed sig))
                   sv-type   (or sv-type   (bsv-sig-type sig))
                   sv-multidim (or sv-multidim (bsv-sig-multidim sig))
                   sv-modport  (or sv-modport  (bsv-sig-modport sig))))
	    ;; Doesn't match next signal, add to queue, zero in prep for next
	    ;; Note sig may also be nil for the last signal in the list
	    (t
	     (setq out-list
		   (cons (bsv-sig-new
			  sv-name
			  (or sv-busstring
			      (if sv-highbit
				  (concat "[" (int-to-string sv-highbit) ":"
					  (int-to-string sv-lowbit) "]")))
			  (concat sv-comment combo buswarn)
			  sv-memory sv-enum sv-signed sv-type sv-multidim sv-modport)
			 out-list)
		   sv-name nil))))
    ;;
    out-list))

(defun bsv-sig-tieoff (sig &optional no-width)
  "Return tieoff expression for given SIG, with appropriate width.
Ignore width if optional NO-WIDTH is set."
  (let* ((width (if no-width nil (bsv-sig-width sig))))
    (concat
     (if (and bsv-active-low-regexp
	      (string-match bsv-active-low-regexp (bsv-sig-name sig)))
	 "~" "")
     (cond ((not width)
	    "0")
	   ((string-match "^[0-9]+$" width)
	    (concat width (if (bsv-sig-signed sig) "'sh0" "'h0")))
	   (t
	    (concat "{" width "{1'b0}}"))))))

;;
;; Port/Wire/Etc Reading
;;

(defun bsv-read-inst-backward-name ()
  "Internal.  Move point back to beginning of inst-name."
    (bsv-backward-open-paren)
    (let (done)
      (while (not done)
	(bsv-re-search-backward-quick "\\()\\|\\b[a-zA-Z0-9`_\$]\\|\\]\\)" nil nil)  ; ] isn't word boundary
	(cond ((looking-at ")")
	       (bsv-backward-open-paren))
	      (t (setq done t)))))
    (while (looking-at "\\]")
      (bsv-backward-open-bracket)
      (bsv-re-search-backward-quick "\\(\\b[a-zA-Z0-9`_\$]\\|\\]\\)" nil nil))
    (skip-chars-backward "a-zA-Z0-9`_$"))

(defun bsv-read-inst-module-matcher ()
  "Set match data 0 with module_name when point is inside instantiation."
  (bsv-read-inst-backward-name)
  ;; Skip over instantiation name
  (bsv-re-search-backward-quick "\\(\\b[a-zA-Z0-9`_\$]\\|)\\)" nil nil)  ; ) isn't word boundary
  ;; Check for parameterized instantiations
  (when (looking-at ")")
    (bsv-backward-open-paren)
    (bsv-re-search-backward-quick "\\b[a-zA-Z0-9`_\$]" nil nil))
  (skip-chars-backward "a-zA-Z0-9'_$")
  (looking-at "[a-zA-Z0-9`_\$]+")
  ;; Important: don't use match string, this must work with Emacs 19 font-lock on
  (buffer-substring-no-properties (match-beginning 0) (match-end 0))
  ;; Caller assumes match-beginning/match-end is still set
  )

(defun bsv-read-inst-module ()
  "Return module_name when point is inside instantiation."
  (save-excursion
    (bsv-read-inst-module-matcher)))

(defun bsv-read-inst-name ()
  "Return instance_name when point is inside instantiation."
  (save-excursion
    (bsv-read-inst-backward-name)
    (looking-at "[a-zA-Z0-9`_\$]+")
    ;; Important: don't use match string, this must work with Emacs 19 font-lock on
    (buffer-substring-no-properties (match-beginning 0) (match-end 0))))

(defun bsv-read-module-name ()
  "Return module name when after its ( or ;."
  (save-excursion
    (re-search-backward "[(;]")
    ;; Due to "module x import y (" we must search for declaration begin
    (bsv-re-search-backward-quick bsv-defun-re nil nil)
    (goto-char (match-end 0))
    (bsv-re-search-forward-quick "\\b[a-zA-Z0-9`_\$]+" nil nil)
    ;; Important: don't use match string, this must work with Emacs 19 font-lock on
    (bsv-symbol-detick
     (buffer-substring-no-properties (match-beginning 0) (match-end 0)) t)))

(defun bsv-read-inst-param-value ()
  "Return list of parameters and values when point is inside instantiation."
  (save-excursion
    (bsv-read-inst-backward-name)
    ;; Skip over instantiation name
    (bsv-re-search-backward-quick "\\(\\b[a-zA-Z0-9`_\$]\\|)\\)" nil nil)  ; ) isn't word boundary
    ;; If there are parameterized instantiations
    (when (looking-at ")")
      (let ((end-pt (point))
	    params
	    param-name paren-beg-pt param-value)
	(bsv-backward-open-paren)
	(while (bsv-re-search-forward-quick "\\." end-pt t)
	  (bsv-re-search-forward-quick "\\([a-zA-Z0-9`_\$]\\)" nil nil)
	  (skip-chars-backward "a-zA-Z0-9'_$")
	  (looking-at "[a-zA-Z0-9`_\$]+")
	  (setq param-name (buffer-substring-no-properties
			    (match-beginning 0) (match-end 0)))
	  (bsv-re-search-forward-quick "(" nil nil)
	  (setq paren-beg-pt (point))
	  (bsv-forward-close-paren)
	  (setq param-value (bsv-string-remove-spaces
			     (buffer-substring-no-properties
			      paren-beg-pt (1- (point)))))
	  (setq params (cons (list param-name param-value) params)))
	params))))

(defun bsv-read-auto-params (num-param &optional max-param)
  "Return parameter list inside auto.
Optional NUM-PARAM and MAX-PARAM check for a specific number of parameters."
  (let ((olist))
    (save-excursion
      ;; /*AUTOPUNT("parameter", "parameter")*/
      (search-backward "(")
      (while (looking-at "(?\\s *\"\\([^\"]*\\)\"\\s *,?")
	(setq olist (cons (match-string 1) olist))
	(goto-char (match-end 0))))
    (or (eq nil num-param)
	(<= num-param (length olist))
	(error "%s: Expected %d parameters" (bsv-point-text) num-param))
    (if (eq max-param nil) (setq max-param num-param))
    (or (eq nil max-param)
	(>= max-param (length olist))
	(error "%s: Expected <= %d parameters" (bsv-point-text) max-param))
    (nreverse olist)))

(defun bsv-read-decls ()
  "Compute signal declaration information for the current module at point.
Return a array of [outputs inouts inputs wire reg assign const]."
  (let ((end-mod-point (or (bsv-get-end-of-defun t) (point-max)))
	(functask 0) (paren 0) (sig-paren 0) (v2kargs-ok t)
	in-modport ign-prop
	sigs-in sigs-out sigs-inout sigs-var sigs-assign sigs-const
	sigs-gparam sigs-intf
	vec expect-signal keywd newsig rvalue enum io signed typedefed multidim
	modport)
    (save-excursion
      (bsv-beg-of-defun-quick)
      (setq sigs-const (bsv-read-auto-constants (point) end-mod-point))
      (while (< (point) end-mod-point)
	;;(if dbg (setq dbg (concat dbg (format "Pt %s  Vec %s   C%c Kwd'%s'\n" (point) vec (following-char) keywd))))
	(cond
	 ((looking-at "//")
	  (if (looking-at "[^\n]*synopsys\\s +enum\\s +\\([a-zA-Z0-9_]+\\)")
	      (setq enum (match-string 1)))
	  (search-forward "\n"))
	 ((looking-at "/\\*")
	  (forward-char 2)
	  (if (looking-at "[^\n]*synopsys\\s +enum\\s +\\([a-zA-Z0-9_]+\\)")
	      (setq enum (match-string 1)))
	  (or (search-forward "*/")
	      (error "%s: Unmatched /* */, at char %d" (bsv-point-text) (point))))
	 ((looking-at "(\\*")
	  ;; To advance past either "(*)" or "(* ... *)" don't forward past first *
	  (forward-char 1)
	  (or (search-forward "*)")
	      (error "%s: Unmatched (* *), at char %d" (bsv-point-text) (point))))
	 ((eq ?\" (following-char))
	  (or (re-search-forward "[^\\]\"" nil t)	;; don't forward-char first, since we look for a non backslash first
	      (error "%s: Unmatched quotes, at char %d" (bsv-point-text) (point))))
	 ((eq ?\; (following-char))
	  (setq vec nil  io nil  expect-signal nil  newsig nil  paren 0  rvalue nil
		v2kargs-ok nil  in-modport nil  ign-prop nil)
	  (forward-char 1))
	 ((eq ?= (following-char))
	  (setq rvalue t  newsig nil)
	  (forward-char 1))
	 ((and (eq ?, (following-char))
	       (eq paren sig-paren))
	  (setq rvalue nil)
	  (forward-char 1))
	 ;; ,'s can occur inside {} & funcs
	 ((looking-at "[{(]")
	  (setq paren (1+ paren))
	  (forward-char 1))
	 ((looking-at "[})]")
	  (setq paren (1- paren))
	  (forward-char 1)
	  (when (< paren sig-paren)
	    (setq expect-signal nil)))   ; ) that ends variables inside v2k arg list
	 ((looking-at "\\s-*\\(\\[[^]]+\\]\\)")
	  (goto-char (match-end 0))
	  (cond (newsig	; Memory, not just width.  Patch last signal added's memory (nth 3)
		 (setcar (cdr (cdr (cdr newsig)))
			 (if (bsv-sig-memory newsig)
			     (concat (bsv-sig-memory newsig) (match-string 1))
			   (match-string 1))))
		(vec ;; Multidimensional
		 (setq multidim (cons vec multidim))
		 (setq vec (bsv-string-replace-matches
			    "\\s-+" "" nil nil (match-string 1))))
		(t ;; Bit width
		 (setq vec (bsv-string-replace-matches
			    "\\s-+" "" nil nil (match-string 1))))))
	 ;; Normal or escaped identifier -- note we remember the \ if escaped
	 ((looking-at "\\s-*\\([a-zA-Z0-9`_$]+\\|\\\\[^ \t\n\f]+\\)")
	  (goto-char (match-end 0))
	  (setq keywd (match-string 1))
	  (when (string-match "^\\\\" (match-string 1))
	    (setq keywd (concat keywd " ")))  ;; Escaped ID needs space at end
	  ;; Add any :: package names to same identifier
	  (while (looking-at "\\s-*::\\s-*\\([a-zA-Z0-9`_$]+\\|\\\\[^ \t\n\f]+\\)")
	    (goto-char (match-end 0))
	    (setq keywd (concat keywd "::" (match-string 1)))
	    (when (string-match "^\\\\" (match-string 1))
	      (setq keywd (concat keywd " "))))  ;; Escaped ID needs space at end
	  (cond ((equal keywd "input")
		 (setq vec nil enum nil  rvalue nil  newsig nil  signed nil  typedefed nil  multidim nil  sig-paren paren
		       expect-signal 'sigs-in  io t  modport nil))
		((equal keywd "output")
		 (setq vec nil enum nil  rvalue nil  newsig nil  signed nil  typedefed nil  multidim nil  sig-paren paren
		       expect-signal 'sigs-out  io t  modport nil))
		((equal keywd "inout")
		 (setq vec nil enum nil  rvalue nil  newsig nil  signed nil  typedefed nil  multidim nil  sig-paren paren
		       expect-signal 'sigs-inout  io t  modport nil))
		((equal keywd "parameter")
		 (setq vec nil  enum nil  rvalue nil  signed nil  typedefed nil  multidim nil  sig-paren paren
		       expect-signal 'sigs-gparam  io t  modport nil))
		((member keywd '("wire"
				 "tri" "tri0" "tri1" "triand" "trior" "wand" "wor"
				 "reg" "trireg"
				 "byte" "shortint" "int" "longint" "integer" "time"
				 "bit" "logic"
				 "shortreal" "real" "realtime"
				 "string" "event" "chandle"))
		 (unless io (setq vec nil  enum nil  rvalue nil  signed nil  typedefed nil  multidim nil  sig-paren paren
				  expect-signal 'sigs-var  modport nil)))
		((equal keywd "assign")
		 (setq vec nil  enum nil  rvalue nil  signed nil  typedefed nil  multidim nil  sig-paren paren
		       expect-signal 'sigs-assign  modport nil))
		((member keywd '("supply0" "supply1" "supply"
				 "localparam" "genvar"))
		 (unless io (setq vec nil  enum nil  rvalue nil  signed nil  typedefed nil  multidim nil  sig-paren paren
				  expect-signal 'sigs-const  modport nil)))
		((member keywd '("signed" "unsigned"))
		 (setq signed keywd))
		((member keywd '("assert" "assume" "cover" "expect" "restrict"))
		 (setq ign-prop t))
		((member keywd '("class" "clocking" "covergroup" "function"
				 "property" "randsequence" "sequence" "task"))
		 (unless ign-prop
		   (setq functask (1+ functask))))
		((member keywd '("endclass" "endclocking" "endgroup" "endfunction"
				 "endproperty" "endsequence" "endtask"))
		 (setq functask (1- functask)))
		((equal keywd "modport")
		 (setq in-modport t))
		;; Ifdef?  Ignore name of define
		((member keywd '("`ifdef" "`ifndef" "`elsif"))
		 (setq rvalue t))
		;; Type?
		((bsv-typedef-name-p keywd)
		 (setq typedefed keywd))
		;; Interface with optional modport in v2k arglist?
		;; Skip over parsing modport, and take the interface name as the type
		((and v2kargs-ok
		      (eq paren 1)
		      (not rvalue)
		      (looking-at "\\s-*\\(\\.\\(\\s-*[a-zA-Z`_$][a-zA-Z0-9`_$]*\\)\\|\\)\\s-*[a-zA-Z`_$][a-zA-Z0-9`_$]*"))
		 (when (match-end 2) (goto-char (match-end 2)))
		 (setq vec nil enum nil  rvalue nil  newsig nil  signed nil  typedefed keywd  multidim nil  sig-paren paren
		       expect-signal 'sigs-intf  io t  modport (match-string 2)))
		;; Ignore dotted LHS assignments: "assign foo.bar = z;"
		((looking-at "\\s-*\\.")
		 (goto-char (match-end 0))
		 (when (not rvalue)
		   (setq expect-signal nil)))
		;; New signal, maybe?
		((and expect-signal
		      (not rvalue)
		      (eq functask 0)
		      (not in-modport)
		      (not (member keywd bsv-keywords)))
		 ;; Add new signal to expect-signal's variable
		 (setq newsig (bsv-sig-new keywd vec nil nil enum signed typedefed multidim modport))
		 (set expect-signal (cons newsig
					  (symbol-value expect-signal))))))
	 (t
	  (forward-char 1)))
	(skip-syntax-forward " "))
      ;; Return arguments
      (bsv-decls-new (nreverse sigs-out)
			 (nreverse sigs-inout)
			 (nreverse sigs-in)
			 (nreverse sigs-var)
			 nil
			 (nreverse sigs-assign)
			 (nreverse sigs-const)
			 (nreverse sigs-gparam)
			 (nreverse sigs-intf)))))

(defvar bsv-read-sub-decls-in-interfaced nil
  "For `bsv-read-sub-decls', process next signal as under interfaced block.")

(defvar bsv-read-sub-decls-gate-ios nil
  "For `bsv-read-sub-decls', gate IO pins remaining, nil if non-primitive.")

(eval-when-compile
  ;; Prevent compile warnings; these are let's, not globals
  ;; Do not remove the eval-when-compile
  ;; - we want a error when we are debugging this code if they are refed.
  (defvar sigs-in)
  (defvar sigs-inout)
  (defvar sigs-out)
  (defvar sigs-intf)
  (defvar sigs-intfd))

(defun bsv-read-sub-decls-sig (submoddecls comment port sig vec multidim)
  "For `bsv-read-sub-decls-line', add a signal."
  ;; sig eq t to indicate .name syntax
  ;;(message "vrsds: %s(%S)" port sig)
  (let ((dotname (eq sig t))
	portdata)
    (when sig
      (setq port (bsv-symbol-detick-denumber port))
      (setq sig  (if dotname port (bsv-symbol-detick-denumber sig)))
      (if vec (setq vec  (bsv-symbol-detick-denumber vec)))
      (if multidim (setq multidim  (mapcar `bsv-symbol-detick-denumber multidim)))
      (unless (or (not sig)
		  (equal sig ""))  ;; Ignore .foo(1'b1) assignments
	(cond ((or (setq portdata (assoc port (bsv-decls-get-inouts submoddecls)))
		   (equal "inout" bsv-read-sub-decls-gate-ios))
	       (setq sigs-inout
		     (cons (bsv-sig-new
			    sig
			    (if dotname (bsv-sig-bits portdata) vec)
			    (concat "To/From " comment)
			    (bsv-sig-memory portdata)
			    nil
			    (bsv-sig-signed portdata)
			    (bsv-sig-type portdata)
			    multidim nil)
			   sigs-inout)))
	      ((or (setq portdata (assoc port (bsv-decls-get-outputs submoddecls)))
		   (equal "output" bsv-read-sub-decls-gate-ios))
	       (setq sigs-out
		     (cons (bsv-sig-new
			    sig
			    (if dotname (bsv-sig-bits portdata) vec)
			    (concat "From " comment)
			    (bsv-sig-memory portdata)
			    nil
			    (bsv-sig-signed portdata)
			    (bsv-sig-type portdata)
			    multidim nil)
			   sigs-out)))
	      ((or (setq portdata (assoc port (bsv-decls-get-inputs submoddecls)))
		   (equal "input" bsv-read-sub-decls-gate-ios))
	       (setq sigs-in
		     (cons (bsv-sig-new
			    sig
			    (if dotname (bsv-sig-bits portdata) vec)
			    (concat "To " comment)
			    (bsv-sig-memory portdata)
			    nil
			    (bsv-sig-signed portdata)
			    (bsv-sig-type portdata)
			    multidim nil)
			   sigs-in)))
	      ((setq portdata (assoc port (bsv-decls-get-interfaces submoddecls)))
	       (setq sigs-intf
		     (cons (bsv-sig-new
			    sig
			    (if dotname (bsv-sig-bits portdata) vec)
			    (concat "To/From " comment)
			    (bsv-sig-memory portdata)
			    nil
			    (bsv-sig-signed portdata)
			    (bsv-sig-type portdata)
			    multidim nil)
			   sigs-intf)))
	      ((setq portdata (and bsv-read-sub-decls-in-interfaced
				   (assoc port (bsv-decls-get-vars submoddecls))))
	       (setq sigs-intfd
		     (cons (bsv-sig-new
			    sig
			    (if dotname (bsv-sig-bits portdata) vec)
			    (concat "To/From " comment)
			    (bsv-sig-memory portdata)
			    nil
			    (bsv-sig-signed portdata)
			    (bsv-sig-type portdata)
			    multidim nil)
			   sigs-intf)))
	      ;; (t  -- warning pin isn't defined.)   ; Leave for lint tool
	      )))))

(defun bsv-read-sub-decls-expr (submoddecls comment port expr)
  "For `bsv-read-sub-decls-line', parse a subexpression and add signals."
  ;;(message "vrsde: '%s'" expr)
  ;; Replace special /*[....]*/ comments inserted by bsv-auto-inst-port
  (setq expr (bsv-string-replace-matches "/\\*\\(\\[[^*]+\\]\\)\\*/" "\\1" nil nil expr))
  ;; Remove front operators
  (setq expr (bsv-string-replace-matches "^\\s-*[---+~!|&]+\\s-*" "" nil nil expr))
  ;;
  (cond
   ;; {..., a, b} requires us to recurse on a,b
   ;; To support {#{},{#{a,b}} we'll just split everything on [{},]
   ((string-match "^\\s-*{\\(.*\\)}\\s-*$" expr)
    (unless bsv-auto-ignore-concat
      (let ((mlst (split-string (match-string 1 expr) "[{},]"))
	    mstr)
	(while (setq mstr (pop mlst))
	  (bsv-read-sub-decls-expr submoddecls comment port mstr)))))
   (t
    (let (sig vec multidim)
      ;; Remove leading reduction operators, etc
      (setq expr (bsv-string-replace-matches "^\\s-*[---+~!|&]+\\s-*" "" nil nil expr))
      ;;(message "vrsde-ptop: '%s'" expr)
      (cond ;; Find \signal. Final space is part of escaped signal name
       ((string-match "^\\s-*\\(\\\\[^ \t\n\f]+\\s-\\)" expr)
	;;(message "vrsde-s: '%s'" (match-string 1 expr))
	(setq sig (match-string 1 expr)
	      expr (substring expr (match-end 0))))
       ;; Find signal
       ((string-match "^\\s-*\\([a-zA-Z_][a-zA-Z_0-9]*\\)" expr)
	;;(message "vrsde-s: '%s'" (match-string 1 expr))
	(setq sig (bsv-string-remove-spaces (match-string 1 expr))
	      expr (substring expr (match-end 0)))))
      ;; Find [vector] or [multi][multi][multi][vector]
      (while (string-match "^\\s-*\\(\\[[^]]+\\]\\)" expr)
	;;(message "vrsde-v: '%s'" (match-string 1 expr))
	(when vec (setq multidim (cons vec multidim)))
	(setq vec (match-string 1 expr)
	      expr (substring expr (match-end 0))))
      ;; If found signal, and nothing unrecognized, add the signal
      ;;(message "vrsde-rem: '%s'" expr)
      (when (and sig (string-match "^\\s-*$" expr))
	(bsv-read-sub-decls-sig submoddecls comment port sig vec multidim))))))

(defun bsv-read-sub-decls-line (submoddecls comment)
  "For `bsv-read-sub-decls', read lines of port defs until none match.
Inserts the list of signals found, using submodi to look up each port."
  (let (done port)
    (save-excursion
      (forward-line 1)
      (while (not done)
	;; Get port name
	(cond ((looking-at "\\s-*\\.\\s-*\\([a-zA-Z0-9`_$]*\\)\\s-*(\\s-*")
	       (setq port (match-string 1))
	       (goto-char (match-end 0)))
	      ;; .\escaped (
	      ((looking-at "\\s-*\\.\\s-*\\(\\\\[^ \t\n\f]*\\)\\s-*(\\s-*")
	       (setq port (concat (match-string 1) " ")) ;; escaped id's need trailing space
	       (goto-char (match-end 0)))
	      ;; .name
	      ((looking-at "\\s-*\\.\\s-*\\([a-zA-Z0-9`_$]*\\)\\s-*[,)/]")
	       (bsv-read-sub-decls-sig
		submoddecls comment (match-string 1) t ; sig==t for .name
		nil nil) ; vec multidim
	       (setq port nil))
	      ;; .\escaped_name
	      ((looking-at "\\s-*\\.\\s-*\\(\\\\[^ \t\n\f]*\\)\\s-*[,)/]")
	       (bsv-read-sub-decls-sig
		submoddecls comment (concat (match-string 1) " ") t ; sig==t for .name
		nil nil) ; vec multidim
	       (setq port nil))
	      ;; random
	      ((looking-at "\\s-*\\.[^(]*(")
	       (setq port nil) ;; skip this line
	       (goto-char (match-end 0)))
	      (t
	       (setq port nil  done t))) ;; Unknown, ignore rest of line
	;; Get signal name.  Point is at the first-non-space after (
	;; We intentionally ignore (non-escaped) signals with .s in them
	;; this prevents AUTOWIRE etc from noticing hierarchical sigs.
	(when port
	  (cond ((looking-at "\\([a-zA-Z_][a-zA-Z_0-9]*\\)\\s-*)")
		 (bsv-read-sub-decls-sig
		  submoddecls comment port
		  (bsv-string-remove-spaces (match-string 1)) ; sig
		  nil nil)) ; vec multidim
		;;
		((looking-at "\\([a-zA-Z_][a-zA-Z_0-9]*\\)\\s-*\\(\\[[^]]+\\]\\)\\s-*)")
		 (bsv-read-sub-decls-sig
		  submoddecls comment port
		  (bsv-string-remove-spaces (match-string 1)) ; sig
		  (match-string 2) nil)) ; vec multidim
		;; Fastpath was above looking-at's.
		;; For something more complicated invoke a parser
		((looking-at "[^)]+")
		 (bsv-read-sub-decls-expr
		  submoddecls comment port
		  (buffer-substring
		   (point) (1- (progn (search-backward "(") ; start at (
				      (bsv-forward-sexp-ign-cmt 1)
				      (point)))))))) ; expr
	;;
	(forward-line 1)))))

(defun bsv-read-sub-decls-gate (submoddecls comment submod end-inst-point)
  "For `bsv-read-sub-decls', read lines of UDP gate decl until none match.
Inserts the list of signals found."
  (save-excursion
    (let ((iolist (cdr (assoc submod bsv-gate-ios))))
      (while (< (point) end-inst-point)
	;; Get primitive's signal name, as will never have port, and no trailing )
	(cond ((looking-at "//")
	       (search-forward "\n"))
	      ((looking-at "/\\*")
	       (or (search-forward "*/")
		   (error "%s: Unmatched /* */, at char %d" (bsv-point-text) (point))))
	      ((looking-at "(\\*")
	       ;; To advance past either "(*)" or "(* ... *)" don't forward past first *
	       (forward-char 1)
	       (or (search-forward "*)")
		   (error "%s: Unmatched (* *), at char %d" (bsv-point-text) (point))))
	      ;; On pins, parse and advance to next pin
	      ;; Looking at pin, but *not* an // Output comment, or ) to end the inst
	      ((looking-at "\\s-*[a-zA-Z0-9`_$({}\\\\][^,]*")
	       (goto-char (match-end 0))
	       (setq bsv-read-sub-decls-gate-ios (or (car iolist) "input")
		     iolist (cdr iolist))
	       (bsv-read-sub-decls-expr
		submoddecls comment "primitive_port"
		(match-string 0)))
	      (t
	       (forward-char 1)
	       (skip-syntax-forward " ")))))))

(defun bsv-read-sub-decls ()
  "Internally parse signals going to modules under this module.
Return a array of [ outputs inouts inputs ] signals for modules that are
instantiated in this module.  For example if declare A A (.B(SIG)) and SIG
is a output, then SIG will be included in the list.

This only works on instantiations created with /*AUTOINST*/ converted by
\\[bsv-auto-inst].  Otherwise, it would have to read in the whole
component library to determine connectivity of the design.

One work around for this problem is to manually create // Inputs and //
Outputs comments above subcell signals, for example:

	module ModuleName (
	    // Outputs
	    .out (out),
	    // Inputs
	    .in  (in));"
  (save-excursion
    (let ((end-mod-point (bsv-get-end-of-defun t))
	  st-point end-inst-point
	  ;; below 3 modified by bsv-read-sub-decls-line
	  sigs-out sigs-inout sigs-in sigs-intf sigs-intfd)
      (bsv-beg-of-defun-quick)
      (while (bsv-re-search-forward-quick "\\(/\\*AUTOINST\\*/\\|\\.\\*\\)" end-mod-point t)
	(save-excursion
	  (goto-char (match-beginning 0))
	  (unless (bsv-inside-comment-or-string-p)
	    ;; Attempt to snarf a comment
	    (let* ((submod (bsv-read-inst-module))
		   (inst (bsv-read-inst-name))
		   (subprim (member submod bsv-gate-keywords))
		   (comment (concat inst " of " submod ".v"))
		   submodi submoddecls)
    	      (cond
	       (subprim
		(setq submodi `primitive
		      submoddecls (bsv-decls-new nil nil nil nil nil nil nil nil nil)
		      comment (concat inst " of " submod))
		(bsv-backward-open-paren)
		(setq end-inst-point (save-excursion (bsv-forward-sexp-ign-cmt 1)
						     (point))
		      st-point (point))
		(forward-char 1)
		(bsv-read-sub-decls-gate submoddecls comment submod end-inst-point))
	       ;; Non-primitive
	       (t
		(when (setq submodi (bsv-modi-lookup submod t))
		  (setq submoddecls (bsv-modi-get-decls submodi)
			bsv-read-sub-decls-gate-ios nil)
		  (bsv-backward-open-paren)
		  (setq end-inst-point (save-excursion (bsv-forward-sexp-ign-cmt 1)
						       (point))
			st-point (point))
		  ;; This could have used a list created by bsv-auto-inst
		  ;; However I want it to be runnable even on user's manually added signals
		  (let ((bsv-read-sub-decls-in-interfaced t))
		    (while (re-search-forward "\\s *(?\\s *// Interfaced" end-inst-point t)
		      (bsv-read-sub-decls-line submoddecls comment))) ;; Modifies sigs-ifd
		  (goto-char st-point)
		  (while (re-search-forward "\\s *(?\\s *// Interfaces" end-inst-point t)
		    (bsv-read-sub-decls-line submoddecls comment)) ;; Modifies sigs-out
		  (goto-char st-point)
		  (while (re-search-forward "\\s *(?\\s *// Outputs" end-inst-point t)
		    (bsv-read-sub-decls-line submoddecls comment)) ;; Modifies sigs-out
		  (goto-char st-point)
		  (while (re-search-forward "\\s *(?\\s *// Inouts" end-inst-point t)
		    (bsv-read-sub-decls-line submoddecls comment)) ;; Modifies sigs-inout
		  (goto-char st-point)
		  (while (re-search-forward "\\s *(?\\s *// Inputs" end-inst-point t)
		    (bsv-read-sub-decls-line submoddecls comment)) ;; Modifies sigs-in
		  )))))))
      ;; Combine duplicate bits
      ;;(setq rr (vector sigs-out sigs-inout sigs-in))
      (bsv-subdecls-new
       (bsv-signals-combine-bus (nreverse sigs-out))
       (bsv-signals-combine-bus (nreverse sigs-inout))
       (bsv-signals-combine-bus (nreverse sigs-in))
       (bsv-signals-combine-bus (nreverse sigs-intf))
       (bsv-signals-combine-bus (nreverse sigs-intfd))))))

(defun bsv-read-inst-pins ()
  "Return an array of [ pins ] for the current instantiation at point.
For example if declare A A (.B(SIG)) then B will be included in the list."
  (save-excursion
    (let ((end-mod-point (point))	;; presume at /*AUTOINST*/ point
	  pins pin)
      (bsv-backward-open-paren)
      (while (re-search-forward "\\.\\([^(,) \t\n\f]*\\)\\s-*" end-mod-point t)
	(setq pin (match-string 1))
	(unless (bsv-inside-comment-or-string-p)
	  (setq pins (cons (list pin) pins))
	  (when (looking-at "(")
	    (bsv-forward-sexp-ign-cmt 1))))
      (vector pins))))

(defun bsv-read-arg-pins ()
  "Return an array of [ pins ] for the current argument declaration at point."
  (save-excursion
    (let ((end-mod-point (point))	;; presume at /*AUTOARG*/ point
	  pins pin)
      (bsv-backward-open-paren)
      (while (re-search-forward "\\([a-zA-Z0-9$_.%`]+\\)" end-mod-point t)
	(setq pin (match-string 1))
	(unless (bsv-inside-comment-or-string-p)
	  (setq pins (cons (list pin) pins))))
      (vector pins))))

(defun bsv-read-auto-constants (beg end-mod-point)
  "Return a list of AUTO_CONSTANTs used in the region from BEG to END-MOD-POINT."
  ;; Insert new
  (save-excursion
    (let (sig-list tpl-end-pt)
      (goto-char beg)
      (while (re-search-forward "\\<AUTO_CONSTANT" end-mod-point t)
	(if (not (looking-at "\\s *("))
	    (error "%s: Missing () after AUTO_CONSTANT" (bsv-point-text)))
	(search-forward "(" end-mod-point)
	(setq tpl-end-pt (save-excursion
			   (backward-char 1)
			   (bsv-forward-sexp-cmt 1)   ;; Moves to paren that closes argdecl's
			   (backward-char 1)
			   (point)))
	(while (re-search-forward "\\s-*\\([\"a-zA-Z0-9$_.%`]+\\)\\s-*,*" tpl-end-pt t)
	  (setq sig-list (cons (list (match-string 1) nil nil) sig-list))))
      sig-list)))

(defvar bsv-cache-has-lisp nil "True if any AUTO_LISP in buffer.")
(make-variable-buffer-local 'bsv-cache-has-lisp)

(defun bsv-read-auto-lisp-present ()
  "Set `bsv-cache-has-lisp' if any AUTO_LISP in this buffer."
  (save-excursion
    (goto-char (point-min))
    (setq bsv-cache-has-lisp (re-search-forward "\\<AUTO_LISP(" nil t))))

(defun bsv-read-auto-lisp (start end)
  "Look for and evaluate a AUTO_LISP between START and END.
Must call `bsv-read-auto-lisp-present' before this function."
  ;; This function is expensive for large buffers, so we cache if any AUTO_LISP exists
  (when bsv-cache-has-lisp
    (save-excursion
      (goto-char start)
      (while (re-search-forward "\\<AUTO_LISP(" end t)
	(backward-char)
	(let* ((beg-pt (prog1 (point)
			 (bsv-forward-sexp-cmt 1)))	;; Closing paren
	       (end-pt (point)))
	  (eval-region beg-pt end-pt nil))))))

(eval-when-compile
  ;; Prevent compile warnings; these are let's, not globals
  ;; Do not remove the eval-when-compile
  ;; - we want a error when we are debugging this code if they are refed.
  (defvar sigs-in)
  (defvar sigs-out-d)
  (defvar sigs-out-i)
  (defvar sigs-out-unk)
  (defvar sigs-temp)
  (defvar vector-skip-list))

(defun bsv-read-always-signals-recurse
  (exit-keywd rvalue temp-next)
  "Recursive routine for parentheses/bracket matching.
EXIT-KEYWD is expression to stop at, nil if top level.
RVALUE is true if at right hand side of equal.
IGNORE-NEXT is true to ignore next token, fake from inside case statement."
  (let* ((semi-rvalue (equal "endcase" exit-keywd)) ;; true if after a ; we are looking for rvalue
	 keywd last-keywd sig-tolk sig-last-tolk gotend got-sig got-list end-else-check
	 ignore-next)
    ;;(if dbg (setq dbg (concat dbg (format "Recursion %S %S %S\n" exit-keywd rvalue temp-next))))
    (while (not (or (eobp) gotend))
      (cond
       ((looking-at "//")
	(search-forward "\n"))
       ((looking-at "/\\*")
	(or (search-forward "*/")
	    (error "%s: Unmatched /* */, at char %d" (bsv-point-text) (point))))
       ((looking-at "(\\*")
	;; To advance past either "(*)" or "(* ... *)" don't forward past first *
	(forward-char 1)
	(or (search-forward "*)")
	    (error "%s: Unmatched (* *), at char %d" (bsv-point-text) (point))))
       (t (setq keywd (buffer-substring-no-properties
		       (point)
		       (save-excursion (when (eq 0 (skip-chars-forward "a-zA-Z0-9$_.%`"))
					 (forward-char 1))
				       (point)))
		sig-last-tolk sig-tolk
		sig-tolk nil)
	  ;;(if dbg (setq dbg (concat dbg (format "\tPt=%S %S\trv=%S in=%S ee=%S gs=%S\n" (point) keywd rvalue ignore-next end-else-check got-sig))))
	  (cond
	   ((equal keywd "\"")
	    (or (re-search-forward "[^\\]\"" nil t)
		(error "%s: Unmatched quotes, at char %d" (bsv-point-text) (point))))
	   ;; else at top level loop, keep parsing
	   ((and end-else-check (equal keywd "else"))
	    ;;(if dbg (setq dbg (concat dbg (format "\tif-check-else %s\n" keywd))))
	    ;; no forward movement, want to see else in lower loop
	    (setq end-else-check nil))
	   ;; End at top level loop
	   ((and end-else-check (looking-at "[^ \t\n\f]"))
	    ;;(if dbg (setq dbg (concat dbg (format "\tif-check-else-other %s\n" keywd))))
	    (setq gotend t))
	   ;; Final statement?
	   ((and exit-keywd (equal keywd exit-keywd))
	    (setq gotend t)
	    (forward-char (length keywd)))
	   ;; Standard tokens...
	   ((equal keywd ";")
	    (setq ignore-next nil  rvalue semi-rvalue)
	    ;; Final statement at top level loop?
	    (when (not exit-keywd)
	      ;;(if dbg (setq dbg (concat dbg (format "\ttop-end-check %s\n" keywd))))
	      (setq end-else-check t))
	    (forward-char 1))
	   ((equal keywd "'")
	    (if (looking-at "'[sS]?[hdxboHDXBO]?[ \t]*[0-9a-fA-F_xzXZ?]+")
		(goto-char (match-end 0))
	      (forward-char 1)))
	   ((equal keywd ":")	;; Case statement, begin/end label, x?y:z
	    (cond ((equal "endcase" exit-keywd)  ;; case x: y=z; statement next
		   (setq ignore-next nil rvalue nil))
		  ((equal "?" exit-keywd)  ;; x?y:z rvalue
		   ) ;; NOP
		  ((equal "]" exit-keywd)  ;; [x:y] rvalue
		   ) ;; NOP
		  (got-sig	;; label: statement
		   (setq ignore-next nil rvalue semi-rvalue got-sig nil))
		  ((not rvalue)	;; begin label
		   (setq ignore-next t rvalue nil)))
	    (forward-char 1))
	   ((equal keywd "=")
	    (when got-sig
	      ;;(if dbg (setq dbg (concat dbg (format "\t\tequal got-sig=%S got-list=%s\n" got-sig got-list))))
	      (set got-list (cons got-sig (symbol-value got-list)))
	      (setq got-sig nil))
	    (when (not rvalue)
	      (if (eq (char-before) ?< )
		  (setq sigs-out-d (append sigs-out-d sigs-out-unk)
			sigs-out-unk nil)
		(setq sigs-out-i (append sigs-out-i sigs-out-unk)
		      sigs-out-unk nil)))
	    (setq ignore-next nil rvalue t)
	    (forward-char 1))
	   ((equal keywd "?")
	    (forward-char 1)
	    (bsv-read-always-signals-recurse ":" rvalue nil))
	   ((equal keywd "[")
	    (forward-char 1)
	    (bsv-read-always-signals-recurse "]" t nil))
	   ((equal keywd "(")
	    (forward-char 1)
	    (cond (sig-last-tolk	;; Function call; zap last signal
		   (setq got-sig nil)))
	    (cond ((equal last-keywd "for")
		   ;; temp-next: Variables on LHS are lvalues, but generally we want
		   ;; to ignore them, assuming they are loop increments
		   (bsv-read-always-signals-recurse ";" nil t)
		   (bsv-read-always-signals-recurse ";" t nil)
		   (bsv-read-always-signals-recurse ")" nil nil))
		  (t (bsv-read-always-signals-recurse ")" t nil))))
	   ((equal keywd "begin")
	    (skip-syntax-forward "w_")
	    (bsv-read-always-signals-recurse "end" nil nil)
	    ;;(if dbg (setq dbg (concat dbg (format "\tgot-end %s\n" exit-keywd))))
	    (setq ignore-next nil  rvalue semi-rvalue)
	    (if (not exit-keywd) (setq end-else-check t)))
	   ((member keywd '("case" "casex" "casez"))
	    (skip-syntax-forward "w_")
	    (bsv-read-always-signals-recurse "endcase" t nil)
	    (setq ignore-next nil  rvalue semi-rvalue)
	    (if (not exit-keywd) (setq gotend t)))	;; top level begin/end
	   ((string-match "^[$`a-zA-Z_]" keywd)	;; not exactly word constituent
	    (cond ((member keywd '("`ifdef" "`ifndef" "`elsif"))
		   (setq ignore-next t))
		  ((or ignore-next
		       (member keywd bsv-keywords)
		       (string-match "^\\$" keywd))	;; PLI task
		   (setq ignore-next nil))
		  (t
		   (setq keywd (bsv-symbol-detick-denumber keywd))
		   (when got-sig
		     (set got-list (cons got-sig (symbol-value got-list)))
		     ;;(if dbg (setq dbg (concat dbg (format "\t\tgot-sig=%S got-list=%S\n" got-sig got-list))))
		     )
		   (setq got-list (cond (temp-next 'sigs-temp)
					(rvalue 'sigs-in)
					(t 'sigs-out-unk))
			 got-sig (if (or (not keywd)
					 (assoc keywd (symbol-value got-list)))
				     nil (list keywd nil nil))
			 temp-next nil
			 sig-tolk t)))
	    (skip-chars-forward "a-zA-Z0-9$_.%`"))
	   (t
	    (forward-char 1)))
	  ;; End of non-comment token
	  (setq last-keywd keywd)))
      (skip-syntax-forward " "))
    ;; Append the final pending signal
    (when got-sig
      ;;(if dbg (setq dbg (concat dbg (format "\t\tfinal got-sig=%S got-list=%s\n" got-sig got-list))))
      (set got-list (cons got-sig (symbol-value got-list)))
      (setq got-sig nil))
    ;;(if dbg (setq dbg (concat dbg (format "ENDRecursion %s\n" exit-keywd))))
    ))

(defun bsv-read-always-signals ()
  "Parse always block at point and return list of (outputs inout inputs)."
  (save-excursion
    (let* (;;(dbg "")
	   sigs-out-d sigs-out-i sigs-out-unk sigs-temp sigs-in)
      (search-forward ")")
      (bsv-read-always-signals-recurse nil nil nil)
      (setq sigs-out-i (append sigs-out-i sigs-out-unk)
	    sigs-out-unk nil)
      ;;(if dbg (with-current-buffer (get-buffer-create "*vl-dbg*")) (delete-region (point-min) (point-max)) (insert dbg) (setq dbg ""))
      ;; Return what was found
      (bsv-alw-new sigs-out-d sigs-out-i sigs-temp sigs-in))))

(defun bsv-read-instants ()
  "Parse module at point and return list of ( ( file instance ) ... )."
  (bsv-beg-of-defun-quick)
  (let* ((end-mod-point (bsv-get-end-of-defun t))
	 (state nil)
	 (instants-list nil))
    (save-excursion
      (while (< (point) end-mod-point)
	;; Stay at level 0, no comments
	(while (progn
		 (setq state (parse-partial-sexp (point) end-mod-point 0 t nil))
		 (or (> (car state) 0)	; in parens
		     (nth 5 state)		; comment
		     ))
	  (forward-line 1))
	(beginning-of-line)
	(if (looking-at "^\\s-*\\([a-zA-Z0-9`_$]+\\)\\s-+\\([a-zA-Z0-9`_$]+\\)\\s-*(")
	    ;;(if (looking-at "^\\(.+\\)$")
	    (let ((module (match-string 1))
		  (instant (match-string 2)))
	      (if (not (member module bsv-keywords))
		  (setq instants-list (cons (list module instant) instants-list)))))
	(forward-line 1)))
    instants-list))


(defun bsv-read-auto-template (module)
  "Look for a auto_template for the instantiation of the given MODULE.
If found returns the signal name connections.  Return REGEXP and
list of ( (signal_name connection_name)... )."
  (save-excursion
    ;; Find beginning
    (let ((tpl-regexp "\\([0-9]+\\)")
	  (lineno -1)  ; -1 to offset for the AUTO_TEMPLATE's newline
	  (templateno 0)
	  (pt (point))
	  tpl-sig-list tpl-wild-list tpl-end-pt rep)
      ;; Note this search is expensive, as we hunt from mod-begin to point
      ;; for every instantiation.  Likewise in bsv-read-auto-lisp.
      ;; So, we look first for an exact string rather than a slow regexp.
      ;; Someday we may keep a cache of every template, but this would also
      ;; need to record the relative position of each AUTOINST, as multiple
      ;; templates exist for each module, and we're inserting lines.
      (cond ((or
	      (bsv-re-search-backward-substr
	       "AUTO_TEMPLATE"
	       (concat "^\\s-*/?\\*?\\s-*" module "\\s-+AUTO_TEMPLATE") nil t)
	      ;; Also try forward of this AUTOINST
	      ;; This is for historical support; this isn't speced as working
	      (progn
		(goto-char pt)
		(bsv-re-search-forward-substr
		 "AUTO_TEMPLATE"
		 (concat "^\\s-*/?\\*?\\s-*" module "\\s-+AUTO_TEMPLATE") nil t)))
	     (goto-char (match-end 0))
	     ;; Parse "REGEXP"
	     ;; We reserve @"..." for future lisp expressions that evaluate
	     ;; once-per-AUTOINST
	     (when (looking-at "\\s-*\"\\([^\"]*\\)\"")
	       (setq tpl-regexp (match-string 1))
	       (goto-char (match-end 0)))
	     (search-forward "(")
	     ;; Parse lines in the template
	     (when bsv-auto-inst-template-numbers
	       (save-excursion
		 (let ((pre-pt (point)))
		   (goto-char (point-min))
		   (while (search-forward "AUTO_TEMPLATE" pre-pt t)
		     (setq templateno (1+ templateno)))
		   (while (< (point) pre-pt)
		     (forward-line 1)
		     (setq lineno (1+ lineno))))))
	     (setq tpl-end-pt (save-excursion
				(backward-char 1)
				(bsv-forward-sexp-cmt 1)   ;; Moves to paren that closes argdecl's
				(backward-char 1)
				(point)))
	     ;;
	     (while (< (point) tpl-end-pt)
	       (cond ((looking-at "\\s-*\\.\\([a-zA-Z0-9`_$]+\\)\\s-*(\\(.*\\))\\s-*\\(,\\|)\\s-*;\\)")
		      (setq tpl-sig-list
			    (cons (list
				   (match-string-no-properties 1)
				   (match-string-no-properties 2)
				   templateno lineno)
				  tpl-sig-list))
		      (goto-char (match-end 0)))
		     ;; Regexp form??
		     ((looking-at
		       ;; Regexp bug in XEmacs disallows ][ inside [], and wants + last
		       "\\s-*\\.\\(\\([a-zA-Z0-9`_$+@^.*?|---]+\\|[][]\\|\\\\[()|]\\)+\\)\\s-*(\\(.*\\))\\s-*\\(,\\|)\\s-*;\\)")
		      (setq rep (match-string-no-properties 3))
		      (goto-char (match-end 0))
		      (setq tpl-wild-list
			    (cons (list
				   (concat "^"
					   (bsv-string-replace-matches "@" "\\\\([0-9]+\\\\)" nil nil
									   (match-string 1))
					   "$")
				   rep
				   templateno lineno)
				  tpl-wild-list)))
		     ((looking-at "[ \t\f]+")
		      (goto-char (match-end 0)))
		     ((looking-at "\n")
		      (setq lineno (1+ lineno))
		      (goto-char (match-end 0)))
		     ((looking-at "//")
		      (search-forward "\n")
		      (setq lineno (1+ lineno)))
		     ((looking-at "/\\*")
		      (forward-char 2)
		      (or (search-forward "*/")
			  (error "%s: Unmatched /* */, at char %d" (bsv-point-text) (point))))
		     (t
		      (error "%s: AUTO_TEMPLATE parsing error: %s"
			     (bsv-point-text)
			     (progn (looking-at ".*$") (match-string 0))))))
	     ;; Return
	     (vector tpl-regexp
		     (list tpl-sig-list tpl-wild-list)))
	    ;; If no template found
	    (t (vector tpl-regexp nil))))))
;;(progn (find-file "auto-template.v") (bsv-read-auto-template "ptl_entry"))

(defun bsv-set-define (defname defvalue &optional buffer enumname)
  "Set the definition DEFNAME to the DEFVALUE in the given BUFFER.
Optionally associate it with the specified enumeration ENUMNAME."
  (with-current-buffer (or buffer (current-buffer))
    (let ((mac (intern (concat "vh-" defname))))
      ;;(message "Define %s=%s" defname defvalue) (sleep-for 1)
      ;; Need to define to a constant if no value given
      (set (make-local-variable mac)
	   (if (equal defvalue "") "1" defvalue)))
    (if enumname
	(let ((enumvar (intern (concat "venum-" enumname))))
	  ;;(message "Define %s=%s" defname defvalue) (sleep-for 1)
	  (unless (boundp enumvar) (set enumvar nil))
          (add-to-list (make-local-variable enumvar) defname)))))

(defun bsv-read-defines (&optional filename recurse subcall)
  "Read `defines and parameters for the current file, or optional FILENAME.
If the filename is provided, `bsv-library-flags' will be used to
resolve it.  If optional RECURSE is non-nil, recurse through `includes.

Parameters must be simple assignments to constants, or have their own
\"parameter\" label rather than a list of parameters.  Thus:

    parameter X = 5, Y = 10;	// Ok
    parameter X = {1'b1, 2'h2};	// Ok
    parameter X = {1'b1, 2'h2}, Y = 10;	// Bad, make into 2 parameter lines

Defines must be simple text substitutions, one on a line, starting
at the beginning of the line.  Any ifdefs or multiline comments around the
define are ignored.

Defines are stored inside Emacs variables using the name vh-{definename}.

This function is useful for setting vh-* variables.  The file variables
feature can be used to set defines that `bsv-mode' can see; put at the
*END* of your file something like:

    // Local Variables:
    // vh-macro:\"macro_definition\"
    // End:

If macros are defined earlier in the same file and you want their values,
you can read them automatically (provided `enable-local-eval' is on):

    // Local Variables:
    // eval:(bsv-read-defines)
    // eval:(bsv-read-defines \"group_standard_includes.v\")
    // End:

Note these are only read when the file is first visited, you must use
\\[find-alternate-file] RET  to have these take effect after editing them!

If you want to disable the \"Process `eval' or hook local variables\"
warning message, you need to add to your .emacs file:

    (setq enable-local-eval t)"
  (let ((origbuf (current-buffer)))
    (save-excursion
      (unless subcall (bsv-getopt-flags))
      (when filename
	(let ((fns (bsv-library-filenames filename (buffer-file-name))))
	  (if fns
	      (set-buffer (find-file-noselect (car fns)))
	    (error (concat (bsv-point-text)
			   ": Can't find bsv-read-defines file: " filename)))))
      (when recurse
	(goto-char (point-min))
	(while (re-search-forward "^\\s-*`include\\s-+\\([^ \t\n\f]+\\)" nil t)
	  (let ((inc (bsv-string-replace-matches
		      "\"" "" nil nil (match-string-no-properties 1))))
	    (unless (bsv-inside-comment-or-string-p)
	      (bsv-read-defines inc recurse t)))))
      ;; Read `defines
      ;; note we don't use bsv-re... it's faster this way, and that
      ;; function has problems when comments are at the end of the define
      (goto-char (point-min))
      (while (re-search-forward "^\\s-*`define\\s-+\\([a-zA-Z0-9_$]+\\)\\s-+\\(.*\\)$" nil t)
	(let ((defname (match-string-no-properties 1))
	      (defvalue (match-string-no-properties 2)))
	  (setq defvalue (bsv-string-replace-matches "\\s-*/[/*].*$" "" nil nil defvalue))
	  (bsv-set-define defname defvalue origbuf)))
      ;; Hack: Read parameters
      (goto-char (point-min))
      (while (re-search-forward
	      "^\\s-*\\(parameter\\|localparam\\)\\(\\s-*\\[[^]]*\\]\\)?\\s-*" nil t)
	(let (enumname)
	  ;; The primary way of getting defines is bsv-read-decls
	  ;; However, that isn't called yet for included files, so we'll add another scheme
	  (if (looking-at "[^\n]*synopsys\\s +enum\\s +\\([a-zA-Z0-9_]+\\)")
	      (setq enumname (match-string-no-properties 1)))
	  (forward-comment 999)
	  (while (looking-at (concat "\\s-*,?\\s-*\\(?:/[/*].*?$\\)?\\s-*\\([a-zA-Z0-9_$]+\\)"
				     "\\s-*=\\s-*\\([^;,]*\\),?\\s-*\\(/[/*].*?$\\)?\\s-*"))
	    (bsv-set-define (match-string-no-properties 1)
				(match-string-no-properties 2) origbuf enumname)
	    (goto-char (match-end 0))
	    (forward-comment 999)))))))

(defun bsv-read-includes ()
  "Read `includes for the current file.
This will find all of the `includes which are at the beginning of lines,
ignoring any ifdefs or multiline comments around them.
`bsv-read-defines' is then performed on the current and each included
file.

It is often useful put at the *END* of your file something like:

    // Local Variables:
    // eval:(bsv-read-defines)
    // eval:(bsv-read-includes)
    // End:

Note includes are only read when the file is first visited, you must use
\\[find-alternate-file] RET  to have these take effect after editing them!

It is good to get in the habit of including all needed files in each .v
file that needs it, rather than waiting for compile time.  This will aid
this process, Verilint, and readability.  To prevent defining the same
variable over and over when many modules are compiled together, put a test
around the inside each include file:

foo.v (a include):
	`ifdef _FOO_V	// include if not already included
	`else
	`define _FOO_V
	... contents of file
	`endif // _FOO_V"
;;slow:  (bsv-read-defines nil t))
  (save-excursion
    (bsv-getopt-flags)
    (goto-char (point-min))
    (while (re-search-forward "^\\s-*`include\\s-+\\([^ \t\n\f]+\\)" nil t)
      (let ((inc (bsv-string-replace-matches "\"" "" nil nil (match-string 1))))
	(bsv-read-defines inc nil t)))))

(defun bsv-read-signals (&optional start end)
  "Return a simple list of all possible signals in the file.
Bounded by optional region from START to END.  Overly aggressive but fast.
Some macros and such are also found and included.  For dinotrace.el."
  (let (sigs-all keywd)
    (progn;save-excursion
      (goto-char (or start (point-min)))
      (setq end (or end (point-max)))
      (while (re-search-forward "[\"/a-zA-Z_.%`]" end t)
	(forward-char -1)
	(cond
	 ((looking-at "//")
	  (search-forward "\n"))
	 ((looking-at "/\\*")
	  (search-forward "*/"))
	 ((looking-at "(\\*")
	  (or (looking-at "(\\*\\s-*)")   ; It's a "always @ (*)"
	      (search-forward "*)")))
	 ((eq ?\" (following-char))
	  (re-search-forward "[^\\]\""))	;; don't forward-char first, since we look for a non backslash first
	 ((looking-at "\\s-*\\([a-zA-Z0-9$_.%`]+\\)")
	  (goto-char (match-end 0))
	  (setq keywd (match-string-no-properties 1))
	  (or (member keywd bsv-keywords)
	      (member keywd sigs-all)
	      (setq sigs-all (cons keywd sigs-all))))
	 (t (forward-char 1))))
      ;; Return list
      sigs-all)))

;;
;; Argument file parsing
;;

(defun bsv-getopt (arglist)
  "Parse -f, -v etc arguments in ARGLIST list or string."
  (unless (listp arglist) (setq arglist (list arglist)))
  (let ((space-args '())
	arg next-param)
    ;; Split on spaces, so users can pass whole command lines
    (while arglist
      (setq arg (car arglist)
	    arglist (cdr arglist))
      (while (string-match "^\\([^ \t\n\f]+\\)[ \t\n\f]*\\(.*$\\)" arg)
	(setq space-args (append space-args
				 (list (match-string-no-properties 1 arg))))
	(setq arg (match-string 2 arg))))
    ;; Parse arguments
    (while space-args
      (setq arg (car space-args)
	    space-args (cdr space-args))
      (cond
       ;; Need another arg
       ((equal arg "-f")
	(setq next-param arg))
       ((equal arg "-v")
	(setq next-param arg))
       ((equal arg "-y")
	(setq next-param arg))
       ;; +libext+(ext1)+(ext2)...
       ((string-match "^\\+libext\\+\\(.*\\)" arg)
	(setq arg (match-string 1 arg))
	(while (string-match "\\([^+]+\\)\\+?\\(.*\\)" arg)
	  (bsv-add-list-unique `bsv-library-extensions
				   (match-string 1 arg))
	  (setq arg (match-string 2 arg))))
       ;;
       ((or (string-match "^-D\\([^+=]*\\)[+=]\\(.*\\)" arg)	;; -Ddefine=val
	    (string-match "^-D\\([^+=]*\\)\\(\\)" arg)	;; -Ddefine
	    (string-match "^\\+define\\([^+=]*\\)[+=]\\(.*\\)" arg)	;; +define+val
	    (string-match "^\\+define\\([^+=]*\\)\\(\\)" arg))		;; +define+define
	(bsv-set-define (match-string 1 arg) (match-string 2 arg)))
       ;;
       ((or (string-match "^\\+incdir\\+\\(.*\\)" arg)	;; +incdir+dir
	    (string-match "^-I\\(.*\\)" arg))	;; -Idir
	(bsv-add-list-unique `bsv-library-directories
				 (match-string 1 (substitute-in-file-name arg))))
       ;; Ignore
       ((equal "+librescan" arg))
       ((string-match "^-U\\(.*\\)" arg))	;; -Udefine
       ;; Second parameters
       ((equal next-param "-f")
	(setq next-param nil)
	(bsv-getopt-file (substitute-in-file-name arg)))
       ((equal next-param "-v")
	(setq next-param nil)
	(bsv-add-list-unique `bsv-library-files
				 (substitute-in-file-name arg)))
       ((equal next-param "-y")
	(setq next-param nil)
	(bsv-add-list-unique `bsv-library-directories
				 (substitute-in-file-name arg)))
       ;; Filename
       ((string-match "^[^-+]" arg)
	(bsv-add-list-unique `bsv-library-files
				 (substitute-in-file-name arg)))
       ;; Default - ignore; no warning
       ))))
;;(bsv-getopt (list "+libext+.a+.b" "+incdir+foodir" "+define+a+aval" "-f" "otherf" "-v" "library" "-y" "dir"))

(defun bsv-getopt-file (filename)
  "Read BSV options from the specified FILENAME."
  (save-excursion
    (let ((fns (bsv-library-filenames filename (buffer-file-name)))
	  (orig-buffer (current-buffer))
	  line)
      (if fns
	  (set-buffer (find-file-noselect (car fns)))
	(error (concat (bsv-point-text)
		       ": Can't find bsv-getopt-file -f file: " filename)))
      (goto-char (point-min))
      (while (not (eobp))
	(setq line (buffer-substring (point) (point-at-eol)))
	(forward-line 1)
	(when (string-match "//" line)
	  (setq line (substring line 0 (match-beginning 0))))
	(with-current-buffer orig-buffer  ; Variables are buffer-local, so need right context.
	  (bsv-getopt line))))))

(defun bsv-getopt-flags ()
  "Convert `bsv-library-flags' into standard library variables."
  ;; If the flags are local, then all the outputs should be local also
  (when (local-variable-p `bsv-library-flags (current-buffer))
    (mapc 'make-local-variable '(bsv-library-extensions
                                 bsv-library-directories
                                 bsv-library-files
                                 bsv-library-flags)))
  ;; Allow user to customize
  (bsv-run-hooks 'bsv-before-getopt-flags-hook)
  ;; Process arguments
  (bsv-getopt bsv-library-flags)
  ;; Allow user to customize
  (bsv-run-hooks 'bsv-getopt-flags-hook))

(defun bsv-add-list-unique (varref object)
  "Append to VARREF list the given OBJECT,
unless it is already a member of the variable's list."
  (unless (member object (symbol-value varref))
    (set varref (append (symbol-value varref) (list object))))
  varref)
;;(progn (setq l '()) (bsv-add-list-unique `l "a") (bsv-add-list-unique `l "a") l)

(defun bsv-current-flags ()
  "Convert `bsv-library-flags' and similar variables to command line.
Used for __FLAGS__ in `bsv-expand-command'."
  (let ((cmd (mapconcat `concat bsv-library-flags " ")))
    (when (equal cmd "")
      (setq cmd (concat
		 "+libext+" (mapconcat `concat bsv-library-extensions "+")
		 (mapconcat (lambda (i) (concat " -y " i " +incdir+" i))
			    bsv-library-directories "")
		 (mapconcat (lambda (i) (concat " -v " i))
			    bsv-library-files ""))))
    cmd))
;;(bsv-current-flags)


;;
;; Cached directory support
;;

(defvar bsv-dir-cache-preserving nil
  "If set, the directory cache is enabled, and file system changes are ignored.
See `bsv-dir-exists-p' and `bsv-dir-files'.")

;; If adding new cached variable, add also to bsv-preserve-dir-cache
(defvar bsv-dir-cache-list nil
  "Alist of (((Cwd Dirname) Results)...) for caching `bsv-dir-files'.")
(defvar bsv-dir-cache-lib-filenames nil
  "Cached data for `bsv-library-filenames'.")

(defmacro bsv-preserve-dir-cache (&rest body)
  "Execute the BODY forms, allowing directory cache preservation within BODY.
This means that changes inside BODY made to the file system will not be
seen by the `bsv-dir-files' and related functions."
  `(let ((bsv-dir-cache-preserving (current-buffer))
	 bsv-dir-cache-list
	 bsv-dir-cache-lib-filenames)
     (progn ,@body)))

(defun bsv-dir-files (dirname)
  "Return all filenames in the DIRNAME directory.
Relative paths depend on the `default-directory'.
Results are cached if inside `bsv-preserve-dir-cache'."
  (unless bsv-dir-cache-preserving
    (setq bsv-dir-cache-list nil)) ;; Cache disabled
  ;; We don't use expand-file-name on the dirname to make key, as it's slow
  (let* ((cache-key (list dirname default-directory))
	 (fass (assoc cache-key bsv-dir-cache-list))
	 exp-dirname data)
    (cond (fass  ;; Return data from cache hit
	   (nth 1 fass))
	  (t
	   (setq exp-dirname (expand-file-name dirname)
		 data (and (file-directory-p exp-dirname)
			   (directory-files exp-dirname nil nil nil)))
	   ;; Note we also encache nil for non-existing dirs.
	   (setq bsv-dir-cache-list (cons (list cache-key data)
					      bsv-dir-cache-list))
	   data))))
;; Miss-and-hit test:
;;(bsv-preserve-dir-cache (prin1 (bsv-dir-files "."))
;; (prin1 (bsv-dir-files ".")) nil)

(defun bsv-dir-file-exists-p (filename)
  "Return true if FILENAME exists.
Like `file-exists-p' but results are cached if inside
`bsv-preserve-dir-cache'."
  (let* ((dirname (file-name-directory filename))
	 ;; Correct for file-name-nondirectory returning same if no slash.
	 (dirnamed (if (or (not dirname) (equal dirname filename))
		       default-directory dirname))
	 (flist (bsv-dir-files dirnamed)))
    (and flist
	 (member (file-name-nondirectory filename) flist)
	 t)))
;;(bsv-dir-file-exists-p "bsv-mode.el")
;;(bsv-dir-file-exists-p "../bsv-mode/bsv-mode.el")


;;
;; Module name lookup
;;

(defun bsv-module-inside-filename-p (module filename)
  "Return modi if MODULE is specified inside FILENAME, else nil.
Allows version control to check out the file if need be."
  (and (or (file-exists-p filename)
	   (and (fboundp 'vc-backend)
		(vc-backend filename)))
       (let (modi type)
	 (with-current-buffer (find-file-noselect filename)
	   (save-excursion
	     (goto-char (point-min))
	     (while (and
		     ;; It may be tempting to look for bsv-defun-re,
		     ;; don't, it slows things down a lot!
		     (bsv-re-search-forward-quick "\\<\\(module\\|interface\\|program\\)\\>" nil t)
		     (setq type (match-string-no-properties 0))
		     (bsv-re-search-forward-quick "[(;]" nil t))
	       (if (equal module (bsv-read-module-name))
		   (setq modi (bsv-modi-new module filename (point) type))))
	     modi)))))

(defun bsv-is-number (symbol)
  "Return true if SYMBOL is number-like."
  (or (string-match "^[0-9 \t:]+$" symbol)
      (string-match "^[---]*[0-9]+$" symbol)
      (string-match "^[0-9 \t]+'s?[hdxbo][0-9a-fA-F_xz? \t]*$" symbol)))

(defun bsv-symbol-detick (symbol wing-it)
  "Return an expanded SYMBOL name without any defines.
If the variable vh-{symbol} is defined, return that value.
If undefined, and WING-IT, return just SYMBOL without the tick, else nil."
  (while (and symbol (string-match "^`" symbol))
    (setq symbol (substring symbol 1))
    (setq symbol
	  (if (boundp (intern (concat "vh-" symbol)))
	      ;; Emacs has a bug where boundp on a buffer-local
	      ;; variable in only one buffer returns t in another.
	      ;; This can confuse, so check for nil.
	      (let ((val (eval (intern (concat "vh-" symbol)))))
		(if (eq val nil)
		    (if wing-it symbol nil)
		  val))
	    (if wing-it symbol nil))))
  symbol)
;;(bsv-symbol-detick "`mod" nil)

(defun bsv-symbol-detick-denumber (symbol)
  "Return SYMBOL with defines converted and any numbers dropped to nil."
  (when (string-match "^`" symbol)
    ;; This only will work if the define is a simple signal, not
    ;; something like a[b].  Sorry, it should be substituted into the parser
    (setq symbol
	  (bsv-string-replace-matches
	   "\[[^0-9: \t]+\]" "" nil nil
	   (or (bsv-symbol-detick symbol nil)
	       (if bsv-auto-sense-defines-constant
		   "0"
		 symbol)))))
  (if (bsv-is-number symbol)
      nil
    symbol))

(defun bsv-symbol-detick-text (text)
  "Return TEXT without any known defines.
If the variable vh-{symbol} is defined, substitute that value."
  (let ((ok t) symbol val)
    (while (and ok (string-match "`\\([a-zA-Z0-9_]+\\)" text))
      (setq symbol (match-string 1 text))
      ;;(message symbol)
      (cond ((and
	      (boundp (intern (concat "vh-" symbol)))
	      ;; Emacs has a bug where boundp on a buffer-local
	      ;; variable in only one buffer returns t in another.
	      ;; This can confuse, so check for nil.
	      (setq val (eval (intern (concat "vh-" symbol)))))
	     (setq text (replace-match val nil nil text)))
	    (t (setq ok nil)))))
  text)
;;(progn (setq vh-mod "`foo" vh-foo "bar") (bsv-symbol-detick-text "bar `mod `undefed"))

(defun bsv-expand-dirnames (&optional dirnames)
  "Return a list of existing directories given a list of wildcarded DIRNAMES.
Or, just the existing dirnames themselves if there are no wildcards."
  ;; Note this function is performance critical.
  ;; Do not call anything that requires disk access that cannot be cached.
  (interactive)
  (unless dirnames (error "`bsv-library-directories' should include at least '.'"))
  (setq dirnames (reverse dirnames))	; not nreverse
  (let ((dirlist nil)
	pattern dirfile dirfiles dirname root filename rest basefile)
    (while dirnames
      (setq dirname (substitute-in-file-name (car dirnames))
	    dirnames (cdr dirnames))
      (cond ((string-match (concat "^\\(\\|[/\\]*[^*?]*[/\\]\\)"  ;; root
				   "\\([^/\\]*[*?][^/\\]*\\)"	  ;; filename with *?
				   "\\(.*\\)")			  ;; rest
			   dirname)
	     (setq root (match-string 1 dirname)
		   filename (match-string 2 dirname)
		   rest (match-string 3 dirname)
		   pattern filename)
	     ;; now replace those * and ? with .+ and .
	     ;; use ^ and /> to get only whole file names
	     (setq pattern (bsv-string-replace-matches "[*]" ".+" nil nil pattern)
		   pattern (bsv-string-replace-matches "[?]" "." nil nil pattern)
		   pattern (concat "^" pattern "$")
		   dirfiles (bsv-dir-files root))
	     (while dirfiles
	       (setq basefile (car dirfiles)
		     dirfile (expand-file-name (concat root basefile rest))
		     dirfiles (cdr dirfiles))
	       (if (and (string-match pattern basefile)
			;; Don't allow abc/*/rtl to match abc/rtl via ..
			(not (equal basefile "."))
			(not (equal basefile ".."))
			(file-directory-p dirfile))
		   (setq dirlist (cons dirfile dirlist)))))
	    ;; Defaults
	    (t
	     (if (file-directory-p dirname)
		 (setq dirlist (cons dirname dirlist))))))
    dirlist))
;;(bsv-expand-dirnames (list "." ".." "nonexist" "../*" "/home/wsnyder/*/v"))

(defun bsv-library-filenames (filename &optional current check-ext)
  "Return a search path to find the given FILENAME or module name.
Uses the optional CURRENT filename or buffer-file-name, plus
`bsv-library-directories' and `bsv-library-extensions'
variables to build the path.  With optional CHECK-EXT also check
`bsv-library-extensions'."
  (unless current (setq current (buffer-file-name)))
  (unless bsv-dir-cache-preserving
    (setq bsv-dir-cache-lib-filenames nil))
  (let* ((cache-key (list filename current check-ext))
	 (fass (assoc cache-key bsv-dir-cache-lib-filenames))
	 chkdirs chkdir chkexts fn outlist)
    (cond (fass  ;; Return data from cache hit
	   (nth 1 fass))
	  (t
	   ;; Note this expand can't be easily cached, as we need to
	   ;; pick up buffer-local variables for newly read sub-module files
	   (setq chkdirs (bsv-expand-dirnames bsv-library-directories))
	   (while chkdirs
	     (setq chkdir (expand-file-name (car chkdirs)
					    (file-name-directory current))
		   chkexts (if check-ext bsv-library-extensions `("")))
	     (while chkexts
	       (setq fn (expand-file-name (concat filename (car chkexts))
					  chkdir))
	       ;;(message "Check for %s" fn)
	       (if (bsv-dir-file-exists-p fn)
		   (setq outlist (cons (expand-file-name
					fn (file-name-directory current))
				       outlist)))
		 (setq chkexts (cdr chkexts)))
	     (setq chkdirs (cdr chkdirs)))
	   (setq outlist (nreverse outlist))
	   (setq bsv-dir-cache-lib-filenames
		 (cons (list cache-key outlist)
		       bsv-dir-cache-lib-filenames))
	   outlist))))

(defun bsv-module-filenames (module current)
  "Return a search path to find the given MODULE name.
Uses the CURRENT filename, `bsv-library-extensions',
`bsv-library-directories' and `bsv-library-files'
variables to build the path."
  ;; Return search locations for it
  (append (list current)		; first, current buffer
	  (bsv-library-filenames module current t)
	  bsv-library-files))	; finally, any libraries

;;
;; Module Information
;;
;; Many of these functions work on "modi" a module information structure
;; A modi is:  [module-name-string file-name begin-point]

(defvar bsv-cache-enabled t
  "If true, enable caching of signals, etc.  Set to nil for debugging to make things SLOW!")

(defvar bsv-modi-cache-list nil
  "Cache of ((Module Function) Buf-Tick Buf-Modtime Func-Returns)...
For speeding up bsv-modi-get-* commands.
Buffer-local.")
(make-variable-buffer-local 'bsv-modi-cache-list)

(defvar bsv-modi-cache-preserve-tick nil
  "Modification tick after which the cache is still considered valid.
Use `bsv-preserve-modi-cache' to set it.")
(defvar bsv-modi-cache-preserve-buffer nil
  "Modification tick after which the cache is still considered valid.
Use `bsv-preserve-modi-cache' to set it.")
(defvar bsv-modi-cache-current-enable nil
  "If true, allow caching `bsv-modi-current', set by let().")
(defvar bsv-modi-cache-current nil
  "Currently active `bsv-modi-current', if any, set by let().")
(defvar bsv-modi-cache-current-max nil
  "Current endmodule point for `bsv-modi-cache-current', if any.")

(defun bsv-modi-current ()
  "Return the modi structure for the module currently at point, possibly cached."
  (cond ((and bsv-modi-cache-current
	      (>= (point) (bsv-modi-get-point bsv-modi-cache-current))
	      (<= (point) bsv-modi-cache-current-max))
	 ;; Slow assertion, for debugging the cache:
	 ;;(or (equal bsv-modi-cache-current (bsv-modi-current-get)) (debug))
	 bsv-modi-cache-current)
	(bsv-modi-cache-current-enable
	 (setq bsv-modi-cache-current (bsv-modi-current-get)
	       bsv-modi-cache-current-max
	       ;; The cache expires when we pass "endmodule" as then the
	       ;; current modi may change to the next module
	       ;; This relies on the AUTOs generally inserting, not deleting text
	       (save-excursion
		 (bsv-re-search-forward-quick bsv-end-defun-re nil nil)))
	 bsv-modi-cache-current)
	(t
	 (bsv-modi-current-get))))

(defun bsv-modi-current-get ()
  "Return the modi structure for the module currently at point."
  (let* (name type pt)
    ;; read current module's name
    (save-excursion
      (bsv-re-search-backward-quick bsv-defun-re nil nil)
      (setq type (match-string-no-properties 0))
      (bsv-re-search-forward-quick "(" nil nil)
      (setq name (bsv-read-module-name))
      (setq pt (point)))
    ;; return modi - note this vector built two places
    (bsv-modi-new name (or (buffer-file-name) (current-buffer)) pt type)))

(defvar bsv-modi-lookup-cache nil "Hash of (modulename modi).")
(make-variable-buffer-local 'bsv-modi-lookup-cache)
(defvar bsv-modi-lookup-last-current nil "Cache of `current-buffer' at last lookup.")
(defvar bsv-modi-lookup-last-tick nil "Cache of `buffer-chars-modified-tick' at last lookup.")

(defun bsv-modi-lookup (module allow-cache &optional ignore-error)
  "Find the file and point at which MODULE is defined.
If ALLOW-CACHE is set, check and remember cache of previous lookups.
Return modi if successful, else print message unless IGNORE-ERROR is true."
  (let* ((current (or (buffer-file-name) (current-buffer)))
	 modi)
    ;; Check cache
    ;;(message "bsv-modi-lookup: %s" module)
    (cond ((and bsv-modi-lookup-cache
		bsv-cache-enabled
		allow-cache
		(setq modi (gethash module bsv-modi-lookup-cache))
		(equal bsv-modi-lookup-last-current current)
		;; Iff hit is in current buffer, then tick must match
		(or (equal bsv-modi-lookup-last-tick (buffer-chars-modified-tick))
		    (not (equal current (bsv-modi-file-or-buffer modi)))))
	   ;;(message "bsv-modi-lookup: HIT %S" modi)
	   modi)
	  ;; Miss
	  (t (let* ((realmod (bsv-symbol-detick module t))
		    (orig-filenames (bsv-module-filenames realmod current))
		    (filenames orig-filenames)
		    mif)
	       (while (and filenames (not mif))
		 (if (not (setq mif (bsv-module-inside-filename-p realmod (car filenames))))
		     (setq filenames (cdr filenames))))
	       ;; mif has correct form to become later elements of modi
	       (cond (mif (setq modi mif))
		     (t (setq modi nil)
			(or ignore-error
			    (error (concat (bsv-point-text)
					   ": Can't locate " module " module definition"
					   (if (not (equal module realmod))
					       (concat " (Expanded macro to " realmod ")")
					     "")
					   "\n    Check the bsv-library-directories variable."
					   "\n    I looked in (if not listed, doesn't exist):\n\t"
					   (mapconcat 'concat orig-filenames "\n\t"))))))
	       (when (eval-when-compile (fboundp 'make-hash-table))
		 (unless bsv-modi-lookup-cache
		   (setq bsv-modi-lookup-cache
			 (make-hash-table :test 'equal :rehash-size 4.0)))
		 (puthash module modi bsv-modi-lookup-cache))
	       (setq bsv-modi-lookup-last-current current
		     bsv-modi-lookup-last-tick (buffer-chars-modified-tick)))))
    modi))

(defun bsv-modi-filename (modi)
  "Filename of MODI, or name of buffer if it's never been saved."
  (if (bufferp (bsv-modi-file-or-buffer modi))
      (or (buffer-file-name (bsv-modi-file-or-buffer modi))
	  (buffer-name (bsv-modi-file-or-buffer modi)))
    (bsv-modi-file-or-buffer modi)))

(defun bsv-modi-goto (modi)
  "Move point/buffer to specified MODI."
  (or modi (error "Passed unfound modi to goto, check earlier"))
  (set-buffer (if (bufferp (bsv-modi-file-or-buffer modi))
		  (bsv-modi-file-or-buffer modi)
		(find-file-noselect (bsv-modi-file-or-buffer modi))))
  (or (equal major-mode `bsv-mode)	;; Put into BSV mode to get syntax
      (bsv-mode))
  (goto-char (bsv-modi-get-point modi)))

(defun bsv-goto-defun-file (module)
  "Move point to the file at which a given MODULE is defined."
  (interactive "sGoto File for Module: ")
  (let* ((modi (bsv-modi-lookup module nil)))
    (when modi
      (bsv-modi-goto modi)
      (switch-to-buffer (current-buffer)))))

(defun bsv-modi-cache-results (modi function)
  "Run on MODI the given FUNCTION.  Locate the module in a file.
Cache the output of function so next call may have faster access."
  (let (fass)
    (save-excursion  ;; Cache is buffer-local so can't avoid this.
      (bsv-modi-goto modi)
      (if (and (setq fass (assoc (list modi function)
				 bsv-modi-cache-list))
	       ;; Destroy caching when incorrect; Modified or file changed
	       (not (and bsv-cache-enabled
			 (or (equal (buffer-chars-modified-tick) (nth 1 fass))
			     (and bsv-modi-cache-preserve-tick
				  (<= bsv-modi-cache-preserve-tick  (nth 1 fass))
				  (equal  bsv-modi-cache-preserve-buffer (current-buffer))))
			 (equal (visited-file-modtime) (nth 2 fass)))))
	  (setq bsv-modi-cache-list nil
		fass nil))
      (cond (fass
	     ;; Return data from cache hit
	     (nth 3 fass))
	    (t
	     ;; Read from file
	     ;; Clear then restore any highlighting to make emacs19 happy
	     (let ((fontlocked (when (and (boundp 'font-lock-mode)
					  font-lock-mode)
				 (font-lock-mode 0)
				 t))
		   func-returns)
	       (setq func-returns (funcall function))
	       (when fontlocked (font-lock-mode t))
	       ;; Cache for next time
	       (setq bsv-modi-cache-list
		     (cons (list (list modi function)
				 (buffer-chars-modified-tick)
				 (visited-file-modtime)
				 func-returns)
			   bsv-modi-cache-list))
	       func-returns))))))

(defun bsv-modi-cache-add (modi function element sig-list)
  "Add function return results to the module cache.
Update MODI's cache for given FUNCTION so that the return ELEMENT of that
function now contains the additional SIG-LIST parameters."
  (let (fass)
    (save-excursion
      (bsv-modi-goto modi)
      (if (setq fass (assoc (list modi function)
			    bsv-modi-cache-list))
	  (let ((func-returns (nth 3 fass)))
	    (aset func-returns element
		  (append sig-list (aref func-returns element))))))))

(defmacro bsv-preserve-modi-cache (&rest body)
  "Execute the BODY forms, allowing cache preservation within BODY.
This means that changes to the buffer will not result in the cache being
flushed.  If the changes affect the modsig state, they must call the
modsig-cache-add-* function, else the results of later calls may be
incorrect.  Without this, changes are assumed to be adding/removing signals
and invalidating the cache."
  `(let ((bsv-modi-cache-preserve-tick (buffer-chars-modified-tick))
	 (bsv-modi-cache-preserve-buffer (current-buffer)))
     (progn ,@body)))


(defun bsv-signals-matching-enum (in-list enum)
  "Return all signals in IN-LIST matching the given ENUM."
  (let (out-list)
    (while in-list
      (if (equal (bsv-sig-enum (car in-list)) enum)
	  (setq out-list (cons (car in-list) out-list)))
      (setq in-list (cdr in-list)))
    ;; New scheme
    (let* ((enumvar (intern (concat "venum-" enum)))
	   (enumlist (and (boundp enumvar) (eval enumvar))))
      (while enumlist
	(add-to-list 'out-list (list (car enumlist)))
	(setq enumlist (cdr enumlist))))
    (nreverse out-list)))

(defun bsv-signals-matching-regexp (in-list regexp)
  "Return all signals in IN-LIST matching the given REGEXP, if non-nil."
  (if (or (not regexp) (equal regexp ""))
      in-list
    (let (out-list)
      (while in-list
	(if (string-match regexp (bsv-sig-name (car in-list)))
	    (setq out-list (cons (car in-list) out-list)))
	(setq in-list (cdr in-list)))
      (nreverse out-list))))

(defun bsv-signals-not-matching-regexp (in-list regexp)
  "Return all signals in IN-LIST not matching the given REGEXP, if non-nil."
  (if (or (not regexp) (equal regexp ""))
      in-list
    (let (out-list)
      (while in-list
	(if (not (string-match regexp (bsv-sig-name (car in-list))))
	    (setq out-list (cons (car in-list) out-list)))
	(setq in-list (cdr in-list)))
      (nreverse out-list))))

(defun bsv-signals-matching-dir-re (in-list decl-type regexp)
  "Return all signals in IN-LIST matching the given DECL-TYPE and REGEXP,
if non-nil."
  (if (or (not regexp) (equal regexp ""))
      in-list
    (let (out-list to-match)
      (while in-list
	;; Note bsv-insert-one-definition matches on this order
	(setq to-match (concat
			decl-type
			" " (bsv-sig-signed (car in-list))
			" " (bsv-sig-multidim (car in-list))
			(bsv-sig-bits (car in-list))))
	(if (string-match regexp to-match)
	    (setq out-list (cons (car in-list) out-list)))
	(setq in-list (cdr in-list)))
      (nreverse out-list))))

;; Combined
(defun bsv-decls-get-signals (decls)
  "Return all declared signals, excluding 'assign' statements."
  (append
   (bsv-decls-get-outputs decls)
   (bsv-decls-get-inouts decls)
   (bsv-decls-get-inputs decls)
   (bsv-decls-get-vars decls)
   (bsv-decls-get-consts decls)
   (bsv-decls-get-gparams decls)))

(defun bsv-decls-get-ports (decls)
  (append
   (bsv-decls-get-outputs decls)
   (bsv-decls-get-inouts decls)
   (bsv-decls-get-inputs decls)))

(defsubst bsv-modi-cache-add-outputs (modi sig-list)
  (bsv-modi-cache-add modi 'bsv-read-decls 0 sig-list))
(defsubst bsv-modi-cache-add-inouts (modi sig-list)
  (bsv-modi-cache-add modi 'bsv-read-decls 1 sig-list))
(defsubst bsv-modi-cache-add-inputs (modi sig-list)
  (bsv-modi-cache-add modi 'bsv-read-decls 2 sig-list))
(defsubst bsv-modi-cache-add-vars (modi sig-list)
  (bsv-modi-cache-add modi 'bsv-read-decls 3 sig-list))

(defun bsv-signals-from-signame (signame-list)
  "Return signals in standard form from SIGNAME-LIST, a simple list of signal names."
  (mapcar (function (lambda (name) (list name nil nil)))
	  signame-list))

;;
;; Auto creation utilities
;;

(defun bsv-auto-re-search-do (search-for func)
  "Search for the given auto text regexp SEARCH-FOR, and perform FUNC where it occurs."
  (goto-char (point-min))
  (while (bsv-re-search-forward-quick search-for nil t)
    (funcall func)))

(defun bsv-insert-one-definition (sig type indent-pt)
  "Print out a definition for SIG of the given TYPE,
with appropriate INDENT-PT indentation."
  (indent-to indent-pt)
  ;; Note bsv-signals-matching-dir-re matches on this order
  (insert type)
  (when (bsv-sig-modport sig)
    (insert "." (bsv-sig-modport sig)))
  (when (bsv-sig-signed sig)
    (insert " " (bsv-sig-signed sig)))
  (when (bsv-sig-multidim sig)
    (insert " " (bsv-sig-multidim-string sig)))
  (when (bsv-sig-bits sig)
    (insert " " (bsv-sig-bits sig)))
  (indent-to (max 24 (+ indent-pt 16)))
  (unless (= (char-syntax (preceding-char)) ?\  )
    (insert " "))  ; Need space between "]name" if indent-to did nothing
  (insert (bsv-sig-name sig))
  (when (bsv-sig-memory sig)
    (insert " " (bsv-sig-memory sig))))

(defun bsv-insert-definition (modi sigs direction indent-pt v2k &optional dont-sort)
  "Print out a definition for MODI's list of SIGS of the given DIRECTION,
with appropriate INDENT-PT indentation.  If V2K, use BSV 2001 I/O
format.  Sort unless DONT-SORT.  DIRECTION is normally wire/reg/output.
When MODI is non-null, also add to modi-cache, for tracking."
  (when modi
    (cond ((equal direction "wire")
	   (bsv-modi-cache-add-vars modi sigs))
	  ((equal direction "reg")
	   (bsv-modi-cache-add-vars modi sigs))
	  ((equal direction "output")
	   (bsv-modi-cache-add-outputs modi sigs)
	   (when bsv-auto-declare-nettype
	     (bsv-modi-cache-add-vars modi sigs)))
	  ((equal direction "input")
	   (bsv-modi-cache-add-inputs modi sigs)
	   (when bsv-auto-declare-nettype
	     (bsv-modi-cache-add-vars modi sigs)))
	  ((equal direction "inout")
	   (bsv-modi-cache-add-inouts modi sigs)
	   (when bsv-auto-declare-nettype
	     (bsv-modi-cache-add-vars modi sigs)))
	  ((equal direction "interface"))
	  (t
	   (error "Unsupported bsv-insert-definition direction: %s" direction))))
  (or dont-sort
      (setq sigs (sort (copy-alist sigs) `bsv-signals-sort-compare)))
  (while sigs
    (let ((sig (car sigs)))
      (bsv-insert-one-definition
       sig
       ;; Want "type x" or "output type x", not "wire type x"
       (cond ((or (bsv-sig-type sig)
		  bsv-auto-wire-type)
	      (concat
	       (when (member direction '("input" "output" "inout"))
		 (concat direction " "))
	       (or (bsv-sig-type sig)
		  bsv-auto-wire-type)))
	     ((and bsv-auto-declare-nettype
		   (member direction '("input" "output" "inout")))
	      (concat direction " " bsv-auto-declare-nettype))
	     (t
	      direction))
       indent-pt)
      (insert (if v2k "," ";"))
      (if (or (not (bsv-sig-comment sig))
	      (equal "" (bsv-sig-comment sig)))
	  (insert "\n")
	(indent-to (max 48 (+ indent-pt 40)))
	(bsv-insert "// " (bsv-sig-comment sig) "\n"))
      (setq sigs (cdr sigs)))))

(eval-when-compile
  (if (not (boundp 'indent-pt))
      (defvar indent-pt nil "Local used by insert-indent")))

(defun bsv-insert-indent (&rest stuff)
  "Indent to position stored in local `indent-pt' variable, then insert STUFF.
Presumes that any newlines end a list element."
  (let ((need-indent t))
    (while stuff
      (if need-indent (indent-to indent-pt))
      (setq need-indent nil)
      (bsv-insert (car stuff))
      (setq need-indent (string-match "\n$" (car stuff))
	    stuff (cdr stuff)))))
;;(let ((indent-pt 10)) (bsv-insert-indent "hello\n" "addon" "there\n"))

(defun bsv-repair-open-comma ()
  "Insert comma if previous argument is other than a open parenthesis or endif."
  ;; We can't just search backward for ) as it might be inside another expression.
  ;; Also want "`ifdef X   input foo   `endif" to just leave things to the human to deal with
  (save-excursion
    (bsv-backward-syntactic-ws-quick)
    (when (and (not (save-excursion ;; Not beginning (, or existing ,
		      (backward-char 1)
		      (looking-at "[(,]")))
	       (not (save-excursion ;; Not `endif, or user define
		      (backward-char 1)
		      (skip-chars-backward "[a-zA-Z0-9_`]")
		      (looking-at "`"))))
      (insert ","))))

(defun bsv-repair-close-comma ()
  "If point is at a comma followed by a close parenthesis, fix it.
This repairs those mis-inserted by a AUTOARG."
  ;; It would be much nicer if BSV allowed extra commas like Perl does!
  (save-excursion
    (bsv-forward-close-paren)
    (backward-char 1)
    (bsv-backward-syntactic-ws-quick)
    (backward-char 1)
    (when (looking-at ",")
      (delete-char 1))))

(defun bsv-get-list (start end)
  "Return the elements of a comma separated list between START and END."
  (interactive)
  (let ((my-list (list))
	my-string)
    (save-excursion
      (while (< (point) end)
	(when (re-search-forward "\\([^,{]+\\)" end t)
	  (setq my-string (bsv-string-remove-spaces (match-string 1)))
	  (setq my-list (nconc my-list (list my-string) ))
	  (goto-char (match-end 0))))
      my-list)))

(defun bsv-make-width-expression (range-exp)
  "Return an expression calculating the length of a range [x:y] in RANGE-EXP."
  ;; strip off the []
  (cond ((not range-exp)
	 "1")
	(t
	 (if (string-match "^\\[\\(.*\\)\\]$" range-exp)
	     (setq range-exp (match-string 1 range-exp)))
	 (cond ((not range-exp)
		"1")
	       ;; [#:#] We can compute a numeric result
	       ((string-match "^\\s *\\([0-9]+\\)\\s *:\\s *\\([0-9]+\\)\\s *$"
			      range-exp)
		(int-to-string
		 (1+ (abs (- (string-to-number (match-string 1 range-exp))
			     (string-to-number (match-string 2 range-exp)))))))
	       ;; [PARAM-1:0] can just return PARAM
	       ((string-match "^\\s *\\([a-zA-Z_][a-zA-Z0-9_]*\\)\\s *-\\s *1\\s *:\\s *0\\s *$" range-exp)
		(match-string 1 range-exp))
	       ;; [arbitrary] need math
	       ((string-match "^\\(.*\\)\\s *:\\s *\\(.*\\)\\s *$" range-exp)
		(concat "(1+(" (match-string 1 range-exp) ")"
			(if (equal "0" (match-string 2 range-exp))
			    ""  ;; Don't bother with -(0)
			  (concat "-(" (match-string 2 range-exp) ")"))
			")"))
	       (t nil)))))
;;(bsv-make-width-expression "`A:`B")

(defun bsv-simplify-range-expression (expr)
  "Return a simplified range expression with constants eliminated from EXPR."
  ;; Note this is always called with brackets; ie [z] or [z:z]
  (if (not (string-match "[---+*()]" expr))
      expr ;; short-circuit
    (let ((out expr)
	  (last-pass ""))
      (while (not (equal last-pass out))
	(setq last-pass out)
	;; Prefix regexp needs beginning of match, or some symbol of
	;; lesser or equal precedence.  We assume the [:]'s exist in expr.
	;; Ditto the end.
	(while (string-match
		(concat "\\([[({:*+-]\\)"  ; - must be last
			"(\\<\\([0-9A-Za-z_]+\\))"
			"\\([])}:*+-]\\)")
		out)
	  (setq out (replace-match "\\1\\2\\3" nil nil out)))
	;; For precedence do * before +/-
	(while (string-match
		(concat "\\([[({:*+-]\\)"
			"\\([0-9]+\\)\\s *\\([*]\\)\\s *\\([0-9]+\\)"
			"\\([])}:*+-]\\)")
		out)
	  (setq out (replace-match
		     (concat (match-string 1 out)
			     (int-to-string (* (string-to-number (match-string 2 out))
					       (string-to-number (match-string 4 out))))
			     (match-string 5 out))
		     nil nil out)))
	(while (string-match
		(concat "\\([[({:+-]\\)" ; No * here as higher prec
			"\\([0-9]+\\)\\s *\\([---+]\\)\\s *\\([0-9]+\\)"
			"\\([])}:+-]\\)")
		out)
	  (let ((pre (match-string 1 out))
		(lhs (string-to-number (match-string 2 out)))
		(rhs (string-to-number (match-string 4 out)))
		(post (match-string 5 out))
		val)
	    (when (equal pre "-")
	      (setq lhs (- lhs)))
	    (setq val (if (equal (match-string 3 out) "-")
			  (- lhs rhs)
			(+ lhs rhs))
		  out (replace-match
		       (concat (if (and (equal pre "-")
					(< val 0))
				   "" ;; Not "--20" but just "-20"
				 pre)
			       (int-to-string val)
			       post)
		       nil nil out)) )))
      out)))
;;(bsv-simplify-range-expression "[1:3]") ;; 1
;;(bsv-simplify-range-expression "[(1):3]") ;; 1
;;(bsv-simplify-range-expression "[(((16)+1)+1+(1+1))]")  ;;20
;;(bsv-simplify-range-expression "[(2*3+6*7)]") ;; 48
;;(bsv-simplify-range-expression "[(FOO*4-1*2)]") ;; FOO*4-2
;;(bsv-simplify-range-expression "[(FOO*4+1-1)]") ;; FOO*4+0
;;(bsv-simplify-range-expression "[(func(BAR))]") ;; func(BAR)
;;(bsv-simplify-range-expression "[FOO-1+1-1+1]") ;; FOO-0

(defun bsv-typedef-name-p (variable-name)
  "Return true if the VARIABLE-NAME is a type definition."
  (when bsv-typedef-regexp
    (string-match bsv-typedef-regexp variable-name)))

;;
;; Auto deletion
;;

(defun bsv-delete-autos-lined ()
  "Delete autos that occupy multiple lines, between begin and end comments."
  ;; The newline must not have a comment property, so we must
  ;; delete the end auto's newline, not the first newline
  (forward-line 1)
  (let ((pt (point)))
    (when (and
	   (looking-at "\\s-*// Beginning")
	   (search-forward "// End of automatic" nil t))
      ;; End exists
      (end-of-line)
      (forward-line 1)
      (delete-region pt (point)))))

(defun bsv-delete-empty-auto-pair ()
  "Delete begin/end auto pair at point, if empty."
  (forward-line 0)
  (when (looking-at (concat "\\s-*// Beginning of automatic.*\n"
			    "\\s-*// End of automatics\n"))
    (delete-region (point) (save-excursion (forward-line 2) (point)))))

(defun bsv-forward-close-paren ()
  "Find the close parenthesis that match the current point.
Ignore other close parenthesis with matching open parens."
  (let ((parens 1))
    (while (> parens 0)
      (unless (bsv-re-search-forward-quick "[()]" nil t)
	(error "%s: Mismatching ()" (bsv-point-text)))
      (cond ((= (preceding-char) ?\( )
	     (setq parens (1+ parens)))
	    ((= (preceding-char) ?\) )
	     (setq parens (1- parens)))))))

(defun bsv-backward-open-paren ()
  "Find the open parenthesis that match the current point.
Ignore other open parenthesis with matching close parens."
  (let ((parens 1))
    (while (> parens 0)
      (unless (bsv-re-search-backward-quick "[()]" nil t)
	(error "%s: Mismatching ()" (bsv-point-text)))
      (cond ((= (following-char) ?\) )
	     (setq parens (1+ parens)))
	    ((= (following-char) ?\( )
	     (setq parens (1- parens)))))))

(defun bsv-backward-open-bracket ()
  "Find the open bracket that match the current point.
Ignore other open bracket with matching close bracket."
  (let ((parens 1))
    (while (> parens 0)
      (unless (bsv-re-search-backward-quick "[][]" nil t)
	(error "%s: Mismatching []" (bsv-point-text)))
      (cond ((= (following-char) ?\] )
	     (setq parens (1+ parens)))
	    ((= (following-char) ?\[ )
	     (setq parens (1- parens)))))))

(defun bsv-delete-to-paren ()
  "Delete the automatic inst/sense/arg created by autos.
Deletion stops at the matching end parenthesis, outside comments."
  (delete-region (point)
		 (save-excursion
		   (bsv-backward-open-paren)
		   (bsv-forward-sexp-ign-cmt 1)   ;; Moves to paren that closes argdecl's
		   (backward-char 1)
		   (point))))

(defun bsv-auto-star-safe ()
  "Return if a .* AUTOINST is safe to delete or expand.
It was created by the AUTOS themselves, or by the user."
  (and bsv-auto-star-expand
       (looking-at
	(concat "[ \t\n\f,]*\\([)]\\|// " bsv-inst-comment-re "\\)"))))

(defun bsv-delete-auto-star-all ()
  "Delete a .* AUTOINST, if it is safe."
  (when (bsv-auto-star-safe)
    (bsv-delete-to-paren)))

(defun bsv-delete-auto-star-implicit ()
  "Delete all .* implicit connections created by `bsv-auto-star'.
This function will be called automatically at save unless
`bsv-auto-star-save' is set, any non-templated expanded pins will be
removed."
  (interactive)
  (let (paren-pt indent have-close-paren)
    (save-excursion
      (goto-char (point-min))
      ;; We need to match these even outside of comments.
      ;; For reasonable performance, we don't check if inside comments, sorry.
      (while (re-search-forward "// Implicit \\.\\*" nil t)
	(setq paren-pt (point))
	(beginning-of-line)
	(setq have-close-paren
	      (save-excursion
		(when (search-forward ");" paren-pt t)
		  (setq indent (current-indentation))
		  t)))
	(delete-region (point) (+ 1 paren-pt))  ; Nuke line incl CR
	(when have-close-paren
	  ;; Delete extra commentary
	  (save-excursion
	    (while (progn
		     (forward-line -1)
		     (looking-at (concat "\\s *//\\s *" bsv-inst-comment-re "\n")))
	      (delete-region (match-beginning 0) (match-end 0))))
	  ;; If it is simple, we can put the ); on the same line as the last text
	  (let ((rtn-pt (point)))
	    (save-excursion
	      (while (progn (backward-char 1)
			    (looking-at "[ \t\n\f]")))
	      (when (looking-at ",")
		(delete-region (+ 1 (point)) rtn-pt))))
	  (when (bolp)
	    (indent-to indent))
	  (insert ");\n")
	  ;; Still need to kill final comma - always is one as we put one after the .*
	  (re-search-backward ",")
	  (delete-char 1))))))

(defun bsv-delete-auto ()
  "Delete the automatic outputs, regs, and wires created by \\[bsv-auto].
Use \\[bsv-auto] to re-insert the updated AUTOs.

The hooks `bsv-before-delete-auto-hook' and `bsv-delete-auto-hook' are
called before and after this function, respectively."
  (interactive)
  (save-excursion
    (if (buffer-file-name)
	(find-file-noselect (buffer-file-name)))	;; To check we have latest version
    (bsv-save-no-change-functions
     (bsv-save-scan-cache
      ;; Allow user to customize
      (bsv-run-hooks 'bsv-before-delete-auto-hook)

      ;; Remove those that have multi-line insertions, possibly with parameters
      ;; We allow anything beginning with AUTO, so that users can add their own
      ;; patterns
      (bsv-auto-re-search-do
       (concat "/\\*AUTO[A-Za-z0-9_]+"
	       ;; Optional parens or quoted parameter or .* for (((...)))
	       "\\(\\|([^)]*)\\|(\"[^\"]*\")\\).*?"
	       "\\*/")
       'bsv-delete-autos-lined)
      ;; Remove those that are in parenthesis
      (bsv-auto-re-search-do
       (concat "/\\*"
	       (eval-when-compile
		 (bsv-regexp-words
		  `("AS" "AUTOARG" "AUTOCONCATWIDTH" "AUTOINST" "AUTOINSTPARAM"
		    "AUTOSENSE")))
	       "\\*/")
       'bsv-delete-to-paren)
      ;; Do .* instantiations, but avoid removing any user pins by looking for our magic comments
      (bsv-auto-re-search-do "\\.\\*"
				 'bsv-delete-auto-star-all)
      ;; Remove template comments ... anywhere in case was pasted after AUTOINST removed
      (goto-char (point-min))
      (while (re-search-forward "\\s-*// \\(Templated\\|Implicit \\.\\*\\)\\([ \tLT0-9]*\\| LHS: .*\\)?$" nil t)
	(replace-match ""))

      ;; Final customize
      (bsv-run-hooks 'bsv-delete-auto-hook)))))

;;
;; Auto inject
;;

(defun bsv-inject-auto ()
  "Examine legacy non-AUTO code and insert AUTOs in appropriate places.

Any always @ blocks with sensitivity lists that match computed lists will
be replaced with /*AS*/ comments.

Any cells will get /*AUTOINST*/ added to the end of the pin list.
Pins with have identical names will be deleted.

Argument lists will not be deleted, /*AUTOARG*/ will only be inserted to
support adding new ports.  You may wish to delete older ports yourself.

For example:

	module ExampInject (i, o);
	  input i;
	  input j;
	  output o;
	  always @ (i or j)
	     o = i | j;
	  InstModule instName
            (.foobar(baz),
	     j(j));
	endmodule

Typing \\[bsv-inject-auto] will make this into:

	module ExampInject (i, o/*AUTOARG*/
	  // Inputs
	  j);
	  input i;
	  output o;
	  always @ (/*AS*/i or j)
	     o = i | j;
	  InstModule instName
            (.foobar(baz),
	     /*AUTOINST*/
	     // Outputs
	     j(j));
	endmodule"
  (interactive)
  (bsv-auto t))

(defun bsv-inject-arg ()
  "Inject AUTOARG into new code.  See `bsv-inject-auto'."
  ;; Presume one module per file.
  (save-excursion
    (goto-char (point-min))
    (while (bsv-re-search-forward-quick "\\<module\\>" nil t)
      (let ((endmodp (save-excursion
		       (bsv-re-search-forward-quick "\\<endmodule\\>" nil t)
		       (point))))
	;; See if there's already a comment .. inside a comment so not bsv-re-search
	(when (not (re-search-forward "/\\*AUTOARG\\*/" endmodp t))
	  (bsv-re-search-forward-quick ";" nil t)
	  (backward-char 1)
	  (bsv-backward-syntactic-ws-quick)
	  (backward-char 1) ; Moves to paren that closes argdecl's
	  (when (looking-at ")")
	    (bsv-insert "/*AUTOARG*/")))))))

(defun bsv-inject-sense ()
  "Inject AUTOSENSE into new code.  See `bsv-inject-auto'."
  (save-excursion
    (goto-char (point-min))
    (while (bsv-re-search-forward-quick "\\<always\\s *@\\s *(" nil t)
      (let* ((start-pt (point))
	     (modi (bsv-modi-current))
	     (moddecls (bsv-modi-get-decls modi))
	     pre-sigs
	     got-sigs)
	(backward-char 1)
	(bsv-forward-sexp-ign-cmt 1)
	(backward-char 1) ;; End )
	(when (not (bsv-re-search-backward-quick "/\\*\\(AUTOSENSE\\|AS\\)\\*/" start-pt t))
	  (setq pre-sigs (bsv-signals-from-signame
			  (bsv-read-signals start-pt (point)))
		got-sigs (bsv-auto-sense-sigs moddecls nil))
	  (when (not (or (bsv-signals-not-in pre-sigs got-sigs)  ; Both are equal?
			 (bsv-signals-not-in got-sigs pre-sigs)))
	    (delete-region start-pt (point))
	    (bsv-insert "/*AS*/")))))))

(defun bsv-inject-inst ()
  "Inject AUTOINST into new code.  See `bsv-inject-auto'."
  (save-excursion
    (goto-char (point-min))
    ;; It's hard to distinguish modules; we'll instead search for pins.
    (while (bsv-re-search-forward-quick "\\.\\s *[a-zA-Z0-9`_\$]+\\s *(\\s *[a-zA-Z0-9`_\$]+\\s *)" nil t)
      (bsv-backward-open-paren) ;; Inst start
      (cond
       ((= (preceding-char) ?\#)  ;; #(...) parameter section, not pin.  Skip.
	(forward-char 1)
	(bsv-forward-close-paren)) ;; Parameters done
       (t
	(forward-char 1)
	(let ((indent-pt (+ (current-column)))
	      (end-pt (save-excursion (bsv-forward-close-paren) (point))))
	  (cond ((bsv-re-search-forward-quick "\\(/\\*AUTOINST\\*/\\|\\.\\*\\)" end-pt t)
		 (goto-char end-pt)) ;; Already there, continue search with next instance
		(t
		 ;; Delete identical interconnect
		 (let ((case-fold-search nil))  ;; So we don't convert upper-to-lower, etc
		   (while (bsv-re-search-forward-quick "\\.\\s *\\([a-zA-Z0-9`_\$]+\\)*\\s *(\\s *\\1\\s *)\\s *" end-pt t)
		     (delete-region (match-beginning 0) (match-end 0))
		     (setq end-pt (- end-pt (- (match-end 0) (match-beginning 0)))) ;; Keep it correct
		     (while (or (looking-at "[ \t\n\f,]+")
				(looking-at "//[^\n]*"))
		       (delete-region (match-beginning 0) (match-end 0))
		       (setq end-pt (- end-pt (- (match-end 0) (match-beginning 0)))))))
		 (bsv-forward-close-paren)
		 (backward-char 1)
		 ;; Not bsv-re-search, as we don't want to strip comments
		 (while (re-search-backward "[ \t\n\f]+" (- (point) 1) t)
		   (delete-region (match-beginning 0) (match-end 0)))
		 (bsv-insert "\n")
		 (bsv-insert-indent "/*AUTOINST*/")))))))))

;;
;; Auto diff
;;

(defun bsv-diff-buffers-p (b1 b2 &optional whitespace)
  "Return nil if buffers B1 and B2 have same contents.
Else, return point in B1 that first mismatches.
If optional WHITESPACE true, ignore whitespace."
  (save-excursion
    (let* ((case-fold-search nil)  ;; compare-buffer-substrings cares
	   (p1 (with-current-buffer b1 (goto-char (point-min))))
	   (p2 (with-current-buffer b2 (goto-char (point-min))))
	   (maxp1 (with-current-buffer b1 (point-max)))
	   (maxp2 (with-current-buffer b2 (point-max)))
	   (op1 -1) (op2 -1)
	   progress size)
      (while (not (and (eq p1 op1) (eq p2 op2)))
	;; If both windows have whitespace optionally skip over it.
	(when whitespace
	  ;; skip-syntax-* doesn't count \n
	  (with-current-buffer b1
	    (goto-char p1)
	    (skip-chars-forward " \t\n\r\f\v")
	    (setq p1 (point)))
	  (with-current-buffer b2
	    (goto-char p2)
	    (skip-chars-forward " \t\n\r\f\v")
	    (setq p2 (point))))
	(setq size (min (- maxp1 p1) (- maxp2 p2)))
	(setq progress (compare-buffer-substrings b2 p2 (+ size p2)
						  b1 p1 (+ size p1)))
	(setq progress (if (zerop progress) size (1- (abs progress))))
	(setq op1 p1  op2 p2
	      p1 (+ p1 progress)
	      p2 (+ p2 progress)))
      ;; Return value
      (if (and (eq p1 maxp1) (eq p2 maxp2))
	  nil p1))))

(defun bsv-diff-file-with-buffer (f1 b2 &optional whitespace show)
  "View the differences between file F1 and buffer B2.
This requires the external program `diff-command' to be in your `exec-path',
and uses `diff-switches' in which you may want to have \"-u\" flag.
Ignores WHITESPACE if t, and writes output to stdout if SHOW."
  ;; Similar to `diff-buffer-with-file' but works on XEmacs, and doesn't
  ;; call `diff' as `diff' has different calling semantics on different
  ;; versions of Emacs.
  (if (not (file-exists-p f1))
      (message "Buffer %s has no associated file on disc" (buffer-name b2))
    (with-temp-buffer "*BSV-Diff*"
      (let ((outbuf (current-buffer))
	    (f2 (make-temp-file "vm-diff-auto-")))
	(unwind-protect
	    (progn
	      (with-current-buffer b2
		(save-restriction
		  (widen)
		  (write-region (point-min) (point-max) f2 nil 'nomessage)))
	      (call-process diff-command nil outbuf t
			    diff-switches ;; User may want -u in diff-switches
			    (if whitespace "-b" "")
			    f1 f2)
	      ;; Print out results.  Alternatively we could have call-processed
	      ;; ourself, but this way we can reuse diff switches
	      (when show
		(with-current-buffer outbuf (message "%s" (buffer-string))))))
	(sit-for 0)
	(when (file-exists-p f2)
	  (delete-file f2))))))

(defun bsv-diff-report (b1 b2 diffpt)
  "Report differences detected with `bsv-diff-auto'.
Differences are between buffers B1 and B2, starting at point
DIFFPT.  This function is called via `bsv-diff-function'."
  (let ((name1 (with-current-buffer b1 (buffer-file-name))))
    (message "%%Warning: %s:%d: Difference in AUTO expansion found"
	     name1 (with-current-buffer b1 (1+ (count-lines (point-min) (point)))))
    (cond (noninteractive
	   (bsv-diff-file-with-buffer name1 b2 t t))
	  (t
	   (ediff-buffers b1 b2)))))

(defun bsv-diff-auto ()
  "Expand AUTOs in a temporary buffer and indicate any changes.
Whitespace differences are ignored to determine identicalness, but
once a difference is detected, whitespace differences may be shown.

To call this from the command line, see \\[bsv-batch-diff-auto].

The action on differences is selected with
`bsv-diff-function'.  The default is `bsv-diff-report'
which will report an error and run `ediff' in interactive mode,
or `diff' in batch mode."
  (interactive)
  (let ((b1 (current-buffer)) b2 diffpt
	(name1 (buffer-file-name))
	(newname "*BSV-Diff*"))
    (save-excursion
      (when (get-buffer newname)
	(kill-buffer newname))
      (setq b2 (let (buffer-file-name)  ;; Else clone is upset
		 (clone-buffer newname)))
      (with-current-buffer b2
	;; auto requires the filename, but can't have same filename in two
	;; buffers; so override both b1 and b2's names
	(let ((buffer-file-name name1))
	  (unwind-protect
	      (progn
		(with-current-buffer b1 (setq buffer-file-name nil))
		(bsv-auto)
		(when (not bsv-auto-star-save)
		  (bsv-delete-auto-star-implicit)))
	    ;; Restore name if unwind
	    (with-current-buffer b1 (setq buffer-file-name name1)))))
      ;;
      (setq diffpt (bsv-diff-buffers-p b1 b2 t))
      (cond ((not diffpt)
	     (unless noninteractive (message "AUTO expansion identical"))
	     (kill-buffer newname)) ;; Nice to cleanup after oneself
	    (t
	     (funcall bsv-diff-function b1 b2 diffpt)))
      ;; Return result of compare
      diffpt)))


;;
;; Auto save
;;

(defun bsv-auto-save-check ()
  "On saving see if we need auto update."
  (cond ((not bsv-auto-save-policy)) ; disabled
	((not (save-excursion
		(save-match-data
		  (let ((case-fold-search nil))
		    (goto-char (point-min))
		    (re-search-forward "AUTO" nil t))))))
	((eq bsv-auto-save-policy 'force)
	 (bsv-auto))
	((not (buffer-modified-p)))
	((eq bsv-auto-update-tick (buffer-chars-modified-tick))) ; up-to-date
	((eq bsv-auto-save-policy 'detect)
	 (bsv-auto))
	(t
	 (when (yes-or-no-p "AUTO statements not recomputed, do it now? ")
	   (bsv-auto))
	 ;; Don't ask again if didn't update
	 (set (make-local-variable 'bsv-auto-update-tick) (buffer-chars-modified-tick))))
  (when (not bsv-auto-star-save)
    (bsv-delete-auto-star-implicit))
  nil)	;; Always return nil -- we don't write the file ourselves

(defun bsv-auto-read-locals ()
  "Return file local variable segment at bottom of file."
  (save-excursion
    (goto-char (point-max))
    (if (re-search-backward "Local Variables:" nil t)
	(buffer-substring-no-properties (point) (point-max))
      "")))

(defun bsv-auto-reeval-locals (&optional force)
  "Read file local variable segment at bottom of file if it has changed.
If FORCE, always reread it."
  (let ((curlocal (bsv-auto-read-locals)))
    (when (or force (not (equal bsv-auto-last-file-locals curlocal)))
      (set (make-local-variable 'bsv-auto-last-file-locals) curlocal)
      ;; Note this may cause this function to be recursively invoked,
      ;; because hack-local-variables may call (bsv-mode)
      ;; The above when statement will prevent it from recursing forever.
      (hack-local-variables)
      t)))

;;
;; Auto creation
;;

(defun bsv-auto-arg-ports (sigs message indent-pt)
  "Print a list of ports for a AUTOINST.
Takes SIGS list, adds MESSAGE to front and inserts each at INDENT-PT."
  (when sigs
    (when bsv-auto-arg-sort
      (setq sigs (sort (copy-alist sigs) `bsv-signals-sort-compare)))
    (insert "\n")
    (indent-to indent-pt)
    (insert message)
    (insert "\n")
    (let ((space ""))
      (indent-to indent-pt)
      (while sigs
	(cond ((> (+ 2 (current-column) (length (bsv-sig-name (car sigs)))) fill-column)
	       (insert "\n")
	       (indent-to indent-pt))
	      (t (insert space)))
	(insert (bsv-sig-name (car sigs)) ",")
	(setq sigs (cdr sigs)
	      space " ")))))

(defun bsv-auto-arg ()
  "Expand AUTOARG statements.
Replace the argument declarations at the beginning of the
module with ones automatically derived from input and output
statements.  This can be dangerous if the module is instantiated
using position-based connections, so use only name-based when
instantiating the resulting module.  Long lines are split based
on the `fill-column', see \\[set-fill-column].

Limitations:
  Concatenation and outputting partial buses is not supported.

  Typedefs must match `bsv-typedef-regexp', which is disabled by default.

For example:

	module ExampArg (/*AUTOARG*/);
	  input i;
	  output o;
	endmodule

Typing \\[bsv-auto] will make this into:

	module ExampArg (/*AUTOARG*/
	  // Outputs
	  o,
	  // Inputs
	  i
	);
	  input i;
	  output o;
	endmodule

The argument declarations may be printed in declaration order to best suit
order based instantiations, or alphabetically, based on the
`bsv-auto-arg-sort' variable.

Any ports declared between the ( and /*AUTOARG*/ are presumed to be
predeclared and are not redeclared by AUTOARG.  AUTOARG will make a
conservative guess on adding a comma for the first signal, if you have
any ifdefs or complicated expressions before the AUTOARG you will need
to choose the comma yourself.

Avoid declaring ports manually, as it makes code harder to maintain."
  (save-excursion
    (let* ((modi (bsv-modi-current))
	   (moddecls (bsv-modi-get-decls modi))
	   (skip-pins (aref (bsv-read-arg-pins) 0)))
      (bsv-repair-open-comma)
      (bsv-auto-arg-ports (bsv-signals-not-in
			       (bsv-decls-get-outputs moddecls)
			       skip-pins)
			      "// Outputs"
			      bsv-indent-level-declaration)
      (bsv-auto-arg-ports (bsv-signals-not-in
			       (bsv-decls-get-inouts moddecls)
			       skip-pins)
			      "// Inouts"
			      bsv-indent-level-declaration)
      (bsv-auto-arg-ports (bsv-signals-not-in
			       (bsv-decls-get-inputs moddecls)
			       skip-pins)
			      "// Inputs"
			      bsv-indent-level-declaration)
      (bsv-repair-close-comma)
      (unless (eq (char-before) ?/ )
	(insert "\n"))
      (indent-to bsv-indent-level-declaration))))

(defun bsv-auto-inst-port-map (port-st)
  nil)

(defvar vl-cell-type nil "See `bsv-auto-inst'.") ; Prevent compile warning
(defvar vl-cell-name nil "See `bsv-auto-inst'.") ; Prevent compile warning
(defvar vl-modport   nil "See `bsv-auto-inst'.") ; Prevent compile warning
(defvar vl-name  nil "See `bsv-auto-inst'.") ; Prevent compile warning
(defvar vl-width nil "See `bsv-auto-inst'.") ; Prevent compile warning
(defvar vl-dir   nil "See `bsv-auto-inst'.") ; Prevent compile warning
(defvar vl-bits  nil "See `bsv-auto-inst'.") ; Prevent compile warning
(defvar vl-mbits nil "See `bsv-auto-inst'.") ; Prevent compile warning

(defun bsv-auto-inst-port (port-st indent-pt tpl-list tpl-num for-star par-values)
  "Print out a instantiation connection for this PORT-ST.
Insert to INDENT-PT, use template TPL-LIST.
@ are instantiation numbers, replaced with TPL-NUM.
@\"(expression @)\" are evaluated, with @ as a variable.
If FOR-STAR add comment it is a .* expansion.
If PAR-VALUES replace final strings with these parameter values."
  (let* ((port (bsv-sig-name port-st))
	 (tpl-ass (or (assoc port (car tpl-list))
		      (bsv-auto-inst-port-map port-st)))
	 ;; vl-* are documented for user use
	 (vl-name (bsv-sig-name port-st))
	 (vl-width (bsv-sig-width port-st))
	 (vl-modport (bsv-sig-modport port-st))
	 (vl-mbits (if (bsv-sig-multidim port-st)
                       (bsv-sig-multidim-string port-st) ""))
	 (vl-bits (if (or bsv-auto-inst-vector
			  (not (assoc port vector-skip-list))
			  (not (equal (bsv-sig-bits port-st)
				      (bsv-sig-bits (assoc port vector-skip-list)))))
		      (or (bsv-sig-bits port-st) "")
		    ""))
	 (case-fold-search nil)
	 (check-values par-values)
	 tpl-net)
    ;; Replace parameters in bit-width
    (when (and check-values
	       (not (equal vl-bits "")))
      (while check-values
	(setq vl-bits (bsv-string-replace-matches
		       (concat "\\<" (nth 0 (car check-values)) "\\>")
		       (concat "(" (nth 1 (car check-values)) ")")
		       t t vl-bits)
	      vl-mbits (bsv-string-replace-matches
			(concat "\\<" (nth 0 (car check-values)) "\\>")
			(concat "(" (nth 1 (car check-values)) ")")
			t t vl-mbits)
	      check-values (cdr check-values)))
      (setq vl-bits (bsv-simplify-range-expression vl-bits)
	    vl-mbits (bsv-simplify-range-expression vl-mbits)
	    vl-width (bsv-make-width-expression vl-bits))) ; Not in the loop for speed
    ;; Default net value if not found
    (setq tpl-net (concat port
			  (if vl-modport (concat "." vl-modport) "")
			  (if (bsv-sig-multidim port-st)
			      (concat "/*" vl-mbits vl-bits "*/")
			    (concat vl-bits))))
    ;; Find template
    (cond (tpl-ass	    ; Template of exact port name
	   (setq tpl-net (nth 1 tpl-ass)))
	  ((nth 1 tpl-list) ; Wildcards in template, search them
	   (let ((wildcards (nth 1 tpl-list)))
	     (while wildcards
	       (when (string-match (nth 0 (car wildcards)) port)
		 (setq tpl-ass (car wildcards)  ; so allow @ parsing
		       tpl-net (replace-match (nth 1 (car wildcards))
					      t nil port)))
	       (setq wildcards (cdr wildcards))))))
    ;; Parse Templated variable
    (when tpl-ass
      ;; Evaluate @"(lispcode)"
      (when (string-match "@\".*[^\\]\"" tpl-net)
	(while (string-match "@\"\\(\\([^\\\"]*\\(\\\\.\\)*\\)*\\)\"" tpl-net)
	  (setq tpl-net
		(concat
		 (substring tpl-net 0 (match-beginning 0))
		 (save-match-data
		   (let* ((expr (match-string 1 tpl-net))
			  (value
			   (progn
			     (setq expr (bsv-string-replace-matches "\\\\\"" "\"" nil nil expr))
			     (setq expr (bsv-string-replace-matches "@" tpl-num nil nil expr))
			     (prin1 (eval (car (read-from-string expr)))
				    (lambda (ch) ())))))
		     (if (numberp value) (setq value (number-to-string value)))
		     value))
		 (substring tpl-net (match-end 0))))))
      ;; Replace @ and [] magic variables in final output
      (setq tpl-net (bsv-string-replace-matches "@" tpl-num nil nil tpl-net))
      (setq tpl-net (bsv-string-replace-matches "\\[\\]" vl-bits nil nil tpl-net)))
    ;; Insert it
    (indent-to indent-pt)
    (insert "." port)
    (unless (and bsv-auto-inst-dot-name
		 (equal port tpl-net))
      (indent-to bsv-auto-inst-column)
      (insert "(" tpl-net ")"))
    (insert ",")
    (cond (tpl-ass
	   (indent-to (+ (if (< bsv-auto-inst-column 48) 24 16)
			 bsv-auto-inst-column))
	   ;; bsv-insert requires the complete comment in one call - including the newline
	   (cond ((equal bsv-auto-inst-template-numbers `lhs)
		  (bsv-insert " // Templated"
				  " LHS: " (nth 0 tpl-ass)
				  "\n"))
		 (bsv-auto-inst-template-numbers
		  (bsv-insert " // Templated"
				  " T" (int-to-string (nth 2 tpl-ass))
				  " L" (int-to-string (nth 3 tpl-ass))
				  "\n"))
		 (t
		  (bsv-insert " // Templated\n"))))
	  (for-star
	   (indent-to (+ (if (< bsv-auto-inst-column 48) 24 16)
			 bsv-auto-inst-column))
	   (bsv-insert " // Implicit .\*\n")) ;For some reason the . or * must be escaped...
	  (t
	   (insert "\n")))))
;;(bsv-auto-inst-port (list "foo" "[5:0]") 10 (list (list "foo" "a@\"(% (+ @ 1) 4)\"a")) "3")
;;(x "incom[@\"(+ (* 8 @) 7)\":@\"(* 8 @)\"]")
;;(x ".out (outgo[@\"(concat (+ (* 8 @) 7) \\\":\\\" ( * 8 @))\"]));")

(defun bsv-auto-inst-port-list (sig-list indent-pt tpl-list tpl-num for-star par-values)
  "For `bsv-auto-inst' print a list of ports using `bsv-auto-inst-port'."
  (when bsv-auto-inst-sort
    (setq sig-list (sort (copy-alist sig-list) `bsv-signals-sort-compare)))
  (mapc (lambda (port)
	  (bsv-auto-inst-port port indent-pt
				  tpl-list tpl-num for-star par-values))
	sig-list))

(defun bsv-auto-inst-first ()
  "Insert , etc before first ever port in this instant, as part of \\[bsv-auto-inst]."
  ;; Do we need a trailing comma?
  ;; There maybe a ifdef or something similar before us.  What a mess.  Thus
  ;; to avoid trouble we only insert on preceding ) or *.
  ;; Insert first port on new line
  (insert "\n")  ;; Must insert before search, so point will move forward if insert comma
  (save-excursion
    (bsv-re-search-backward-quick "[^ \t\n\f]" nil nil)
    (when (looking-at ")\\|\\*")  ;; Generally don't insert, unless we are fairly sure
      (forward-char 1)
      (insert ","))))

(defun bsv-auto-star ()
  "Expand SystemBSV .* pins, as part of \\[bsv-auto].

If `bsv-auto-star-expand' is set, .* pins are treated if they were
AUTOINST statements, otherwise they are ignored.  For safety, BSV mode
will also ignore any .* that are not last in your pin list (this prevents
it from deleting pins following the .* when it expands the AUTOINST.)

On writing your file, unless `bsv-auto-star-save' is set, any
non-templated expanded pins will be removed.  You may do this at any time
with \\[bsv-delete-auto-star-implicit].

If you are converting a module to use .* for the first time, you may wish
to use \\[bsv-inject-auto] and then replace the created AUTOINST with .*.

See `bsv-auto-inst' for examples, templates, and more information."
  (when (bsv-auto-star-safe)
    (bsv-auto-inst)))

(defun bsv-auto-inst ()
  "Expand AUTOINST statements, as part of \\[bsv-auto].
Replace the pin connections to an instantiation or interface
declaration with ones automatically derived from the module or
interface header of the instantiated item.

If `bsv-auto-star-expand' is set, also expand SystemBSV .* ports,
and delete them before saving unless `bsv-auto-star-save' is set.
See `bsv-auto-star' for more information.

The pins are printed in declaration order or alphabetically,
based on the `bsv-auto-inst-sort' variable.

Limitations:
  Module names must be resolvable to filenames by adding a
  `bsv-library-extensions', and being found in the same directory, or
  by changing the variable `bsv-library-flags' or
  `bsv-library-directories'.  Macros `modname are translated through the
  vh-{name} Emacs variable, if that is not found, it just ignores the `.

  In templates you must have one signal per line, ending in a ), or ));,
  and have proper () nesting, including a final ); to end the template.

  Typedefs must match `bsv-typedef-regexp', which is disabled by default.

  SystemBSV multidimensional input/output has only experimental support.

  SystemBSV .name syntax is used if `bsv-auto-inst-dot-name' is set.

  Parameters referenced by the instantiation will remain symbolic, unless
  `bsv-auto-inst-param-value' is set.

  Gate primitives (and/or) may have AUTOINST for the purpose of
  AUTOWIRE declarations, etc.  Gates are the only case when
  position based connections are passed.

For example, first take the submodule InstModule.v:

	module InstModule (o,i);
	   output [31:0] o;
	   input i;
	   wire [31:0] o = {32{i}};
	endmodule

This is then used in a upper level module:

	module ExampInst (o,i);
	   output o;
	   input i;
	   InstModule instName
	     (/*AUTOINST*/);
	endmodule

Typing \\[bsv-auto] will make this into:

	module ExampInst (o,i);
	   output o;
	   input i;
	   InstModule instName
	     (/*AUTOINST*/
	      // Outputs
	      .ov	(ov[31:0]),
	      // Inputs
	      .i	(i));
	endmodule

Where the list of inputs and outputs came from the inst module.

Exceptions:

  Unless you are instantiating a module multiple times, or the module is
  something trivial like an adder, DO NOT CHANGE SIGNAL NAMES ACROSS HIERARCHY.
  It just makes for unmaintainable code.  To sanitize signal names, try
  vrename from URL `http://www.veripool.org'.

  When you need to violate this suggestion there are two ways to list
  exceptions, placing them before the AUTOINST, or using templates.

  Any ports defined before the /*AUTOINST*/ are not included in the list of
  automatics.  This is similar to making a template as described below, but
  is restricted to simple connections just like you normally make.  Also note
  that any signals before the AUTOINST will only be picked up by AUTOWIRE if
  you have the appropriate // Input or // Output comment, and exactly the
  same line formatting as AUTOINST itself uses.

	InstModule instName
          (// Inputs
	   .i		(my_i_dont_mess_with_it),
	   /*AUTOINST*/
	   // Outputs
	   .ov		(ov[31:0]));


Templates:

  For multiple instantiations based upon a single template, create a
  commented out template:

	/* InstModule AUTO_TEMPLATE (
		.sig3	(sigz[]),
		);
	*/

  Templates go ABOVE the instantiation(s).  When an instantiation is
  expanded `bsv-mode' simply searches up for the closest template.
  Thus you can have multiple templates for the same module, just alternate
  between the template for an instantiation and the instantiation itself.

  The module name must be the same as the name of the module in the
  instantiation name, and the code \"AUTO_TEMPLATE\" must be in these exact
  words and capitalized.  Only signals that must be different for each
  instantiation need to be listed.

  Inside a template, a [] in a connection name (with nothing else inside
  the brackets) will be replaced by the same bus subscript as it is being
  connected to, or the [] will be removed if it is a single bit signal.
  Generally it is a good idea to do this for all connections in a template,
  as then they will work for any width signal, and with AUTOWIRE.  See
  PTL_BUS becoming PTL_BUSNEW below.

  If you have a complicated template, set `bsv-auto-inst-template-numbers'
  to see which regexps are matching.  Don't leave that mode set after
  debugging is completed though, it will result in lots of extra differences
  and merge conflicts.

  For example:

	/* InstModule AUTO_TEMPLATE (
		.ptl_bus	(ptl_busnew[]),
		);
	*/
	InstModule ms2m (/*AUTOINST*/);

  Typing \\[bsv-auto] will make this into:

	InstModule ms2m (/*AUTOINST*/
	    // Outputs
	    .NotInTemplate	(NotInTemplate),
	    .ptl_bus		(ptl_busnew[3:0]),  // Templated
	    ....


Multiple Module Templates:

  The same template lines can be applied to multiple modules with
  the syntax as follows:

	/* InstModuleA AUTO_TEMPLATE
	   InstModuleB AUTO_TEMPLATE
	   InstModuleC AUTO_TEMPLATE
	   InstModuleD AUTO_TEMPLATE (
		.ptl_bus	(ptl_busnew[]),
		);
	*/

  Note there is only one AUTO_TEMPLATE opening parenthesis.

@ Templates:

  It is common to instantiate a cell multiple times, so templates make it
  trivial to substitute part of the cell name into the connection name.

	/* InstName AUTO_TEMPLATE <optional \"REGEXP\"> (
		.sig1	(sigx[@]),
		.sig2	(sigy[@\"(% (+ 1 @) 4)\"]),
		);
	*/

  If no regular expression is provided immediately after the AUTO_TEMPLATE
  keyword, then the @ character in any connection names will be replaced
  with the instantiation number; the first digits found in the cell's
  instantiation name.

  If a regular expression is provided, the @ character will be replaced
  with the first \(\) grouping that matches against the cell name.  Using a
  regexp of \"\\([0-9]+\\)\" provides identical values for @ as when no
  regexp is provided.  If you use multiple layers of parenthesis,
  \"test\\([^0-9]+\\)_\\([0-9]+\\)\" would replace @ with non-number
  characters after test and before _, whereas
  \"\\(test\\([a-z]+\\)_\\([0-9]+\\)\\)\" would replace @ with the entire
  match.

  For example:

	/* InstModule AUTO_TEMPLATE (
		.ptl_mapvalidx		(ptl_mapvalid[@]),
		.ptl_mapvalidp1x	(ptl_mapvalid[@\"(% (+ 1 @) 4)\"]),
		);
	*/
	InstModule ms2m (/*AUTOINST*/);

  Typing \\[bsv-auto] will make this into:

	InstModule ms2m (/*AUTOINST*/
	    // Outputs
	    .ptl_mapvalidx		(ptl_mapvalid[2]),
	    .ptl_mapvalidp1x		(ptl_mapvalid[3]));

  Note the @ character was replaced with the 2 from \"ms2m\".

  Alternatively, using a regular expression for @:

	/* InstModule AUTO_TEMPLATE \"_\\([a-z]+\\)\" (
		.ptl_mapvalidx		(@_ptl_mapvalid),
		.ptl_mapvalidp1x	(ptl_mapvalid_@),
		);
	*/
	InstModule ms2_FOO (/*AUTOINST*/);
	InstModule ms2_BAR (/*AUTOINST*/);

  Typing \\[bsv-auto] will make this into:

	InstModule ms2_FOO (/*AUTOINST*/
	    // Outputs
	    .ptl_mapvalidx		(FOO_ptl_mapvalid),
	    .ptl_mapvalidp1x		(ptl_mapvalid_FOO));
	InstModule ms2_BAR (/*AUTOINST*/
	    // Outputs
	    .ptl_mapvalidx		(BAR_ptl_mapvalid),
	    .ptl_mapvalidp1x		(ptl_mapvalid_BAR));


Regexp Templates:

  A template entry of the form

	    .pci_req\\([0-9]+\\)_l	(pci_req_jtag_[\\1]),

  will apply an Emacs style regular expression search for any port beginning
  in pci_req followed by numbers and ending in _l and connecting that to
  the pci_req_jtag_[] net, with the bus subscript coming from what matches
  inside the first set of \\( \\).  Thus pci_req2_l becomes pci_req_jtag_[2].

  Since \\([0-9]+\\) is so common and ugly to read, a @ in the port name
  does the same thing.  (Note a @ in the connection/replacement text is
  completely different -- still use \\1 there!)  Thus this is the same as
  the above template:

	    .pci_req@_l		(pci_req_jtag_[\\1]),

  Here's another example to remove the _l, useful when naming conventions
  specify _ alone to mean active low.  Note the use of [] to keep the bus
  subscript:

	    .\\(.*\\)_l		(\\1_[]),

Lisp Templates:

  First any regular expression template is expanded.

  If the syntax @\"( ... )\" is found in a connection, the expression in
  quotes will be evaluated as a Lisp expression, with @ replaced by the
  instantiation number.  The MAPVALIDP1X example above would put @+1 modulo
  4 into the brackets.  Quote all double-quotes inside the expression with
  a leading backslash (\\\"...\\\"); or if the Lisp template is also a
  regexp template backslash the backslash quote (\\\\\"...\\\\\").

  There are special variables defined that are useful in these
  Lisp functions:

	vl-name        Name portion of the input/output port.
	vl-bits        Bus bits portion of the input/output port ('[2:0]').
	vl-mbits       Multidimensional array bits for port ('[2:0][3:0]').
	vl-width       Width of the input/output port ('3' for [2:0]).
                       May be a (...) expression if bits isn't a constant.
	vl-dir         Direction of the pin input/output/inout/interface.
	vl-modport     The modport, if an interface with a modport.
	vl-cell-type   Module name/type of the cell ('InstModule').
	vl-cell-name   Instance name of the cell ('instName').

  Normal Lisp variables may be used in expressions.  See
  `bsv-read-defines' which can set vh-{definename} variables for use
  here.  Also, any comments of the form:

	/*AUTO_LISP(setq foo 1)*/

  will evaluate any Lisp expression inside the parenthesis between the
  beginning of the buffer and the point of the AUTOINST.  This allows
  functions to be defined or variables to be changed between instantiations.
  (See also `bsv-auto-insert-lisp' if you want the output from your
  lisp function to be inserted.)

  Note that when using lisp expressions errors may occur when @ is not a
  number; you may need to use the standard Emacs Lisp functions
  `number-to-string' and `string-to-number'.

  After the evaluation is completed, @ substitution and [] substitution
  occur.

For more information see the \\[bsv-faq] and forums at URL
`http://www.veripool.org'."
  (save-excursion
    ;; Find beginning
    (let* ((pt (point))
	   (for-star (save-excursion (backward-char 2) (looking-at "\\.\\*")))
	   (indent-pt (save-excursion (bsv-backward-open-paren)
				      (1+ (current-column))))
	   (bsv-auto-inst-column (max bsv-auto-inst-column
					  (+ 16 (* 8 (/ (+ indent-pt 7) 8)))))
	   (modi (bsv-modi-current))
	   (moddecls (bsv-modi-get-decls modi))
	   (vector-skip-list (unless bsv-auto-inst-vector
			       (bsv-decls-get-signals moddecls)))
	   submod submodi submoddecls
	   inst skip-pins tpl-list tpl-num did-first par-values)

      ;; Find module name that is instantiated
      (setq submod  (bsv-read-inst-module)
	    inst (bsv-read-inst-name)
	    vl-cell-type submod
	    vl-cell-name inst
	    skip-pins (aref (bsv-read-inst-pins) 0))

      ;; Parse any AUTO_LISP() before here
      (bsv-read-auto-lisp (point-min) pt)

      ;; Read parameters (after AUTO_LISP)
      (setq par-values (and bsv-auto-inst-param-value
			    (bsv-read-inst-param-value)))

      ;; Lookup position, etc of submodule
      ;; Note this may raise an error
      (when (and (not (member submod bsv-gate-keywords))
		 (setq submodi (bsv-modi-lookup submod t)))
	(setq submoddecls (bsv-modi-get-decls submodi))
	;; If there's a number in the instantiation, it may be a argument to the
	;; automatic variable instantiation program.
	(let* ((tpl-info (bsv-read-auto-template submod))
	       (tpl-regexp (aref tpl-info 0)))
	  (setq tpl-num (if (string-match tpl-regexp inst)
			    (match-string 1 inst)
			  "")
		tpl-list (aref tpl-info 1)))
	;; Find submodule's signals and dump
	(let ((sig-list (and (equal (bsv-modi-get-type submodi) "interface")
			     (bsv-signals-not-in
			      (bsv-decls-get-vars submoddecls)
			      skip-pins)))
	      (vl-dir "interfaced"))
	  (when sig-list
	    (when (not did-first) (bsv-auto-inst-first) (setq did-first t))
            ;; Note these are searched for in bsv-read-sub-decls.
	    (bsv-insert-indent "// Interfaced\n")
	    (bsv-auto-inst-port-list sig-list indent-pt
					 tpl-list tpl-num for-star par-values)))
	(let ((sig-list (bsv-signals-not-in
			 (bsv-decls-get-interfaces submoddecls)
			 skip-pins))
	      (vl-dir "interface"))
	  (when sig-list
	    (when (not did-first) (bsv-auto-inst-first) (setq did-first t))
            ;; Note these are searched for in bsv-read-sub-decls.
	    (bsv-insert-indent "// Interfaces\n")
	    (bsv-auto-inst-port-list sig-list indent-pt
					 tpl-list tpl-num for-star par-values)))
	(let ((sig-list (bsv-signals-not-in
			 (bsv-decls-get-outputs submoddecls)
			 skip-pins))
	      (vl-dir "output"))
	  (when sig-list
	    (when (not did-first) (bsv-auto-inst-first) (setq did-first t))
	    (bsv-insert-indent "// Outputs\n")
	    (bsv-auto-inst-port-list sig-list indent-pt
					 tpl-list tpl-num for-star par-values)))
	(let ((sig-list (bsv-signals-not-in
			 (bsv-decls-get-inouts submoddecls)
			 skip-pins))
	      (vl-dir "inout"))
	  (when sig-list
	    (when (not did-first) (bsv-auto-inst-first) (setq did-first t))
	    (bsv-insert-indent "// Inouts\n")
	    (bsv-auto-inst-port-list sig-list indent-pt
					 tpl-list tpl-num for-star par-values)))
	(let ((sig-list (bsv-signals-not-in
			 (bsv-decls-get-inputs submoddecls)
			 skip-pins))
	      (vl-dir "input"))
	  (when sig-list
	    (when (not did-first) (bsv-auto-inst-first) (setq did-first t))
	    (bsv-insert-indent "// Inputs\n")
	    (bsv-auto-inst-port-list sig-list indent-pt
					 tpl-list tpl-num for-star par-values)))
	;; Kill extra semi
	(save-excursion
	  (cond (did-first
		 (re-search-backward "," pt t)
		 (delete-char 1)
		 (insert ");")
		 (search-forward "\n")	;; Added by inst-port
		 (delete-char -1)
		 (if (search-forward ")" nil t) ;; From user, moved up a line
		     (delete-char -1))
		 (if (search-forward ";" nil t) ;; Don't error if user had syntax error and forgot it
		     (delete-char -1)))))))))

(defun bsv-auto-inst-param ()
  "Expand AUTOINSTPARAM statements, as part of \\[bsv-auto].
Replace the parameter connections to an instantiation with ones
automatically derived from the module header of the instantiated netlist.

See \\[bsv-auto-inst] for limitations, and templates to customize the
output.

For example, first take the submodule InstModule.v:

	module InstModule (o,i);
	   parameter PAR;
	endmodule

This is then used in a upper level module:

	module ExampInst (o,i);
	   parameter PAR;
	   InstModule #(/*AUTOINSTPARAM*/)
		instName (/*AUTOINST*/);
	endmodule

Typing \\[bsv-auto] will make this into:

	module ExampInst (o,i);
	   output o;
	   input i;
	   InstModule #(/*AUTOINSTPARAM*/
		        // Parameters
		        .PAR	(PAR));
		instName (/*AUTOINST*/);
	endmodule

Where the list of parameter connections come from the inst module.

Templates:

  You can customize the parameter connections using AUTO_TEMPLATEs,
  just as you would with \\[bsv-auto-inst]."
  (save-excursion
    ;; Find beginning
    (let* ((pt (point))
	   (indent-pt (save-excursion (bsv-backward-open-paren)
				      (1+ (current-column))))
	   (bsv-auto-inst-column (max bsv-auto-inst-column
					  (+ 16 (* 8 (/ (+ indent-pt 7) 8)))))
	   (modi (bsv-modi-current))
	   (moddecls (bsv-modi-get-decls modi))
	   (vector-skip-list (unless bsv-auto-inst-vector
			       (bsv-decls-get-signals moddecls)))
	   submod submodi submoddecls
	   inst skip-pins tpl-list tpl-num did-first)
      ;; Find module name that is instantiated
      (setq submod (save-excursion
		     ;; Get to the point where AUTOINST normally is to read the module
		     (bsv-re-search-forward-quick "[(;]" nil nil)
		     (bsv-read-inst-module))
	    inst   (save-excursion
		     ;; Get to the point where AUTOINST normally is to read the module
		     (bsv-re-search-forward-quick "[(;]" nil nil)
		     (bsv-read-inst-name))
	    vl-cell-type submod
	    vl-cell-name inst
	    skip-pins (aref (bsv-read-inst-pins) 0))

      ;; Parse any AUTO_LISP() before here
      (bsv-read-auto-lisp (point-min) pt)

      ;; Lookup position, etc of submodule
      ;; Note this may raise an error
      (when (setq submodi (bsv-modi-lookup submod t))
	(setq submoddecls (bsv-modi-get-decls submodi))
	;; If there's a number in the instantiation, it may be a argument to the
	;; automatic variable instantiation program.
	(let* ((tpl-info (bsv-read-auto-template submod))
	       (tpl-regexp (aref tpl-info 0)))
	  (setq tpl-num (if (string-match tpl-regexp inst)
			    (match-string 1 inst)
			  "")
		tpl-list (aref tpl-info 1)))
	;; Find submodule's signals and dump
	(let ((sig-list (bsv-signals-not-in
			 (bsv-decls-get-gparams submoddecls)
			 skip-pins))
	      (vl-dir "parameter"))
	  (when sig-list
	    (when (not did-first) (bsv-auto-inst-first) (setq did-first t))
            ;; Note these are searched for in bsv-read-sub-decls.
	    (bsv-insert-indent "// Parameters\n")
	    (bsv-auto-inst-port-list sig-list indent-pt
					 tpl-list tpl-num nil nil)))
	;; Kill extra semi
	(save-excursion
	  (cond (did-first
		 (re-search-backward "," pt t)
		 (delete-char 1)
		 (insert ")")
		 (search-forward "\n")	;; Added by inst-port
		 (delete-char -1)
		 (if (search-forward ")" nil t) ;; From user, moved up a line
		     (delete-char -1)))))))))

(defun bsv-auto-reg ()
  "Expand AUTOREG statements, as part of \\[bsv-auto].
Make reg statements for any output that isn't already declared,
and isn't a wire output from a block.  `bsv-auto-wire-type'
may be used to change the datatype of the declarations.

Limitations:
  This ONLY detects outputs of AUTOINSTants (see `bsv-read-sub-decls').

  This does NOT work on memories, declare those yourself.

An example:

	module ExampReg (o,i);
	   output o;
	   input i;
	   /*AUTOREG*/
	   always o = i;
	endmodule

Typing \\[bsv-auto] will make this into:

	module ExampReg (o,i);
	   output o;
	   input i;
	   /*AUTOREG*/
	   // Beginning of automatic regs (for this module's undeclared outputs)
	   reg		o;
	   // End of automatics
	   always o = i;
	endmodule"
  (save-excursion
    ;; Point must be at insertion point.
    (let* ((indent-pt (current-indentation))
	   (modi (bsv-modi-current))
	   (moddecls (bsv-modi-get-decls modi))
	   (modsubdecls (bsv-modi-get-sub-decls modi))
	   (sig-list (bsv-signals-not-in
		      (bsv-decls-get-outputs moddecls)
		      (append (bsv-decls-get-vars moddecls)
			      (bsv-decls-get-assigns moddecls)
			      (bsv-decls-get-consts moddecls)
			      (bsv-decls-get-gparams moddecls)
			      (bsv-subdecls-get-interfaced modsubdecls)
			      (bsv-subdecls-get-outputs modsubdecls)
			      (bsv-subdecls-get-inouts modsubdecls)))))
      (forward-line 1)
      (when sig-list
	(bsv-insert-indent "// Beginning of automatic regs (for this module's undeclared outputs)\n")
	(bsv-insert-definition modi sig-list "reg" indent-pt nil)
	(bsv-insert-indent "// End of automatics\n")))))

(defun bsv-auto-reg-input ()
  "Expand AUTOREGINPUT statements, as part of \\[bsv-auto].
Make reg statements instantiation inputs that aren't already declared.
This is useful for making a top level shell for testing the module that is
to be instantiated.

Limitations:
  This ONLY detects inputs of AUTOINSTants (see `bsv-read-sub-decls').

  This does NOT work on memories, declare those yourself.

An example (see `bsv-auto-inst' for what else is going on here):

	module ExampRegInput (o,i);
	   output o;
	   input i;
	   /*AUTOREGINPUT*/
           InstModule instName
             (/*AUTOINST*/);
	endmodule

Typing \\[bsv-auto] will make this into:

	module ExampRegInput (o,i);
	   output o;
	   input i;
	   /*AUTOREGINPUT*/
	   // Beginning of automatic reg inputs (for undeclared ...
	   reg [31:0]		iv;	// From inst of inst.v
	   // End of automatics
	   InstModule instName
             (/*AUTOINST*/
	      // Outputs
	      .o		(o[31:0]),
	      // Inputs
	      .iv		(iv));
	endmodule"
  (save-excursion
    ;; Point must be at insertion point.
    (let* ((indent-pt (current-indentation))
	   (modi (bsv-modi-current))
	   (moddecls (bsv-modi-get-decls modi))
	   (modsubdecls (bsv-modi-get-sub-decls modi))
	   (sig-list (bsv-signals-combine-bus
		      (bsv-signals-not-in
		       (append (bsv-subdecls-get-inputs modsubdecls)
			       (bsv-subdecls-get-inouts modsubdecls))
		       (append (bsv-decls-get-signals moddecls)
			       (bsv-decls-get-assigns moddecls))))))
      (forward-line 1)
      (when sig-list
	(bsv-insert-indent "// Beginning of automatic reg inputs (for undeclared instantiated-module inputs)\n")
	(bsv-insert-definition modi sig-list "reg" indent-pt nil)
	(bsv-insert-indent "// End of automatics\n")))))

(defun bsv-auto-logic ()
  "Expand AUTOLOGIC statements, as part of \\[bsv-auto].
Make wire statements using the SystemBSV logic keyword.
This is currently equivalent to:

    /*AUTOWIRE*/

with the below at the bottom of the file

    // Local Variables:
    // bsv-auto-logic-type:\"logic\"
    // End:

In the future AUTOLOGIC may declare additional identifiers,
while AUTOWIRE will not."
  (save-excursion
    (unless bsv-auto-wire-type
      (set (make-local-variable 'bsv-auto-wire-type)
	   "logic"))
    (bsv-auto-wire)))

(defun bsv-auto-wire ()
  "Expand AUTOWIRE statements, as part of \\[bsv-auto].
Make wire statements for instantiations outputs that aren't
already declared. `bsv-auto-wire-type' may be used to change
the datatype of the declarations.

Limitations:
  This ONLY detects outputs of AUTOINSTants (see `bsv-read-sub-decls'),
  and all buses must have widths, such as those from AUTOINST, or using []
  in AUTO_TEMPLATEs.

  This does NOT work on memories or SystemBSV .name connections,
  declare those yourself.

  BSV mode will add \"Couldn't Merge\" comments to signals it cannot
  determine how to bus together.  This occurs when you have ports with
  non-numeric or non-sequential bus subscripts.  If BSV mode
  mis-guessed, you'll have to declare them yourself.

An example (see `bsv-auto-inst' for what else is going on here):

	module ExampWire (o,i);
	   output o;
	   input i;
	   /*AUTOWIRE*/
           InstModule instName
	     (/*AUTOINST*/);
	endmodule

Typing \\[bsv-auto] will make this into:

	module ExampWire (o,i);
	   output o;
	   input i;
	   /*AUTOWIRE*/
	   // Beginning of automatic wires
	   wire [31:0]		ov;	// From inst of inst.v
	   // End of automatics
	   InstModule instName
	     (/*AUTOINST*/
	      // Outputs
	      .ov	(ov[31:0]),
	      // Inputs
	      .i	(i));
	   wire o = | ov;
	endmodule"
  (save-excursion
    ;; Point must be at insertion point.
    (let* ((indent-pt (current-indentation))
	   (modi (bsv-modi-current))
	   (moddecls (bsv-modi-get-decls modi))
	   (modsubdecls (bsv-modi-get-sub-decls modi))
	   (sig-list (bsv-signals-combine-bus
		      (bsv-signals-not-in
		       (append (bsv-subdecls-get-outputs modsubdecls)
			       (bsv-subdecls-get-inouts modsubdecls))
		       (bsv-decls-get-signals moddecls)))))
      (forward-line 1)
      (when sig-list
	(bsv-insert-indent "// Beginning of automatic wires (for undeclared instantiated-module outputs)\n")
	(bsv-insert-definition modi sig-list "wire" indent-pt nil)
	(bsv-insert-indent "// End of automatics\n")
	;; We used to optionally call bsv-pretty-declarations and
	;; bsv-pretty-expr here, but it's too slow on huge modules,
	;; plus makes everyone's module change. Finally those call
	;; syntax-ppss which is broken when change hooks are disabled.
	))))

(defun bsv-auto-output (&optional with-params)
  "Expand AUTOOUTPUT statements, as part of \\[bsv-auto].
Make output statements for any output signal from an /*AUTOINST*/ that
isn't a input to another AUTOINST.  This is useful for modules which
only instantiate other modules.

Limitations:
  This ONLY detects outputs of AUTOINSTants (see `bsv-read-sub-decls').

  If placed inside the parenthesis of a module declaration, it creates
  BSV 2001 style, else uses BSV 1995 style.

  If any concatenation, or bit-subscripts are missing in the AUTOINSTant's
  instantiation, all bets are off.  (For example due to a AUTO_TEMPLATE).

  Typedefs must match `bsv-typedef-regexp', which is disabled by default.

  Signals matching `bsv-auto-output-ignore-regexp' are not included.

An example (see `bsv-auto-inst' for what else is going on here):

	module ExampOutput (ov,i);
	   input i;
	   /*AUTOOUTPUT*/
	   InstModule instName
	     (/*AUTOINST*/);
	endmodule

Typing \\[bsv-auto] will make this into:

	module ExampOutput (ov,i);
	   input i;
	   /*AUTOOUTPUT*/
	   // Beginning of automatic outputs (from unused autoinst outputs)
	   output [31:0]	ov;	// From inst of inst.v
	   // End of automatics
	   InstModule instName
	     (/*AUTOINST*/
	      // Outputs
	      .ov	(ov[31:0]),
	      // Inputs
	      .i	(i));
	endmodule

You may also provide an optional regular expression, in which case only
signals matching the regular expression will be included.  For example the
same expansion will result from only extracting outputs starting with ov:

	   /*AUTOOUTPUT(\"^ov\")*/"
  (save-excursion
    ;; Point must be at insertion point.
    (let* ((indent-pt (current-indentation))
	   (regexp (and with-params
			(nth 0 (bsv-read-auto-params 1))))
	   (v2k  (bsv-in-paren-quick))
	   (modi (bsv-modi-current))
	   (moddecls (bsv-modi-get-decls modi))
	   (modsubdecls (bsv-modi-get-sub-decls modi))
	   (sig-list (bsv-signals-not-in
		      (bsv-subdecls-get-outputs modsubdecls)
		      (append (bsv-decls-get-outputs moddecls)
			      (bsv-decls-get-inouts moddecls)
			      (bsv-subdecls-get-inputs modsubdecls)
			      (bsv-subdecls-get-inouts modsubdecls)))))
      (when regexp
	(setq sig-list (bsv-signals-matching-regexp
			sig-list regexp)))
      (setq sig-list (bsv-signals-not-matching-regexp
		      sig-list bsv-auto-output-ignore-regexp))
      (forward-line 1)
      (when v2k (bsv-repair-open-comma))
      (when sig-list
	(bsv-insert-indent "// Beginning of automatic outputs (from unused autoinst outputs)\n")
	(bsv-insert-definition modi sig-list "output" indent-pt v2k)
	(bsv-insert-indent "// End of automatics\n"))
      (when v2k (bsv-repair-close-comma)))))

(defun bsv-auto-output-every ()
  "Expand AUTOOUTPUTEVERY statements, as part of \\[bsv-auto].
Make output statements for any signals that aren't primary inputs or
outputs already.  This makes every signal in the design a output.  This is
useful to get Synopsys to preserve every signal in the design, since it
won't optimize away the outputs.

An example:

	module ExampOutputEvery (o,i,tempa,tempb);
	   output o;
	   input i;
	   /*AUTOOUTPUTEVERY*/
	   wire tempa = i;
	   wire tempb = tempa;
	   wire o = tempb;
	endmodule

Typing \\[bsv-auto] will make this into:

	module ExampOutputEvery (o,i,tempa,tempb);
	   output o;
	   input i;
	   /*AUTOOUTPUTEVERY*/
	   // Beginning of automatic outputs (every signal)
	   output	tempb;
	   output	tempa;
	   // End of automatics
	   wire tempa = i;
	   wire tempb = tempa;
	   wire o = tempb;
	endmodule"
  (save-excursion
    ;;Point must be at insertion point
    (let* ((indent-pt (current-indentation))
	   (v2k  (bsv-in-paren-quick))
	   (modi (bsv-modi-current))
	   (moddecls (bsv-modi-get-decls modi))
	   (sig-list (bsv-signals-combine-bus
		      (bsv-signals-not-in
		       (bsv-decls-get-signals moddecls)
		       (bsv-decls-get-ports moddecls)))))
      (forward-line 1)
      (when v2k (bsv-repair-open-comma))
      (when sig-list
	(bsv-insert-indent "// Beginning of automatic outputs (every signal)\n")
	(bsv-insert-definition modi sig-list "output" indent-pt v2k)
	(bsv-insert-indent "// End of automatics\n"))
      (when v2k (bsv-repair-close-comma)))))

(defun bsv-auto-input (&optional with-params)
  "Expand AUTOINPUT statements, as part of \\[bsv-auto].
Make input statements for any input signal into an /*AUTOINST*/ that
isn't declared elsewhere inside the module.  This is useful for modules which
only instantiate other modules.

Limitations:
  This ONLY detects outputs of AUTOINSTants (see `bsv-read-sub-decls').

  If placed inside the parenthesis of a module declaration, it creates
  BSV 2001 style, else uses BSV 1995 style.

  If any concatenation, or bit-subscripts are missing in the AUTOINSTant's
  instantiation, all bets are off.  (For example due to a AUTO_TEMPLATE).

  Typedefs must match `bsv-typedef-regexp', which is disabled by default.

  Signals matching `bsv-auto-input-ignore-regexp' are not included.

An example (see `bsv-auto-inst' for what else is going on here):

	module ExampInput (ov,i);
	   output [31:0] ov;
	   /*AUTOINPUT*/
	   InstModule instName
	     (/*AUTOINST*/);
	endmodule

Typing \\[bsv-auto] will make this into:

	module ExampInput (ov,i);
	   output [31:0] ov;
	   /*AUTOINPUT*/
	   // Beginning of automatic inputs (from unused autoinst inputs)
	   input	i;	// From inst of inst.v
	   // End of automatics
	   InstModule instName
	     (/*AUTOINST*/
	      // Outputs
	      .ov	(ov[31:0]),
	      // Inputs
	      .i	(i));
	endmodule

You may also provide an optional regular expression, in which case only
signals matching the regular expression will be included.  For example the
same expansion will result from only extracting inputs starting with i:

	   /*AUTOINPUT(\"^i\")*/"
  (save-excursion
    (let* ((indent-pt (current-indentation))
	   (regexp (and with-params
			(nth 0 (bsv-read-auto-params 1))))
	   (v2k  (bsv-in-paren-quick))
	   (modi (bsv-modi-current))
	   (moddecls (bsv-modi-get-decls modi))
	   (modsubdecls (bsv-modi-get-sub-decls modi))
	   (sig-list (bsv-signals-not-in
		      (bsv-subdecls-get-inputs modsubdecls)
		      (append (bsv-decls-get-inputs moddecls)
			      (bsv-decls-get-inouts moddecls)
			      (bsv-decls-get-vars moddecls)
			      (bsv-decls-get-consts moddecls)
			      (bsv-decls-get-gparams moddecls)
			      (bsv-subdecls-get-interfaced modsubdecls)
			      (bsv-subdecls-get-outputs modsubdecls)
			      (bsv-subdecls-get-inouts modsubdecls)))))
      (when regexp
	(setq sig-list (bsv-signals-matching-regexp
			sig-list regexp)))
      (setq sig-list (bsv-signals-not-matching-regexp
		      sig-list bsv-auto-input-ignore-regexp))
      (forward-line 1)
      (when v2k (bsv-repair-open-comma))
      (when sig-list
	(bsv-insert-indent "// Beginning of automatic inputs (from unused autoinst inputs)\n")
	(bsv-insert-definition modi sig-list "input" indent-pt v2k)
	(bsv-insert-indent "// End of automatics\n"))
      (when v2k (bsv-repair-close-comma)))))

(defun bsv-auto-inout (&optional with-params)
  "Expand AUTOINOUT statements, as part of \\[bsv-auto].
Make inout statements for any inout signal in an /*AUTOINST*/ that
isn't declared elsewhere inside the module.

Limitations:
  This ONLY detects outputs of AUTOINSTants (see `bsv-read-sub-decls').

  If placed inside the parenthesis of a module declaration, it creates
  BSV 2001 style, else uses BSV 1995 style.

  If any concatenation, or bit-subscripts are missing in the AUTOINSTant's
  instantiation, all bets are off.  (For example due to a AUTO_TEMPLATE).

  Typedefs must match `bsv-typedef-regexp', which is disabled by default.

  Signals matching `bsv-auto-inout-ignore-regexp' are not included.

An example (see `bsv-auto-inst' for what else is going on here):

	module ExampInout (ov,i);
	   input i;
	   /*AUTOINOUT*/
	   InstModule instName
	     (/*AUTOINST*/);
	endmodule

Typing \\[bsv-auto] will make this into:

	module ExampInout (ov,i);
	   input i;
	   /*AUTOINOUT*/
	   // Beginning of automatic inouts (from unused autoinst inouts)
	   inout [31:0]	ov;	// From inst of inst.v
	   // End of automatics
	   InstModule instName
	     (/*AUTOINST*/
	      // Inouts
	      .ov	(ov[31:0]),
	      // Inputs
	      .i	(i));
	endmodule

You may also provide an optional regular expression, in which case only
signals matching the regular expression will be included.  For example the
same expansion will result from only extracting inouts starting with i:

	   /*AUTOINOUT(\"^i\")*/"
  (save-excursion
    ;; Point must be at insertion point.
    (let* ((indent-pt (current-indentation))
	   (regexp (and with-params
			(nth 0 (bsv-read-auto-params 1))))
	   (v2k  (bsv-in-paren-quick))
	   (modi (bsv-modi-current))
	   (moddecls (bsv-modi-get-decls modi))
	   (modsubdecls (bsv-modi-get-sub-decls modi))
	   (sig-list (bsv-signals-not-in
		      (bsv-subdecls-get-inouts modsubdecls)
		      (append (bsv-decls-get-outputs moddecls)
			      (bsv-decls-get-inouts moddecls)
			      (bsv-decls-get-inputs moddecls)
			      (bsv-subdecls-get-inputs modsubdecls)
			      (bsv-subdecls-get-outputs modsubdecls)))))
      (when regexp
	(setq sig-list (bsv-signals-matching-regexp
			sig-list regexp)))
      (setq sig-list (bsv-signals-not-matching-regexp
		      sig-list bsv-auto-inout-ignore-regexp))
      (forward-line 1)
      (when v2k (bsv-repair-open-comma))
      (when sig-list
	(bsv-insert-indent "// Beginning of automatic inouts (from unused autoinst inouts)\n")
	(bsv-insert-definition modi sig-list "inout" indent-pt v2k)
	(bsv-insert-indent "// End of automatics\n"))
      (when v2k (bsv-repair-close-comma)))))

(defun bsv-auto-inout-module (&optional complement all-in)
  "Expand AUTOINOUTMODULE statements, as part of \\[bsv-auto].
Take input/output/inout statements from the specified module and insert
into the current module.  This is useful for making null templates and
shell modules which need to have identical I/O with another module.
Any I/O which are already defined in this module will not be redefined.
For the complement of this function, see `bsv-auto-inout-comp',
and to make monitors with all inputs, see `bsv-auto-inout-in'.

Limitations:
  If placed inside the parenthesis of a module declaration, it creates
  BSV 2001 style, else uses BSV 1995 style.

  Concatenation and outputting partial buses is not supported.

  Module names must be resolvable to filenames.  See `bsv-auto-inst'.

  Signals are not inserted in the same order as in the original module,
  though they will appear to be in the same order to a AUTOINST
  instantiating either module.

An example:

	module ExampShell (/*AUTOARG*/);
	   /*AUTOINOUTMODULE(\"ExampMain\")*/
	endmodule

	module ExampMain (i,o,io);
          input i;
          output o;
          inout io;
        endmodule

Typing \\[bsv-auto] will make this into:

	module ExampShell (/*AUTOARG*/i,o,io);
	   /*AUTOINOUTMODULE(\"ExampMain\")*/
           // Beginning of automatic in/out/inouts (from specific module)
           output o;
           inout io;
           input i;
	   // End of automatics
	endmodule

You may also provide an optional regular expression, in which case only
signals matching the regular expression will be included.  For example the
same expansion will result from only extracting signals starting with i:

	   /*AUTOINOUTMODULE(\"ExampMain\",\"^i\")*/

You may also provide an optional second regular expression, in
which case only signals which have that pin direction and data
type will be included.  This matches against everything before
the signal name in the declaration, for example against
\"input\" (single bit), \"output logic\" (direction and type) or
\"output [1:0]\" (direction and implicit type).  You also
probably want to skip spaces in your regexp.

For example, the below will result in matching the output \"o\"
against the previous example's module:

	   /*AUTOINOUTMODULE(\"ExampMain\",\"\",\"^output.*\")*/"
  (save-excursion
    (let* ((params (bsv-read-auto-params 1 3))
	   (submod (nth 0 params))
	   (regexp (nth 1 params))
	   (direction-re (nth 2 params))
	   submodi)
      ;; Lookup position, etc of co-module
      ;; Note this may raise an error
      (when (setq submodi (bsv-modi-lookup submod t))
	(let* ((indent-pt (current-indentation))
	       (v2k  (bsv-in-paren-quick))
	       (modi (bsv-modi-current))
	       (moddecls (bsv-modi-get-decls modi))
	       (submoddecls (bsv-modi-get-decls submodi))
	       (sig-list-i  (bsv-signals-not-in
			     (cond (all-in
				    (append
				     (bsv-decls-get-inputs submoddecls)
				     (bsv-decls-get-inouts submoddecls)
				     (bsv-decls-get-outputs submoddecls)))
				   (complement
				    (bsv-decls-get-outputs submoddecls))
				   (t (bsv-decls-get-inputs submoddecls)))
			     (append (bsv-decls-get-inputs moddecls))))
	       (sig-list-o  (bsv-signals-not-in
			     (cond (all-in nil)
				   (complement
				    (bsv-decls-get-inputs submoddecls))
				   (t (bsv-decls-get-outputs submoddecls)))
			     (append (bsv-decls-get-outputs moddecls))))
	       (sig-list-io (bsv-signals-not-in
			     (cond (all-in nil)
				   (t (bsv-decls-get-inouts submoddecls)))
			     (append (bsv-decls-get-inouts moddecls))))
	       (sig-list-if (bsv-signals-not-in
			     (bsv-decls-get-interfaces submoddecls)
			     (append (bsv-decls-get-interfaces moddecls)))))
	  (forward-line 1)
	  (setq sig-list-i  (bsv-signals-matching-dir-re
			     (bsv-signals-matching-regexp sig-list-i regexp)
			     "input" direction-re)
		sig-list-o  (bsv-signals-matching-dir-re
			     (bsv-signals-matching-regexp sig-list-o regexp)
			     "output" direction-re)
		sig-list-io (bsv-signals-matching-dir-re
			     (bsv-signals-matching-regexp sig-list-io regexp)
			     "inout" direction-re)
		sig-list-if (bsv-signals-matching-dir-re
			     (bsv-signals-matching-regexp sig-list-if regexp)
			     "interface" direction-re))
	  (when v2k (bsv-repair-open-comma))
	  (when (or sig-list-i sig-list-o sig-list-io)
	    (bsv-insert-indent "// Beginning of automatic in/out/inouts (from specific module)\n")
	    ;; Don't sort them so a upper AUTOINST will match the main module
	    (bsv-insert-definition modi sig-list-o  "output" indent-pt v2k t)
	    (bsv-insert-definition modi sig-list-io "inout" indent-pt v2k t)
	    (bsv-insert-definition modi sig-list-i  "input" indent-pt v2k t)
	    (bsv-insert-definition modi sig-list-if "interface" indent-pt v2k t)
	    (bsv-insert-indent "// End of automatics\n"))
	  (when v2k (bsv-repair-close-comma)))))))

(defun bsv-auto-inout-comp ()
  "Expand AUTOINOUTCOMP statements, as part of \\[bsv-auto].
Take input/output/inout statements from the specified module and
insert the inverse into the current module (inputs become outputs
and vice-versa.)  This is useful for making test and stimulus
modules which need to have complementing I/O with another module.
Any I/O which are already defined in this module will not be
redefined.  For the complement of this function, see
`bsv-auto-inout-module'.

Limitations:
  If placed inside the parenthesis of a module declaration, it creates
  BSV 2001 style, else uses BSV 1995 style.

  Concatenation and outputting partial buses is not supported.

  Module names must be resolvable to filenames.  See `bsv-auto-inst'.

  Signals are not inserted in the same order as in the original module,
  though they will appear to be in the same order to a AUTOINST
  instantiating either module.

An example:

	module ExampShell (/*AUTOARG*/);
	   /*AUTOINOUTCOMP(\"ExampMain\")*/
	endmodule

	module ExampMain (i,o,io);
          input i;
          output o;
          inout io;
        endmodule

Typing \\[bsv-auto] will make this into:

	module ExampShell (/*AUTOARG*/i,o,io);
	   /*AUTOINOUTCOMP(\"ExampMain\")*/
           // Beginning of automatic in/out/inouts (from specific module)
           output i;
           inout io;
           input o;
	   // End of automatics
	endmodule

You may also provide an optional regular expression, in which case only
signals matching the regular expression will be included.  For example the
same expansion will result from only extracting signals starting with i:

	   /*AUTOINOUTCOMP(\"ExampMain\",\"^i\")*/"
  (bsv-auto-inout-module t nil))

(defun bsv-auto-inout-in ()
  "Expand AUTOINOUTIN statements, as part of \\[bsv-auto].
Take input/output/inout statements from the specified module and
insert them as all inputs into the current module.  This is
useful for making monitor modules which need to see all signals
as inputs based on another module.  Any I/O which are already
defined in this module will not be redefined.  See also
`bsv-auto-inout-module'.

Limitations:
  If placed inside the parenthesis of a module declaration, it creates
  BSV 2001 style, else uses BSV 1995 style.

  Concatenation and outputting partial buses is not supported.

  Module names must be resolvable to filenames.  See `bsv-auto-inst'.

  Signals are not inserted in the same order as in the original module,
  though they will appear to be in the same order to a AUTOINST
  instantiating either module.

An example:

	module ExampShell (/*AUTOARG*/);
	   /*AUTOINOUTIN(\"ExampMain\")*/
	endmodule

	module ExampMain (i,o,io);
          input i;
          output o;
          inout io;
        endmodule

Typing \\[bsv-auto] will make this into:

	module ExampShell (/*AUTOARG*/i,o,io);
	   /*AUTOINOUTIN(\"ExampMain\")*/
           // Beginning of automatic in/out/inouts (from specific module)
           input i;
           input io;
           input o;
	   // End of automatics
	endmodule

You may also provide an optional regular expression, in which case only
signals matching the regular expression will be included.  For example the
same expansion will result from only extracting signals starting with i:

	   /*AUTOINOUTCOMP(\"ExampMain\",\"^i\")*/"
  (bsv-auto-inout-module nil t))

(defun bsv-auto-insert-lisp ()
  "Expand AUTOINSERTLISP statements, as part of \\[bsv-auto].
The Lisp code provided is called, and the Lisp code calls
`insert` to insert text into the current file beginning on the
line after the AUTOINSERTLISP.

See also AUTO_LISP, which takes a Lisp expression and evaluates
it during `bsv-auto-inst' but does not insert any text.

An example:

	module ExampInsertLisp;
	   /*AUTOINSERTLISP(my-bsv-insert-hello \"world\")*/
	endmodule

	// For this example we declare the function in the
	// module's file itself.  Often you'd define it instead
	// in a site-start.el or .emacs file.
	/*
	 Local Variables:
	 eval:
	   (defun my-bsv-insert-hello (who)
	     (insert (concat \"initial $write(\\\"hello \" who \"\\\");\\n\")))
	 End:
	*/

Typing \\[bsv-auto] will call my-bsv-insert-hello and
expand the above into:

	// Beginning of automatic insert lisp
	initial $write(\"hello world\");
	// End of automatics

You can also call an external program and insert the returned
text:

	/*AUTOINSERTLISP(insert (shell-command-to-string \"echo //hello\"))*/
	// Beginning of automatic insert lisp
	//hello
	// End of automatics"
  (save-excursion
    ;; Point is at end of /*AUTO...*/
    (let* ((indent-pt (current-indentation))
	   (cmd-end-pt (save-excursion (search-backward ")")
				       (forward-char)
				       (point)))	;; Closing paren
	   (cmd-beg-pt (save-excursion (goto-char cmd-end-pt)
				       (backward-sexp 1)  ;; Inside comment
				       (point))) ;; Beginning paren
	   (cmd (buffer-substring-no-properties cmd-beg-pt cmd-end-pt)))
      (forward-line 1)
      ;; Some commands don't move point (like insert-file) so we always
      ;; add the begin/end comments, then delete it if not needed
      (bsv-insert-indent "// Beginning of automatic insert lisp\n")
      (bsv-insert-indent "// End of automatics\n")
      (forward-line -1)
      (eval (read cmd))
      (forward-line -1)
      (setq bsv-scan-cache-tick nil) ;; Clear cache; inserted unknown text
      (bsv-delete-empty-auto-pair))))

(defun bsv-auto-sense-sigs (moddecls presense-sigs)
  "Return list of signals for current AUTOSENSE block."
  (let* ((sigss (bsv-read-always-signals))
	 (sig-list (bsv-signals-not-params
		    (bsv-signals-not-in (bsv-alw-get-inputs sigss)
					    (append (and (not bsv-auto-sense-include-inputs)
							 (bsv-alw-get-outputs-delayed sigss))
						    (and (not bsv-auto-sense-include-inputs)
							 (bsv-alw-get-outputs-immediate sigss))
						    (bsv-alw-get-temps sigss)
						    (bsv-decls-get-consts moddecls)
						    (bsv-decls-get-gparams moddecls)
						    presense-sigs)))))
    sig-list))

(defun bsv-auto-sense ()
  "Expand AUTOSENSE statements, as part of \\[bsv-auto].
Replace the always (/*AUTOSENSE*/) sensitivity list (/*AS*/ for short)
with one automatically derived from all inputs declared in the always
statement.  Signals that are generated within the same always block are NOT
placed into the sensitivity list (see `bsv-auto-sense-include-inputs').
Long lines are split based on the `fill-column', see \\[set-fill-column].

Limitations:
  BSV does not allow memories (multidimensional arrays) in sensitivity
  lists.  AUTOSENSE will thus exclude them, and add a /*memory or*/ comment.

Constant signals:
  AUTOSENSE cannot always determine if a `define is a constant or a signal
  (it could be in a include file for example).  If a `define or other signal
  is put into the AUTOSENSE list and is not desired, use the AUTO_CONSTANT
  declaration anywhere in the module (parenthesis are required):

	/* AUTO_CONSTANT ( `this_is_really_constant_dont_autosense_it ) */

  Better yet, use a parameter, which will be understood to be constant
  automatically.

OOps!
  If AUTOSENSE makes a mistake, please report it.  (First try putting
  a begin/end after your always!) As a workaround, if a signal that
  shouldn't be in the sensitivity list was, use the AUTO_CONSTANT above.
  If a signal should be in the sensitivity list wasn't, placing it before
  the /*AUTOSENSE*/ comment will prevent it from being deleted when the
  autos are updated (or added if it occurs there already).

An example:

	   always @ (/*AS*/) begin
	      /* AUTO_CONSTANT (`constant) */
	      outin = ina | inb | `constant;
	      out = outin;
	   end

Typing \\[bsv-auto] will make this into:

	   always @ (/*AS*/ina or inb) begin
	      /* AUTO_CONSTANT (`constant) */
	      outin = ina | inb | `constant;
	      out = outin;
	   end

Note in BSV 2001, you can often get the same result from the new @*
operator.  (This was added to the language in part due to AUTOSENSE!)

	   always @* begin
	      outin = ina | inb | `constant;
	      out = outin;
	   end"
  (save-excursion
    ;; Find beginning
    (let* ((start-pt (save-excursion
		       (bsv-re-search-backward-quick "(" nil t)
		       (point)))
	   (indent-pt (save-excursion
			(or (and (goto-char start-pt) (1+ (current-column)))
			    (current-indentation))))
	   (modi (bsv-modi-current))
	   (moddecls (bsv-modi-get-decls modi))
	   (sig-memories (bsv-signals-memory
			  (bsv-decls-get-vars moddecls)))
	   sig-list not-first presense-sigs)
      ;; Read signals in always, eliminate outputs from sense list
      (setq presense-sigs (bsv-signals-from-signame
			   (save-excursion
			     (bsv-read-signals start-pt (point)))))
      (setq sig-list (bsv-auto-sense-sigs moddecls presense-sigs))
      (when sig-memories
	(let ((tlen (length sig-list)))
	  (setq sig-list (bsv-signals-not-in sig-list sig-memories))
	  (if (not (eq tlen (length sig-list))) (bsv-insert " /*memory or*/ "))))
      (if (and presense-sigs  ;; Add a "or" if not "(.... or /*AUTOSENSE*/"
	       (save-excursion (goto-char (point))
			       (bsv-re-search-backward-quick "[a-zA-Z0-9$_.%`]+" start-pt t)
			       (bsv-re-search-backward-quick "\\s-" start-pt t)
			       (while (looking-at "\\s-`endif")
				 (bsv-re-search-backward-quick "[a-zA-Z0-9$_.%`]+" start-pt t)
				 (bsv-re-search-backward-quick "\\s-" start-pt t))
			       (not (looking-at "\\s-or\\b"))))
	  (setq not-first t))
      (setq sig-list (sort sig-list `bsv-signals-sort-compare))
      (while sig-list
	(cond ((> (+ 4 (current-column) (length (bsv-sig-name (car sig-list)))) fill-column) ;+4 for width of or
	       (insert "\n")
	       (indent-to indent-pt)
	       (if not-first (insert "or ")))
	      (not-first (insert " or ")))
	(insert (bsv-sig-name (car sig-list)))
	(setq sig-list (cdr sig-list)
	      not-first t)))))

(defun bsv-auto-reset ()
  "Expand AUTORESET statements, as part of \\[bsv-auto].
Replace the /*AUTORESET*/ comment with code to initialize all
registers set elsewhere in the always block.

Limitations:
  AUTORESET will not clear memories.

  AUTORESET uses <= if the signal has a <= assignment in the block,
  else it uses =.

  If <= is used, all = assigned variables are ignored if
  `bsv-auto-reset-blocking-in-non' is nil; they are presumed
  to be temporaries.

/*AUTORESET*/ presumes that any signals mentioned between the previous
begin/case/if statement and the AUTORESET comment are being reset manually
and should not be automatically reset.  This includes omitting any signals
used on the right hand side of assignments.

By default, AUTORESET will include the width of the signal in the autos,
this is a recent change.  To control this behavior, see
`bsv-auto-reset-widths'.

AUTORESET ties signals to deasserted, which is presumed to be zero.
Signals that match `bsv-active-low-regexp' will be deasserted by tying
them to a one.

An example:

    always @(posedge clk or negedge reset_l) begin
        if (!reset_l) begin
            c <= 1;
            /*AUTORESET*/
        end
        else begin
            a <= in_a;
            b <= in_b;
            c <= in_c;
        end
    end

Typing \\[bsv-auto] will make this into:

    always @(posedge core_clk or negedge reset_l) begin
        if (!reset_l) begin
            c <= 1;
            /*AUTORESET*/
            // Beginning of autoreset for uninitialized flops
            a <= 0;
            b = 0;   // if `bsv-auto-reset-blocking-in-non' true
            // End of automatics
        end
        else begin
            a <= in_a;
            b  = in_b;
            c <= in_c;
        end
    end"

  (interactive)
  (save-excursion
    ;; Find beginning
    (let* ((indent-pt (current-indentation))
	   (modi (bsv-modi-current))
	   (moddecls (bsv-modi-get-decls modi))
	   (all-list (bsv-decls-get-signals moddecls))
	   sigss sig-list dly-list prereset-sigs)
      ;; Read signals in always, eliminate outputs from reset list
      (setq prereset-sigs (bsv-signals-from-signame
			   (save-excursion
			     (bsv-read-signals
			      (save-excursion
				(bsv-re-search-backward-quick "\\(@\\|\\<begin\\>\\|\\<if\\>\\|\\<case\\>\\)" nil t)
				(point))
			      (point)))))
      (save-excursion
	(bsv-re-search-backward-quick "@" nil t)
        (setq sigss (bsv-read-always-signals)))
      (setq dly-list (bsv-alw-get-outputs-delayed sigss))
      (setq sig-list (bsv-signals-not-in (append
					      (bsv-alw-get-outputs-delayed sigss)
					      (when (or (not (bsv-alw-get-uses-delayed sigss))
							bsv-auto-reset-blocking-in-non)
						(bsv-alw-get-outputs-immediate sigss)))
					     (append
					      (bsv-alw-get-temps sigss)
					      prereset-sigs)))
      (setq sig-list (sort sig-list `bsv-signals-sort-compare))
      (when sig-list
	(insert "\n");
	(bsv-insert-indent "// Beginning of autoreset for uninitialized flops\n");
	(while sig-list
	  (let ((sig (or (assoc (bsv-sig-name (car sig-list)) all-list) ;; As sig-list has no widths
			 (car sig-list))))
	    (indent-to indent-pt)
	    (insert (bsv-sig-name sig)
		    (if (assoc (bsv-sig-name sig) dly-list)
			(concat " <= " bsv-assignment-delay)
		      " = ")
		    (bsv-sig-tieoff sig (not bsv-auto-reset-widths))
		    ";\n")
	    (setq sig-list (cdr sig-list))))
	(bsv-insert-indent "// End of automatics")))))

(defun bsv-auto-tieoff ()
  "Expand AUTOTIEOFF statements, as part of \\[bsv-auto].
Replace the /*AUTOTIEOFF*/ comment with code to wire-tie all unused output
signals to deasserted.

/*AUTOTIEOFF*/ is used to make stub modules; modules that have the same
input/output list as another module, but no internals.  Specifically, it
finds all outputs in the module, and if that input is not otherwise declared
as a register or wire, creates a tieoff.

AUTORESET ties signals to deasserted, which is presumed to be zero.
Signals that match `bsv-active-low-regexp' will be deasserted by tying
them to a one.

You can add signals you do not want included in AUTOTIEOFF with
`bsv-auto-tieoff-ignore-regexp'.

`bsv-auto-wire-type' may be used to change the datatype of
the declarations.

An example of making a stub for another module:

    module ExampStub (/*AUTOINST*/);
	/*AUTOINOUTMODULE(\"Foo\")*/
        /*AUTOTIEOFF*/
        // verilator lint_off UNUSED
        wire _unused_ok = &{1'b0,
                            /*AUTOUNUSED*/
                            1'b0};
        // verilator lint_on  UNUSED
    endmodule

Typing \\[bsv-auto] will make this into:

    module ExampStub (/*AUTOINST*/...);
	/*AUTOINOUTMODULE(\"Foo\")*/
        // Beginning of autotieoff
        output [2:0] foo;
        // End of automatics

        /*AUTOTIEOFF*/
        // Beginning of autotieoff
        wire [2:0] foo = 3'b0;
        // End of automatics
        ...
    endmodule"
  (interactive)
  (save-excursion
    ;; Find beginning
    (let* ((indent-pt (current-indentation))
	   (modi (bsv-modi-current))
	   (moddecls (bsv-modi-get-decls modi))
	   (modsubdecls (bsv-modi-get-sub-decls modi))
	   (sig-list (bsv-signals-not-in
		      (bsv-decls-get-outputs moddecls)
		      (append (bsv-decls-get-vars moddecls)
			      (bsv-decls-get-assigns moddecls)
			      (bsv-decls-get-consts moddecls)
			      (bsv-decls-get-gparams moddecls)
			      (bsv-subdecls-get-interfaced modsubdecls)
			      (bsv-subdecls-get-outputs modsubdecls)
			      (bsv-subdecls-get-inouts modsubdecls)))))
      (setq sig-list (bsv-signals-not-matching-regexp
		      sig-list bsv-auto-tieoff-ignore-regexp))
      (when sig-list
	(forward-line 1)
	(bsv-insert-indent "// Beginning of automatic tieoffs (for this module's unterminated outputs)\n")
	(setq sig-list (sort (copy-alist sig-list) `bsv-signals-sort-compare))
	(bsv-modi-cache-add-vars modi sig-list)  ; Before we trash list
	(while sig-list
	  (let ((sig (car sig-list)))
	    (cond ((equal bsv-auto-tieoff-declaration "assign")
		   (indent-to indent-pt)
		   (insert "assign " (bsv-sig-name sig)))
		  (t
		   (bsv-insert-one-definition sig bsv-auto-tieoff-declaration indent-pt)))
	    (indent-to (max 48 (+ indent-pt 40)))
	    (insert "= " (bsv-sig-tieoff sig)
		    ";\n")
	    (setq sig-list (cdr sig-list))))
	(bsv-insert-indent "// End of automatics\n")))))

(defun bsv-auto-unused ()
  "Expand AUTOUNUSED statements, as part of \\[bsv-auto].
Replace the /*AUTOUNUSED*/ comment with a comma separated list of all unused
input and inout signals.

/*AUTOUNUSED*/ is used to make stub modules; modules that have the same
input/output list as another module, but no internals.  Specifically, it
finds all inputs and inouts in the module, and if that input is not otherwise
used, adds it to a comma separated list.

The comma separated list is intended to be used to create a _unused_ok
signal.  Using the exact name \"_unused_ok\" for name of the temporary
signal is recommended as it will insure maximum forward compatibility, it
also makes lint warnings easy to understand; ignore any unused warnings
with \"unused\" in the signal name.

To reduce simulation time, the _unused_ok signal should be forced to a
constant to prevent wiggling.  The easiest thing to do is use a
reduction-and with 1'b0 as shown.

This way all unused signals are in one place, making it convenient to add
your tool's specific pragmas around the assignment to disable any unused
warnings.

You can add signals you do not want included in AUTOUNUSED with
`bsv-auto-unused-ignore-regexp'.

An example of making a stub for another module:

    module ExampStub (/*AUTOINST*/);
	/*AUTOINOUTMODULE(\"Examp\")*/
        /*AUTOTIEOFF*/
        // verilator lint_off UNUSED
        wire _unused_ok = &{1'b0,
                            /*AUTOUNUSED*/
                            1'b0};
        // verilator lint_on  UNUSED
    endmodule

Typing \\[bsv-auto] will make this into:

        ...
        // verilator lint_off UNUSED
        wire _unused_ok = &{1'b0,
                            /*AUTOUNUSED*/
			    // Beginning of automatics
			    unused_input_a,
			    unused_input_b,
			    unused_input_c,
			    // End of automatics
                            1'b0};
        // verilator lint_on  UNUSED
    endmodule"
  (interactive)
  (save-excursion
    ;; Find beginning
    (let* ((indent-pt (progn (search-backward "/*") (current-column)))
	   (modi (bsv-modi-current))
	   (moddecls (bsv-modi-get-decls modi))
	   (modsubdecls (bsv-modi-get-sub-decls modi))
	   (sig-list (bsv-signals-not-in
		      (append (bsv-decls-get-inputs moddecls)
			      (bsv-decls-get-inouts moddecls))
		      (append (bsv-subdecls-get-inputs modsubdecls)
			      (bsv-subdecls-get-inouts modsubdecls)))))
      (setq sig-list (bsv-signals-not-matching-regexp
		      sig-list bsv-auto-unused-ignore-regexp))
      (when sig-list
	(forward-line 1)
	(bsv-insert-indent "// Beginning of automatic unused inputs\n")
	(setq sig-list (sort (copy-alist sig-list) `bsv-signals-sort-compare))
	(while sig-list
	  (let ((sig (car sig-list)))
	    (indent-to indent-pt)
	    (insert (bsv-sig-name sig) ",\n")
	    (setq sig-list (cdr sig-list))))
	(bsv-insert-indent "// End of automatics\n")))))

(defun bsv-enum-ascii (signm elim-regexp)
  "Convert an enum name SIGNM to an ascii string for insertion.
Remove user provided prefix ELIM-REGEXP."
  (or elim-regexp (setq elim-regexp "_ DONT MATCH IT_"))
  (let ((case-fold-search t))
    ;; All upper becomes all lower for readability
    (downcase (bsv-string-replace-matches elim-regexp "" nil nil signm))))

(defun bsv-auto-ascii-enum ()
  "Expand AUTOASCIIENUM statements, as part of \\[bsv-auto].
Create a register to contain the ASCII decode of a enumerated signal type.
This will allow trace viewers to show the ASCII name of states.

First, parameters are built into a enumeration using the synopsys enum
comment.  The comment must be between the keyword and the symbol.
\(Annoying, but that's what Synopsys's dc_shell FSM reader requires.)

Next, registers which that enum applies to are also tagged with the same
enum.

Finally, a AUTOASCIIENUM command is used.

  The first parameter is the name of the signal to be decoded.

  The second parameter is the name to store the ASCII code into.  For the
  signal foo, I suggest the name _foo__ascii, where the leading _ indicates
  a signal that is just for simulation, and the magic characters _ascii
  tell viewers like Dinotrace to display in ASCII format.

  The third optional parameter is a string which will be removed
  from the state names. It defaults to "" which removes nothing.

  The fourth optional parameter is \"onehot\" to force one-hot
  decoding. If unspecified, if and only if the first parameter
  width is 2^(number of states in enum) and does NOT match the
  width of the enum, the signal is assumed to be a one hot
  decode.  Otherwise, it's a normal encoded state vector.

  `bsv-auto-wire-type' may be used to change the datatype of
  the declarations.

An example:

	//== State enumeration
	parameter [2:0] // synopsys enum state_info
			   SM_IDLE =  3'b000,
			   SM_SEND =  3'b001,
			   SM_WAIT1 = 3'b010;
	//== State variables
	reg [2:0]  /* synopsys enum state_info */
		   state_r;  /* synopsys state_vector state_r */
	reg [2:0]  /* synopsys enum state_info */
		   state_e1;

	/*AUTOASCIIENUM(\"state_r\", \"state_ascii_r\", \"SM_\")*/

Typing \\[bsv-auto] will make this into:

	... same front matter ...

	/*AUTOASCIIENUM(\"state_r\", \"state_ascii_r\", \"SM_\")*/
	// Beginning of automatic ASCII enum decoding
	reg [39:0]		state_ascii_r;		// Decode of state_r
	always @(state_r) begin
	   case ({state_r})
		SM_IDLE:  state_ascii_r = \"idle \";
		SM_SEND:  state_ascii_r = \"send \";
		SM_WAIT1: state_ascii_r = \"wait1\";
		default:  state_ascii_r = \"%Erro\";
	   endcase
	end
	// End of automatics"
  (save-excursion
    (let* ((params (bsv-read-auto-params 2 4))
	   (undecode-name (nth 0 params))
	   (ascii-name (nth 1 params))
	   (elim-regexp (and (nth 2 params)
			     (not (equal (nth 2 params) ""))
			     (nth 2 params)))
	   (one-hot-flag (nth 3 params))
	   ;;
	   (indent-pt (current-indentation))
	   (modi (bsv-modi-current))
	   (moddecls (bsv-modi-get-decls modi))
	   ;;
	   (sig-list-consts (append (bsv-decls-get-consts moddecls)
				    (bsv-decls-get-gparams moddecls)))
	   (sig-list-all  (append (bsv-decls-get-vars moddecls)
				  (bsv-decls-get-outputs moddecls)
				  (bsv-decls-get-inouts moddecls)
				  (bsv-decls-get-inputs moddecls)))
	   ;;
	   (undecode-sig (or (assoc undecode-name sig-list-all)
			     (error "%s: Signal %s not found in design" (bsv-point-text) undecode-name)))
	   (undecode-enum (or (bsv-sig-enum undecode-sig)
			      (error "%s: Signal %s does not have a enum tag" (bsv-point-text) undecode-name)))
	   ;;
	   (enum-sigs (bsv-signals-not-in
		       (or (bsv-signals-matching-enum sig-list-consts undecode-enum)
			   (error "%s: No state definitions for %s" (bsv-point-text) undecode-enum))
		       nil))
	   ;;
	   (one-hot (or
		     (string-match "onehot" (or one-hot-flag ""))
		     (and ;; width(enum) != width(sig)
		      (or (not (bsv-sig-bits (car enum-sigs)))
			  (not (equal (bsv-sig-width (car enum-sigs))
				      (bsv-sig-width undecode-sig))))
		      ;; count(enums) == width(sig)
		      (equal (number-to-string (length enum-sigs))
			     (bsv-sig-width undecode-sig)))))
  	   (enum-chars 0)
	   (ascii-chars 0))
      ;;
      ;; Find number of ascii chars needed
      (let ((tmp-sigs enum-sigs))
	(while tmp-sigs
	  (setq enum-chars (max enum-chars (length (bsv-sig-name (car tmp-sigs))))
		ascii-chars (max ascii-chars (length (bsv-enum-ascii
						      (bsv-sig-name (car tmp-sigs))
						      elim-regexp)))
		tmp-sigs (cdr tmp-sigs))))
      ;;
      (forward-line 1)
      (bsv-insert-indent "// Beginning of automatic ASCII enum decoding\n")
      (let ((decode-sig-list (list (list ascii-name (format "[%d:0]" (- (* ascii-chars 8) 1))
					 (concat "Decode of " undecode-name) nil nil))))
	(bsv-insert-definition modi decode-sig-list "reg" indent-pt nil))
      ;;
      (bsv-insert-indent "always @(" undecode-name ") begin\n")
      (setq indent-pt (+ indent-pt bsv-indent-level))
      (bsv-insert-indent "case ({" undecode-name "})\n")
      (setq indent-pt (+ indent-pt bsv-case-indent))
      ;;
      (let ((tmp-sigs enum-sigs)
	    (chrfmt (format "%%-%ds %s = \"%%-%ds\";\n"
			    (+ (if one-hot 9 1) (max 8 enum-chars))
			    ascii-name ascii-chars))
	    (errname (substring "%Error" 0 (min 6 ascii-chars))))
	(while tmp-sigs
	  (bsv-insert-indent
	   (concat
	    (format chrfmt
		    (concat (if one-hot "(")
			    ;; Use enum-sigs length as that's numeric
			    ;; bsv-sig-width undecode-sig might not be.
			    (if one-hot (number-to-string (length enum-sigs)))
			    ;; We use a shift instead of var[index]
			    ;; so that a non-one hot value will show as error.
			    (if one-hot "'b1<<")
			    (bsv-sig-name (car tmp-sigs))
			    (if one-hot ")") ":")
		    (bsv-enum-ascii (bsv-sig-name (car tmp-sigs))
					elim-regexp))))
	  (setq tmp-sigs (cdr tmp-sigs)))
	(bsv-insert-indent (format chrfmt "default:" errname)))
      ;;
      (setq indent-pt (- indent-pt bsv-case-indent))
      (bsv-insert-indent "endcase\n")
      (setq indent-pt (- indent-pt bsv-indent-level))
      (bsv-insert-indent "end\n"
			     "// End of automatics\n"))))

(defun bsv-auto-templated-rel ()
  "Replace Templated relative line numbers with absolute line numbers.
Internal use only.  This hacks around the line numbers in AUTOINST Templates
being different from the final output's line numbering."
  (let ((templateno 0) (template-line (list 0)) (buf-line 1))
    ;; Find line number each template is on
    ;; Count lines as we go, as otherwise it's O(n^2) to use count-lines
    (goto-char (point-min))
    (while (not (eobp))
      (when (looking-at ".*AUTO_TEMPLATE")
	(setq templateno (1+ templateno))
	(setq template-line (cons buf-line template-line)))
      (setq buf-line (1+ buf-line))
      (forward-line 1))
    (setq template-line (nreverse template-line))
    ;; Replace T# L# with absolute line number
    (goto-char (point-min))
    (while (re-search-forward " Templated T\\([0-9]+\\) L\\([0-9]+\\)" nil t)
      (replace-match
       (concat " Templated "
	       (int-to-string (+ (nth (string-to-number (match-string 1))
				      template-line)
				 (string-to-number (match-string 2)))))
       t t))))


;;
;; Auto top level
;;

(defun bsv-auto (&optional inject)  ; Use bsv-inject-auto instead of passing a arg
  "Expand AUTO statements.
Look for any /*AUTO...*/ commands in the code, as used in
instantiations or argument headers.  Update the list of signals
following the /*AUTO...*/ command.

Use \\[bsv-delete-auto] to remove the AUTOs.

Use \\[bsv-diff-auto] to see differences in AUTO expansion.

Use \\[bsv-inject-auto] to insert AUTOs for the first time.

Use \\[bsv-faq] for a pointer to frequently asked questions.

The hooks `bsv-before-auto-hook' and `bsv-auto-hook' are
called before and after this function, respectively.

For example:
	module ModuleName (/*AUTOARG*/);
	/*AUTOINPUT*/
	/*AUTOOUTPUT*/
	/*AUTOWIRE*/
	/*AUTOREG*/
	InstMod instName #(/*AUTOINSTPARAM*/) (/*AUTOINST*/);

You can also update the AUTOs from the shell using:
	emacs --batch  <filenames.v>  -f bsv-batch-auto
Or fix indentation with:
	emacs --batch  <filenames.v>  -f bsv-batch-indent
Likewise, you can delete or inject AUTOs with:
	emacs --batch  <filenames.v>  -f bsv-batch-delete-auto
	emacs --batch  <filenames.v>  -f bsv-batch-inject-auto
Or check if AUTOs have the same expansion
	emacs --batch  <filenames.v>  -f bsv-batch-diff-auto

Using \\[describe-function], see also:
    `bsv-auto-arg'          for AUTOARG module instantiations
    `bsv-auto-ascii-enum'   for AUTOASCIIENUM enumeration decoding
    `bsv-auto-inout-comp'   for AUTOINOUTCOMP copy complemented i/o
    `bsv-auto-inout-in'     for AUTOINOUTIN inputs for all i/o
    `bsv-auto-inout-module' for AUTOINOUTMODULE copying i/o from elsewhere
    `bsv-auto-inout'        for AUTOINOUT making hierarchy inouts
    `bsv-auto-input'        for AUTOINPUT making hierarchy inputs
    `bsv-auto-insert-lisp'  for AUTOINSERTLISP insert code from lisp function
    `bsv-auto-inst'         for AUTOINST instantiation pins
    `bsv-auto-star'         for AUTOINST .* SystemBSV pins
    `bsv-auto-inst-param'   for AUTOINSTPARAM instantiation params
    `bsv-auto-logic'        for AUTOLOGIC declaring logic signals
    `bsv-auto-output'       for AUTOOUTPUT making hierarchy outputs
    `bsv-auto-output-every' for AUTOOUTPUTEVERY making all outputs
    `bsv-auto-reg'          for AUTOREG registers
    `bsv-auto-reg-input'    for AUTOREGINPUT instantiation registers
    `bsv-auto-reset'        for AUTORESET flop resets
    `bsv-auto-sense'        for AUTOSENSE always sensitivity lists
    `bsv-auto-tieoff'       for AUTOTIEOFF output tieoffs
    `bsv-auto-unused'       for AUTOUNUSED unused inputs/inouts
    `bsv-auto-wire'         for AUTOWIRE instantiation wires

    `bsv-read-defines'      for reading `define values
    `bsv-read-includes'     for reading `includes

If you have bugs with these autos, please inform the BSC developers,
by filing an issue at URL `https://github.com/B-Lang-org/bsc/issues'"
  (interactive)
  (unless noninteractive (message "Updating AUTOs..."))
  (if (fboundp 'dinotrace-unannotate-all)
      (dinotrace-unannotate-all))
  (let ((oldbuf (if (not (buffer-modified-p))
		    (buffer-string)))
	;; Before version 20, match-string with font-lock returns a
	;; vector that is not equal to the string.  IE if on "input"
	;; nil==(equal "input" (progn (looking-at "input") (match-string 0)))
	(fontlocked (when (and (boundp 'font-lock-mode)
			       font-lock-mode)
		      (font-lock-mode 0)
		      t))
	;; Cache directories; we don't write new files, so can't change
	(bsv-dir-cache-preserving t)
	;; Cache current module
	(bsv-modi-cache-current-enable t)
	(bsv-modi-cache-current-max (point-min)) ; IE it's invalid
	bsv-modi-cache-current)
     (unwind-protect
	 ;; Disable change hooks for speed
	 ;; This let can't be part of above let; must restore
	 ;; after-change-functions before font-lock resumes
	 (bsv-save-no-change-functions
	  (bsv-save-scan-cache
	   (save-excursion
	     ;; Wipe cache; otherwise if we AUTOed a block above this one,
	     ;; we'll misremember we have generated IOs, confusing AUTOOUTPUT
	     (setq bsv-modi-cache-list nil)
	     ;; If we're not in bsv-mode, change syntax table so parsing works right
	     (unless (eq major-mode `bsv-mode) (bsv-mode))
	     ;; Allow user to customize
	     (bsv-run-hooks 'bsv-before-auto-hook)
	     ;; Try to save the user from needing to revert-file to reread file local-variables
	     (bsv-auto-reeval-locals)
	     (bsv-read-auto-lisp-present)
	     (bsv-read-auto-lisp (point-min) (point-max))
	     (bsv-getopt-flags)
	     ;; From here on out, we can cache anything we read from disk
	     (bsv-preserve-dir-cache
	      ;; These two may seem obvious to do always, but on large includes it can be way too slow
	      (when bsv-auto-read-includes
		(bsv-read-includes)
		(bsv-read-defines nil nil t))
	      ;; This particular ordering is important
	      ;; INST: Lower modules correct, no internal dependencies, FIRST
	      (bsv-preserve-modi-cache
	       ;; Clear existing autos else we'll be screwed by existing ones
	       (bsv-delete-auto)
	       ;; Injection if appropriate
	       (when inject
		 (bsv-inject-inst)
		 (bsv-inject-sense)
		 (bsv-inject-arg))
	       ;;
	       ;; Do user inserts first, so their code can insert AUTOs
	       ;; We may provide a AUTOINSERTLISPLAST if another cleanup pass is needed
	       (bsv-auto-re-search-do "/\\*AUTOINSERTLISP(.*?)\\*/"
					  'bsv-auto-insert-lisp)
	       ;; Expand instances before need the signals the instances input/output
	       (bsv-auto-re-search-do "/\\*AUTOINSTPARAM\\*/" 'bsv-auto-inst-param)
	       (bsv-auto-re-search-do "/\\*AUTOINST\\*/" 'bsv-auto-inst)
	       (bsv-auto-re-search-do "\\.\\*" 'bsv-auto-star)
	       ;; Doesn't matter when done, but combine it with a common changer
	       (bsv-auto-re-search-do "/\\*\\(AUTOSENSE\\|AS\\)\\*/" 'bsv-auto-sense)
	       (bsv-auto-re-search-do "/\\*AUTORESET\\*/" 'bsv-auto-reset)
	       ;; Must be done before autoin/out as creates a reg
	       (bsv-auto-re-search-do "/\\*AUTOASCIIENUM([^)]*)\\*/" 'bsv-auto-ascii-enum)
	       ;;
	       ;; first in/outs from other files
	       (bsv-auto-re-search-do "/\\*AUTOINOUTMODULE([^)]*)\\*/" 'bsv-auto-inout-module)
	       (bsv-auto-re-search-do "/\\*AUTOINOUTCOMP([^)]*)\\*/" 'bsv-auto-inout-comp)
	       (bsv-auto-re-search-do "/\\*AUTOINOUTIN([^)]*)\\*/" 'bsv-auto-inout-in)
	       ;; next in/outs which need previous sucked inputs first
	       (bsv-auto-re-search-do "/\\*AUTOOUTPUT\\((\"[^\"]*\")\\)\\*/"
					  (lambda () (bsv-auto-output t)))
	       (bsv-auto-re-search-do "/\\*AUTOOUTPUT\\*/" 'bsv-auto-output)
	       (bsv-auto-re-search-do "/\\*AUTOINPUT\\((\"[^\"]*\")\\)\\*/"
					  (lambda () (bsv-auto-input t)))
	       (bsv-auto-re-search-do "/\\*AUTOINPUT\\*/"  'bsv-auto-input)
	       (bsv-auto-re-search-do "/\\*AUTOINOUT\\((\"[^\"]*\")\\)\\*/"
					  (lambda () (bsv-auto-inout t)))
	       (bsv-auto-re-search-do "/\\*AUTOINOUT\\*/" 'bsv-auto-inout)
	       ;; Then tie off those in/outs
	       (bsv-auto-re-search-do "/\\*AUTOTIEOFF\\*/" 'bsv-auto-tieoff)
	       ;; Wires/regs must be after inputs/outputs
	       (bsv-auto-re-search-do "/\\*AUTOLOGIC\\*/" 'bsv-auto-logic)
	       (bsv-auto-re-search-do "/\\*AUTOWIRE\\*/" 'bsv-auto-wire)
	       (bsv-auto-re-search-do "/\\*AUTOREG\\*/" 'bsv-auto-reg)
	       (bsv-auto-re-search-do "/\\*AUTOREGINPUT\\*/" 'bsv-auto-reg-input)
	       ;; outputevery needs AUTOOUTPUTs done first
	       (bsv-auto-re-search-do "/\\*AUTOOUTPUTEVERY\\*/" 'bsv-auto-output-every)
	       ;; After we've created all new variables
	       (bsv-auto-re-search-do "/\\*AUTOUNUSED\\*/" 'bsv-auto-unused)
	       ;; Must be after all inputs outputs are generated
	       (bsv-auto-re-search-do "/\\*AUTOARG\\*/" 'bsv-auto-arg)
	       ;; Fix line numbers (comments only)
	       (when bsv-auto-inst-template-numbers
		 (bsv-auto-templated-rel))))
	     ;;
	     (bsv-run-hooks 'bsv-auto-hook)
	     ;;
	     (when bsv-auto-delete-trailing-whitespace
	       (bsv-delete-trailing-whitespace))
	     ;;
	     (set (make-local-variable 'bsv-auto-update-tick) (buffer-chars-modified-tick))
	     ;;
	     ;; If end result is same as when started, clear modified flag
	     (cond ((and oldbuf (equal oldbuf (buffer-string)))
		    (set-buffer-modified-p nil)
		    (unless noninteractive (message "Updating AUTOs...done (no changes)")))
		   (t (unless noninteractive (message "Updating AUTOs...done"))))
	     ;; End of after-change protection
	     )))
       ;; Unwind forms
       (progn
	 ;; Restore font-lock
	 (when fontlocked (font-lock-mode t))))))


;;
;; Skeleton based code insertion
;;
(defvar bsv-template-map
  (let ((map (make-sparse-keymap)))
    (define-key map "a" 'bsv-sk-always)
    (define-key map "b" 'bsv-sk-begin)
    (define-key map "c" 'bsv-sk-case)
    (define-key map "f" 'bsv-sk-for)
    (define-key map "g" 'bsv-sk-generate)
    (define-key map "h" 'bsv-sk-header)
    (define-key map "i" 'bsv-sk-initial)
    (define-key map "j" 'bsv-sk-fork)
    (define-key map "m" 'bsv-sk-module)
    (define-key map "o" 'bsv-sk-ovm-class)
    (define-key map "p" 'bsv-sk-primitive)
    (define-key map "r" 'bsv-sk-repeat)
    (define-key map "s" 'bsv-sk-specify)
    (define-key map "t" 'bsv-sk-task)
    (define-key map "u" 'bsv-sk-uvm-class)
    (define-key map "w" 'bsv-sk-while)
    (define-key map "x" 'bsv-sk-casex)
    (define-key map "z" 'bsv-sk-casez)
    (define-key map "?" 'bsv-sk-if)
    (define-key map ":" 'bsv-sk-else-if)
    (define-key map "/" 'bsv-sk-comment)
    (define-key map "A" 'bsv-sk-assign)
    (define-key map "F" 'bsv-sk-function)
    (define-key map "I" 'bsv-sk-input)
    (define-key map "O" 'bsv-sk-output)
    (define-key map "S" 'bsv-sk-state-machine)
    (define-key map "=" 'bsv-sk-inout)
    (define-key map "W" 'bsv-sk-wire)
    (define-key map "R" 'bsv-sk-reg)
    (define-key map "D" 'bsv-sk-define-signal)
    map)
  "Keymap used in BSV mode for smart template operations.")


;;
;; Place the templates into BSV Mode.  They may be inserted under any key.
;; C-c C-t will be the default.  If you use templates a lot, you
;; may want to consider moving the binding to another key in your .emacs
;; file.
;;
;; Note \C-c and letter are reserved for users
(define-key bsv-mode-map "\C-c\C-t" bsv-template-map)

;;; ---- statement skeletons ------------------------------------------

(define-skeleton bsv-sk-prompt-condition
  "Prompt for the loop condition."
  "[condition]: " str )

(define-skeleton bsv-sk-prompt-init
  "Prompt for the loop init statement."
  "[initial statement]: " str )

(define-skeleton bsv-sk-prompt-inc
  "Prompt for the loop increment statement."
  "[increment statement]: " str )

(define-skeleton bsv-sk-prompt-name
  "Prompt for the name of something."
  "[name]: " str)

(define-skeleton bsv-sk-prompt-clock
  "Prompt for the name of something."
  "name and edge of clock(s): " str)

(defvar bsv-sk-reset nil)
(defun bsv-sk-prompt-reset ()
  "Prompt for the name of a state machine reset."
  (setq bsv-sk-reset (read-string "name of reset: " "rst")))


(define-skeleton bsv-sk-prompt-state-selector
  "Prompt for the name of a state machine selector."
  "name of selector (eg {a,b,c,d}): " str )

(define-skeleton bsv-sk-prompt-output
  "Prompt for the name of something."
  "output: " str)

(define-skeleton bsv-sk-prompt-msb
  "Prompt for most significant bit specification."
  "msb:" str & ?: & '(bsv-sk-prompt-lsb) | -1 )

(define-skeleton bsv-sk-prompt-lsb
  "Prompt for least significant bit specification."
  "lsb:" str )

(defvar bsv-sk-p nil)
(define-skeleton bsv-sk-prompt-width
  "Prompt for a width specification."
  ()
  (progn
    (setq bsv-sk-p (point))
    (bsv-sk-prompt-msb)
    (if (> (point) bsv-sk-p) "] " " ")))

(defun bsv-sk-header ()
  "Insert a descriptive header at the top of the file.
See also `bsv-header' for an alternative format."
  (interactive "*")
  (save-excursion
    (goto-char (point-min))
    (bsv-sk-header-tmpl)))

(define-skeleton bsv-sk-header-tmpl
  "Insert a comment block containing the module title, author, etc."
  "[Description]: "
  "//                              -*- Mode: BSV -*-"
  "\n// Filename        : " (buffer-name)
  "\n// Description     : " str
  "\n// Author          : " (user-full-name)
  "\n// Created On      : " (current-time-string)
  "\n// Last Modified By: " (user-full-name)
  "\n// Last Modified On: " (current-time-string)
  "\n// Update Count    : 0"
  "\n// Status          : Unknown, Use with caution!"
  "\n")

(define-skeleton bsv-sk-module
  "Insert a module definition."
  ()
  > "module " '(bsv-sk-prompt-name) " (/*AUTOARG*/ ) ;" \n
  > _ \n
  > (- bsv-indent-level-behavioral) "endmodule" (progn (electric-bsv-terminate-line) nil))

;;; ------------------------------------------------------------------------
;;; Define a default OVM class, with macros and new()
;;; ------------------------------------------------------------------------

(define-skeleton bsv-sk-ovm-class
  "Insert a class definition"
  ()
  > "class " (setq name (skeleton-read "Name: ")) " extends " (skeleton-read "Extends: ") ";" \n
  > _ \n
  > "`ovm_object_utils_begin(" name ")" \n
  > (- bsv-indent-level) " `ovm_object_utils_end" \n
  > _ \n
  > "function new(name=\"" name "\");" \n
  > "super.new(name);" \n
  > (- bsv-indent-level) "endfunction" \n
  > _ \n
  > "endclass" (progn (electric-bsv-terminate-line) nil))

(define-skeleton bsv-sk-uvm-class
  "Insert a class definition"
  ()
  > "class " (setq name (skeleton-read "Name: ")) " extends " (skeleton-read "Extends: ") ";" \n
  > _ \n
  > "`uvm_object_utils_begin(" name ")" \n
  > (- bsv-indent-level) " `uvm_object_utils_end" \n
  > _ \n
  > "function new(name=\"" name "\");" \n
  > "super.new(name);" \n
  > (- bsv-indent-level) "endfunction" \n
  > _ \n
  > "endclass" (progn (electric-bsv-terminate-line) nil))

(define-skeleton bsv-sk-primitive
  "Insert a task definition."
  ()
  > "primitive " '(bsv-sk-prompt-name) " ( " '(bsv-sk-prompt-output) ("input:" ", " str ) " );"\n
  > _ \n
  > (- bsv-indent-level-behavioral) "endprimitive" (progn (electric-bsv-terminate-line) nil))

(define-skeleton bsv-sk-task
  "Insert a task definition."
  ()
  > "task " '(bsv-sk-prompt-name) & ?\; \n
  > _ \n
  > "begin" \n
  > \n
  > (- bsv-indent-level-behavioral) "end" \n
  > (- bsv-indent-level-behavioral) "endtask" (progn (electric-bsv-terminate-line) nil))

(define-skeleton bsv-sk-function
  "Insert a function definition."
  ()
  > "function [" '(bsv-sk-prompt-width) | -1 '(bsv-sk-prompt-name) ?\; \n
  > _ \n
  > "begin" \n
  > \n
  > (- bsv-indent-level-behavioral) "end" \n
  > (- bsv-indent-level-behavioral) "endfunction" (progn (electric-bsv-terminate-line) nil))

(define-skeleton bsv-sk-always
  "Insert always block.  Uses the minibuffer to prompt
for sensitivity list."
  ()
  > "always @ ( /*AUTOSENSE*/ ) begin\n"
  > _ \n
  > (- bsv-indent-level-behavioral) "end" \n >
  )

(define-skeleton bsv-sk-initial
  "Insert an initial block."
  ()
  > "initial begin\n"
  > _ \n
  > (- bsv-indent-level-behavioral) "end" \n > )

(define-skeleton bsv-sk-specify
  "Insert specify block.  "
  ()
  > "specify\n"
  > _ \n
  > (- bsv-indent-level-behavioral) "endspecify" \n > )

(define-skeleton bsv-sk-generate
  "Insert generate block.  "
  ()
  > "generate\n"
  > _ \n
  > (- bsv-indent-level-behavioral) "endgenerate" \n > )

(define-skeleton bsv-sk-begin
  "Insert begin end block.  Uses the minibuffer to prompt for name."
  ()
  > "begin" '(bsv-sk-prompt-name) \n
  > _ \n
  > (- bsv-indent-level-behavioral) "end"
)

(define-skeleton bsv-sk-fork
  "Insert a fork join block."
  ()
  > "fork\n"
  > "begin" \n
  > _ \n
  > (- bsv-indent-level-behavioral) "end" \n
  > "begin" \n
  > \n
  > (- bsv-indent-level-behavioral) "end" \n
  > (- bsv-indent-level-behavioral) "join" \n
  > )


(define-skeleton bsv-sk-case
  "Build skeleton case statement, prompting for the selector expression,
and the case items."
  "[selector expression]: "
  > "case (" str ") " \n
  > ("case selector: " str ": begin" \n > _ \n > (- bsv-indent-level-behavioral) "end" \n > )
  resume: >  (- bsv-case-indent) "endcase" (progn (electric-bsv-terminate-line) nil))

(define-skeleton bsv-sk-casex
  "Build skeleton casex statement, prompting for the selector expression,
and the case items."
  "[selector expression]: "
  > "casex (" str ") " \n
  > ("case selector: " str ": begin" \n > _ \n > (- bsv-indent-level-behavioral) "end" \n > )
  resume: >  (- bsv-case-indent) "endcase" (progn (electric-bsv-terminate-line) nil))

(define-skeleton bsv-sk-casez
  "Build skeleton casez statement, prompting for the selector expression,
and the case items."
  "[selector expression]: "
  > "casez (" str ") " \n
  > ("case selector: " str ": begin" \n > _ \n > (- bsv-indent-level-behavioral) "end" \n > )
  resume: >  (- bsv-case-indent) "endcase" (progn (electric-bsv-terminate-line) nil))

(define-skeleton bsv-sk-if
  "Insert a skeleton if statement."
  > "if (" '(bsv-sk-prompt-condition) & ")" " begin" \n
  > _ \n
  > (- bsv-indent-level-behavioral) "end " \n )

(define-skeleton bsv-sk-else-if
  "Insert a skeleton else if statement."
  > (bsv-indent-line) "else if ("
  (progn (setq bsv-sk-p (point)) nil) '(bsv-sk-prompt-condition) (if (> (point) bsv-sk-p) ") " -1 ) & " begin" \n
  > _ \n
  > "end" (progn (electric-bsv-terminate-line) nil))

(define-skeleton bsv-sk-datadef
  "Common routine to get data definition."
  ()
  '(bsv-sk-prompt-width) | -1 ("name (RET to end):" str ", ") -2 ";" \n)

(define-skeleton bsv-sk-input
  "Insert an input definition."
  ()
  > "input  [" '(bsv-sk-datadef))

(define-skeleton bsv-sk-output
  "Insert an output definition."
  ()
  > "output [" '(bsv-sk-datadef))

(define-skeleton bsv-sk-inout
  "Insert an inout definition."
  ()
  > "inout  [" '(bsv-sk-datadef))

(defvar bsv-sk-signal nil)
(define-skeleton bsv-sk-def-reg
  "Insert a reg definition."
  ()
  > "reg    [" '(bsv-sk-prompt-width) | -1 bsv-sk-signal ";" \n (bsv-pretty-declarations) )

(defun bsv-sk-define-signal ()
  "Insert a definition of signal under point at top of module."
  (interactive "*")
  (let* ((sig-re "[a-zA-Z0-9_]*")
	 (v1 (buffer-substring
	       (save-excursion
		 (skip-chars-backward sig-re)
		 (point))
	       (save-excursion
		 (skip-chars-forward sig-re)
		 (point)))))
    (if (not (member v1 bsv-keywords))
	(save-excursion
	  (setq bsv-sk-signal v1)
	  (bsv-beg-of-defun)
	  (bsv-end-of-statement)
	  (bsv-forward-syntactic-ws)
	  (bsv-sk-def-reg)
	  (message "signal at point is %s" v1))
      (message "object at point (%s) is a keyword" v1))))

(define-skeleton bsv-sk-wire
  "Insert a wire definition."
  ()
  > "wire   [" '(bsv-sk-datadef))

(define-skeleton bsv-sk-reg
  "Insert a reg definition."
  ()
  > "reg   [" '(bsv-sk-datadef))

(define-skeleton bsv-sk-assign
  "Insert a skeleton assign statement."
  ()
  > "assign " '(bsv-sk-prompt-name) " = " _ ";" \n)

(define-skeleton bsv-sk-while
  "Insert a skeleton while loop statement."
  ()
  > "while ("  '(bsv-sk-prompt-condition)  ") begin" \n
  > _ \n
  > (- bsv-indent-level-behavioral) "end " (progn (electric-bsv-terminate-line) nil))

(define-skeleton bsv-sk-repeat
  "Insert a skeleton repeat loop statement."
  ()
  > "repeat ("  '(bsv-sk-prompt-condition)  ") begin" \n
  > _ \n
  > (- bsv-indent-level-behavioral) "end " (progn (electric-bsv-terminate-line) nil))

(define-skeleton bsv-sk-for
  "Insert a skeleton while loop statement."
  ()
  > "for ("
  '(bsv-sk-prompt-init) "; "
  '(bsv-sk-prompt-condition) "; "
  '(bsv-sk-prompt-inc)
  ") begin" \n
  > _ \n
  > (- bsv-indent-level-behavioral) "end " (progn (electric-bsv-terminate-line) nil))

(define-skeleton bsv-sk-comment
  "Inserts three comment lines, making a display comment."
  ()
  > "/*\n"
  > "* " _ \n
  > "*/")

(define-skeleton bsv-sk-state-machine
  "Insert a state machine definition."
  "Name of state variable: "
  '(setq input "state")
  > "// State registers for " str | -23 \n
  '(setq bsv-sk-state str)
  > "reg [" '(bsv-sk-prompt-width) | -1 bsv-sk-state ", next_" bsv-sk-state ?\; \n
  '(setq input nil)
  > \n
  > "// State FF for " bsv-sk-state \n
  > "always @ ( " (read-string "clock:" "posedge clk") " or " (bsv-sk-prompt-reset) " ) begin" \n
  > "if ( " bsv-sk-reset " ) " bsv-sk-state " = 0; else" \n
  > bsv-sk-state " = next_" bsv-sk-state ?\; \n
  > (- bsv-indent-level-behavioral) "end" (progn (electric-bsv-terminate-line) nil)
  > \n
  > "// Next State Logic for " bsv-sk-state \n
  > "always @ ( /*AUTOSENSE*/ ) begin\n"
  > "case (" '(bsv-sk-prompt-state-selector) ") " \n
  > ("case selector: " str ": begin" \n > "next_" bsv-sk-state " = " _ ";" \n > (- bsv-indent-level-behavioral) "end" \n )
  resume: >  (- bsv-case-indent) "endcase" (progn (electric-bsv-terminate-line) nil)
  > (- bsv-indent-level-behavioral) "end" (progn (electric-bsv-terminate-line) nil))


;;
;; Include file loading with mouse/return event
;;
;; idea & first impl.: M. Rouat (eldo-mode.el)
;; second (emacs/xemacs) impl.: G. Van der Plas (spice-mode.el)

(if (featurep 'xemacs)
    (require 'overlay))

(defconst bsv-include-file-regexp
  "^`include\\s-+\"\\([^\n\"]*\\)\""
  "Regexp that matches the include file.")

(defvar bsv-mode-mouse-map
  (let ((map (make-sparse-keymap))) ; as described in info pages, make a map
    (set-keymap-parent map bsv-mode-map)
    ;; mouse button bindings
    (define-key map "\r"            'bsv-load-file-at-point)
    (if (featurep 'xemacs)
	(define-key map 'button2    'bsv-load-file-at-mouse);ffap-at-mouse ?
      (define-key map [mouse-2]     'bsv-load-file-at-mouse))
    (if (featurep 'xemacs)
	(define-key map 'Sh-button2 'mouse-yank) ; you wanna paste don't you ?
      (define-key map [S-mouse-2]   'mouse-yank-at-click))
    map)
  "Map containing mouse bindings for `bsv-mode'.")


(defun bsv-highlight-region (beg end old-len)
  "Colorize included files and modules in the (changed?) region.
Clicking on the middle-mouse button loads them in a buffer (as in dired)."
  (when (or bsv-highlight-includes
	    bsv-highlight-modules)
    (save-excursion
      (save-match-data  ;; A query-replace may call this function - do not disturb
	(bsv-save-buffer-state
	 (bsv-save-scan-cache
	  (let (end-point)
	    (goto-char end)
	    (setq end-point (point-at-eol))
	    (goto-char beg)
	    (beginning-of-line)  ; scan entire line
	    ;; delete overlays existing on this line
	    (let ((overlays (overlays-in (point) end-point)))
	      (while overlays
		(if (and
		     (overlay-get (car overlays) 'detachable)
		     (or (overlay-get (car overlays) 'bsv-include-file)
			 (overlay-get (car overlays) 'bsv-inst-module)))
		    (delete-overlay (car overlays)))
		(setq overlays (cdr overlays))))
	    ;;
	    ;; make new include overlays
	    (when bsv-highlight-includes
	      (while (search-forward-regexp bsv-include-file-regexp end-point t)
		(goto-char (match-beginning 1))
		(let ((ov (make-overlay (match-beginning 1) (match-end 1))))
		  (overlay-put ov 'start-closed 't)
		  (overlay-put ov 'end-closed 't)
		  (overlay-put ov 'evaporate 't)
		  (overlay-put ov 'bsv-include-file 't)
		  (overlay-put ov 'mouse-face 'highlight)
		  (overlay-put ov 'local-map bsv-mode-mouse-map))))
	    ;;
	    ;; make new module overlays
	    (goto-char beg)
	    ;; This scanner is syntax-fragile, so don't get bent
	    (when bsv-highlight-modules
	      (condition-case nil
		  (while (bsv-re-search-forward-quick "\\(/\\*AUTOINST\\*/\\|\\.\\*\\)" end-point t)
		    (save-excursion
		      (goto-char (match-beginning 0))
		      (unless (bsv-inside-comment-or-string-p)
			(bsv-read-inst-module-matcher)   ;; sets match 0
			(let* ((ov (make-overlay (match-beginning 0) (match-end 0))))
			  (overlay-put ov 'start-closed 't)
			  (overlay-put ov 'end-closed 't)
			  (overlay-put ov 'evaporate 't)
			  (overlay-put ov 'bsv-inst-module 't)
			  (overlay-put ov 'mouse-face 'highlight)
			  (overlay-put ov 'local-map bsv-mode-mouse-map)))))
		(error nil)))
	    ;;
	    ;; Future highlights:
	    ;;  variables - make an Occur buffer of where referenced
	    ;;  pins - make an Occur buffer of the sig in the declaration module
	    )))))))

(defun bsv-highlight-buffer ()
  "Colorize included files and modules across the whole buffer."
  ;; Invoked via bsv-mode calling font-lock then `font-lock-mode-hook'
  (interactive)
  ;; delete and remake overlays
  (bsv-highlight-region (point-min) (point-max) nil))

;; Deprecated, but was interactive, so we'll keep it around
(defalias 'bsv-colorize-include-files-buffer 'bsv-highlight-buffer)

;; ffap-at-mouse isn't useful for BSV mode. It uses library paths.
;; so define this function to do more or less the same as ffap-at-mouse
;; but first resolve filename...
(defun bsv-load-file-at-mouse (event)
  "Load file under button 2 click's EVENT.
Files are checked based on `bsv-library-flags'."
  (interactive "@e")
  (save-excursion ;; implement a BSV specific ffap-at-mouse
    (mouse-set-point event)
    (bsv-load-file-at-point t)))

;; ffap isn't usable for BSV mode. It uses library paths.
;; so define this function to do more or less the same as ffap
;; but first resolve filename...
(defun bsv-load-file-at-point (&optional warn)
  "Load file under point.
If WARN, throw warning if not found.
Files are checked based on `bsv-library-flags'."
  (interactive)
  (save-excursion ;; implement a BSV specific ffap
    (let ((overlays (overlays-in (point) (point)))
	  hit)
      (while (and overlays (not hit))
	(when (overlay-get (car overlays) 'bsv-inst-module)
	  (bsv-goto-defun-file (buffer-substring
				    (overlay-start (car overlays))
				    (overlay-end (car overlays))))
	  (setq hit t))
	(setq overlays (cdr overlays)))
      ;; Include?
      (beginning-of-line)
      (when (and (not hit)
		 (looking-at bsv-include-file-regexp))
	(if (and (car (bsv-library-filenames
		       (match-string 1) (buffer-file-name)))
		 (file-readable-p (car (bsv-library-filenames
					(match-string 1) (buffer-file-name)))))
	    (find-file (car (bsv-library-filenames
			     (match-string 1) (buffer-file-name))))
	  (when warn
	    (message
	     "File '%s' isn't readable, use shift-mouse2 to paste in this field"
	     (match-string 1))))))))

;;
;; Bug reporting
;;

(defun bsv-faq ()
  "Tell the user their current version, and where to get the FAQ etc."
  (interactive)
  (with-output-to-temp-buffer "*bsv-mode help*"
    (princ (format "You are using bsv-mode %s\n" bsv-mode-version))
    (princ "\n")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst bsv-start-end-alist
  (list
   (list "action" "endaction")
   (list "actionvalue" "endactionvalue")
   (list "begin" "end")
   (list "case" "endcase")
   (list "function" "endfunction")
   (list "interface" "endinterface")
   (list "method" "endmethod")
   (list "module" "endmodule")
   (list "package" "endpackage")
   (list "rule" "endrule")
   (list "rules" "endrules")
   (list "seq" "endseq")
   (list "par" "endpar")
   (list "if" "else")
   (list "instance" "endinstance")
   (list "typeclass" "endtypeclass")
;;   (list "{" "}")
   ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst bsv-end-start-alist
  (mapcar 'reverse bsv-start-end-alist))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst bsv-start-only-list
      (list "if" 
	    "else" 
	    "for"
	    "while"
	    "tagged"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst bsv-block-start-end-re
  (eval-when-compile
    (bsv-regexp-opt
     (append
      bsv-start-only-list
      (mapcar 'car bsv-start-end-alist)
      (mapcar 'cadr bsv-start-end-alist))
     'words)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst bsv-block-start-re
  (eval-when-compile
    (bsv-regexp-opt
     (mapcar 'car bsv-start-end-alist)
     'words)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst bsv-block-end-re
  (eval-when-compile
    (bsv-regexp-opt
     (mapcar 'cadr bsv-start-end-alist)
     'words)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst bsv-block-start-only-re
  (eval-when-compile
    (bsv-regexp-opt
     bsv-start-only-list
     'words)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun bsv-complete-or-indent-command ()
  (interactive)
  (cond
   ((looking-at "^")
    (bsv-indent-line))
   ((bsv-inside-tag-p)
    (bsv-indent-line))
;    (bsv-combined-completion))
   (t
    (bsv-indent-line))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun bsv-inside-tag-p ()
 (let (tag inside-p)
  (setq tag (bsv-find-tag-and-match))
  (setq inside-p nil)
  (unless (null tag)
   (setq inside-p
    (and (<= (point) (match-end 0))
     (> (point) (match-beginning 0)))))
  (cond
   (inside-p tag)
   (t nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun bsv-find-tag-and-match ()
 (let (tag)
  (setq tag nil)
  (save-excursion
   (while (looking-at "\\sw\\|\\s_")
    (forward-char 1))
   (if (or (re-search-backward "\\sw\\|\\s_"
	    (save-excursion (beginning-of-line) (point))
	    t)
	(re-search-forward "\\(\\sw\\|\\s_\\)+"
	 (save-excursion (end-of-line) (point))
	 t))
    (progn (goto-char (match-end 0))
     (setq tag (buffer-substring (point)
		(progn (forward-sexp -1)
		 (while (looking-at "\\s'")
		  (forward-char 1))
		 (point))))))
   (unless (null tag)
     (progn
       (let (pos)
	 (setq pos (string-match "^[ \t]*\\[.*" tag))
	 (if (not (null pos)) 
	     (while (not (null pos))
	       (progn
		 (setq tag (substring tag 1))
	 	 (setq pos (string-match "^[ \t]*\\[.*" tag))))))
       (re-search-forward tag () t))))
  tag))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun bsv-calculate-indent-offset (start-word end-word)
  (let (default-offset offset)
    (setq default-offset bsv-indent-level)
    (setq offset default-offset)
    (cond
     ((string-equal start-word (bsv-get-matching-start-keyword end-word))
      (setq offset 0))
     ((and
       (string-equal start-word "method")
       (string-equal end-word "method"))
      (setq offset 0))
     ((and
       (string-equal start-word "if")
       (string-equal end-word "else"))
      (setq offset 0))
     ((and
       (string-equal start-word "else")
       (string-equal end-word "else"))
      (setq offset 0))
     ((string-equal start-word "package")
      (setq offset 0)))
    offset))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(setq bsv-package-point nil)

(defun bsv-update-package-point ()
  (save-excursion
    (if (not (null bsv-package-point))
	(let (word)
	  (goto-char bsv-package-point)
	  (setq word (current-word t))
	  (if (and (not (null word)) (string-equal word "package"))
	      (let (indent)
		(move-to-column (current-indentation))
		(setq bsv-package-point (point)))
	    (setq bsv-package-point nil)
	    (bsv-update-package-point)))
      (setq bsv-package-point
	    (bsv-search-backward-regexp (regexp-opt (list "package") 'word) (point-min) t))
      (if (null bsv-package-point)
	  (let ()
	    (goto-char (point-max))
	    (setq bsv-package-point
		  (bsv-search-backward-regexp (regexp-opt (list "package") 'word) (point-min) t))
	    )))))

(defun bsv-get-package-column ()
  (if (null bsv-package-point)
      0
    (save-excursion
      (goto-char bsv-package-point)
      (current-column))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(setq bsv-multiple-indent-current-point nil)
(setq bsv-multiple-indent-list nil)
(setq bsv-multiple-indent-num 0)
(setq bsv-multiple-indent-tick (buffer-modified-tick))

(if (string-match "^20." emacs-version)
    (setq modified-tick-delta-limit 0)
  (setq modified-tick-delta-limit 21))

(defun bsv-multiple-indent-unchanged-p ()
  (let (delta)
    (setq delta (- (buffer-modified-tick) bsv-multiple-indent-tick))
    (and
     (eq (line-beginning-position) bsv-multiple-indent-current-point)
     (<= delta  modified-tick-delta-limit))))

(defun bsv-multiple-indent-reset ()
  (setq bsv-multiple-indent-current-point (line-beginning-position))
  (setq bsv-multiple-indent-list nil)
  (setq bsv-multiple-indent-num 0)
  (setq bsv-multiple-indent-tick (buffer-modified-tick)))

(defun bsv-multiple-indent-update ()
  (setq bsv-multiple-indent-current-point (line-beginning-position))
  (setq bsv-multiple-indent-tick (buffer-modified-tick)))

(defun bsv-indent-line ()
  (let (pos col shift)
    (setq pos (point))
    (bsv-indent-line-multiple)
    (setq shift (- (point) pos))))

(defun bsv-indent-line-multiple ()
  (let (col-orig col length n)
    (setq col-orig (current-indentation))
    (if (bsv-multiple-indent-unchanged-p)
	(setq bsv-multiple-indent-num (+ bsv-multiple-indent-num 1))
      (bsv-multiple-indent-reset)
      (bsv-update-package-point)
      (setq bsv-multiple-indent-list 
	    (bsv-sort-indent-list-closest-first col-orig (bsv-get-combined-indent-list)))
      (if (eq col-orig (car bsv-multiple-indent-list))
	  (setq bsv-multiple-indent-list 
		(append (cdr bsv-multiple-indent-list) 
			(list (car bsv-multiple-indent-list))))))
    (setq length (length bsv-multiple-indent-list))
    (if (> length 0)
	(let ()
	  (setq n (mod bsv-multiple-indent-num length))
	  (setq col (nth n bsv-multiple-indent-list))
	  (if (not (null col))
	      (let ()
		(indent-line-to col)
		(bsv-multiple-indent-update))
	    )))))
  
(defun bsv-indent-line-conservative ()
  (let (col indent-list)
    (setq col (current-indentation))
    (setq indent-list (bsv-get-combined-indent-list 1))
    (if (eq col (car indent-list))
	()
      (setq indent-list (bsv-get-combined-indent-list))
      (bsv-indent-line-to-closest col indent-list))))

(defun bsv-indent-line-basic ()
  (let (indent-list)
    (setq indent-list (bsv-get-combined-indent-list 1))
    (if (not (null indent-list))
	(indent-line-to (car indent-list)))))

(defun bsv-indent-line-to-closest (col indent-list)
  (if (not (null indent-list))
	(let ()
	  (setq indent-list (bsv-sort-indent-list-closest-first col indent-list))
	  (indent-line-to (car indent-list)))))

(defun bsv-sort-indent-list-closest-first (col indent-list)
  (sort indent-list 
	(lambda (l r) (< (abs (- l col)) (abs (- r col))))))

(defun bsv-get-combined-indent-list (&optional limit)
  (let (paren-indent block-indent-list)
    (setq paren-indent (bsv-calculate-paren-indent))
    (setq block-indent-list (bsv-get-block-indent-list limit))
    (if (not (null paren-indent))
	(let (col (default-offset 3))
	  (setq col 
		(min
		 paren-indent
		 (+ (bsv-get-start-paren-line-indentation) default-offset)))
	  (setq block-indent-list
		(mapcar (lambda (x) (max x col)) block-indent-list))
	  (remove-duplicates (cons col (cons paren-indent block-indent-list))))
      block-indent-list)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun bsv-calculate-paren-indent ()
  (let ((state
	 (save-excursion
	   (beginning-of-line)
	   (parse-partial-sexp (point-min) (point))))
	column)
    (cond 
     ((and
       (/= 0 (nth 0 state))
       (not (null (nth 1 state))))
      (save-excursion
	(goto-char (nth 1 state))
	(setq column (+ 1 (current-column))))
      column))))

(defun bsv-get-start-paren-line-indentation ()
  (let ((state
	 (save-excursion
	   (beginning-of-line)
	   (parse-partial-sexp (point-min) (point))))
	column)
    (cond 
     ((and
       (/= 0 (nth 0 state))
       (not (null (nth 1 state))))
      (save-excursion
	(goto-char (nth 1 state))
	(setq column (current-indentation)))
      column))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun bsv-get-block-indent-list (&optional limit)
  (let (col-orig point-orig start-word start-col current-word
		 (done-p nil) (num 1) (current-indent 1) (indents ()))
    (setq col-orig (current-indentation))
    (setq point-orig (point))
    (if (null limit) (setq limit 50))
    (save-excursion
      (while (and (not done-p) (<= num limit))
	(setq values (bsv-block-indent-line num))
	(setq current-indent (current-indentation))
	(setq start-word (second values))
	(setq current-word (third values))
	(setq start-col (fourth values))
	(if (not (null start-word))
	    (setq indents (cons current-indent indents)))
	(if (bsv-multiple-indents-p start-word start-col current-word)
	    (setq num (+ num 1))
	  (setq done-p t))))
    (indent-line-to col-orig)
    (goto-char point-orig)
    (if (null indents) (setq indents (list 0)))
    (reverse (remove-duplicates indents))))

(defun bsv-block-indent-line (&optional num)
  (let (values col start-word current-word)
    (setq values (bsv-calculate-block-indent num))
    (setq col (car values))
    (if (null col) (setq col 0))
    (cond
     ((not (null col))
      (indent-line-to col)))
    values))
    

(defun bsv-calculate-block-indent (&optional num)
  (let (none-p point-orig start-word start-col current-word col start-word-2 offset)
    (save-excursion
      (beginning-of-line)
      (skip-chars-forward " \t" (line-end-position))
      (setq point-orig (point))
      (setq current-word (current-word t))
      (if (and (not (null current-word)) (string-equal current-word "endinterface"))
	  (let ()
	    (setq none-p
		  (or
		   none-p
		   (bsv-goto-next-enclosing-start-keyword nil)))
	    (setq none-p
		  (or
		   none-p
		   (bsv-goto-enclosing-start-keyword (- num 1) t))))
	(setq none-p
	      (or
	       none-p
	       (bsv-goto-enclosing-start-keyword num t))))
      (if (not none-p)
	  (let ()
	    (setq start-word (current-word t))
	    (setq col (current-column))
	    (setq start-col (current-column))
	    (if  (and (not (null start-word)) (bsv-start-keyword-p start-word))
		(progn
		  (beginning-of-line)
		  (skip-chars-forward " \t" (line-end-position))
		  (setq start-word-2 (current-word t))
		  (if (and
		       (not (null start-word-2))
		       (not (string-equal start-word start-word-2))
		       (bsv-start-only-keyword-p start-word-2)
		       )
		      (progn
			(setq col (current-column)))))
	      (if (not (member start-word bsv-start-only-list))
		  (let ()
		    (setq start-word nil)
		    (setq start-col nil)))
	      )))
      (if (and (not none-p) (eq point-orig (point)))
	  (let ()
	    (setq none-p t)
	    (setq col 0)))
      )
    (cond
     ((not none-p)
      (setq offset (bsv-calculate-indent-offset start-word current-word))
      (setq col (+ col offset))))
    (list col start-word current-word start-col)))

(defun bsv-multiple-indents-p (start-word start-col current-word)
  (if (and 
       (not (null start-col))
       (not (null bsv-package-point))
       (<= start-col (bsv-get-package-column)))
      nil
    (or 
     (and (string-equal start-word "interface") (null current-word))
     (and (string-equal start-word "module") (null current-word))
     (and (string-equal start-word "function") (null current-word))
     (and (string-equal start-word "method") (null current-word))
     (and (string-equal start-word "interface") (string-equal current-word "endinterface"))
     (and (string-equal start-word "interface") (string-equal current-word "interface"))
     (and (string-equal start-word "interface") (string-equal current-word "method"))
;     (and (string-equal start-word "method") (string-equal current-word "method"))
     (and (string-equal start-word "method") (string-equal current-word "interface"))
     (and (string-equal start-word "module") (string-equal current-word "module"))
     (and (string-equal start-word "module") (string-equal current-word "function"))
     (and (string-equal start-word "function")))))

(defun bsv-start-current-possible-p (start-word current-word)
  (not
   (and (string-equal start-word "method") (string-equal current-word "interface"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; The "strict" flag requires that interface/endinterface pairs must be aligned
;;; to "match".
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun bsv-goto-enclosing-start-keyword (num strict)
  (if (null num) (setq num 1))
  (if (> num 0)
      (let (point-0 point-1)
	(save-excursion
	  (setq point-0 (point))
	  (bsv-goto-next-enclosing-start-keyword strict)
	  (setq point-1 (point)))
	(if (not (eq point-0 point-1))
	    (let ()
	      (goto-char point-1)
	      (bsv-goto-enclosing-start-keyword (- num 1) strict))))))

(defun bsv-goto-next-enclosing-start-keyword (strict)
  (let (case-fold-search point none-p current-word current-col repeat)
    (setq case-fold-search nil)
    (save-excursion
      (setq current-word (current-word t))
      (if (not (null current-word))
	  (let ()
	    (forward-char 1)
	    (forward-word -1))
	(beginning-of-line)
	(skip-chars-forward " \t" (line-end-position)))
      (setq current-word (current-word t))
      (if strict (setq current-col (current-indentation)))
      (if (and (not (null current-word)) (bsv-end-keyword-p current-word))
	  (let ()
	    (setq none-p
		  (bsv-goto-matching-start-keyword current-word current-col))
	    (if (not none-p) (setq point (point))))
	(if (and
	     (not (null current-word))
	     (bsv-end-keyword-p current-word)
	     (not (string-equal current-word "else")))
	    (setq none-p t)
	  (if (string-equal current-word "else")
	      (setq point 
		    (bsv-search-backward-regexp "\\<\\(if\\)\\>" nil t))
	    (setq point 
		  (bsv-search-backward-regexp 
		   (concat bsv-block-start-end-re "\\|;[ \t]*$") nil t)))
	  (setq none-p (null point)))
	(if (not none-p)
	    (let ()
	      (setq current-word (current-word t))
	      (if (or
		   (looking-at ";[ \t]*$")
		   (bsv-start-only-keyword-p current-word))
		  (progn
		    (setq point (point))
		    (if (looking-at ";[ \t]*$") 
			(progn
			  (setq none-p t))))
		(setq none-p t))))
	(if (and
	     (not none-p)
	     (string-equal current-word "if"))
	    (progn
	      (backward-word 1)
	      (if (looking-at "else[ \t]+if")
		  (setq point (point)))))
	(if (and
	     (not none-p)
	     (string-equal current-word "tagged"))
	    (progn
	      (backward-word 1)
	      (if (looking-at "matches[ \t]+tagged")
		  (let ()
		    (setq repeat t)
		    (setq none-p t)
		    (setq point (point))))))
      ))
    (cond 
     ((not none-p) 
      (goto-char point))
     (repeat
      (goto-char point)
      (setq none-p 
	    (bsv-goto-next-enclosing-start-keyword strict)))
     (t
      (setq none-p 
	    (bsv-goto-next-enclosing-start-keyword-internal strict))))
    none-p))

(defun bsv-goto-next-enclosing-start-keyword-internal (strict)
  (let (case-fold-search point none-p orig-word current-word current-col)
    (setq case-fold-search nil)
    (setq orig-word (current-word t))
    (save-excursion
      (setq point 
	    (bsv-search-backward-regexp bsv-block-start-end-re nil t))
      (setq none-p (null point))
      (if (not none-p)
	  (let ()
	    (setq current-word (current-word t))
	    (if strict (setq current-col (current-indentation)))
	    (cond
	     ((and (not (null orig-word)) 
		   (not (bsv-start-current-possible-p current-word orig-word)))
	      (setq none-p
		    (or none-p
			(bsv-goto-next-enclosing-start-keyword-internal strict))))
	     ((eq (point) (point-min)) 
	      nil)
	     ((looking-at ";[ \t]*$")
	      (setq none-p
		    (or none-p
			(bsv-goto-next-enclosing-start-keyword-internal strict))))
	     ((bsv-end-keyword-p current-word)
	      (setq none-p
		    (or none-p
			(bsv-goto-matching-start-keyword current-word current-col)))
	      (setq none-p
		    (or none-p
			(bsv-goto-next-enclosing-start-keyword-internal strict))))
	     ((bsv-start-only-keyword-p current-word)
	      (setq none-p
		    (or none-p
			(bsv-goto-next-enclosing-start-keyword-internal strict))))
	     )))
      (if (not none-p)
	  (setq point (point))))
    (if (not none-p) (goto-char point))
    none-p))

(defun bsv-goto-matching-start-keyword (end-word end-col)
  (let (case-fold-search current-word current-col start-word none-p point)
    (setq case-fold-search nil)
    (setq start-word (bsv-get-matching-start-keyword end-word))
    (save-excursion
      (if (not (null start-word))
	  (let (point)
	    (setq point (bsv-search-backward-regexp bsv-block-start-end-re nil t))
;;	    (setq point (bsv-search-backward-regexp (regexp-opt (list start-word) 'words) nil t))
	    (setq none-p (null point))
	    (if (not none-p)
		(let ()
		  (setq current-word (current-word t))
		  (setq current-col (current-indentation))
		  (cond
		   ((eq (point) (point-min)) nil)
		   ((or
		     (not (string-equal current-word start-word))
		     (and (not (null end-col))
			  (not (<= current-col end-col)) 
			  (string-equal start-word "interface"))
		     (and (or (string-equal start-word "function")
			      (string-equal start-word "module"))
			  (> (current-column) current-col)))
		    (if (bsv-end-keyword-p current-word)
			(setq none-p
			      (or none-p
				  (bsv-goto-matching-start-keyword current-word current-col))
			      ))
		    (setq none-p
			  (or none-p
			      (bsv-goto-matching-start-keyword end-word end-col))))))))
	(setq none-p t))
      (setq point (point)))
    (if (not none-p) 
	(goto-char point))
    none-p))
  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun bsv-search-backward-regexp (regexp &optional bound noerror count)
  (let (point)
    (setq point (search-backward-regexp regexp bound noerror count))
    (cond
     ((null point) nil)
     ((bsv-in-comment-or-string-p)
      (setq point (bsv-search-backward-regexp regexp bound noerror count))))
    point))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun bsv-get-matching-start-keyword (word)
  (cadr
   (assoc word bsv-end-start-alist)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun bsv-get-matching-end-keyword (word)
  (cadr
   (assoc word bsv-start-end-alist)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun bsv-start-keyword-p (word)
  (string-match bsv-block-start-re word))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun bsv-end-keyword-p (word)
  (string-match bsv-block-end-re word))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun bsv-start-only-keyword-p (word)
  (string-match bsv-block-start-only-re word))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun bsv-goto-most-recent-line-indent ()
  (let (col ignore)
    (setq col -1)
      (while (< col 0)
	(forward-line -1)
	(end-of-line)
	(setq ignore (bsv-inside-comment-p))
	(beginning-of-line)
	(setq ignore (or ignore (bsv-inside-comment-p)))
	(if (not ignore)
	    (setq col (current-indentation))
	  (if (and (< col 0)
		   (eq (point) (point-min)))
	      (setq col (current-column)))))
      (beginning-of-line)
      (forward-char col)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun bsv-inside-comment-p ()
  "Check if point inside a nested comment."
  (save-excursion
    (let ((st-point (point)) hitbeg value)
      (or (search-backward "//" (line-beginning-position) t)
	  (if (progn
		;; This is for tricky case //*, we keep searching if /* is proceeded by // on same line
		(while (and (setq hitbeg (search-backward "/*" nil t))
			    (progn (forward-char 1) (search-backward "//" (bsv-get-beg-of-line) t))))
		hitbeg)
	      (not (search-forward "*/" st-point t)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun bsv-indent-region  (start end column)  
  (interactive "r\nP")
  (bsv-update-package-point)
  (indent-region start end column)
  (when transient-mark-mode
    (deactivate-mark)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun bsv-recenter-and-font-lock-fontify-buffer (arg)
  "Recenter, then fontify buffer"
  (interactive "P")
  (recenter arg)
  (font-lock-fontify-buffer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun bsv-current-year-string ()
  (let (time-string)
    (setq time-string (current-time-string))
    (substring time-string -4)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun bsv-add-comment-bar ()
  (interactive)
  (unless (looking-at "^")
    (insert "\n"))
  (insert "////////////////////////////////////////////////////////////////////////////////\n")
  (insert "///\n")
  (insert "////////////////////////////////////////////////////////////////////////////////\n")
  (insert "\n"))

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ;;; The font-lock personalization.
;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defconst bsv-font-lock-keywords-1 nil
;;   "Subdued level highlighting for BSV modes.")

;; (defconst bsv-font-lock-keywords-2 nil
;;   "Medium level highlighting for BSV modes.")

;; (defconst bsv-font-lock-keywords-3 nil
;;   "Gaudy level highlighting for BSV modes.")

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ;;;
;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defun font-lock-match-bsv-style-declaration-item-and-skip-to-next (limit)
;;   ;; Match, and move over, any declaration/definition item after point.
;;   ;; The expect syntax of an item is "word" or "word::word", possibly ending
;;   ;; with optional whitespace and a "(".  Everything following the item (but
;;   ;; belonging to it) is expected to by skip-able by `forward-sexp', and items
;;   ;; are expected to be separated with a " ".
;;   (if (looking-at "[ \t*&]*\\(\\sw+\\)\\(::\\(\\sw+\\)\\)?[ \t]*\\((\\)?")
;;       (save-match-data
;; 	(condition-case nil
;; 	    (save-restriction
;; 	      ;; Restrict to the end of line, currently guaranteed to be LIMIT.
;; 	      (narrow-to-region (point-min) limit)
;; 	      (goto-char (match-end 1))
;; 	      ;; Move over any item value, etc., to the next item.
;; 	      (while (not (looking-at "[ \t]*\\([ ]\\|$\\)"))
;; 		(goto-char (or (scan-sexps (point) 1) (point-max))))
;; 	      (goto-char (match-end 0)))
;; 	  (error t)))))



;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ;;;
;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (let ((bsv-keywords
;;        (bsv-regexp-opt
;; 	(append
;; 	 (list "typedef" "import" "export" "tagged")
;; 	 (list "provisos" "return" "matches" "match")
;;          (list "union" "struct" "type" "void")
;; 	 bsv-start-only-list
;; 	 (mapcar 'car bsv-start-end-alist)
;; 	 (mapcar 'cadr bsv-start-end-alist))))
;;       (bsv-type-types
;;        (concat
;; 	"enum\\|"
;; 	"Action\\|"
;; 	"Bool\\|Bit\\|"
;; 	"Integer\\|Int\\|Nat\\|"
;; 	"Vector\\|List\\|ListN\\|"
;; 	)
;;        ))
;;  (setq bsv-font-lock-keywords-1
;;   (list
;;    ;;
;;    ;; These are all anchored at the beginning of line for speed.
;;    ;;

;;    ;; Fontify comments.
;;    '("\\([ \t]*//+.*\\)" 1 font-lock-comment-face t)
;;    '("\\(/\\*.*\\*/\\)" 1 font-lock-comment-face t)

;;    ;; Fontify attributes
;;    '("synthesize" 0 font-lock-reference-face)
;;    '("noinline" 0 font-lock-reference-face)
;;    '("always_enabled" 0 font-lock-reference-face)
;;    '("always_ready" 0 font-lock-reference-face)
;;    '("no_implicit_conditions" 0 font-lock-reference-face)
;;    '("fire_when_enabled" 0 font-lock-reference-face)

;;    ;; and other stuff
;;    '("\\(^[ \t]*\\|[ \t]+\\)package[ \t]+\\(\\sw+\\)[ \t]*" 2 font-lock-function-name-face)
;;    '("\\(^[ \t]*\\|[ \t]+\\)module[ \t]+\\(\\sw+#*\\)[ \t]*" 2 font-lock-function-name-face)
;;    '("\\(^[ \t]*\\|[ \t]+\\)interface[ \t]+\\(\\sw+\\)[ \t]*" 2 font-lock-function-name-face)
;;    '("\\(^[ \t]*\\|[ \t]+\\)rule[ \t]+\\(\\sw+\\)[ \t]*" 2 font-lock-function-name-face)
;;    '("\\(^[ \t]*\\|[ \t]+\\)end[^ \t]+:[ \t]+\\(\\sw+\\)[ \t]*" 2 font-lock-function-name-face)

;;    ;; Fontify all builtin keywords.
;;    (cons (concat "\\<\\(" bsv-keywords "\\)\\>") 'font-lock-keyword-face)

;;    ))

;;  (setq bsv-font-lock-keywords-2
;;   (append bsv-font-lock-keywords-1
;;    (list
;;     ;;
;;     ;; Simple regexps for speed.
;;     ;;
;;     ;; Fontify all type specifiers.

;;     `("\\(^[ \t]*\\|(\\|const[ \t]+\\)\\(list\\)[ \t]+" 2 font-lock-type-face)
;;     (cons "\\<const\\>\\|\\<abstract\\>\\|\\<xx\\>" 'font-lock-type-face)
;;     (cons (concat "\\<\\(" bsv-type-types "\\)\\>") 'font-lock-type-face)

;;     )))

;;  (setq bsv-font-lock-keywords-3
;;   (append 
;;    bsv-font-lock-keywords-2
   
;;    (list
    
;;     ;; Fontify variable names.
;;     '("\\(\\sw+\\)[ \t]+=" 1 font-lock-variable-name-face)
;;     '("\\(@\\|[ \t(]ref[ \t]+\\|[ \t(]prepend[ \t]+\\)\\(\\sw+\\)" 2 font-lock-variable-name-face)

;;     ;; More complicated regexps for more complete highlighting for types.
;;     ;;
;;     ;; Fontify all type specifiers, plus their items.
;;     (list (concat "\\<\\(" "list\\|" bsv-type-types "\\)\\>"
;; 		  "\\([ \t*&]+\\sw+\\>\\)*")
;; 	  ;; Fontify each declaration item.
;; 	  '(font-lock-match-bsv-style-declaration-item-and-skip-to-next
;; 	    ;; Start with point after all type specifiers.
;; 	    (goto-char (or (match-beginning 8) (match-end 1)))
;; 	    ;; Finish with point after first type specifier.
;; 	    (goto-char (match-end 1))
;; 	    ;; Fontify as a variable or function name.
;; 	    (1 (if (match-beginning 4)
;; 		   font-lock-function-name-face
;; 		 font-lock-variable-name-face))))

;;     )))
;;  )

;; (defvar bsv-font-lock-keywords bsv-font-lock-keywords-1
;;   "Default expressions to highlight in BSV mode.")

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ;;;
;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (unless bsv-running-on-xemacs
;;   (push 
;;    (cons 'bsv-mode
;; 	 '((bsv-font-lock-keywords bsv-font-lock-keywords-1
;; 				   bsv-font-lock-keywords-2 bsv-font-lock-keywords-3)
;; 	   nil nil ((?_ . "w")) bsv-beg-of-defun
;; 	   (font-lock-mark-block-function . bsv-mark-function)))
;;    font-lock-defaults-alist))
  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; the following keys and commands are useful to allow you to hit a single key
;;   and compile the buffer (f3 in this example below).  If you have errors 
;;   hit the f4 key and emacs will look at the error lines in *compilation*
;;   open the file that the error occurred in, and move the cursor the the
;;   place the error occurred

;; (global-set-key [f3]  'bsv-compile)
;; (global-set-key [f4]  'bsv-goto-error-from-compilation-buffer)
;; (global-set-key [f5]  'bsv-goto-error)

;; this is the regexp used to look for the last error message
(setq   bsv-error1-regexp  "\"\\([^\n\"\\]+bsv\\)[\\\"]*\", line \\([0-9]+\\), column \\([0-9]+\\)")

;; this is the default command to compile the current buffer with
(defvar bsc-compile-command "bsc -u -verilog -keep-fires -cross-info -aggressive-conditions")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; you can use a make call if you wish
;; if the buffer is Foo.bsv, this will call "make mkFoo.v"
(defun bsv-make ()
  (interactive)
  (let (bsv verilog)
    (setq bsv (buffer-name))
    (setq verilog (concat "mk" bsv))
    (if (string-match "bsv" verilog)
        (compile (concat "make " (replace-match "v" nil 1 verilog))))))

;; the interactive compile command
(defun bsv-compile ()
  (interactive)
  (compile (concat bsc-compile-command " " (buffer-name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun bsv-goto-error ()
  "Goto to file, line, character based in line that looks like 
\"./ViterbiEnc.bsv\", line 40, column 25: (T0007) Error:
"
  (interactive)
  (save-excursion
    ;; search back for suitable regexp
    (if (search-backward-regexp bsv-error1-regexp (point-min) t) 
	(let ((file   (match-string 1))
	      (line   (string-to-int (match-string 2)))
	      (column (string-to-int (match-string 3))))
	  (find-file-other-window file)
	  (goto-line line)
	  (forward-char (- column 1))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; this function will switch to the *compilation* buffer
;; find the error line, jump to the file that has
;; the error and goto that file
(defun bsv-goto-error-from-compilation-buffer ()
  (interactive)
  (let ((this-buffer (buffer-name))
        (file   "")
        (line   0)
        (column 0))

    (save-excursion
      (set-buffer "*compilation*")       ;; messages are here
      (goto-char (point-max))
      (if (search-backward-regexp bsv-error1-regexp (point-min) t) 
          (progn
            (setq file (match-string 1))
            (setq line (string-to-int (match-string 2)))
            (setq column (string-to-int (match-string 3))))))

    ;; if file is set, then we have an actual error
    ;; setup two windows, one for the BSV file, one for the erro
    (if (string= file "")
        (message "No Errors Found in BSV compilation window")
      (progn
        ;; two buffers, BSV on top, *compilation on bottom
        (switch-to-buffer-other-window "*compilation*")
        (find-file-other-window file)
        (goto-line line)
        (forward-char (- column 1))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defalias 'first 'car)
(defalias 'second 'cadr)
(defalias 'third  'caddr)
(defalias 'forth  'cadddr)

(provide 'bsv-mode-23)

