;;; -*- Emacs-Lisp -*- ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; bsv-mode.el --- major mode for editing bsv source in Emacs
;;
;;
;; Copyright (C) 2003 Free Software Foundation, Inc.

;; Based On Micheal McNamara Verilog Mode.
;;
;; Verilog Mode Author: Michael McNamara (mac@bsv.com)
;; Senior Vice President of Technology, Verisity Design, Inc.
;; IEEE 1364 Verilog standards committee Chairman
;; (SureFire and Verisity merged October 1999)
;;      http://www.verisity.com
;; AUTO features, signal, modsig; by: Wilson Snyder
;;	(wsnyder@wsnyder.org or wsnyder@world.std.com)
;;	http://www.veripool.com
;; Keywords: languages

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

;;; Commentary:

;; This mode borrows heavily from the Pascal-mode and the cc-mode of emacs

;; USAGE
;; =====

;; A major mode for editing BSV HDL source code. When you have
;; entered BSV mode, you may get more info by pressing C-h m. You
;; may also get online help describing various functions by: C-h f
;; <Name of function you want described>

;; The short list of installation instructions are: To set up
;; automatic bsv mode, put this file in your load path, and put
;; the following in code (please un comment it first!) in your
;; .emacs, or in your site's site-load.el

; (autoload 'bsv-mode "bsv-mode" "BSV mode" t )
; (setq auto-mode-alist (cons  '("\\.bsv\\'" . bsv-mode) auto-mode-alist))

;; If you want to customize BSV mode to fit your needs better,
;; you may add these lines (the values of the variables presented
;; here are the defaults). Note also that if you use an emacs that
;; supports custom, it's probably better to use the custom menu to
;; edit these.
;;
;; Be sure to examine at the help for bsv-auto, and the other
;; bsv-auto-* functions for some major coding time savers.
;;
; ;; User customization for BSV mode
; (setq bsv-indent-level             3
;       bsv-indent-level-module      3
;       bsv-indent-level-declaration 3
;       bsv-indent-level-behavioral  3
;       bsv-indent-level-directive   1
;       bsv-case-indent              2
;       bsv-auto-newline             t
;       bsv-auto-indent-on-newline   t
;       bsv-tab-always-indent        t
;       bsv-auto-endcomments         t
;       bsv-minimum-comment-distance 40
;       bsv-indent-begin-after-if    t
;       bsv-auto-lineup              '(all))

;; KNOWN BUGS / BUG REPORTS
;; =======================
;; This is beta code, and likely has bugs. Please report any and all
;; bugs to me at bsv-mode-bugs@surefirev.com.  Use
;; bsv-submit-bug-report to submit a report.
;; 

;;; History:
;; 

;; 
;;; Code:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require 'mark)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(if (assoc "\\.bsv" auto-mode-alist)
    nil
  (nconc auto-mode-alist '(("\\.bsv". bsv-mode))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst bsv-running-on-xemacs (string-match "XEmacs" emacs-version))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(if (and (string-match "^20." emacs-version) (not bsv-running-on-xemacs))
    (progn
      (load "emacs20-extras")
      (require 'cl)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(unless (fboundp 'line-beginning-position)
  (defun line-beginning-position (&optional n)
    "Return the `point' of the beginning of the current line."
    (save-excursion
      (beginning-of-line n)
      (point))))

(unless (fboundp 'line-end-position)
  (defun line-end-position (&optional n)
    "Return the `point' of the end of the current line."
    (save-excursion
      (end-of-line n)
      (point))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(provide 'bsv-mode-22)

;; This variable will always hold the version number of the mode
(defconst bsv-mode-version "$$Revision: 3.61 $$"
  "Version of this bsv mode.")

(defun bsv-version ()
  "Inform caller of the version of this file."
  (interactive)
  (message (concat "Using bsv-mode version " (substring bsv-mode-version 12 -3 )) ))

;; Insure we have certain packages, and deal with it if we don't
(if (fboundp 'eval-when-compile)
    (eval-when-compile
      (condition-case nil
          (require 'imenu)
        (error nil))
      (condition-case nil
	  (require 'reporter)
        (error nil))
      (condition-case nil
          (require 'easymenu)
        (error nil))
      (condition-case nil
	  (load "skeleton") ;; bug in 19.28 through 19.30 skeleton.el, not provided.
        (error nil))
      (condition-case nil
          (if (fboundp 'when)
	      nil ;; fab
	    (defmacro when (var &rest body)
	      (` (cond ( (, var) (,@ body))))))
        (error nil))
      (condition-case nil
          (if (fboundp 'unless)
	      nil ;; fab
	    (defmacro unless (var &rest body)
	      (` (if (, var) nil (,@ body)))))
        (error nil))
      (condition-case nil
          (if (fboundp 'store-match-data)
	      nil ;; fab
	    (defmacro store-match-data (&rest args) nil))
        (error nil))
      (condition-case nil
	  (if (boundp 'current-menubar)
	      nil ;; great
	    (defmacro set-buffer-menubar (&rest args) nil)
	    (defmacro add-submenu (&rest args) nil))
	(error nil))
      (condition-case nil
	  (if (fboundp 'zmacs-activate-region)
	      nil ;; great
	    (defmacro zmacs-activate-region (&rest args) nil))
	(error nil))
      (condition-case nil
	  (if (fboundp 'char-before)
	      nil ;; great
	    (defmacro char-before (&rest body)
	      (` (char-after (1- (point))))))
	(error nil))
      ;; Requires to define variables that would be "free" warnings
      (condition-case nil
	  (require 'font-lock)
	(error nil))
      (condition-case nil
	  (require 'compile)
	(error nil))
      (condition-case nil
	  (require 'custom)
	(error nil))
      (condition-case nil
	  (require 'dinotrace)
	(error nil))
      (condition-case nil
	  (if (fboundp 'dinotrace-unannotate-all)
	      nil ;; great
	    (defun dinotrace-unannotate-all (&rest args) nil))
	(error nil))
      (condition-case nil
	  (if (fboundp 'customize-apropos)
	      nil ;; great
	    (defun customize-apropos (&rest args) nil))
	(error nil))
      (condition-case nil
	  (if (fboundp 'match-string-no-properties)
	      nil ;; great
	    (defsubst match-string-no-properties (match)
	      (buffer-substring-no-properties (match-beginning match) (match-end match))))
	(error nil))
      (if (and (featurep 'custom) (fboundp 'custom-declare-variable))
	  nil ;; We've got what we needed
	;; We have the old custom-library, hack around it!
	(defmacro defgroup (&rest args)  nil)
	(defmacro customize (&rest args)
	  (message "Sorry, Customize is not available with this version of emacs"))
	(defmacro defcustom (var value doc &rest args)
	  (` (defvar (, var) (, value) (, doc))))
	)
      (if (fboundp 'defface)
	  nil ; great!
	(defmacro defface (var value doc &rest args)
	  (` (make-face (, var))))
	)

      (if (and (featurep 'custom) (fboundp 'customize-group))
	  nil ;; We've got what we needed
	;; We have an intermediate custom-library, hack around it!
	(defmacro customize-group (var &rest args)
	  (`(customize (, var) )))
	)

      ))

(when bsv-running-on-xemacs
  (defun regexp-opt (strings &optional paren shy)
    (let ((open (if paren "\\(" "")) (close (if paren "\\)" "")) out)
      (setq out 
	    (concat open (mapconcat 'regexp-quote strings "\\|") close))
      (if (eq paren 'words) (concat "\\<" out "\\>") out))))

(eval-when-compile
  (defun bsv-regexp-opt (a &optional b)
    "Wrapper to deal with XEmacs and FSF emacs having similar functions with differing number of arguments."
    (if (string-match "XEmacs" emacs-version)
	(regexp-opt a b 't)
      (regexp-opt a b)))
  )

(defun bsv-regexp-opt (a &optional b)
  "Deal with XEmacs & FSF both have `regexp-opt'; with different interface.
Call 'regexp-opt' on A and B."
  (if bsv-running-on-xemacs
      (unwind-protect (regexp-opt a b 't))
    (regexp-opt a b)))

(defun bsv-customize ()
  "Link to customize screen for BSV."
  (interactive)
  (customize-group 'bsv-mode))

(defun bsv-font-customize ()
  "Link to customize fonts used for BSV."
  (interactive)
  (customize-apropos "font-lock-*" 'faces))

(defgroup bsv-mode nil
  "Facilitates easy editing of BSV source text"
  :group 'languages)

; (defgroup bsv-mode-fonts nil
;   "Facilitates easy customization fonts used in BSV source text"
;   :link '(customize-apropos "font-lock-*" 'faces)
;  :group 'bsv-mode)

(defgroup bsv-mode-indent nil
  "Customize indentation and highlighting of bsv source text"
  :group 'bsv-mode)

(defgroup bsv-mode-actions nil
  "Customize actions on bsv source text"
  :group 'bsv-mode)

(defgroup bsv-mode-auto nil
  "Customize AUTO actions when expanding bsv source text"
  :group 'bsv-mode)

(defcustom bsv-linter "surelint --std --synth --style --sim --race --fsm --msglimit=none "
  "*Unix program and arguments to call to run a lint checker on bsv source.
Invoked when you type \\[compile].  \\[next-error] will take you to
   the next lint error as expected."
  :type 'string
  :group 'bsv-mode-actions)

(defcustom bsv-coverage "surecov --code --fsm --expr "
  "*Program and arguments to use to annotate for coverage bsv source."
  :type 'string
  :group 'bsv-mode-actions)

(defcustom bsv-simulator "bsc -sim "
  "*Program and arguments to use to interpret bsv source."
  :type 'string
  :group 'bsv-mode-actions)

(defcustom bsv-compiler "bsc -verilog "
  "*Program and arguments to use to compile bsv source."
  :type 'string
  :group 'bsv-mode-actions)

(defvar bsv-tool 'bsv-compiler)

(defcustom bsv-highlight-translate-off nil
  "*Non-nil means background-highlight code excluded from translation.
That is, all code between \"// synopsys translate_off\" and
\"// synopsys translate_on\" is highlighted using a different background color
\(face `bsv-font-lock-translate-off-face').
Note: this will slow down on-the-fly fontification (and thus editing).
NOTE: Activate the new setting in a BSV buffer by re-fontifying it (menu
      entry \"Fontify Buffer\").  XEmacs: turn off and on font locking."
  :type 'boolean
  :group 'bsv-mode-indent)

(defcustom bsv-indent-tabs-mode t
  "* Whether or not TABs are used for indentation."
  :group 'bsv-mode-indent
  :type 'boolean)

(defcustom bsv-indent-level 3
  "*Indentation of BSV statements with respect to containing block."
  :group 'bsv-mode-indent
  :type 'integer)

(defcustom bsv-indent-level-module 3
  "* Indentation of Module level BSV statements.  (eg always, initial)
Set to 0 to get initial and always statements lined up
    on the left side of your screen."
  :group 'bsv-mode-indent
  :type 'integer)

(defcustom bsv-indent-level-declaration 3
  "*Indentation of declarations with respect to containing block.
Set to 0 to get them list right under containing block."
  :group 'bsv-mode-indent
  :type 'integer)

(defcustom bsv-indent-declaration-macros nil
  "*How to treat macro expansions in a declaration.
If nil, indent as:
  input [31:0] a;
  input        `CP;
  output       c;
If non nil, treat as
  input [31:0] a;
  input `CP    ;
  output       c;"
  :group 'bsv-mode-indent
  :type 'boolean)

(defcustom bsv-indent-lists t
  "*How to treat indenting items in a list.
If t (the default), indent as:
  always @( posedge a or
            reset ) begin
If nil, treat as
  always @( posedge a or
     reset ) begin"
  :group 'bsv-mode-indent
  :type 'boolean)

(defcustom bsv-indent-level-behavioral 3
  "*Absolute indentation of first begin in a task or function block.
Set to 0 to get such code to start at the left side of the screen."
  :group 'bsv-mode-indent
  :type 'integer)

(defcustom bsv-indent-level-directive 1
  "*Indentation to add to each level of `ifdef declarations.
Set to 0 to have all directives start at the left side of the screen."
  :group 'bsv-mode-indent
  :type 'integer)

(defcustom bsv-cexp-indent 2
  "*Indentation of BSV statements split across lines."
  :group 'bsv-mode-indent
  :type 'integer)

(defcustom bsv-case-indent 2
  "*Indentation for case statements."
  :group 'bsv-mode-indent
  :type 'integer)

(defcustom bsv-auto-newline t
  "*True means automatically newline after semicolons."
  :group 'bsv-mode-indent
  :type 'boolean)

(defcustom bsv-auto-indent-on-newline t
  "*True means automatically indent line after newline."
  :group 'bsv-mode-indent
  :type 'boolean)

(defcustom bsv-tab-always-indent t
  "*True means TAB should always re-indent the current line.
Nil means TAB will only reindent when at the beginning of the line."
  :group 'bsv-mode-indent
  :type 'boolean)

(defcustom bsv-tab-to-comment nil
  "*True means TAB moves to the right hand column in preparation for a comment."
  :group 'bsv-mode-actions
  :type 'boolean)

(defcustom bsv-indent-begin-after-if t
  "*If true, indent begin statements following if, else, while, for and repeat.
Otherwise, line them up."
  :group 'bsv-mode-indent
  :type 'boolean )


(defcustom bsv-align-ifelse nil
  "*If true, align `else' under matching `if'.
Otherwise else is lined up with first character on line holding matching if."
  :group 'bsv-mode-indent
  :type 'boolean )

(defcustom bsv-minimum-comment-distance 10
  "*Minimum distance (in lines) between begin and end required before a comment.
Setting this variable to zero results in every end acquiring a comment; the
default avoids too many redundant comments in tight quarters"
  :group 'bsv-mode-indent
  :type 'integer)

(defcustom bsv-auto-endcomments t
  "*True means insert a comment /* ... */ after 'end's.
The name of the function or case will be set between the braces."
  :group 'bsv-mode-actions
  :type 'boolean )

(defcustom bsv-auto-read-includes nil
  "*True means do a `bsv-read-defines' and `bsv-read-includes'
before each AUTO expansion.  This makes it easier to embed defines and
includes, but can result in very slow reading times if there are many or
large include files."
  :group 'bsv-mode-actions
  :type 'boolean )

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

(defvar bsv-auto-update-tick nil
  "Modification tick at which autos were last performed.")

(defvar bsv-auto-last-file-locals nil
  "Text from file-local-variables during last evaluation.")

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
    ("Warning: \"\\([A-Za-z0-9\._/]+\\)\", line \\([0-9]+\\), column \\([0-9]+\\)" 1 2 3)
    ;;
    ;; Most SureFire tools
;;     ("\\(WARNING\\|ERROR\\|INFO\\)[^:]*: \\([^,]+\\), \\(line \\|\\)\\([0-9]+\\):" 2 4 )
;;     ("\
;; \\([a-zA-Z]?:?[^:( \t\n]+\\)[:(][ \t]*\\([0-9]+\\)\\([) \t]\\|\
;; :\\([^0-9\n]\\|\\([0-9]+:\\)\\)\\)" 1 2 5)
;;     ;; vcs
;;     ("\\(Error\\|Warning\\):[^(]*(\\([^ \t]+\\) line *\\([0-9]+\\))" 2 3)
;;     ("Warning:.*(port.*(\\([^ \t]+\\) line \\([0-9]+\\))" 1 2)
;;     ("\\(Error\\|Warning\\):[\n.]*\\([^ \t]+\\) *\\([0-9]+\\):" 2 3)
;;     ("syntax error:.*\n\\([^ \t]+\\) *\\([0-9]+\\):" 1 2)
;;     ;; Verilator
;;     ("%?\\(Error\\|Warning\\)\\(-[^:]+\\|\\):[\n ]*\\([^ \t:]+\\):\\([0-9]+\\):" 3 4)
;;     ("%?\\(Error\\|Warning\\)\\(-[^:]+\\|\\):[\n ]*\\([^ \t:]+\\):\\([0-9]+\\):" 3 4)
;;     ;; vxl
;;     ("\\(Error\\|Warning\\)!.*\n?.*\"\\([^\"]+\\)\", \\([0-9]+\\)" 2 3)
;;     ("([WE][0-9A-Z]+)[ \t]+\\([^ \t\n,]+\\)[, \t]+\\([0-9]+\\):.*$" 1 2)	       ; vxl
;;     ("([WE][0-9A-Z]+)[ \t]+\\([^ \t\n,]+\\)[, \t]+line[ \t]+\\([0-9]+\\):.*$" 1 2)
;;     ;; Leda
;;     ("In file \\([^ \t]+\\)[ \t]+line[ \t]+\\([0-9]+\\):\n[^\n]*\n[^\n]*\n\\[\\(Warning\\|Error\\|Failure\\)\\][^\n]*" 1 2)

    )
;  "*List of regexps for bsv compilers, like verilint. See compilation-error-regexp-alist for the formatting."
)

(defvar bsv-error-font-lock-keywords
  '(
    ("[^\n]*\\[\\([^:]+\\):\\([0-9]+\\)\\]" 1 bold t)
    ("[^\n]*\\[\\([^:]+\\):\\([0-9]+\\)\\]" 2 bold t)

    ("\\(WARNING\\|ERROR\\|INFO\\): \\([^,]+\\), line \\([0-9]+\\):" 2 bold t)
    ("\\(WARNING\\|ERROR\\|INFO\\): \\([^,]+\\), line \\([0-9]+\\):" 3 bold t)

    ("\
\\([a-zA-Z]?:?[^:( \t\n]+\\)[:(][ \t]*\\([0-9]+\\)\\([) \t]\\|\
:\\([^0-9\n]\\|\\([0-9]+:\\)\\)\\)" 1 bold t)
    ("\
\\([a-zA-Z]?:?[^:( \t\n]+\\)[:(][ \t]*\\([0-9]+\\)\\([) \t]\\|\
:\\([^0-9\n]\\|\\([0-9]+:\\)\\)\\)" 1 bold t)

    ("\\(Error\\|Warning\\):[^(]*(\\([^ \t]+\\) line *\\([0-9]+\\))" 2 bold t)
    ("\\(Error\\|Warning\\):[^(]*(\\([^ \t]+\\) line *\\([0-9]+\\))" 3 bold t)

    ("%?\\(Error\\|Warning\\)\\(-[^:]+\\|\\):[\n ]*\\([^ \t:]+\\):\\([0-9]+\\):" 3 bold t)
    ("%?\\(Error\\|Warning\\)\\(-[^:]+\\|\\):[\n ]*\\([^ \t:]+\\):\\([0-9]+\\):" 4 bold t)

    ("Warning:.*(port.*(\\([^ \t]+\\) line \\([0-9]+\\))" 1 bold t)
    ("Warning:.*(port.*(\\([^ \t]+\\) line \\([0-9]+\\))" 1 bold t)

    ("\\(Error\\|Warning\\):[\n.]*\\([^ \t]+\\) *\\([0-9]+\\):" 2 bold t)
    ("\\(Error\\|Warning\\):[\n.]*\\([^ \t]+\\) *\\([0-9]+\\):" 3 bold t)

    ("syntax error:.*\n\\([^ \t]+\\) *\\([0-9]+\\):" 1 bold t)
    ("syntax error:.*\n\\([^ \t]+\\) *\\([0-9]+\\):" 2 bold t)
       ; vxl
    ("\\(Error\\|Warning\\)!.*\n?.*\"\\([^\"]+\\)\", \\([0-9]+\\)" 2 bold t)
    ("\\(Error\\|Warning\\)!.*\n?.*\"\\([^\"]+\\)\", \\([0-9]+\\)" 2 bold t)

    ("([WE][0-9A-Z]+)[ \t]+\\([^ \t\n,]+\\)[, \t]+\\([0-9]+\\):.*$" 1 bold t)
    ("([WE][0-9A-Z]+)[ \t]+\\([^ \t\n,]+\\)[, \t]+\\([0-9]+\\):.*$" 2 bold t)

    ("([WE][0-9A-Z]+)[ \t]+\\([^ \t\n,]+\\)[, \t]+line[ \t]+\\([0-9]+\\):.*$" 1 bold t)
    ("([WE][0-9A-Z]+)[ \t]+\\([^ \t\n,]+\\)[, \t]+line[ \t]+\\([0-9]+\\):.*$" 2 bold t)
       ; Leda
    ("In file \\([^ \t]+\\)[ \t]+line[ \t]+\\([0-9]+\\):\n[^\n]*\n[^\n]*\n\\[\\(Warning\\|Error\\|Failure\\)\\][^\n]*" 1 bold t)
    ("In file \\([^ \t]+\\)[ \t]+line[ \t]+\\([0-9]+\\):\n[^\n]*\n[^\n]*\n\\[\\(Warning\\|Error\\|Failure\\)\\][^\n]*" 2 bold t)
    )
  "*Keywords to also highlight in BSV *compilation* buffers."
  )

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

BSV-mode attempts to detect changes to this local variable, but they
are only insured to be correct when the file is first visited. Thus if you
have problems, use \\[find-alternate-file] RET to have these take effect.

See also bsv-library-files and bsv-library-extensions."
  :group 'bsv-mode-auto
  :type '(repeat file))

(defcustom bsv-library-files '(".")
  "*List of files to search for modules in when looking for files for
/*AUTOINST*/.  This is a complete path, usually to a technology file with
many standard cells defined in it.

You might want these defined in each file; put at the *END* of your file
something like:

// Local Variables:
// bsv-library-files:(\"/some/path/technology.v\" \"/some/path/tech2.v\")
// End:

BSV-mode attempts to detect changes to this local variable, but they
are only insured to be correct when the file is first visited. Thus if you
have problems, use \\[find-alternate-file] RET to have these take effect.

See also bsv-library-directories."
  :group 'bsv-mode-auto
  :type '(repeat directory))

(defcustom bsv-library-extensions '(".v")
  "*List of extensions to use when looking for files for /*AUTOINST*/.
See also `bsv-library-directories'."
  :type '(repeat string)
  :group 'bsv-mode-auto)

(defcustom bsv-auto-sense-include-inputs nil
  "*If true, AUTOSENSE should include all inputs.
If nil, only inputs that are NOT output signals in the same block are
included."
  :type 'boolean
  :group 'bsv-mode-auto)

(defcustom bsv-auto-sense-defines-constant nil
  "*If true, AUTOSENSE should assume all defines represent constants.
When true, the defines will not be included in sensitivity lists.  To
maintain compatibility with other sites, this should be set at the bottom
of each bsv file that requires it, rather then being set globally."
  :type 'boolean
  :group 'bsv-mode-auto)

(defcustom bsv-auto-reset-widths nil
  "*If true, AUTORESET should determine the width of signals and use it
to widen the zero (32'h0 for example).  This is required by some lint
tools that aren't smart enough to ignore widths of the constant zero.
This is not on my default, as it results in ugly code when parameters
determine the MSB or LSB of a signal inside a AUTORESET."
  :type 'boolean
  :group 'bsv-mode-auto)

(defcustom bsv-assignment-delay ""
  "*Text used for delayes in delayed assignments.  Add a trailing space if set."
  :type 'string
  :group 'bsv-mode-auto)

(defcustom bsv-auto-inst-vector t
  "*If true, when creating default ports with AUTOINST, use bus subscripts.
If nil, skip the subscript when it matches the entire bus as declared in
the module (AUTOWIRE signals always are subscripted, you must manually
declare the wire to have the subscrips removed.)  Nil may speed up some
simulators, but is less general and harder to read, so avoid."
  :group 'bsv-mode-auto
  :type 'boolean )

(defcustom bsv-mode-hook   'bsv-set-compile-command
  "*Hook (List of functions) run after bsv mode is loaded."
  :type 'hook
  :group 'bsv-mode)

(defcustom bsv-before-auto-hook nil
  "*Hook run before `bsv-mode' updates AUTOs."
  :type 'hook
  :group 'bsv-mode-auto
)

(defcustom bsv-auto-hook nil
  "*Hook run after `bsv-mode' updates AUTOs."
  :type 'hook
  :group 'bsv-mode-auto)

(defvar bsv-auto-lineup '(all)
  "*List of contexts where auto lineup of :'s or ='s should be done.
Elements can be of type: 'declaration' or 'case', which will do auto
lineup in declarations or case-statements respectively.  The word 'all'
will do all lineups.  '(case declaration) for instance will do lineup
in case-statements and parameter list, while '(all) will do all
lineups.")

(defvar bsv-mode-abbrev-table nil
  "Abbrev table in use in BSV-mode buffers.")

(defvar bsv-imenu-generic-expression
  '((nil "^\\s-*\\(\\(m\\(odule\\|acromodule\\)\\)\\|primitive\\)\\s-+\\([a-zA-Z0-9_.:]+\\)" 4)
    ("*Vars*" "^\\s-*\\(reg\\|wire\\)\\s-+\\(\\|\\[[^]]+\\]\\s-+\\)\\([A-Za-z0-9_]+\\)" 3))
  "Imenu expression for BSV-mode.  See `imenu-generic-expression'.")

(defvar bsv-mode-abbrev-table nil
  "Abbrev table in use in BSV-mode buffers.")

;;
;; provide a bsv-header function.
;; Customization variables:
;;
(defvar bsv-date-scientific-format nil
  "*If non-nil, dates are written in scientific format (e.g.  1997/09/17).
If nil, in European format (e.g.  17.09.1997).  The brain-dead American
format (e.g.  09/17/1997) is not supported.")

(defvar bsv-company nil
  "*Default name of Company for bsv header.
If set will become buffer local.")

(defvar bsv-project nil
  "*Default name of Project for bsv header.
If set will become buffer local.")

(define-abbrev-table 'bsv-mode-abbrev-table ())

(defvar bsv-mode-map ()
  "Keymap used in BSV mode.")
(if (and nil bsv-mode-map)
    ()
  (setq bsv-mode-map (make-sparse-keymap))
;  (define-key bsv-mode-map ";"        'electric-bsv-semi)
  (define-key bsv-mode-map [(control 59)]    'electric-bsv-semi-with-comment)
  (define-key bsv-mode-map ":"        'electric-bsv-colon)
  (define-key bsv-mode-map "="        'electric-bsv-equal)
  (define-key bsv-mode-map "\`"       'electric-bsv-tick)
  (define-key bsv-mode-map "\t"       'bsv-complete-or-indent-command)
  (define-key bsv-mode-map "\r"       'bsv-electric-terminate-line)
  ;; backspace/delete key bindings
  (define-key bsv-mode-map [backspace]    'backward-delete-char-untabify)
  (unless (boundp 'delete-key-deletes-forward) ; XEmacs variable
    (define-key bsv-mode-map [delete]       'delete-char)
    (define-key bsv-mode-map [(meta delete)] 'kill-word))
  (define-key bsv-mode-map "\M-\C-b"  'electric-bsv-backward-sexp)
  (define-key bsv-mode-map "\M-\C-f"  'electric-bsv-forward-sexp)
  (define-key bsv-mode-map "\M-\r"    (function (lambda ()
                                                  (interactive) (bsv-electric-terminate-line 1))))
  (define-key bsv-mode-map "\M-\t"    'bsv-complete-word)
  (define-key bsv-mode-map "\M-?"     'bsv-show-completions)
  (define-key bsv-mode-map "\M-\C-h"  'bsv-mark-defun)
  (define-key bsv-mode-map "\C-c\`"   'bsv-lint-off)
  (define-key bsv-mode-map "\C-c\C-r" 'bsv-label-be)
  (define-key bsv-mode-map "\C-c\C-i" 'bsv-pretty-declarations)
  (define-key bsv-mode-map "\C-c="    'bsv-pretty-expr)
  (define-key bsv-mode-map "\C-c\C-b" 'bsv-submit-bug-report)
  (define-key bsv-mode-map "\M-*"     'bsv-star-comment)
;  (define-key bsv-mode-map "\C-c\C-c" 'bsv-comment-region)
  (define-key bsv-mode-map "\C-c\C-u" 'bsv-uncomment-region)
  (define-key bsv-mode-map "\M-\C-a"  'bsv-beg-of-defun)
  (define-key bsv-mode-map "\M-\C-e"  'bsv-end-of-defun)
  (define-key bsv-mode-map "\C-c\C-d" 'bsv-goto-defun)
  (define-key bsv-mode-map "\C-c\C-k" 'bsv-delete-auto)
  (define-key bsv-mode-map "\C-c\C-a" 'bsv-auto)
  (define-key bsv-mode-map "\C-c\C-s" 'bsv-auto-save-compile)
  (define-key bsv-mode-map "\C-c\C-e" 'bsv-expand-vector)
  (define-key bsv-mode-map "\M-\C-\\" 'bsv-indent-region)
  (define-key bsv-mode-map "\C-x;"    'bsv-comment-region)
  (define-key bsv-mode-map "\C-c\C-h" 'bsv-add-header)
  (define-key bsv-mode-map "\C-c\C-c" 'bsv-add-comment-bar)
  (define-key bsv-mode-map "\C-l" 'bsv-recenter-and-font-lock-fontify-buffer)
  )

;; menus
(defvar bsv-which-tool 1)
(defvar bsv-xemacs-menu
  '("BSV"
    ("Choose Compilation Action"
     ["Lint"
      (progn
	(setq bsv-tool 'bsv-linter)
	(setq bsv-which-tool 1)
	(bsv-set-compile-command))
      :style radio
      :selected (= bsv-which-tool 1)]
     ["Coverage"
      (progn
	(setq bsv-tool 'bsv-coverage)
	(setq bsv-which-tool 2)
	(bsv-set-compile-command))
      :style radio
      :selected (= bsv-which-tool 2)]
     ["Simulator"
      (progn
	(setq bsv-tool 'bsv-simulator)
	(setq bsv-which-tool 3)
	(bsv-set-compile-command))
      :style radio
      :selected (= bsv-which-tool 3)]
     ["Compiler"
      (progn
	(setq bsv-tool 'bsv-compiler)
	(setq bsv-which-tool 4)
	(bsv-set-compile-command))
      :style radio
      :selected (= bsv-which-tool 4)]
     )
    ("Move"
     ["Beginning of function"		bsv-beg-of-defun t]
     ["End of function"			bsv-end-of-defun t]
     ["Mark function"			bsv-mark-defun t]
     ["Goto function"			bsv-goto-defun t]
     ["Move to beginning of block"	electric-bsv-backward-sexp t]
     ["Move to end of block"		electric-bsv-forward-sexp t]
     )
    ("Comments"
     ["Comment Region"			bsv-comment-region t]
     ["UnComment Region"			bsv-uncomment-region t]
     ["Multi-line comment insert"	bsv-star-comment t]
     ["Lint error to comment"		bsv-lint-off t]
     )
    "----"
    ["Compile"				compile t]
    ["AUTO, Save, Compile"		bsv-auto-save-compile t]
    ["Next Compile Error"		next-error t]
    ["Ignore Lint Warning at point"	bsv-lint-off t]
    "----"
    ["Line up declarations around point"	bsv-pretty-declarations t]
    ["Line up equations around point"		bsv-pretty-expr t]
    ["Redo/insert comments on every end"	bsv-label-be t]
    ["Expand [x:y] vector line"		bsv-expand-vector t]
    ["Insert begin-end block"		bsv-insert-block t]
    ["Complete word"			bsv-complete-word t]
    "----"
    ["Recompute AUTOs"			bsv-auto t]
    ["Kill AUTOs"			bsv-delete-auto t]
    ("AUTO Help..."
     ["AUTO General"			(describe-function 'bsv-auto) t]
     ["AUTO Library Path"		(describe-variable 'bsv-library-directories) t]
     ["AUTO Library Files"		(describe-variable 'bsv-library-files) t]
     ["AUTO Library Extensions"		(describe-variable 'bsv-library-extensions) t]
     ["AUTO `define Reading"		(describe-function 'bsv-read-defines) t]
     ["AUTO `include Reading"		(describe-function 'bsv-read-includes) t]
     ["AUTOARG"				(describe-function 'bsv-auto-arg) t]
     ["AUTOASCIIENUM"			(describe-function 'bsv-auto-ascii-enum) t]
     ["AUTOINOUTMODULE"			(describe-function 'bsv-auto-inout-module) t]
     ["AUTOINPUT"			(describe-function 'bsv-auto-input) t]
     ["AUTOINST"			(describe-function 'bsv-auto-inst) t]
     ["AUTOOUTPUT"			(describe-function 'bsv-auto-output) t]
     ["AUTOOUTPUTEVERY"			(describe-function 'bsv-auto-output-every) t]
     ["AUTOREG"				(describe-function 'bsv-auto-reg) t]
     ["AUTOREGINPUT"			(describe-function 'bsv-auto-reg-input) t]
     ["AUTORESET"			(describe-function 'bsv-auto-reset) t]
     ["AUTOSENSE"			(describe-function 'bsv-auto-sense) t]
     ["AUTOWIRE"			(describe-function 'bsv-auto-wire) t]
     )
    "----"
    ["Submit bug report"		bsv-submit-bug-report t]
    ["Customize BSV Mode..."	bsv-customize t]
    ["Customize BSV Fonts & Colors"	bsv-font-customize t]
    )
  "Emacs menu for BSV mode."
  )
(unless bsv-running-on-xemacs
    (easy-menu-define bsv-menu bsv-mode-map "Menu for BSV mode"
		      bsv-xemacs-menu))

(defvar bsv-mode-abbrev-table nil
  "Abbrev table in use in BSV-mode buffers.")

(define-abbrev-table 'bsv-mode-abbrev-table ())

;; compilation program
(defun bsv-set-compile-command ()
  "Function to compute shell command to compile bsv.
Can be the path and arguments for your BSV simulator:
  \"vcs -p123 -O\"
or a string like
  \"(cd /tmp; surecov %s)\".
In the former case, the path to the current buffer is concat'ed to the
value of bsv-tool; in the later, the path to the current buffer is
substituted for the %s"
  (interactive)
  (or (file-exists-p "makefile")	;If there is a makefile, use it
      (file-exists-p "Makefile")
      (progn (make-local-variable 'compile-command)
	     (setq compile-command
		   (if (string-match "%s" (eval bsv-tool))
		       (format (eval bsv-tool) (or buffer-file-name ""))
		     (concat (eval bsv-tool) " " (or buffer-file-name "")))))))

(defun bsv-error-regexp-add ()
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

(add-hook 'compilation-mode-hook 'bsv-error-regexp-add)

;;
;; Regular expressions used to calculate indent, etc.
;;
(defconst bsv-symbol-re      "\\<[a-zA-Z_][a-zA-Z_0-9.]*\\>")
(defconst bsv-case-re        "\\(\\<case[xz]?\\>\\)")
;; Want to match
;; aa :
;; aa,bb :
;; a[34:32] :
;; a,
;;   b :
(defconst
  bsv-no-indent-begin-re
  "\\<\\(if\\|else\\|while\\|for\\|repeat\\|always\\)\\>")
(defconst bsv-ends-re
  (concat
   "\\(\\<else\\>\\)\\|"
   "\\(\\<if\\>\\)\\|"
   "\\(\\<end\\>\\)\\|"
   "\\(\\<join\\>\\)\\|"
   "\\(\\<endcase\\>\\)\\|"
   "\\(\\<endtable\\>\\)\\|"
   "\\(\\<endspecify\\>\\)\\|"
   "\\(\\<endfunction\\>\\)\\|"
   "\\(\\<endinterface\\>\\)\\|"
   "\\(\\<endmethod\\>\\)\\|"
   "\\(\\<endrule\\>\\)\\|"
   "\\(\\<endaction\\>\\)\\|"
   "\\(\\<endtask\\>\\)\\|"
   "\\(\\<endgenerate\\>\\)"))


(defconst bsv-enders-re
  (concat "\\(\\<endcase\\>\\)\\|"
	  "\\(\\<end\\>\\)\\|"
	  "\\(\\<endmethod\\>\\)\\|"
	  "\\(\\<endrule\\>\\)\\|"
	  "\\(\\<endaction\\>\\)\\|"
	  "\\(\\<endinterface\\>\\)\\|"
	  "\\(\\<end\\(\\(function\\)\\|\\(task\\)\\|\\(module\\)\\|\\(primitive\\)\\)\\>\\)"))
(defconst bsv-endcomment-reason-re
  (concat
   "\\(\\<fork\\>\\)\\|"
   "\\(\\<begin\\>\\)\\|"
   "\\(\\<if\\>\\)\\|"
   "\\(\\<else\\>\\)\\|"
   "\\(\\<end\\>.*\\<else\\>\\)\\|"
   "\\(\\<task\\>\\)\\|"
   "\\(\\<function\\>\\)\\|"
   "\\(\\<interface\\>\\)\\|"
   "\\(\\<method\\>\\)\\|"
   "\\(\\<rule\\>\\)\\|"
   "\\(\\<action\\>\\)\\|"
   "\\(\\<initial\\>\\)\\|"
   "\\(\\<always\\>\\(\[ \t\]*@\\)?\\)\\|"
   "\\(@\\)\\|"
   "\\(\\<while\\>\\)\\|"
   "\\(\\<for\\(ever\\)?\\>\\)\\|"
   "\\(\\<repeat\\>\\)\\|\\(\\<wait\\>\\)\\|"
   "#"))

(defconst bsv-named-block-re  "begin[ \t]*:")
(defconst bsv-beg-block-re
  ;; "begin" "case" "casex" "fork" "casez" "table" "specify" "function" "task"
  "\\(\\<\\(begin\\>\\|case\\(\\>\\|x\\>\\|z\\>\\)\\|generate\\|interface\\|method\\|rule\\|action\\|f\\(ork\\>\\|unction\\>\\)\\|specify\\>\\|ta\\(ble\\>\\|sk\\>\\)\\)\\)")

(defconst bsv-beg-block-re-1
  "\\<\\(begin\\)\\|\\(case[xz]?\\)\\|\\(fork\\)\\|\\(table\\)\\|\\(specify\\)\\|\\(function\\)\\|\\(interface\\)\\|\\(method\\)\\|\\(rule\\)\\|\\(action\\)\\|\\(task\\)\\|\\(generate\\)\\>")
(defconst bsv-end-block-re
  ;; "end" "join" "endcase" "endtable" "endspecify" "endtask" "endfunction" "endgenerate"
  "\\<\\(end\\(\\>\\|case\\>\\|function\\>\\|interface\\>\\|method\\>\\|rule\\>\\|action\\>\\|generate\\>\\|specify\\>\\|ta\\(ble\\>\\|sk\\>\\)\\)\\|join\\>\\)")

(defconst bsv-end-block-re-1 "\\(\\<end\\>\\)\\|\\(\\<endcase\\>\\)\\|\\(\\<join\\>\\)\\|\\(\\<endtable\\>\\)\\|\\(\\<endspecify\\>\\)\\|\\(\\<endfunction\\>\\)\\|\\(\\<endinterface\\>\\)\\|\\(\\<endgenerate\\>\\)\\|\\(\\<endtask\\>\\)")
(defconst bsv-declaration-re
  (eval-when-compile
    (concat "\\<"
	    (bsv-regexp-opt
	     (list
	      "assign" "defparam" "event" "inout" "input" "integer" "output"
	      "parameter" "real" "realtime" "reg" "supply" "supply0" "supply1"
	      "time" "tri" "tri0" "tri1" "triand" "trior" "trireg" "wand" "wire"
	      "wor") t )
	    "\\>")))
(defconst bsv-range-re "\\[[^]]*\\]")
(defconst bsv-macroexp-re "`\\sw+")
(defconst bsv-delay-re "#\\s-*\\(\\([0-9_]+\\('s?[hdxbo][0-9a-fA-F_xz]+\\)?\\)\\|\\(([^)]*)\\)\\|\\(\\sw+\\)\\)")
(defconst bsv-declaration-re-2-no-macro
  (concat "\\s-*" bsv-declaration-re
	  "\\s-*\\(\\(" bsv-range-re "\\)\\|\\(" bsv-delay-re "\\)"
;	  "\\|\\(" bsv-macroexp-re "\\)"
	  "\\)?"))
(defconst bsv-declaration-re-2-macro
  (concat "\\s-*" bsv-declaration-re
	  "\\s-*\\(\\(" bsv-range-re "\\)\\|\\(" bsv-delay-re "\\)"
	  "\\|\\(" bsv-macroexp-re "\\)"
	  "\\)?"))
(defconst bsv-declaration-re-1-macro (concat "^" bsv-declaration-re-2-macro))
(defconst bsv-declaration-re-1-no-macro (concat "^" bsv-declaration-re-2-no-macro))
(defconst bsv-defun-re
  ;;"module" "macromodule" "primitive"
  "\\(\\<\\(m\\(acromodule\\>\\|odule\\>\\)\\|primitive\\>\\)\\)")
(defconst bsv-end-defun-re
  ;; "endmodule" "endprimitive"
"\\(\\<end\\(module\\>\\|primitive\\>\\)\\)")
(defconst bsv-zero-indent-re
  (concat bsv-defun-re "\\|" bsv-end-defun-re))
(defconst bsv-directive-re
  ;; "`case" "`default" "`define" "`define" "`else" "`endfor" "`endif"
  ;; "`endprotect" "`endswitch" "`endwhile" "`for" "`format" "`if" "`ifdef"
  ;; "`ifndef" "`include" "`let" "`protect" "`switch" "`timescale"
  ;; "`time_scale" "`undef" "`while"
  "\\<`\\(case\\|def\\(ault\\|ine\\(\\)?\\)\\|e\\(lse\\|nd\\(for\\|if\\|protect\\|switch\\|while\\)\\)\\|for\\(mat\\)?\\|i\\(f\\(def\\|ndef\\)?\\|nclude\\)\\|let\\|protect\\|switch\\|time\\(_scale\\|scale\\)\\|undef\\|while\\)\\>")

(defconst bsv-directive-begin
  "\\<`\\(for\\|i\\(f\\|fdef\\|fndef\\)\\|switch\\|while\\)\\>")

(defconst bsv-directive-middle
  "\\<`\\(else\\|default\\|case\\)\\>")

(defconst bsv-directive-end
  "`\\(endfor\\|endif\\|endswitch\\|endwhile\\)\\>")

(defconst bsv-directive-re-1
  (concat "[ \t]*"  bsv-directive-re))

(defconst bsv-autoindent-lines-re
  ;; "macromodule" "module" "primitive" "end" "endcase" "endfunction"
  ;; "endtask" "endmodule" "endprimitive" "endspecify" "endtable" "join"
  ;; "begin" "else" "`else" "`ifdef" "`endif" "`define" "`undef" "`include"
  (concat "\\("
	  bsv-directive-re
	  "\\|\\(\\<begin\\>\\|e\\(lse\\>\\|nd\\(\\>\\|case\\>\\|function\\>\\|interface\\>\\|method\\>\\|rule\\>\\|action\\>\\|module\\>\\|primitive\\>\\|specify\\>\\|ta\\(ble\\>\\|sk\\>\\)\\)\\)\\|join\\>\\|m\\(acromodule\\>\\|odule\\>\\)\\|primitive\\>\\)\\)" ))

(defconst bsv-behavioral-block-beg-re
  "\\(\\<initial\\>\\|\\<always\\>\\|\\<function\\>\\|\\<interface\\>\\|\\<method\\>\\|\\<rule\\>\\|\\<action\\>\\|\\<task\\>\\)")
(defconst bsv-indent-reg
  (concat
   "\\(\\<begin\\>\\|\\<case[xz]?\\>\\|\\<specify\\>\\|\\<fork\\>\\|\\<table\\>\\)\\|"
   "\\(\\<end\\>\\|\\<join\\>\\|\\<endcase\\>\\|\\<endtable\\>\\|\\<endspecify\\>\\)\\|"
   "\\(\\<module\\>\\|\\<macromodule\\>\\|\\<primitive\\>\\|\\<initial\\>\\|\\<always\\>\\)\\|"
   "\\(\\<endmodule\\>\\|\\<endprimitive\\>\\)\\|"
   "\\(\\<generate\\>\\|\\<endgenerate\\>\\)\\|"
   "\\(\\<function\\>\\|\\<endfunction\\>\\)\\|"
   "\\(\\<interface\\>\\|\\<endinterface\\>\\)\\|"
   "\\(\\<method\\>\\|\\<endmethod\\>\\)\\|"
   "\\(\\<rule\\>\\|\\<endrule\\>\\)\\|"
   "\\(\\<action\\>\\|\\<endaction\\>\\)\\|"
   "\\(\\<task\\>\\|\\<endtask\\>\\)"
   ;;	  "\\|\\(\\<if\\>\\|\\<else\\>\\)"
   ))
(defconst bsv-indent-re
  (concat
   "\\(\\<\\(always\\>\\|begin\\>\\|case\\(\\>\\|x\\>\\|z\\>\\)\\|end\\(\\>\\|case\\>\\|function\\>\\|interface\\>\\|method\\>\\|rule\\>\\|action\\>\\|generate\\>\\|module\\>\\|primitive\\>\\|specify\\>\\|ta\\(ble\\>\\|sk\\>\\)\\)\\|f\\(ork\\>\\|unction\\>\\)\\|interface\\>\\|method\\>\\|rule\\>\\|action\\>\\|generate\\>\\|initial\\>\\|join\\>\\|m\\(acromodule\\>\\|odule\\>\\)\\|primitive\\>\\|specify\\>\\|ta\\(ble\\>\\|sk\\>\\)\\)"
   "\\|" bsv-directive-re "\\)"))

(defconst bsv-defun-level-re
  ;; "module" "macromodule" "primitive" "initial" "always" "endtask" "endfunction"
  "\\(\\<\\(always\\>\\|end\\(function\\>\\|task\\>\\)\\|initial\\>\\|m\\(acromodule\\>\\|odule\\>\\)\\|primitive\\>\\)\\)")
(defconst bsv-cpp-level-re
 ;;"endmodule" "endprimitive"
  "\\(\\<end\\(module\\>\\|primitive\\>\\)\\)")
(defconst bsv-behavioral-level-re
  ;; "function" "task"
  "\\(\\<\\(function\\>\\|interface\\>\\|method\\>\\|rule\\>\\|action\\>\\|task\\>\\)\\)")
(defconst bsv-complete-reg
  ;; "always" "initial" "repeat" "case" "casex" "casez" "while" "if" "for" "forever" "else" "parameter"
  "\\<\\(always\\|case\\(\\|[xz]\\)\\|begin\\|else\\|generate\\|for\\(\\|ever\\)\\|i\\(f\\|nitial\\)\\|parameter\\|repeat\\|while\\)\\>")
(defconst bsv-end-statement-re
  (concat "\\(" bsv-beg-block-re "\\)\\|\\("
	  bsv-end-block-re "\\)"))
(defconst bsv-endcase-re
  (concat bsv-case-re "\\|"
	  "\\(endcase\\)\\|"
	  bsv-defun-re
	  ))
;; Strings used to mark beginning and end of excluded text
(defconst bsv-exclude-str-start "/* -----\\/----- EXCLUDED -----\\/-----")
(defconst bsv-exclude-str-end " -----/\\----- EXCLUDED -----/\\----- */")

(defconst bsv-keywords
 '("`define" "`else" "`endif" "`ifdef" "`include" "`timescale"
   "`undef" "always" "and" "assign" "begin" "buf" "bufif0" "bufif1"
   "case" "casex" "casez" "cmos" "default" "defparam" "disable" "else" "end"
   "endcase" "endfunction" "endgenerate" "endmodule" "endprimitive"
   "endspecify" "endtable" "endtask" "event" "for" "force" "forever"
   "fork" "function" "generate" "if" "initial" "inout" "input" "integer"
   "join" "macromodule" "makefile" "module" "nand" "negedge" "nmos" "nor"
   "not" "notif0" "notif1" "or" "output" "parameter" "pmos" "posedge"
   "primitive" "pulldown" "pullup" "rcmos" "real" "realtime" "reg"
   "repeat" "rnmos" "rpmos" "rtran" "rtranif0" "rtranif1" "signed"
   "specify" "supply" "supply0" "supply1" "table" "task" "time" "tran"
   "tranif0" "tranif1" "tri" "tri0" "tri1" "triand" "trior" "trireg"
   "vectored" "wait" "wand" "while" "wire" "wor" "xnor" "xor" 
   "interface" "endinterface" "method" "endmethod" 
   "rule" "endrule" "action" "endaction"
   "package" "endpackage" "provisos" "return" "parameter" "deriving"
   )
 "List of BSV keywords.")


(defconst bsv-emacs-features
  (let ((major (and (boundp 'emacs-major-version)
		    emacs-major-version))
	(minor (and (boundp 'emacs-minor-version)
		    emacs-minor-version))
	flavor comments flock-syntax)
    ;; figure out version numbers if not already discovered
    (and (or (not major) (not minor))
	 (string-match "\\([0-9]+\\).\\([0-9]+\\)" emacs-version)
	 (setq major (string-to-int (substring emacs-version
					       (match-beginning 1)
					       (match-end 1)))
	       minor (string-to-int (substring emacs-version
					       (match-beginning 2)
					       (match-end 2)))))
    (if (not (and major minor))
	(error "Cannot figure out the major and minor version numbers"))
    ;; calculate the major version
    (cond
     ((= major 4)  (setq major 'v18))	;Epoch 4
     ((= major 18) (setq major 'v18))	;Emacs 18
     ((= major 19) (setq major 'v19	;Emacs 19
			 flavor (if (or (string-match "Lucid" emacs-version)
					(string-match "XEmacs" emacs-version))
				    'XEmacs 'FSF)))
     ((> major 19) (setq major 'v20
			 flavor (if (or (string-match "Lucid" emacs-version)
					(string-match "XEmacs" emacs-version))
				    'XEmacs 'FSF)))
     ;; I don't know
     (t (error "Cannot recognize major version number: %s" major)))
    ;; XEmacs 19 uses 8-bit modify-syntax-entry flags, as do all
    ;; patched Emacs 19, Emacs 18, Epoch 4's.  Only Emacs 19 uses a
    ;; 1-bit flag.  Let's be as smart as we can about figuring this
    ;; out.
    (if (or (eq major 'v20) (eq major 'v19))
	(let ((table (copy-syntax-table)))
	  (modify-syntax-entry ?a ". 12345678" table)
	  (cond
	   ;; XEmacs pre 20 and Emacs pre 19.30 use vectors for syntax tables.
	   ((vectorp table)
	    (if (= (logand (lsh (aref table ?a) -16) 255) 255)
		(setq comments '8-bit)
	      (setq comments '1-bit)))
	   ;; XEmacs 20 is known to be 8-bit
	   ((eq flavor 'XEmacs) (setq comments '8-bit))
	   ;; Emacs 19.30 and beyond are known to be 1-bit
	   ((eq flavor 'FSF) (setq comments '1-bit))
	   ;; Don't know what this is
	   (t (error "Couldn't figure out syntax table format"))
	   ))
      ;; Emacs 18 has no support for dual comments
      (setq comments 'no-dual-comments))
    ;; determine whether to use old or new font lock syntax
    ;; We can assume 8-bit syntax table emacsen aupport new syntax, otherwise
    ;; look for version > 19.30
    (setq flock-syntax
        (if (or (equal comments '8-bit)
                (equal major 'v20)
                (and (equal major 'v19) (> minor 30)))
            'flock-syntax-after-1930
          'flock-syntax-before-1930))
    ;; lets do some minimal sanity checking.
    (if (or
	 ;; Lemacs before 19.6 had bugs
	 (and (eq major 'v19) (eq flavor 'XEmacs) (< minor 6))
	 ;; Emacs 19 before 19.21 has known bugs
	 (and (eq major 'v19) (eq flavor 'FSF) (< minor 21))
	 )
	(with-output-to-temp-buffer "*bsv-mode warnings*"
	  (print (format
"The version of Emacs that you are running, %s,
has known bugs in its syntax parsing routines which will affect the
performance of bsv-mode. You should strongly consider upgrading to the
latest available version.  bsv-mode may continue to work, after a
fashion, but strange indentation errors could be encountered."
		     emacs-version))))
    ;; Emacs 18, with no patch is not too good
    (if (and (eq major 'v18) (eq comments 'no-dual-comments))
	(with-output-to-temp-buffer "*bsv-mode warnings*"
	  (print (format
"The version of Emacs 18 you are running, %s,
has known deficiencies in its ability to handle the dual bsv
(and C++) comments, (e.g. the // and /* */ comments). This will
not be much of a problem for you if you only use the /* */ comments,
but you really should strongly consider upgrading to one of the latest
Emacs 19's.  In Emacs 18, you may also experience performance degradations.
Emacs 19 has some new built-in routines which will speed things up for you.
Because of these inherent problems, bsv-mode is not supported
on emacs-18."
			    emacs-version))))
    ;; Emacs 18 with the syntax patches are no longer supported
    (if (and (eq major 'v18) (not (eq comments 'no-dual-comments)))
	(with-output-to-temp-buffer "*bsv-mode warnings*"
	  (print (format
"You are running a syntax patched Emacs 18 variant.  While this should
work for you, you may want to consider upgrading to Emacs 19.
The syntax patches are no longer supported either for bsv-mode."))))
    (list major comments flock-syntax))
  "A list of features extant in the Emacs you are using.
There are many flavors of Emacs out there, each with different
features supporting those needed by `bsv-mode'.  Here's the current
supported list, along with the values for this variable:

 Vanilla Emacs 18/Epoch 4:   (v18 no-dual-comments flock-syntax-before-1930)
 Emacs 18/Epoch 4 (patch2):  (v18 8-bit flock-syntax-after-1930)
 XEmacs (formerly Lucid) 19: (v19 8-bit flock-syntax-after-1930)
 XEmacs 20:                  (v20 8-bit flock-syntax-after-1930)
 Emacs 19.1-19.30:           (v19 8-bit flock-syntax-before-1930)
 Emacs 19.31-19.xx:          (v19 8-bit flock-syntax-after-1930)
 Emacs20        :            (v20 1-bit flock-syntax-after-1930).")

(defconst bsv-comment-start-regexp "//\\|/\\*"
  "Dual comment value for `comment-start-regexp'.")

(defun bsv-populate-syntax-table (table)
  "Populate the syntax TABLE."
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
)

(defun bsv-setup-dual-comments (table)
  "Set up TABLE to handle block and line style comments."
  (cond
   ((memq '8-bit bsv-emacs-features)
    ;; XEmacs (formerly Lucid) has the best implementation
    (modify-syntax-entry ?/  ". 1456" table)
    (modify-syntax-entry ?*  ". 23"   table)
    (modify-syntax-entry ?\n "> b"    table)
    )
   ((memq '1-bit bsv-emacs-features)
    ;; Emacs 19 does things differently, but we can work with it
    (modify-syntax-entry ?/  ". 124b" table)
    (modify-syntax-entry ?*  ". 23"   table)
    (modify-syntax-entry ?\n "> b"    table)
    )
   ))

(defvar bsv-mode-syntax-table nil
  "Syntax table used in `bsv-mode' buffers.")

;;
;;  Macros
;;

(defsubst bsv-string-replace-matches (from-string to-string fixedcase literal string)
  "Replace occurrences of FROM-STRING with TO-STRING.
FIXEDCASE and LITERAL as in `replace-match`.  STRING is what to replace.
The case (bsv-string-replace-matches \"o\" \"oo\" nil nil \"foobar\")
will break, as the o's continuously replace.  xa -> x works ok though."
  ;; Hopefully soon to a emacs built-in
  (let ((start 0))
    (while (string-match from-string string start)
      (setq string (replace-match to-string fixedcase literal string)
	    start (min (length string) (match-end 0))))
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
  (store-match-data '(nil nil))
  (while (and
	  (re-search-forward REGEXP BOUND NOERROR)
	  (and (bsv-skip-forward-comment-or-string)
	       (progn
		 (store-match-data '(nil nil))
		 (if BOUND
		     (< (point) BOUND)
		   t)
		 ))))
  (match-end 0))

(defsubst bsv-re-search-backward (REGEXP BOUND NOERROR)
  ; checkdoc-params: (REGEXP BOUND NOERROR)
  "Like `re-search-backward', but skips over match in comments or strings."
  (store-match-data '(nil nil))
  (while (and
	  (re-search-backward REGEXP BOUND NOERROR)
	  (and (bsv-skip-backward-comment-or-string)
	       (progn
		 (store-match-data '(nil nil))
		 (if BOUND
		     (> (point) BOUND)
		   t)
		 ))))
  (match-end 0))

(defsubst bsv-re-search-forward-quick (regexp bound noerror)
  "Like `bsv-re-search-forward', including use of REGEXP BOUND and NOERROR,
but trashes match data and is faster for REGEXP that doesn't match often.
This may at some point use text properties to ignore comments,
so there may be a large up front penalty for the first search."
  (let (pt)
    (while (and (not pt)
		(re-search-forward regexp bound noerror))
      (if (not (bsv-inside-comment-p))
	  (setq pt (match-end 0))))
    pt))

(defsubst bsv-re-search-backward-quick (regexp bound noerror)
  ; checkdoc-params: (REGEXP BOUND NOERROR)
  "Like `bsv-re-search-backward', including use of REGEXP BOUND and NOERROR,
but trashes match data and is faster for REGEXP that doesn't match often.
This may at some point use text properties to ignore comments,
so there may be a large up front penalty for the first search."
  (let (pt)
    (while (and (not pt)
		(re-search-backward regexp bound noerror))
      (if (not (bsv-inside-comment-p))
	  (setq pt (match-end 0))))
    pt))

(defsubst bsv-get-beg-of-line (&optional arg)
  (save-excursion
    (beginning-of-line arg)
    (point)))

(defsubst bsv-get-end-of-line (&optional arg)
  (save-excursion
    (end-of-line arg)
    (point)))

(defun bsv-inside-comment-p ()
  "Check if point inside a nested comment."
  (save-excursion
    (let ((st-point (point)) hitbeg)
      (or (search-backward "//" (bsv-get-beg-of-line) t)
	  (if (progn
		;; This is for tricky case //*, we keep searching if /* is proceeded by // on same line
		(while (and (setq hitbeg (search-backward "/*" nil t))
			    (progn (forward-char 1) (search-backward "//" (bsv-get-beg-of-line) t))))
		hitbeg)
	      (not (search-forward "*/" st-point t)))))))

(defun bsv-declaration-end ()
  (search-forward ";"))

(defun bsv-point-text (&optional pointnum)
  "Return text describing where POINTNUM or current point is (for errors).
Use filename, if current buffer being edited shorten to just buffer name."
  (concat (or (and (equal (window-buffer (selected-window)) (current-buffer))
		   (buffer-name))
	      buffer-file-name
	      (buffer-name))
	  ":" (int-to-string (count-lines (point-min) (or pointnum (point))))))

(defun electric-bsv-backward-sexp ()
  "Move backward over a sexp."
  (interactive)
  ;; before that see if we are in a comment
  (bsv-backward-sexp)
)
(defun electric-bsv-forward-sexp ()
  "Move backward over a sexp."
  (interactive)
  ;; before that see if we are in a comment
  (bsv-forward-sexp)
)

(defun bsv-backward-sexp ()
  (let ((reg)
	(elsec 1)
	(found nil)
	(st (point))
	)
    (if (not (looking-at "\\<"))
	(forward-word -1))
    (cond
     ((bsv-skip-backward-comment-or-string)
      )
     ((looking-at "\\<else\\>")
      (setq reg (concat
		 bsv-end-block-re
		 "\\|\\(\\<else\\>\\)"
		 "\\|\\(\\<if\\>\\)"
		 ))
      (while (and (not found)
		  (bsv-re-search-backward reg nil 'move))
	(cond
	 ((match-end 1) ; endblock
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
	      (setq found 't)
	    ))
	 )
	)
      )
     ((looking-at bsv-end-block-re)
      (bsv-leap-to-head))
     ((looking-at "\\(endmodule\\>\\)\\|\\(\\<endprimitive\\>\\)")
      (cond
       ((match-end 1)
	(bsv-re-search-backward "\\<\\(macro\\)?module\\>" nil 'move))
       ((match-end 2)
	(bsv-re-search-backward "\\<primitive\\>" nil 'move))
       (t
	(goto-char st)
	(backward-sexp 1))))
     (t
      (goto-char st)
      (backward-sexp))
     ) ;; cond
    ))

(defun bsv-forward-sexp ()
  (let ((reg)
	(st (point)))
    (if (not (looking-at "\\<"))
	(forward-word -1))
    (cond
     ((bsv-skip-forward-comment-or-string)
      (bsv-forward-syntactic-ws)
      )
     ((looking-at bsv-beg-block-re-1);; begin|case|fork|table|specify|function|interface|method|rule|action|task|generate
      (cond
       ((match-end 1) ; end
	;; Search forward for matching begin
	(setq reg "\\(\\<begin\\>\\)\\|\\(\\<end\\>\\)" ))
       ((match-end 2) ; endcase
	;; Search forward for matching case
	(setq reg "\\(\\<case[xz]?\\>[^:]\\)\\|\\(\\<endcase\\>\\)" ))
       ((match-end 3) ; join
	;; Search forward for matching fork
	(setq reg "\\(\\<fork\\>\\)\\|\\(\\<join\\>\\)" ))
       ((match-end 4) ; endtable
	;; Search forward for matching table
	(setq reg "\\(\\<table\\>\\)\\|\\(\\<endtable\\>\\)" ))
       ((match-end 5) ; endspecify
	;; Search forward for matching specify
	(setq reg "\\(\\<specify\\>\\)\\|\\(\\<endspecify\\>\\)" ))
       ((match-end 6) ; endfunction
	;; Search forward for matching function
	(setq reg "\\(\\<function\\>\\)\\|\\(\\<endfunction\\>\\)" ))
       ((match-end 7) ; endinterface
	;; Search forward for matching interface
	(setq reg "\\(\\<interface\\>\\)\\|\\(\\<endinterface\\>\\)" ))
       ((match-end 8) ; endmethod
	;; Search forward for matching method
	(setq reg "\\(\\<method\\>\\)\\|\\(\\<endmethod\\>\\)" ))
       ((match-end 9) ; endrule
	;; Search forward for matching rule
	(setq reg "\\(\\<rule\\>\\)\\|\\(\\<endrule\\>\\)" ))
       ((match-end 10) ; endaction
	;; Search forward for matching action
	(setq reg "\\(\\<action\\>\\)\\|\\(\\<endaction\\>\\)" ))
       ((match-end 11) ; endspecify
	;; Search forward for matching task
	(setq reg "\\(\\<task\\>\\)\\|\\(\\<endtask\\>\\)" ))
       ((match-end 12) ; endgenerate
	;; Search forward for matching generate
	(setq reg "\\(\\<generate\\>\\)\\|\\(\\<endgenerate\\>\\)" ))
       )
      (if (forward-word 1)
	  (catch 'skip
	    (let ((nest 1))
	      (while (bsv-re-search-forward reg nil 'move)
		(cond
		 ((match-end 2) ; end
		  (setq nest (1- nest))
		  (if (= 0 nest)
		      (throw 'skip 1)))
		 ((match-end 1) ; begin
		  (setq nest (1+ nest)))))
	      )))
      )
     ((looking-at "\\(\\<\\(macro\\)?module\\>\\)\\|\\(\\<primitive\\>\\)")
      (cond
       ((match-end 1)
	(bsv-re-search-forward "\\<endmodule\\>" nil 'move))
       ((match-end 2)
	(bsv-re-search-forward "\\<endprimitive\\>" nil 'move))
       (t
	(goto-char st)
	(if (= (following-char) ?\) )
	    (forward-char 1)
	  (forward-sexp 1)))))
     (t
      (goto-char st)
      (if (= (following-char) ?\) )
	  (forward-char 1)
	(forward-sexp 1)))
     ) ;; cond
    ))

(defun bsv-declaration-beg ()
  (bsv-re-search-backward bsv-declaration-re (bobp) t))

(defsubst bsv-within-string ()
  (save-excursion
    (nth 3 (parse-partial-sexp (bsv-get-beg-of-line) (point)))))

;; 
;;
;;  Mode
;;

;;###autoload
(defun bsv-mode ()
"Major mode for editing BSV code.
\\<bsv-mode-map>

NEWLINE, TAB indents for BSV code.
Delete converts tabs to spaces as it moves back.
Supports highlighting.

Variables controlling indentation/edit style:

 variable `bsv-indent-tabs-mode'       (default t)
    Whether or not TABs are used for indentation.
 `bsv-indent-level'               (default 3)
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
    Set to 0 to get such code to lined up underneath the task or function keyword
 `bsv-indent-level-directive'     (default 1)
    Indentation of `ifdef/`endif blocks
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
    Non-nil means automatically indent line after newline
 `bsv-tab-always-indent'        (default t)
    Non-nil means TAB in BSV mode should always reindent the current line,
    regardless of where in the line point is when the TAB command is used.
 `bsv-indent-begin-after-if'    (default t)
    Non-nil means to indent begin statements following a preceding
    if, else, while, for and repeat statements, if any.  otherwise,
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
 `bsv-auto-lineup'              (default `(all))
    List of contexts where auto lineup of :'s or ='s should be done.

Turning on BSV mode calls the value of the variable `bsv-mode-hook' with
no args, if that value is non-nil.
Other useful functions are:
\\[bsv-complete-word]\t-complete word with appropriate possibilities
   (functions, bsv keywords...)
\\[bsv-comment-region]\t- Put marked area in a comment, fixing
   nested comments.
\\[bsv-uncomment-region]\t- Uncomment an area commented with \
\\[bsv-comment-region].
\\[bsv-insert-block]\t- insert begin ... end;
\\[bsv-star-comment]\t- insert /* ... */
\\[bsv-mark-defun]\t- Mark function.
\\[bsv-beg-of-defun]\t- Move to beginning of current function.
\\[bsv-end-of-defun]\t- Move to end of current function.
\\[bsv-label-be]\t- Label matching begin ... end, fork ... join
  and case ... endcase statements;

\\[bsv-sk-always]  Insert a always @(AS) begin .. end block
\\[bsv-sk-begin]  Insert a begin .. end block
\\[bsv-sk-case]  Insert a case block, prompting for details
\\[bsv-sk-else]  Insert an else begin .. end block
\\[bsv-sk-for]  Insert a for (...) begin .. end block, prompting for details
\\[bsv-sk-generate]  Insert a generate .. endgenerate block
\\[bsv-sk-header]  Insert a nice header block at the top of file
\\[bsv-sk-initial]  Insert an initial begin .. end block
\\[bsv-sk-fork]  Insert a fork begin .. end .. join block
\\[bsv-sk-module]  Insert a module .. (/*AUTOARG*/);.. endmodule block
\\[bsv-sk-primitive]  Insert a primitive .. (.. );.. endprimitive block
\\[bsv-sk-repeat]  Insert a repeat (..) begin .. end block
\\[bsv-sk-specify]  Insert a specify .. endspecify block
\\[bsv-sk-task]  Insert a task .. begin .. end endtask block
\\[bsv-sk-while]  Insert a while (...) begin .. end block, prompting for details
\\[bsv-sk-casex]  Insert a casex (...) item: begin.. end endcase block, prompting for details
\\[bsv-sk-casez]  Insert a casez (...) item: begin.. end endcase block, prompting for details
\\[bsv-sk-if]  Insert an if (..) begin .. end block
\\[bsv-sk-else-if]  Insert an else if (..) begin .. end block
\\[bsv-sk-comment]  Insert a comment block
\\[bsv-sk-assign]  Insert an assign .. = ..; statement
\\[bsv-sk-function]  Insert a function .. begin .. end endfunction block
\\[bsv-sk-input]  Insert an input declaration, prompting for details
\\[bsv-sk-output]  Insert an output declaration, prompting for details
\\[bsv-sk-state-machine]  Insert a state machine definition, prompting for details!
\\[bsv-sk-inout]  Insert an inout declaration, prompting for details
\\[bsv-sk-wire]  Insert a wire declaration, prompting for details
\\[bsv-sk-reg]  Insert a register declaration, prompting for details"
  (interactive)
  (kill-all-local-variables)
  (use-local-map bsv-mode-map)
  (setq major-mode 'bsv-mode)
  (setq mode-name "BSV")
  (setq local-abbrev-table bsv-mode-abbrev-table)
  (setq bsv-mode-syntax-table (make-syntax-table))
  (bsv-populate-syntax-table bsv-mode-syntax-table)
  ;; add extra comment syntax
  (bsv-setup-dual-comments bsv-mode-syntax-table)
  (set-syntax-table bsv-mode-syntax-table)
  (make-local-variable 'indent-tabs-mode)
  (setq indent-tabs-mode bsv-indent-tabs-mode)
  (make-local-variable 'indent-line-function)
  (setq indent-line-function 'bsv-indent-line-conservative)
  (setq comment-indent-function 'bsv-comment-indent)
  (make-local-variable 'parse-sexp-ignore-comments)
  (setq parse-sexp-ignore-comments nil)
  (make-local-variable 'comment-start)
  (make-local-variable 'comment-end)
  (make-local-variable 'comment-multi-line)
  (make-local-variable 'comment-start-skip)
  (setq comment-start "// "
	comment-end ""
	comment-start-skip "/\\*+ *\\|// *"
	comment-multi-line nil)
  (make-local-variable 'max-lisp-eval-depth)
  (setq max-lisp-eval-depth 10000)
  ;; Set up for compilation
  (setq bsv-which-tool 1)
  (setq bsv-tool 'bsv-compiler)
  (bsv-set-compile-command)

  ;; Setting up things for font-lock
  (if bsv-running-on-xemacs
      (progn
        (if (and current-menubar
                 (not (assoc "BSV" current-menubar)))
            (progn
             ;; (set-buffer-menubar (copy-sequence current-menubar))
              (add-submenu nil bsv-xemacs-menu))) ))
  ;; Stuff for GNU emacs
  (make-local-variable 'font-lock-defaults)
  ;;------------------------------------------------------------
  ;; now hook in 'bsv-colorize-include-files (eldo-mode.el&spice-mode.el)
  ;; all buffer local:
  (make-local-hook 'font-lock-mode-hook)
  (make-local-hook 'font-lock-after-fontify-buffer-hook); doesn't exist in emacs 20
  (add-hook 'font-lock-mode-hook 'bsv-colorize-include-files-buffer t t)
  (add-hook 'font-lock-after-fontify-buffer-hook 'bsv-colorize-include-files-buffer t t) ; not in emacs 20
  (make-local-hook 'after-change-functions)
  (add-hook 'after-change-functions 'bsv-colorize-include-files t t)

  ;; Tell imenu how to handle bsv.
  (make-local-variable 'imenu-generic-expression)
  (setq imenu-generic-expression bsv-imenu-generic-expression)
  ;; Stuff for autos
  (add-hook 'write-contents-hooks 'bsv-auto-save-check) ; already local
  (bsv-auto-reeval-locals t)   ; Save locals in case user changes them
  (run-hooks 'bsv-mode-hook))


;;
;;  Electric functions
;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun bsv-electric-terminate-line (&optional arg)
  "Terminate line and indent next line.
With optional ARG, remove existing end of line comments."
  (interactive)
  (bsv-update-package-point)
  ;; before that see if we are in a comment
  (let ((state
	 (save-excursion
	   (parse-partial-sexp (point-min) (point)))))
    (cond
     ((nth 7 state)			; Inside // comment
      (if (eolp)
	  (progn
	    (delete-horizontal-space)
	    (newline))
	(progn
	  (newline)
	  (insert-string "// ")
	  (beginning-of-line)))
      (bsv-indent-line-basic))
     ((nth 4 state)			; Inside any comment (hence /**/)
      (newline)
      (bsv-more-comment))
     ((eolp)
      ;; First, check if current line should be indented
      (bsv-indent-line-conservative)
      (end-of-line)

;       (if (and nil (save-excursion
; 	    (delete-horizontal-space)
; 	    (beginning-of-line)
; 	    (skip-chars-forward " \t")
; 	    (if (looking-at bsv-autoindent-lines-re)
; 		(let ((indent-str (bsv-indent-line-conservative)))
; 		  ;; Maybe we should set some endcomments
; 		  (if (and nil bsv-auto-endcomments)
; 		      (bsv-set-auto-endcomments indent-str arg))
; 		  (end-of-line)
; 		  (delete-horizontal-space)
; 		  (if arg
; 		      ()
; 		    (newline))
; 		  nil)
; 	      (progn
; 		(end-of-line)
; 		(delete-horizontal-space)
; 		't
; 		))))
; 	  (newline)
; 	(forward-line 1)
; 	)

      (newline)
      ;; Indent next line
      (if bsv-auto-indent-on-newline
	  (bsv-indent-line-basic))
      )
     (t
      (newline))
     )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun electric-bsv-terminate-line (&optional arg)
  "Terminate line and indent next line.
With optional ARG, remove existing end of line comments."
  (interactive)
  ;; before that see if we are in a comment
  (let ((state
	 (save-excursion
	   (parse-partial-sexp (point-min) (point)))))
    (cond
     ((nth 7 state)			; Inside // comment
      (if (eolp)
	  (progn
	    (delete-horizontal-space)
	    (newline))
	(progn
	  (newline)
	  (insert-string "// ")
	  (beginning-of-line)))
      (bsv-indent-line))
     ((nth 4 state)			; Inside any comment (hence /**/)
      (newline)
      (bsv-more-comment))
     ((eolp)
       ;; First, check if current line should be indented
       (if (save-excursion
             (delete-horizontal-space)
	     (beginning-of-line)
	     (skip-chars-forward " \t")
	     (if (looking-at bsv-autoindent-lines-re)
		 (let ((indent-str (bsv-indent-line)))
		   ;; Maybe we should set some endcomments
		   (if bsv-auto-endcomments
		       (bsv-set-auto-endcomments indent-str arg))
		   (end-of-line)
		   (delete-horizontal-space)
		   (if arg
		       ()
		     (newline))
		   nil)
	       (progn
		 (end-of-line)
		 (delete-horizontal-space)
		 't
		 )))
	   (newline)
	 (forward-line 1)
	 )
       ;; Indent next line
       (if bsv-auto-indent-on-newline
	   (bsv-indent-line))
       )
     (t
      (newline))
     )))

(defun electric-bsv-semi ()
  "Insert `;' character and reindent the line."
  (interactive)
  (insert last-command-char)
  (if (or (bsv-in-comment-or-string-p)
	  (bsv-in-escaped-name-p))
      ()
    (save-excursion
      (beginning-of-line)
      (bsv-forward-ws&directives)
      (bsv-indent-line))
    (if (and bsv-auto-newline
	     (not (bsv-parenthesis-depth)))
	(bsv-electric-terminate-line))))

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
  (insert last-command-char)
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

(defun electric-bsv-equal ()
  "Insert `=', and do indentation if within block."
  (interactive)
  (insert last-command-char)
;; Could auto line up expressions, but not yet
;;  (if (eq (car (bsv-calculate-indent)) 'block)
;;      (let ((bsv-tab-always-indent nil))
;;	(bsv-indent-command)))
  )

(defun electric-bsv-tick ()
  "Insert back-tick, and indent to column 0 if this is a CPP directive."
  (interactive)
  (insert last-command-char)
  (save-excursion
    (if (progn
	  (beginning-of-line)
	  (looking-at bsv-directive-re-1))
	(bsv-indent-line))))

(defun electric-bsv-tab ()
  "Function called when TAB is pressed in BSV mode."
  (interactive)
  ;; If bsv-tab-always-indent, indent the beginning of the line.
  (if (or bsv-tab-always-indent
	  (save-excursion
	    (skip-chars-backward " \t")
	    (bolp)))
      (let* ((oldpnt (point))
	     (boi-point
	      (save-excursion
		(beginning-of-line)
		(skip-chars-forward " \t")
		(let (type state )
		  (setq type (bsv-indent-line))
		  (setq state (car type))
		  (cond
		   ((eq state 'block)
		    (if (looking-at bsv-behavioral-block-beg-re )
			(error
			 (concat
			  (bsv-point-text)
			  ": The reserved word \""
			  (buffer-substring (match-beginning 0) (match-end 0))
			  "\" must be at the behavioral level!"))))
		   ))
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
		   (kill-region (point) oldpnt)
		   ))))
	)
    (progn (insert "\t"))))



;;
;; Interactive functions
;;
(defun bsv-insert-block ()
  "Insert BSV begin ... end; block in the code with right indentation."
  (interactive)
  (bsv-indent-line)
  (insert "begin")
  (bsv-electric-terminate-line)
  (save-excursion
    (bsv-electric-terminate-line)
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

(defun bsv-insert-indices (MAX)
  "Insert a set of indices at into the rectangle.
The upper left corner is defined by the current point.  Indices always
begin with 0 and extend to the MAX - 1.  If no prefix arg is given, the
user is prompted for a value.  The indices are surrounded by square brackets
[].  For example, the following code with the point located after the first
'a' gives:

    a = b                           a[  0] = b
    a = b                           a[  1] = b
    a = b                           a[  2] = b
    a = b                           a[  3] = b
    a = b   ==> insert-indices ==>  a[  4] = b
    a = b                           a[  5] = b
    a = b                           a[  6] = b
    a = b                           a[  7] = b
    a = b                           a[  8] = b"

  (interactive "NMAX?")
  (save-excursion
  (let ((n 0))
    (while (< n MAX)
      (save-excursion
      (insert (format "[%3d]" n)))
      (next-line 1)
      (setq n (1+ n))))))


(defun bsv-generate-numbers (MAX)
  "Insert a set of generated numbers into a rectangle.
The upper left corner is defined by point.  The numbers are padded to three
digits, starting with 000 and extending to (MAX - 1).  If no prefix argument
is supplied, then the user is prompted for the MAX number.  consider the
following code fragment:

    buf buf                           buf buf000
    buf buf                           buf buf001
    buf buf                           buf buf002
    buf buf                           buf buf003
    buf buf   ==> insert-indices ==>  buf buf004
    buf buf                           buf buf005
    buf buf                           buf buf006
    buf buf                           buf buf007
    buf buf                           buf buf008"

  (interactive "NMAX?")
  (save-excursion
  (let ((n 0))
    (while (< n MAX)
      (save-excursion
      (insert (format "%3.3d" n)))
      (next-line 1)
      (setq n (1+ n))))))

(defun bsv-mark-defun ()
  "Put mark at end of this bsv defun, point at beginning.
The bsv defun marked is the one that contains point or follows point."
  (interactive)
  (push-mark (point))
  (bsv-end-of-defun)
  (push-mark (point) nil t)
  (bsv-beg-of-defun)
  (when transient-mark-mode
    (setq deactivate-mark nil)))

(defun bsv-comment-region (start end)
  ; checkdoc-params: (start end)
  "Put the region into a BSV comment.
The comments that are in this area are \"deformed\":
`*)' becomes `!(*' and `}' becomes `!{'.
These deformed comments are returned to normal if you use
\\[bsv-uncomment-region] to undo the commenting.

The commented area starts with `bsv-exclude-str-start', and ends with
`bsv-include-str-end'.  But if you change these variables,
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
	  (replace-match "/-*" t t))))
    ))

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
	     (point-marker)))
	)
    (goto-char (marker-position b))
    (if (> (- e b) 200)
	(message  "Relabeling module..."))
    (while (and
	    (> (marker-position e) (point))
	    (bsv-re-search-forward
	     (concat
	      "\\<end\\(\\(function\\)\\|\\(interface\\)\\|\\(method\\)"
	      "\\|\\(rule\\)"
	      "\\|\\(action\\)"
	      "\\|\\(task\\)\\|\\(module\\)\\|"
	      "\\(primitive\\)\\|\\(case\\)\\)?\\>"
	      "\\|\\(`endif\\)\\|\\(`else\\)")
	     nil 'move))
      (goto-char (match-beginning 0))
      (let ((indent-str (bsv-indent-line)))
	(bsv-set-auto-endcomments indent-str 't)
	(end-of-line)
	(delete-horizontal-space)
	)
      (setq cnt (1+ cnt))
      (if (= 9 (% cnt 10))
	  (message "%d..." cnt))
      )
    (goto-char oldpos)
    (if (or
	 (> (- e b) 200)
	 (> cnt 20))
	(message  "%d lines auto commented" cnt))
    ))

(defun bsv-beg-of-statement ()
  "Move backward to beginning of statement."
  (interactive)
  (while (save-excursion
	   (and
	    (not (looking-at bsv-complete-reg))
	    (bsv-backward-syntactic-ws)
	    (not (or (bolp) (= (preceding-char) ?\;)))
	    ))
    (skip-chars-backward " \t")
    (bsv-backward-token))
  (let ((last (point)))
    (while (progn
	     (setq last (point))
	     (and (not (looking-at bsv-complete-reg))
		  (bsv-continued-line))))
    (goto-char last)
    (bsv-forward-syntactic-ws)))

(defun bsv-beg-of-statement-1 ()
  "Move backward to beginning of statement."
  (interactive)
  (let ((pt (point)))

    (while (and (not (looking-at bsv-complete-reg))
		(setq pt (point))
		(bsv-backward-token)
		(bsv-backward-syntactic-ws)
		(setq pt (point))
		(not (bolp))
		(not (= (preceding-char) ?\;))))
    (while (progn
	     (setq pt (point))
	     (and (not (looking-at bsv-complete-reg))
		  (not (= (preceding-char) ?\;))
		  (bsv-continued-line))))
    (goto-char pt)
    (bsv-forward-ws&directives)))

(defun bsv-end-of-statement ()
  "Move forward to end of current statement."
  (interactive)
  (let ((nest 0) pos)
    (or (looking-at bsv-beg-block-re)
	;; Skip to end of statement
	(setq pos (catch 'found
		    (while t
		      (forward-sexp 1)
		      (bsv-skip-forward-comment-or-string)
		      (cond ((looking-at "[ \t]*;")
			     (skip-chars-forward "^;")
			     (forward-char 1)
			     (throw 'found (point)))
			    ((save-excursion
			       (forward-sexp -1)
			       (looking-at bsv-beg-block-re))
			     (goto-char (match-beginning 0))
			     (throw 'found nil))
			    ((eobp)
			     (throw 'found (point))))))))
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
      pos)))

(defun bsv-in-case-region-p ()
  "Return TRUE if in a case region;
more specifically, point @ in the line foo : @ begin"
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
	       (concat "\\(\\<module\\>\\)\\|\\(\\<case[xz]?\\>[^:]\\)\\|"
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
		(throw 'found (= nest 0)))
	       ))))
      nil)))

(defun bsv-in-fork-region-p ()
  "Return true if between a fork and join."
  (interactive)
  (let ((lim (save-excursion (bsv-beg-of-defun)  (point)))
	(nest 1)
	)
    (save-excursion
      (while (and
	      (/= nest 0)
	      (bsv-re-search-backward "\\<\\(fork\\)\\|\\(join\\)\\>" lim 'move)
	      (cond
	       ((match-end 1) ; fork
		(setq nest (1- nest)))
	       ((match-end 2) ; join
		(setq nest (1+ nest)))
	       ))
	))
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
	      (setq colon (1+ colon)))
	     ))
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
			  (point))
			 ))
		    (error "Malformed case item")
		    )))
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

(defun kill-existing-comment ()
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
	  "\\(`ifndef\\>\\)"))
(defun bsv-set-auto-endcomments (indent-str kill-existing-comment)
  "Add ending comment with given INDENT-STR.
With KILL-EXISTING-COMMENT, remove what was there before.
Insert `// case: 7 ' or `// NAME ' on this line if appropriate.
Insert `// case expr ' if this line ends a case block.
Insert `// ifdef FOO ' if this line ends code conditional on FOO.
Insert `// NAME ' if this line ends a module or primitive named NAME."
  (save-excursion
    (cond
     (; Comment close preprocessor directives
      (and
       (looking-at "\\(`endif\\)\\|\\(`else\\)")
       (or  kill-existing-comment
	    (not (save-excursion
		   (end-of-line)
		   (search-backward "//" (bsv-get-beg-of-line) t)))))
      (let ((nest 1) b e
	    m
	    (else (if (match-end 2) "!" " "))
	    )
	(end-of-line)
	(if kill-existing-comment
	    (kill-existing-comment))
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
	     ))
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
		   (point)
		   ))))
	(if b
	    (if (> (count-lines (point) b) bsv-minimum-comment-distance)
		(insert (concat " // " else m " " (buffer-substring b e))))
	  (progn
	    (insert " // unmatched `else or `endif")
	    (ding 't))
	  )))

     (; Comment close case/function/task/module and named block
      (and (looking-at "\\<end")
	   (or kill-existing-comment
	       (not (save-excursion
		      (end-of-line)
		      (search-backward "//" (bsv-get-beg-of-line) t)))))
      (let ((type (car indent-str)))
	(if (eq type 'declaration)
	    ()
	  (if
	      (looking-at bsv-enders-re)
	      (cond
	       (;- This is a case block; search back for the start of this case
		(match-end 1)

		(let ((err 't)
		      (str "UNMATCHED!!"))
		  (save-excursion
		    (bsv-leap-to-head)
		    (if (match-end 0)
			(progn
			  (goto-char (match-end 1))
			  (setq str (concat (buffer-substring (match-beginning 1) (match-end 1))
					    (bsv-get-expr)))
			  (setq err nil))))
		  (end-of-line)
		  (if kill-existing-comment
		      (kill-existing-comment))
		  (delete-horizontal-space)
		  (insert (concat " // " str ))
		  (if err (ding 't))
		  ))

	       (;- This is a begin..end block
		(match-end 2)
		(let ((str " // UNMATCHED !!")
		      (err 't)
		      (here (point))
		      there
		      cntx
		      )
		  (save-excursion
		    (bsv-leap-to-head)
		    (setq there (point))
		    (if (not (match-end 0))
			(progn
			  (goto-char here)
			  (end-of-line)
			  (if kill-existing-comment
			      (kill-existing-comment))
			  (delete-horizontal-space)
			  (insert str)
			  (ding 't)
			  )
		      (let ((lim
			     (save-excursion (bsv-beg-of-defun) (point)))
			    (here (point))
			    )
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
				       (bsv-backward-token)
				       (bsv-beg-of-statement-1)
				       (point)))
			    (setq err nil)
			    (setq str ""))
			   ((looking-at bsv-endcomment-reason-re)
			    (setq there (match-end 0))
			    (setq cntx (concat
					(buffer-substring (match-beginning 0) (match-end 0)) " "))
			    (cond
			     (;- begin
			      (match-end 2)
			      (setq err nil)
			      (save-excursion
				(if (and (bsv-continued-line)
					 (looking-at "\\<repeat\\>\\|\\<wait\\>\\|\\<always\\>"))
				    (progn
				      (goto-char (match-end 0))
				      (setq there (point))
				      (setq str
					    (concat " // "
						    (buffer-substring (match-beginning 0) (match-end 0)) " "
						    (bsv-get-expr))))
				  (setq str ""))))

			     (;- else
			      (match-end 4)
			      (let ((nest 0)
				    ( reg "\\(\\<begin\\>\\)\\|\\(\\<end\\>\\)\\|\\(\\<if\\>\\)")
				    )
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
					    (throw 'skip 1))
					)))
				    ))))

			     (;- end else
			      (match-end 5)
			      (goto-char there)
			      (let ((nest 0)
				    ( reg "\\(\\<begin\\>\\)\\|\\(\\<end\\>\\)\\|\\(\\<if\\>\\)")
				    )
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
					    (throw 'skip 1))
					)))
				    ))))

			     (;- task/function/initial et cetera
			      t
			      (match-end 0)
			      (goto-char (match-end 0))
			      (setq there (point))
			      (setq err nil)
			      (setq str (bsv-get-expr))
			      (setq str (concat " // " cntx str )))

			     (;-- otherwise...
			      (setq str " // auto-endcomment confused "))
			     ))

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
			  (kill-existing-comment))
		      (delete-horizontal-space)
		      (if (or err
			      (> (count-lines here there) bsv-minimum-comment-distance))
			  (insert str))
		      (if err (ding 't))
		      ))))
	       
	       (;- this is end{function,task,module,primative,table,generate}
		t
		(let (string reg (width nil))
		  (end-of-line)
		  (if kill-existing-comment
		      (save-match-data
		       (kill-existing-comment)))
		  (delete-horizontal-space)
		  (backward-sexp)
		  (cond
		   ((match-end 5)
		    (setq reg "\\(\\<function\\>\\)\\|\\(\\<\\(endfunction\\|task\\|\\(macro\\)?module\\|primitive\\)\\>\\)")
		    (setq width "\\(\\s-*\\(\\[[^]]*\\]\\)\\|\\(real\\(time\\)?\\)\\|\\(integer\\)\\|\\(time\\)\\)?")
		    )
		   ((match-end 6)
		    (setq reg "\\(\\<task\\>\\)\\|\\(\\<\\(endtask\\|function\\|\\(macro\\)?module\\|primitive\\)\\>\\)"))
		   ((match-end 7)
		    (setq reg "\\(\\<\\(macro\\)?module\\>\\)\\|\\<endmodule\\>"))
		   ((match-end 8)
		    (setq reg "\\(\\<primitive\\>\\)\\|\\(\\<\\(endprimitive\\|function\\|task\\|\\(macro\\)?module\\)\\>\\)"))
		   )
		  (let (b e)
		    (save-excursion
		      (bsv-re-search-backward reg nil 'move)
		      (cond
		       ((match-end 1)
			(setq b (progn
				  (skip-chars-forward "^ \t")
				  (bsv-forward-ws&directives)
				  (if (and width (looking-at width))
				      (progn
					(goto-char (match-end 0))
					(bsv-forward-ws&directives)
					))
				  (point))
			      e (progn
				  (skip-chars-forward "a-zA-Z0-9_")
				  (point)))
			(setq string (buffer-substring b e)))
		       (t
			(ding 't)
			(setq string "unmatched end(function|task|module|primitive)")))))
		  (end-of-line)
		  (insert (concat " // " string )))
		)))))))))

(defun bsv-get-expr()
  "Grab expression at point, e.g, case ( a | b & (c ^d))"
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
		(skip-chars-forward "^ \t\n")
		(point))
	       ((looking-at "/[/\\*]")
		b)
	       ('t
		(skip-chars-forward "^: \t\n")
		(point)
		))))
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
      (if (string-match (concat "\\(.*\\)"
				(regexp-quote bra)
				"\\([0-9]*\\)\\(:[0-9]*\\|\\)\\(::[0-9---]*\\|\\)"
				(regexp-quote ket)
				"\\(.*\\)$") signal-string)
	  (let* ((sig-head (match-string 1 signal-string))
		 (vec-start (string-to-int (match-string 2 signal-string)))
		 (vec-end (if (= (match-beginning 3) (match-end 3))
			      vec-start
			    (string-to-int (substring signal-string (1+ (match-beginning 3)) (match-end 3)))))
		 (vec-range (if (= (match-beginning 4) (match-end 4))
				1
			      (string-to-int (substring signal-string (+ 2 (match-beginning 4)) (match-end 4)))))
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
	      (insert (concat sig-head bra (int-to-string (car vec)) ket sig-tail "\n"))
	      (setq vec (cdr vec)))
	    (delete-char -1)
	    ;;
	    )))))

(defun bsv-strip-comments ()
  "Strip all comments from the bsv code."
  (interactive)
  (goto-char (point-min))
  (while (re-search-forward "//" nil t)
    (let ((bpt (- (point) 2)))
      (end-of-line)
      (delete-region bpt (point))))
  ;;
  (goto-char (point-min))
  (while (re-search-forward "/\\*" nil t)
    (let ((bpt (- (point) 2)))
      (re-search-forward "\\*/")
      (delete-region bpt (point)))))

(defun bsv-one-line ()
  "Converts structural bsv instances to occupy one line."
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
variables are used to determine which product is being used.

See \\[bsv-surelint-off] and \\[bsv-verilint-off]."
  (interactive)
  (let ((linter (bsv-linter-name)))
    (cond ((equal linter `surelint)
	   (bsv-surelint-off))
	  ((equal linter `verilint)
	   (bsv-verilint-off))
	  (t (error "Linter name not set")))))

(defun bsv-surelint-off ()
  "Convert a SureLint warning line into a disable statement.
Run from BSV source window; assumes there is a *compile* buffer
with point set appropriately.
For example:
 WARNING [STD-UDDONX]: xx.v, line 8: output out is never assigned.
becomes:
	// surefire lint_line_off UDDONX"
  (interactive)
  (save-excursion
    (switch-to-buffer compilation-last-buffer)
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
	(goto-line (string-to-number line))
	(end-of-line)
	(catch 'already
	  (cond
	   ((bsv-in-slash-comment-p)
	    (re-search-backward "//")
	    (cond 
	     ((looking-at "// surefire lint_off_line ")
	      (goto-char (match-end 0))
	      (let ((lim (save-excursion (end-of-line) (point))))
		(if (re-search-forward code lim 'move) 
		    (throw 'already t)
		  (insert-string (concat " " code)))))
	     (t
	      )))
	   ((bsv-in-star-comment-p)
	    (re-search-backward "/\*")
	    (insert-string (format " // surefire lint_off_line %6s" code ))
	    )
	   (t
	    (insert-string (format " // surefire lint_off_line %6s" code ))
	    )))))))

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
type of the current line, return that lines' indent level and its
type.  Return a list of two elements: (INDENT-TYPE INDENT-LEVEL)."
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
		   (if (bsv-in-star-comment-p)   (throw 'nesting 'comment))

		   ;; if we are in a parenthesized list, and the user likes to indent
		   ;; these, return.
 		   (if (and bsv-indent-lists
			    (bsv-in-paren))
		       (progn (setq par 1) (throw 'nesting 'block)))
;		   (if (/= 0 (bsv-parenthesis-depth)) (progn (setq par 1) (throw 'nesting 'block)))

		   ;; if we have a directive, done.
		   (if (save-excursion
			 (beginning-of-line)
			 (looking-at bsv-directive-re-1))
		       (throw 'nesting 'directive))

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
			      (t ; endblock
				; try to leap back to matching outward block by striding across
				; indent level changing tokens then immediately
				; previous line governs indentation.
			       (let ((reg)(nest 1))
;;				 bsv-ends =>  else|if|end|join|endcase|endtable|endspecify|endfunction|endinterface|endmethod|endrule|endaction|endtask|endgenerate
				 (cond
				  ((match-end 3) ; end
				   ;; Search back for matching begin
				   (setq reg "\\(\\<begin\\>\\)\\|\\(\\<end\\>\\)" ))
				  ((match-end 5) ; endcase
				   ;; Search back for matching case
				   (setq reg "\\(\\<case[xz]?\\>[^:]\\)\\|\\(\\<endcase\\>\\)" ))
				  ((match-end 7) ; endspecify
				   ;; Search back for matching specify
				   (setq reg "\\(\\<specify\\>\\)\\|\\(\\<endspecify\\>\\)" ))
				  ((match-end 8) ; endfunction
				   ;; Search back for matching function
				   (setq reg "\\(\\<function\\>\\)\\|\\(\\<endfunction\\>\\)" ))
				  ((match-end 9) ; endinterface
				   ;; Search back for matching interface
				   (setq reg "\\(\\<interface\\>\\)\\|\\(\\<endinterface\\>\\)" ))
				  ((match-end 10) ; endmethod
				   ;; Search back for matching method
				   (setq reg "\\(\\<method\\>\\)\\|\\(\\<endmethod\\>\\)" ))
				  ((match-end 11) ; endrule
				   ;; Search back for matching rule
				   (setq reg "\\(\\<rule\\>\\)\\|\\(\\<endrule\\>\\)" ))
				  ((match-end 12) ; endaction
				   ;; Search back for matching action
				   (setq reg "\\(\\<action\\>\\)\\|\\(\\<endaction\\>\\)" ))
				  ((match-end 13) ; endtask
				   ;; Search back for matching task
				   (setq reg "\\(\\<task\\>\\)\\|\\(\\<endtask\\>\\)" ))
				  ((match-end 14) ; endgenerate
				   ;; Search back for matching generate
				   (setq reg "\\(\\<generate\\>\\)\\|\\(\\<endgenerate\\>\\)" ))
				  ((match-end 4) ; join
				   ;; Search back for matching fork
				   (setq reg "\\(\\<fork\\>\\)\\|\\(\\<join\\>\\)" ))
				  ((match-end 6) ; endtable
				   ;; Search back for matching table
				   (setq reg "\\(\\<table\\>\\)\\|\\(\\<endtable\\>\\)" ))
				  )
				 (catch 'skip
				   (while (bsv-re-search-backward reg nil 'move)
				     (cond
				      ((match-end 1) ; begin
				       (setq nest (1- nest))
				       (if (= 0 nest)
					   (throw 'skip 1)))
				      ((match-end 2) ; end
				       (setq nest (1+ nest)))))
				   )
				 ))
			      ))))
		     (throw 'nesting (bsv-calc-1))
		     ))))
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
	   (list type (bsv-indent-level)))))
      )))

(defun bsv-calc-1 ()
  (catch 'nesting
    (while (bsv-re-search-backward bsv-indent-re nil 'move)
      (cond
       ((looking-at bsv-behavioral-level-re)
	(throw 'nesting 'behavioral))

       ((looking-at bsv-beg-block-re-1)
	(cond
	 ((match-end 2)  (throw 'nesting 'case))
	 (t              (throw 'nesting 'block))))

       ((looking-at bsv-end-block-re)
	(bsv-leap-to-head)
	(if (bsv-in-case-region-p)
	    (progn
	      (bsv-leap-to-case-head)
	      (if (looking-at bsv-case-re)
		  (throw 'nesting 'case)))))

       ((looking-at bsv-defun-level-re)
	(throw 'nesting 'defun))

       ((looking-at bsv-cpp-level-re)
	(throw 'nesting 'cpp))

       ((bobp)
	(throw 'nesting 'cpp))
       ))))

(defun bsv-calculate-indent-directive ()
  "Return indentation level for directive.
For speed, the searcher looks at the last directive, not the indent
of the appropriate enclosing block."
  (let ((base -1)	;; Indent of the line that determines our indentation
	(ind 0)	        ;; Relative offset caused by other directives (like `endif on same line as `else)
	)
    ;; Start at current location, scan back for another directive

    (save-excursion
      (beginning-of-line)
      (while (and (< base 0)
		  (bsv-re-search-backward bsv-directive-re nil t))
	(cond ((save-excursion (skip-chars-backward " \t") (bolp))
	       (setq base (current-indentation))
	       ))
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
      (bsv-re-search-backward "\\(\\<case[xz]?\\>[^:]\\)\\|\\(\\<endcase\\>\\)" nil 'move)
      (cond
       ((match-end 1)
	(setq nest (1- nest)))
       ((match-end 2)
	(setq nest (1+ nest)))
       ((bobp)
	(ding 't)
	(setq nest 0))))))

(defun bsv-leap-to-head ()
  "Move point to the head of this block; jump from end to matching begin,
from endcase to matching case, and so on."
  (let (reg
	snest
	(nest 1))
    (cond
     ((looking-at "\\<end\\>")
      ;; Search back for matching begin
      (setq reg (concat "\\(\\<begin\\>\\)\\|\\(\\<end\\>\\)\\|"
			"\\(\\<endcase\\>\\)\\|\\(\\<join\\>\\)" )))

     ((looking-at "\\<endcase\\>")
      ;; Search back for matching case
      (setq reg "\\(\\<case[xz]?\\>\\)\\|\\(\\<endcase\\>\\)" ))
     ((looking-at "\\<join\\>")
      ;; Search back for matching fork
      (setq reg "\\(\\<fork\\>\\)\\|\\(\\<join\\>\\)" ))
     ((looking-at "\\<endtable\\>")
      ;; Search back for matching table
      (setq reg "\\(\\<table\\>\\)\\|\\(\\<endtable\\>\\)" ))
     ((looking-at "\\<endspecify\\>")
      ;; Search back for matching specify
      (setq reg "\\(\\<specify\\>\\)\\|\\(\\<endspecify\\>\\)" ))
     ((looking-at "\\<endfunction\\>")
      ;; Search back for matching function
      (setq reg "\\(\\<function\\>\\)\\|\\(\\<endfunction\\>\\)" ))
     ((looking-at "\\<endinterface\\>")
      ;; Search back for matching interface
      (setq reg "\\(\\<interface\\>\\)\\|\\(\\<endinterface\\>\\)" ))
     ((looking-at "\\<endmethod\\>")
      ;; Search back for matching method
      (setq reg "\\(\\<method\\>\\)\\|\\(\\<endmethod\\>\\)" ))
     ((looking-at "\\<endrule\\>")
      ;; Search back for matching rule
      (setq reg "\\(\\<rule\\>\\)\\|\\(\\<endrule\\>\\)" ))
     ((looking-at "\\<endaction\\>")
      ;; Search back for matching action
      (setq reg "\\(\\<action\\>\\)\\|\\(\\<endaction\\>\\)" ))
     ((looking-at "\\<endgenerate\\>")
      ;; Search back for matching generate
      (setq reg "\\(\\<generate\\>\\)\\|\\(\\<endgenerate\\>\\)" ))
     ((looking-at "\\<endtask\\>")
      ;; Search back for matching task
      (setq reg "\\(\\<task\\>\\)\\|\\(\\<endtask\\>\\)" ))
     )
    (catch 'skip
      (let (sreg)
	(while (bsv-re-search-backward reg nil 'move)
	  (cond
	   ((match-end 1) ; begin
	    (setq nest (1- nest))
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
	    (setq reg "\\(\\<case[xz]?\\>[^:]\\)\\|\\(\\<endcase\\>\\)" ))
	   ((match-end 4)
	    ;; join, jump to fork
	    (setq snest nest)
	    (setq nest (1+ nest))
	    (setq sreg reg)
	    (setq reg "\\(\\<fork\\>\\)\\|\\(\\<join\\>\\)" ))
	   ))))))

(defun bsv-continued-line ()
  "Return true if this is a continued line.
Set point to where line starts"
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
	    (setq continued (bsv-backward-token))
	    ) ;; while
	    ))
      (setq continued nil))
    continued))

(defun bsv-backward-token ()
  "Step backward token, returning true if we are now at an end of line token."
  (bsv-backward-syntactic-ws)
  (cond
   ((bolp)
    nil)
   (;-- Anything ending in a ; is complete
    (= (preceding-char) ?\;)
    nil)
   (;-- Could be 'case (foo)' or 'always @(bar)' which is complete
    ;   also could be simply '@(foo)'
    ;   or foo u1 #(a=8)
    ;            (b, ... which ISN'T complete
    ;;;; Do we need this???
    (= (preceding-char) ?\))
    (progn
      (backward-char)
      (backward-up-list 1)
      (bsv-backward-syntactic-ws)
      (let ((back (point)))
	(forward-word -1)
	(cond
	 ((looking-at "\\<\\(always\\|case\\(\\|[xz]\\)\\|for\\(\\|ever\\)\\|i\\(f\\|nitial\\)\\|repeat\\|while\\)\\>")
	  (not (looking-at "\\<case[xz]?\\>[^:]")))
	 (t
	  (goto-char back)
	  (cond 
	   ((= (preceding-char) ?\@)
	    (backward-char)
	    (save-excursion
	      (bsv-backward-token)
	      (not (looking-at "\\<\\(always\\|initial\\|while\\)\\>"))))
	   ((= (preceding-char) ?\#)
	    t)
	   (t t))
	  )))))
	 
   (;-- any of begin|initial|while are complete statements; 'begin : foo' is also complete
    t
    (forward-word -1)
    (cond
     ((looking-at "\\(else\\)\\|\\(initial\\>\\)\\|\\(always\\>\\)")
      t)
     ((looking-at bsv-indent-reg)
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
	  (if (looking-at "begin")
	      nil
	    t)
	  )
	 ((= (preceding-char) ?\#)
	  (backward-char)
	  t)
	 ((= (preceding-char) ?\`)
	  (backward-char)
	  t)
	 
	 (t
	  (goto-char back)
	  t)
	 )))))))

(defun bsv-backward-syntactic-ws (&optional bound)
  "Backward skip over syntactic whitespace for Emacs 19.
Optional BOUND limits search."
  (save-restriction
    (let* ((bound (or bound (point-min))) (here bound) )
      (if (< bound (point))
	  (progn
	    (narrow-to-region bound (point))
	    (while (/= here (point))
	      (setq here (point))
	      (forward-comment (-(buffer-size)))
	      )))
      ))
  t)

(defun bsv-forward-syntactic-ws (&optional bound)
  "Forward skip over syntactic whitespace for Emacs 19.
Optional BOUND limits search."
  (save-restriction
    (let* ((bound (or bound (point-max)))
	   (here bound)
	   )
      (if (> bound (point))
	  (progn
	    (narrow-to-region (point) bound)
	    (while (/= here (point))
	      (setq here (point))
	      (forward-comment (buffer-size))
	      )))
      )))

(defun bsv-backward-ws&directives (&optional bound)
  "Backward skip over syntactic whitespace and compiler directives for Emacs 19.
Optional BOUND limits search."
  (save-restriction
    (let* ((bound (or bound (point-min)))
	   (here bound)
	   (p nil) )
      (if (< bound (point))
	  (progn
	    (let ((state
		   (save-excursion
		     (parse-partial-sexp (point-min) (point)))))
	      (cond
	       ((nth 7 state) ;; in // comment
		(bsv-re-search-backward "//" nil 'move)
                (skip-chars-backward "/"))
	       ((nth 4 state) ;; in /* */ comment
		(bsv-re-search-backward "/\*" nil 'move))))
	    (narrow-to-region bound (point))
	    (while (/= here (point))
	      (setq here (point))
	      (forward-comment (-(buffer-size)))
	      (setq p
		    (save-excursion
		      (beginning-of-line)
		      (cond
		       ((bsv-within-translate-off)
			(bsv-back-to-start-translate-off (point-min)))
		       ((looking-at bsv-directive-re-1)
			(point))
		       (t
			nil))))
	      (if p (goto-char p))
	      )))
      )))

(defun bsv-forward-ws&directives (&optional bound)
  "Forward skip over syntactic whitespace and compiler directives for Emacs 19.
Optional BOUND limits search."
  (save-restriction
    (let* ((bound (or bound (point-max)))
	   (here bound)
	   jump
	   )
      (if (> bound (point))
	  (progn
	    (let ((state
		   (save-excursion
		     (parse-partial-sexp (point-min) (point)))))
	      (cond
	       ((nth 7 state) ;; in // comment
		(bsv-re-search-forward "//" nil 'move))
	       ((nth 4 state) ;; in /* */ comment
		(bsv-re-search-forward "/\*" nil 'move))))
	    (narrow-to-region (point) bound)
	    (while (/= here (point))
	      (setq here (point)
		    jump nil)
	      (forward-comment (buffer-size))
	      (save-excursion
		(beginning-of-line)
		(if (looking-at bsv-directive-re-1)
		    (setq jump t)))
	      (if jump
		  (beginning-of-line 2))
	      )))
      )))

(defun bsv-in-comment-p ()
 "Return true if in a star or // comment."
 (let ((state
	(save-excursion
	  (parse-partial-sexp (point-min) (point)))))
   (or (nth 4 state) (nth 7 state))))

(defun bsv-in-star-comment-p ()
 "Return true if in a star comment."
 (let ((state
	(save-excursion
	  (parse-partial-sexp (point-min) (point)))))
   (nth 4 state)))

(defun bsv-in-slash-comment-p ()
 "Return true if in a slash comment."
 (let ((state
	(save-excursion
	  (parse-partial-sexp (point-min) (point)))))
   (nth 7 state)))

(defun bsv-in-comment-or-string-p ()
 "Return true if in a string or comment."
 (let ((state
	(save-excursion
	  (parse-partial-sexp (point-min) (point)))))
   (or (nth 3 state) (nth 4 state) (nth 7 state)))) ; Inside string or comment)

(defun bsv-in-escaped-name-p ()
 "Return true if in an escaped name."
 (save-excursion
   (backward-char)
   (skip-chars-backward "^ \t\n")
   (if (= (char-after (point) ) ?\\ )
       t
     nil)))

(defun bsv-in-paren ()
 "Return true if in a parenthetical expression."
 (let ((state
	(save-excursion
	  (parse-partial-sexp (point-min) (point)))))
   (/= 0 (nth 0 state))))

(defun bsv-parenthesis-depth ()
 "Return non zero if in parenthetical-expression."
 (save-excursion
   (nth 1 (parse-partial-sexp (point-min) (point)))))

(defun bsv-skip-forward-comment-or-string ()
 "Return true if in a string or comment."
 (let ((state
	(save-excursion
	  (parse-partial-sexp (point-min) (point)))))
   (cond
    ((nth 3 state)			;Inside string
     (goto-char (nth 3 state))
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
 (let ((state
	(save-excursion
	  (parse-partial-sexp (point-min) (point)))))
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

(defun bsv-skip-forward-comment-p ()
  "If in comment, move to end and return true."
  (let (state)
    (progn
      (setq state
	    (save-excursion
	      (parse-partial-sexp (point-min) (point))))
      (cond
       ((nth 3 state)
	t)
       ((nth 7 state)			;Inside // comment
	(end-of-line)
	(forward-char 1)
	t)
       ((nth 4 state)			;Inside any comment
	t)
       (t
	nil)))))

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
		(progn (goto-char sp)
		       (setq indent-str (list 'statement (bsv-indent-level))))
	      (goto-char sp1)
	      (setq indent-str (list 'block (bsv-indent-level)))))
	  (goto-char sp))
	 ((goto-char sp)
	  (setq indent-str (bsv-calculate-indent))))
      (progn (skip-chars-forward " \t")
	     (setq indent-str (bsv-calculate-indent))))
    (bsv-do-indent indent-str)))

;; (defun bsv-indent-line ()
;;  "Indent for special part of code."
;;  (bsv-do-indent (bsv-calculate-indent)))

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
			       (backward-up-list -1)
			       (skip-chars-forward " \t")))
			    )
			   (current-column))
		       (progn
			 (goto-char fst)
			 (+ (current-column) bsv-cexp-indent))
		       ))))
	    (goto-char here)
	    (indent-line-to val))
	  )
	 ((= (preceding-char) ?\) )
	  (goto-char here)
	  (let ((val (eval (cdr (assoc type bsv-indent-alist)))))
	    (indent-line-to val)))
	 (t
	  (goto-char here)
	  (let ((val))
	    (bsv-beg-of-statement-1)
	    (if (bsv-re-search-forward "=[ \\t]*" here 'move)
		(setq val (current-column))
	      (setq val (eval (cdr (assoc type bsv-indent-alist)))))
	    (goto-char here)
	    (indent-line-to val)))
	 )))

     (; handle inside parenthetical expressions
      (eq type 'cparenexp)
      (let ((val (save-excursion
		   (backward-up-list 1)
		   (forward-char 1)
		   (skip-chars-forward " \t")
		   (current-column))))
	(indent-line-to val)))

     (;-- Handle the ends
      (looking-at bsv-end-block-re )
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
	(indent-line-to val)))
     )
    (if (looking-at "[ \t]+$")
	(skip-chars-forward " \t"))
    indent-str				; Return indent data
    ))

(defun bsv-indent-level ()
  "Return the indent-level the current statement has."
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
  "Return the indent-level the current statement has.
Do not count named blocks or case-statements."
  (save-excursion
    (skip-chars-forward " \t")
    (cond
     ((looking-at bsv-named-block-re)
      (current-column))
     ((and (not (looking-at bsv-case-re))
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
	      (current-column)))
	   )))
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
	      (current-column)))
	   )))
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

(defun bsv-pretty-declarations ()
  "Line up declarations around point."
  (interactive)
  (save-excursion
    (if (progn
	  (bsv-beg-of-statement-1)
	  (looking-at bsv-declaration-re))
	(let* ((m1 (make-marker))
	       (e) (r)
	       (here (point))
	       (start
		(progn
		  (bsv-beg-of-statement-1)
		  (while (looking-at bsv-declaration-re)
		    (beginning-of-line)
		    (setq e (point))
		    (bsv-backward-syntactic-ws)
		    (backward-char)
		    (bsv-beg-of-statement-1)) ;Ack, need to grok `define
		  e))
	       (end
		(progn
		  (goto-char here)
		  (bsv-end-of-statement)
		  (setq e (point))	;Might be on last line
		  (bsv-forward-syntactic-ws)
		  (while (looking-at bsv-declaration-re)
		    (beginning-of-line)
		    (bsv-end-of-statement)
		    (setq e (point))
		    (bsv-forward-syntactic-ws))
		  e))
	       (edpos (set-marker (make-marker) end))
	       (ind)
	       (base-ind
		(progn
		  (goto-char start)
		  (bsv-do-indent (bsv-calculate-indent))
		  (bsv-forward-ws&directives)
		  (current-column)))
	       )
	  (goto-char end)
	  (goto-char start)
	  (if (> (- end start) 100)
	      (message "Lining up declarations..(please stand by)"))
	  ;; Get the beginning of line indent first
	  (while (progn (setq e (marker-position edpos))
			(< (point) e))
	    (indent-line-to base-ind)
	    (forward-line))
	  ;; Now find biggest prefix
	  (setq ind (bsv-get-lineup-indent start edpos))
	  ;; Now indent each line.
	  (goto-char start)
	  (while (progn (setq e (marker-position edpos))
			(setq r (- e (point)))
			(> r 0))
	    (setq e (point))
	    (message "%d" r)
	    (cond
	     ((or (and bsv-indent-declaration-macros
		       (looking-at bsv-declaration-re-1-macro))
		  (looking-at bsv-declaration-re-1-no-macro))
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
		    (indent-to ind))
		  )))
	     ((bsv-continued-line-1 start)
	      (goto-char e)
	      (indent-line-to ind))
	     (t 	; Must be comment or white space
	      (goto-char e)
	      (bsv-forward-ws&directives)
	      (forward-line -1))
	     )
	    (forward-line 1))
	  (message "")))))

(defun bsv-pretty-expr (&optional myre)
  "Line up expressions around point"
  (interactive)
  (save-excursion
    (if (not myre)
	(setq myre (read-string "Regular Expression: (<=) ")))
    (if (string-equal myre "") (setq myre "<="))
    (setq myre (concat "\\(^.*\\)\\(" myre "\\)"))
    (beginning-of-line)
    (if (and (not(looking-at bsv-complete-reg))
	     (looking-at myre))
	(let* ((m1 (make-marker))
	       (e) (r)
	       (here (point))
	       (start
		(progn
		  (beginning-of-line)
		  (setq e (point))
		  (bsv-backward-syntactic-ws)
		  (beginning-of-line)
		  (while (and (not(looking-at (concat "^\\s-*" bsv-complete-reg)))
			      (looking-at myre))
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
		  (while (and (not(looking-at (concat "^\\s-*" bsv-complete-reg)))
			      (looking-at myre))
		    (end-of-line)
		    (setq e (point))
		    (bsv-forward-syntactic-ws)
		    (beginning-of-line)
		    )
		  e))
	       (edpos (set-marker (make-marker) end))
	       (ind) 
	       )
	  (goto-char start)
	  (bsv-do-indent (bsv-calculate-indent))
	  (goto-char end)
	  ;;(insert "/*end*/")
	  (goto-char start)
	  ;;(insert "/*start*/")
	  (if (> (- end start) 100)
	      (message "Lining up expressions..(please stand by)"))
	  ;; Get the begining of line indent first
	  (while (progn (setq e (marker-position edpos))
			(< (point) e))
	    (beginning-of-line)
	    (bsv-just-one-space myre)
	    (forward-line))
	  ;; Now find biggest prefix
	  (setq ind (bsv-get-lineup-indent-2 myre start edpos))
	  ;; Now indent each line.
	  (goto-char start)
	  (while (progn (setq e (marker-position edpos))
			(setq r (- e (point)))
			(> r 0))
	    (setq e (point))
	    (message "%d" r)
	    (cond
	     ((looking-at myre)
	      (let ((p1 (match-end 1)))
		(set-marker m1 p1)
		(progn
		  (set-marker m1 p1)
		  (goto-char (marker-position m1))
		  (indent-to ind)
		  )))
	     ((bsv-continued-line-1 start)
	      (goto-char e)
	      (indent-line-to ind))
	     (t 	; Must be comment or white space
	      (goto-char e)
	      (bsv-forward-ws&directives)
	      (forward-line -1))
	     )
	    (forward-line 1))
	  (message "")
	  ))))

(defun bsv-just-one-space (myre)
  "Remove extra spaces around regular expression"
  (interactive)
  (save-excursion
    (if (and (not(looking-at bsv-complete-reg))
			      (looking-at myre))
	(let ((m1 (make-marker))
	      (p2 (match-end 2))
	      (p1 (match-end 1)))
	  (set-marker m1 p1)
	  (progn
	    (set-marker m1 p2)
	    (goto-char (marker-position m1))
	    (if (looking-at "\\s-")
		(just-one-space) )
	    (set-marker m1 p1)
	    (goto-char (marker-position m1))
	    (forward-char -1)
	    (if (looking-at "\\s-")
		(just-one-space))
	    )
	  ))
    (message "")))

(defun bsv-indent-declaration (baseind)
  "Indent current lines as declaration.
Line up the variable names based on previous declaration's indentation.
BASEIND is the base indent to offset everything."
  (interactive)
  (let ((pos (point-marker))
	(lim (save-excursion
	       (bsv-re-search-backward "\\(\\<begin\\>\\)\\|\\(\\<module\\>\\)" nil 'move)
	       (point)))
	(ind)
	(val)
	(m1 (make-marker))
	)
    ;; Use previous declaration (in this module) as template.
    (if (bsv-re-search-backward (or (and bsv-indent-declaration-macros
					     bsv-declaration-re-1-macro)
					bsv-declaration-re-1-no-macro) lim t)
	(progn
	  (goto-char (match-end 0))
	  (skip-chars-forward " \t")
	  (setq ind (current-column))
	  (goto-char pos)
	  (setq val (+ baseind (eval (cdr (assoc 'declaration bsv-indent-alist)))))
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
		      (indent-to ind)
		      )
		  (if (/= (current-column) ind)
		      (progn
			(just-one-space)
			(indent-to ind))
		    )))
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
			  (indent-to ind))
		      )))
	      )))
      (let ((val (+ baseind (eval (cdr (assoc 'declaration bsv-indent-alist))))))
	(indent-line-to val))
      )
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
	(if (bsv-re-search-forward (or (and bsv-indent-declaration-macros
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
	(skip-chars-backward " \t")
	(1+ (current-column))))))

(defun bsv-get-lineup-indent-2 (myre b edpos)
  "Return the indent level that will line up several lines within the region
from b to e nicely. The lineup string is str."
  (save-excursion
    (let ((ind 0) e)
      (goto-char b)
      ;; Get rightmost position
      (while (progn (setq e (marker-position edpos))
		    (< (point) e))
	(if (re-search-forward myre e 'move)
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
  '("and" "buf" "bufif0" "bufif1" "cmos" "defparam" "inout" "input"
    "integer" "nand" "nmos" "nor" "not" "notif0" "notif1" "or" "output" "parameter"
    "pmos" "pull0" "pull1" "pullup" "rcmos" "real" "realtime" "reg" "rnmos" "rpmos" "rtran"
    "rtranif0" "rtranif1" "time" "tran" "tranif0" "tranif1" "tri" "tri0" "tri1"
    "triand" "trior" "trireg" "wand" "wire" "wor" "xnor" "xor" )
  "*Keywords for types used when completing a word in a declaration or parmlist.
\(eg.  integer, real, reg...)")

(defvar bsv-cpp-keywords
  '("module" "macromodule" "primitive" "timescale" "define" "ifdef"
    "endif")
  "*Keywords to complete when at first word of a line in declarative scope.
\(eg.  initial, always, begin, assign.)
The procedures and variables defined within the BSV program
will be completed runtime and should not be added to this list.")

(defvar bsv-defun-keywords
  (append
   '("begin" "function" "task" "initial" "always" "assign"
     "endmodule" "specify" "endspecify" "generate" "endgenerate")
   bsv-type-keywords)
  "*Keywords to complete when at first word of a line in declarative scope.
\(eg.  initial, always, begin, assign.)
The procedures and variables defined within the BSV program
will be completed runtime and should not be added to this list.")

(defvar bsv-block-keywords
  '("begin" "fork" "join" "case" "end" "if" "else" "for" "while" "repeat"
    "endgenerate" "endspecify" "endfunction" "endtask")
  "*Keywords to complete when at first word of a line in behavioral scope.
\(eg.  begin, if, then, else, for, fork.)
The procedures and variables defined within the BSV program
will be completed runtime and should not be added to this list.")

(defvar bsv-tf-keywords
  '("begin" "fork" "join" "case" "end" "endtask" "endfunction" "if" "else" "for" "while" "repeat")
  "*Keywords to complete when at first word of a line in a task or function.
\(eg.  begin, if, then, else, for, fork.)
The procedures and variables defined within the BSV program
will be completed runtime and should not be added to this list.")

(defvar bsv-case-keywords
  '("begin" "fork" "join" "case" "end" "endcase" "if" "else" "for" "repeat")
  "*Keywords to complete when at first word of a line in case scope.
\(eg.  begin, if, then, else, for, fork.)
The procedures and variables defined within the BSV program
will be completed runtime and should not be added to this list.")

(defvar bsv-separator-keywords
  '("else" "then" "begin")
  "*Keywords to complete when NOT standing at the first word of a statement.
\(eg.  else, then.)
Variables and function names defined within the
BSV program are completed runtime and should not be added to this list.")

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
for matches of `str' and adding the occurence tp `all' through point END."
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
      (forward-line 1)
      )
    )
  bsv-all
  )

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
  (mapcar '(lambda (s)
	     (if (string-match (concat "\\<" bsv-str) s)
		 (if (or (null bsv-pred)
			 (funcall bsv-pred s))
		     (setq bsv-all (cons s bsv-all)))))
	  keyword-list))


(defun bsv-completion (bsv-str bsv-pred bsv-flag)
  "Function passed to `completing-read', `try-completion' or `all-completions'.
Called to get completion on BSV-STR.  If BSV-PRED is non-nil, it
must be a function to be called for every match to check if this should
really be a match.  If BSV-FLAG is t, the function returns a list of all
possible completions.  If BSV-FLAG is nil it returns a string, the
longest possible completion, or t if STR is an exact match.  If BSV-FLAG
is 'lambda, the function returns t if STR is an exact match, nil
otherwise."
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
`bsv-start-keywords' and `bsv-separator-keywords'.)"
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
			bsv-str (mapcar '(lambda (elm)
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
  "Move to specified BSV module/task/function.
The default is a name found in the buffer around point.
If search fails, other files are checked based on
`bsv-library-directories', `bsv-library-files',
and `bsv-library-extensions'."
  (interactive)
  (let* ((default (bsv-get-default-symbol))
	 ;; The following variable is used in bsv-comp-function
	 (bsv-buffer-to-use (current-buffer))
	 (label (if (not (string= default ""))
		    ;; Do completion with default
		    (completing-read (concat "Label: (default " default ") ")
				     'bsv-comp-defun nil nil "")
		  ;; There is no default value. Complete without it
		  (completing-read "Label: "
				   'bsv-comp-defun nil nil "")))
	 pt)
    ;; If there was no response on prompt, use default value
    (if (string= label "")
	(setq label default))
    ;; Goto right place in buffer if label is not an empty string
    (or (string= label "")
	(progn
	  (save-excursion
	    (goto-char (point-min))
	    (setq pt (re-search-forward (bsv-build-defun-re label t) nil t)))
	  (when pt
	    (goto-char pt)
	    (beginning-of-line))
	  pt)
	(bsv-goto-defun-file label)
	)))

;; Eliminate compile warning
(eval-when-compile
  (if (not (boundp 'occur-pos-list))
      (defvar occur-pos-list nil "Backward compatibility occur positions.")))

(defun bsv-showscopes ()
  "List all scopes in this module."
  (interactive)
  (let ((buffer (current-buffer))
	(linenum 1)
	(nlines 0)
	(first 1)
	(prevpos (point-min))
        (final-context-start (make-marker))
	(regexp "\\(module\\s-+\\w+\\s-*(\\)\\|\\(\\w+\\s-+\\w+\\s-*(\\)")
	)
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
    (error t)))


;; Added by Subbu Meiyappan for Header

(defun bsv-header ()
  "Insert a standard BSV file header."
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
    (insert-date)
    (search-forward "<moddate>") (replace-match "" t t)
    (insert-date)
    (search-forward "<copydate>") (replace-match "" t t)
    (insert-year)
    (search-forward "<modhist>") (replace-match "" t t)
    (insert-date)
    (insert " : created")
    (goto-char start)
    (let (string)
      (setq string (read-string "title: "))
      (search-forward "<title>")
      (replace-match string t t)
      (setq string (read-string "project: " bsv-project))
      (make-variable-buffer-local 'bsv-project)
      (setq bsv-project string)
      (search-forward "<project>")
      (replace-match string t t)
      (setq string (read-string "Company: " bsv-company))
      (make-variable-buffer-local 'bsv-company)
      (setq bsv-company string)
      (search-forward "<company>")
      (replace-match string t t)
      (search-forward "<company>")
      (replace-match string t t)
      (search-forward "<company>")
      (replace-match string t t)
      (search-backward "<description>")
      (replace-match "" t t)
      )))

;; bsv-header Uses the insert-date function

(defun insert-date ()
  "Insert date from the system."
  (interactive)
  (let ((timpos))
    (setq timpos (point))
    (if bsv-date-scientific-format
	(shell-command  "date \"+@%Y/%m/%d\"" t)
      (shell-command  "date \"+@%d.%m.%Y\"" t))
    (search-forward "@")
    (delete-region timpos (point))
    (end-of-line))
    (delete-char 1))

(defun insert-year ()
  "Insert year from the system."
  (interactive)
  (let ((timpos))
    (setq timpos (point))
    (shell-command  "date \"+@%Y\"" t)
    (search-forward "@")
    (delete-region timpos (point))
    (end-of-line))
  (delete-char 1))


;;
;; Signal list parsing
;;

(defun bsv-signals-not-in (in-list not-list)
  "Return list of signals in IN-LIST that aren't also in NOT-LIST.
Signals must be in standard (base vector) form."
  (let (out-list)
    (while in-list
      (if (not (assoc (car (car in-list)) not-list))
	  (setq out-list (cons (car in-list) out-list)))
      (setq in-list (cdr in-list)))
    (nreverse out-list)))
;;(bsv-signals-not-in '(("A" "") ("B" "") ("DEL" "[2:3]")) '(("DEL" "") ("EXT" "")))

(defun bsv-signals-in (in-list other-list)
  "Return list of signals in IN-LIST that are also in other-list.
Signals must be in standard (base vector) form."
  (let (out-list)
    (while in-list
      (if (assoc (car (car in-list)) other-list)
	  (setq out-list (cons (car in-list) out-list)))
      (setq in-list (cdr in-list)))
    (nreverse out-list)))
;;(bsv-signals-in '(("A" "") ("B" "") ("DEL" "[2:3]")) '(("DEL" "") ("EXT" "")))

(defun bsv-signals-memory (in-list)
  "Return list of signals in IN-LIST that are memoried (multidimensional)."
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
  "Return list of signals in IN-LIST that aren't parameters or
numeric constants."
  (let (out-list)
    (while in-list
      (unless (boundp (intern (concat "vh-" (car (car in-list)))))
	(setq out-list (cons (car in-list) out-list)))
      (setq in-list (cdr in-list)))
    (nreverse out-list)))

(defun bsv-signals-combine-bus (in-list)
  "Return a list of signals in IN-LIST, with busses combined.
Duplicate signals are also removed.  For example A[2] and A[1] become A[2:1]."
  (let (combo
	out-list 
	sig highbit lowbit		; Temp information about current signal
	sv-name sv-highbit sv-lowbit	; Details about signal we are forming
	sv-comment sv-memory sv-enum sv-signed sv-busstring
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
	      combo ""
	      ))
      ;; Extract bus details
      (setq bus (bsv-sig-bits sig))
      (cond ((and bus
		  (or (and (string-match "\\[\\([0-9]+\\):\\([0-9]+\\)\\]" bus)
			   (setq highbit (string-to-int (match-string 1 bus))
				 lowbit  (string-to-int (match-string 2 bus))))
		      (and (string-match "\\[\\([0-9]+\\)\\]" bus)
			   (setq highbit (string-to-int (match-string 1 bus))
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
	     (if (and sv-busstring (not (equal sv-busstring (bsv-sig-bits sig))))
		 (message (concat "Warning, can't merge into single bus "
				  sv-name bus
				  ", the AUTOs may be wrong")))
	     (if (bsv-sig-comment sig) (setq combo ", ..."))
	     (setq sv-memory (or sv-memory (bsv-sig-memory sig))
		   sv-enum   (or sv-enum   (bsv-sig-enum sig))
		   sv-signed (or sv-signed (bsv-sig-signed sig))))
	    ;; Doesn't match next signal, add to que, zero in prep for next
	    ;; Note sig may also be nil for the last signal in the list
	    (t
	     (setq out-list
		   (cons (list sv-name
			       (or sv-busstring
				   (if sv-highbit
				       (concat "[" (int-to-string sv-highbit) ":" (int-to-string sv-lowbit) "]")))
			       (concat sv-comment combo)
			       sv-memory sv-enum sv-signed)
			 out-list)
		   sv-name nil)))
      )
    ;;
    out-list))

;;
;; Port/Wire/Etc Reading
;;

(defun bsv-read-inst-module ()
  "Return module_name when point is inside instantiation."
  (save-excursion
    (bsv-backward-open-paren)
    ;; Skip over instantiation name
    (bsv-re-search-backward-quick "\\b[a-zA-Z0-9`_\$]" nil nil)
    (skip-chars-backward "a-zA-Z0-9`_$")
    (bsv-re-search-backward-quick "\\(\\b[a-zA-Z0-9`_\$]\\|)\\)" nil nil)  ; ) isn't word boundary
    ;; Check for parameterized instantiations
    (when (looking-at ")")
      (bsv-backward-open-paren)
      (bsv-re-search-backward-quick "\\b[a-zA-Z0-9`_\$]" nil nil))
    (skip-chars-backward "a-zA-Z0-9'_$")
    (looking-at "[a-zA-Z0-9`_\$]+")
    ;; Important: don't use match string, this must work with emacs 19 font-lock on
    (buffer-substring-no-properties (match-beginning 0) (match-end 0))))

(defun bsv-read-inst-name ()
  "Return instance_name when point is inside instantiation."
  (save-excursion
    (bsv-backward-open-paren)
    (bsv-re-search-backward-quick "\\b[a-zA-Z0-9`_\$]" nil nil)
    (skip-chars-backward "a-zA-Z0-9`_$")
    (looking-at "[a-zA-Z0-9`_\$]+")
    ;; Important: don't use match string, this must work with emacs 19 font-lock on
    (buffer-substring-no-properties (match-beginning 0) (match-end 0))))

(defun bsv-read-module-name ()
  "Return module name when after its ( or ;."
  (save-excursion
    (re-search-backward "[(;]")
    (bsv-re-search-backward-quick "\\b[a-zA-Z0-9`_\$]" nil nil)
    (skip-chars-backward "a-zA-Z0-9`_$")
    (looking-at "[a-zA-Z0-9`_\$]+")
    ;; Important: don't use match string, this must work with emacs 19 font-lock on
    (buffer-substring-no-properties (match-beginning 0) (match-end 0))))

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
	(functask 0) (paren 0)
	sigs-in sigs-out sigs-inout sigs-wire sigs-reg sigs-assign sigs-const
	vec expect-signal keywd newsig rvalue enum io signed)
    (save-excursion
      (bsv-beg-of-defun)
      (setq sigs-const (bsv-read-auto-constants (point) end-mod-point))
      (while (< (point) end-mod-point)
	;;(if dbg (setq dbg (cons (format "Pt %s  Vec %s   Kwd'%s'\n" (point) vec keywd) dbg)))
	(cond
	 ((looking-at "//")
	  (if (looking-at "[^\n]*synopsys\\s +enum\\s +\\([a-zA-Z0-9_]+\\)")
	      (setq enum (match-string 1)))
	  (search-forward "\n"))
	 ((looking-at "/\\*")
	  (forward-char 2)
	  (if (looking-at "[^*]*synopsys\\s +enum\\s +\\([a-zA-Z0-9_]+\\)")
	      (setq enum (match-string 1)))
	  (or (search-forward "*/")
	      (error "%s: Unmatched /* */, at char %d" (bsv-point-text) (point))))
	 ((eq ?\" (following-char))
	  (or (re-search-forward "[^\\]\"" nil t)	;; don't forward-char first, since we look for a non backslash first
	      (error "%s: Unmatched quotes, at char %d" (bsv-point-text) (point))))
	 ((eq ?\; (following-char))
	  (setq vec nil  io nil  expect-signal nil  newsig nil  paren 0  rvalue nil)
	  (forward-char 1))
	 ((eq ?= (following-char))
	  (setq rvalue t newsig nil)
	  (forward-char 1))
	 ((and rvalue
	       (cond ((and (eq ?, (following-char))
			   (eq paren 0))
		      (setq rvalue nil)
		      (forward-char 1)
		      t)
		     ;; ,'s can occur inside {} & funcs
		     ((looking-at "[{(]")
		      (setq paren (1+ paren))
		      (forward-char 1)
		      t)
		     ((looking-at "[})]")
		      (setq paren (1- paren))
		      (forward-char 1)
		      t)
		     )))
	 ((looking-at "\\s-*\\(\\[[^]]+\\]\\)")
	  (goto-char (match-end 0))
	  (cond (newsig	; Memory, not just width.  Patch last signal added's memory (nth 3)
		 (setcar (cdr (cdr (cdr newsig))) (match-string 1)))
		(t ;; Bit width
		 (setq vec (bsv-string-replace-matches
			    "\\s-+" "" nil nil (match-string 1))))))
	 ;; Normal or escaped identifier -- note we remember the \ if escaped
	 ((looking-at "\\s-*\\([a-zA-Z0-9`_$]+\\|\\\\[^ \t\n]+\\)")
	  (goto-char (match-end 0))
	  (setq keywd (match-string 1))
	  (when (string-match "^\\\\" keywd)
	    (setq keywd (concat keywd " ")))  ;; Escaped ID needs space at end
	  (cond ((equal keywd "input")
		 (setq vec nil enum nil  newsig nil  signed nil  io t  expect-signal 'sigs-in))
		((equal keywd "output")
		 (setq vec nil enum nil  newsig nil  signed nil  io t  expect-signal 'sigs-out))
		((equal keywd "inout")
		 (setq vec nil enum nil  newsig nil  signed nil  io t  expect-signal 'sigs-inout))
 		((or (equal keywd "wire")
 		     (equal keywd "tri"))
		 (unless io (setq vec nil  enum nil  signed nil  expect-signal 'sigs-wire)))
 		((or (equal keywd "reg")
 		     (equal keywd "trireg"))
		 (unless io (setq vec nil  enum nil  signed nil  expect-signal 'sigs-reg)))
		((equal keywd "assign")
		 (setq vec nil  enum nil  signed nil  expect-signal 'sigs-assign))
		((or (equal keywd "supply0")
		     (equal keywd "supply1")
		     (equal keywd "supply")
		     (equal keywd "parameter"))
		 (unless io (setq vec nil  enum nil  signed nil  expect-signal 'sigs-const)))
		((equal keywd "signed")
		 (setq signed "signed"))
		((or (equal keywd "function")
		     (equal keywd "task"))
		 (setq functask (1+ functask)))
		((or (equal keywd "endfunction")
		     (equal keywd "endtask"))
		 (setq functask (1- functask)))
		((and expect-signal
		      (eq functask 0)
		      (not (member keywd bsv-keywords))
		      (not rvalue))
		 ;; Add new signal to expect-signal's variable
		 (setq newsig (list keywd vec nil nil enum signed))
		 (set expect-signal (cons newsig
					  (symbol-value expect-signal))))))
	 (t
	  (forward-char 1)))
	(skip-syntax-forward " "))
      ;; Return arguments
      (vector (nreverse sigs-out)
	      (nreverse sigs-inout)
	      (nreverse sigs-in)
	      (nreverse sigs-wire)
	      (nreverse sigs-reg)
	      (nreverse sigs-assign)
	      (nreverse sigs-const)
	      ))))

(defvar sigs-in nil) ; Prevent compile warning
(defvar sigs-inout nil) ; Prevent compile warning
(defvar sigs-out nil) ; Prevent compile warning

(defun bsv-read-sub-decls-line (submodi comment)
  "For read-sub-decl, read lines of port defs until none match anymore.
Return the list of signals found, using submodi to look up each port."
  (let (done port portdata sig vec)
    (save-excursion
      (forward-line 1)
      (while (not done)
	;; Get port name
	(cond ((looking-at "\\s-*\\.\\s-*\\([a-zA-Z0-9`_$]*\\)\\s-*(\\s-*")
	       (setq port (match-string 1))
	       (goto-char (match-end 0)))
	      ((looking-at "\\s-*\\.\\s-*\\(\\\\[^ \t\n]*\\)\\s-*(\\s-*")
	       (setq port (concat (match-string 1) " ")) ;; escaped id's need trailing space
	       (goto-char (match-end 0)))
	      ((looking-at "\\s-*\\.[^(]*(")
	       (setq port nil) ;; skip this line
	       (goto-char (match-end 0)))
	      (t
	       (setq port nil  done t))) ;; Unknown, ignore rest of line
	;; Get signal name
	(when port
	  (cond ((looking-at "\\(\\\\[^ \t\n]*\\)\\s-*)")
		 (setq sig (concat (match-string 1) " ") ;; escaped id's need trailing space
		       vec nil))
		((looking-at "\\([^[({)]*\\)\\s-*)")
		 (setq sig (bsv-string-remove-spaces (match-string 1))
		       vec nil))
		((looking-at "\\([^[({)]*\\)\\s-*\\(\\[[^]]+\\]\\)\\s-*)")
		 (setq sig (bsv-string-remove-spaces (match-string 1))
		       vec (bsv-symbol-detick-denumber (match-string 2))))
		(t
		 (setq sig nil)))
	  ;; Process signals
	  (when sig
	    (setq port (bsv-symbol-detick-denumber port))
	    (setq sig  (bsv-symbol-detick-denumber sig))
	    (unless (or (not sig)
			(equal sig ""))  ;; Ignore .foo(1'b1) assignments
	      (cond ((setq portdata (assoc port (bsv-modi-get-inouts submodi)))
		     (setq sigs-inout (cons (list sig vec (concat "To/From " comment) nil nil
		   				  (bsv-sig-signed portdata)) sigs-inout)))
		    ((setq portdata (assoc port (bsv-modi-get-outputs submodi)))
		     (setq sigs-out   (cons (list sig vec (concat "From " comment) nil nil
						  (bsv-sig-signed portdata)) sigs-out)))
		    ((setq portdata (assoc port (bsv-modi-get-inputs submodi)))
		     (setq sigs-in    (cons (list sig vec (concat "To " comment) nil nil
						  (bsv-sig-signed portdata)) sigs-in)))
		    ;; (t  -- warning pin isn't defined.)   ; Leave for lint tool
		    )
	      )))
	;;
	(forward-line 1)))))
  
(defun bsv-read-sub-decls ()
  "Parse signals going to modules under this module.
Return a array of [ outputs inouts inputs ] signals for modules that are
instantiated in this module.  For example if declare A A (.B(SIG)) and SIG
is a output, then SIG will be included in the list.

This only works on instantiations created with /*AUTOINST*/ converted by
\\[bsv-auto-instant].  Otherwise, it would have to read in the whole
component library to determine connectivity of the design."
  (save-excursion
    (let ((end-mod-point (bsv-get-end-of-defun t))
	  st-point end-inst-point
	  ;; below 3 modified by bsv-read-sub-decls-line
	  sigs-out sigs-inout sigs-in)
      (bsv-beg-of-defun)
      (while (search-forward "/*AUTOINST*/" end-mod-point t)
	(save-excursion
	  (goto-char (match-beginning 0))
	  (unless (bsv-inside-comment-p)
	    ;; Attempt to snarf a comment
	    (let* ((submod (bsv-read-inst-module))
		   (inst (bsv-read-inst-name))
		   (comment (concat inst " of " submod ".v")) submodi)
	      (when (setq submodi (bsv-modi-lookup submod t))
		;; This could have used a list created by bsv-auto-instant
		;; However I want it to be runnable even on user's manually added signals
		(bsv-backward-open-paren)
		(setq end-inst-point (save-excursion (forward-sexp 1) (point))
		      st-point (point))
		(while (re-search-forward "^\\s *// Outputs" end-inst-point t)
		  (bsv-read-sub-decls-line submodi comment)) ;; Modifies sigs-out
		(goto-char st-point)
		(while (re-search-forward "\\s *// Inouts" end-inst-point t)
		  (bsv-read-sub-decls-line submodi comment)) ;; Modifies sigs-inout
		(goto-char st-point)
		(while (re-search-forward "\\s *// Inputs" end-inst-point t)
		  (bsv-read-sub-decls-line submodi comment)) ;; Modifies sigs-in
		)))))
      ;; Combine duplicate bits
      ;;(setq rr (vector sigs-out sigs-inout sigs-in))
      (vector (bsv-signals-combine-bus (nreverse sigs-out))
	      (bsv-signals-combine-bus (nreverse sigs-inout))
	      (bsv-signals-combine-bus (nreverse sigs-in))))))

(defun bsv-read-inst-pins ()
  "Return a array of [ pins ] for the current instantiation at point.
For example if declare A A (.B(SIG)) then B will be included in the list."
  (save-excursion
    (let ((end-mod-point (point))	;; presume at /*AUTOINST*/ point
	  pins pin)
      (bsv-backward-open-paren)
      (while (re-search-forward "\\.\\([^( \t\n]*\\)\\s-*(" end-mod-point t)
	(setq pin (match-string 1))
	(unless (bsv-inside-comment-p)
	  (setq pins (cons (list pin) pins))))
      (vector pins))))

(defun bsv-read-arg-pins ()
  "Return a array of [ pins ] for the current argument declaration at point."
  (save-excursion
    (let ((end-mod-point (point))	;; presume at /*AUTOARG*/ point
	  pins pin)
      (bsv-backward-open-paren)
      (while (re-search-forward "\\([a-zA-Z0-9`_$]+\\)" end-mod-point t)
	(setq pin (match-string 1))
	(unless (bsv-inside-comment-p)
	  (setq pins (cons (list pin) pins))))
      (vector pins))))

(defun bsv-read-auto-constants (beg end-mod-point)
  "Return a list of AUTO_CONSTANTs used in the region from BEG to END-MOD-POINT."
  ;; Insert new
  (save-excursion
    (let (sig-list tpl-end-pt)
      (goto-char beg)
      (while (re-search-forward "\\<AUTO_CONSTANT" end-mod-point t)
	(search-forward "(" end-mod-point)
	(setq tpl-end-pt (save-excursion
			   (backward-char 1)
			   (forward-sexp 1)   ;; Moves to paren that closes argdecl's
			   (backward-char 1)
			   (point)))
	(while (re-search-forward "\\s-*\\([\"a-zA-Z0-9`_$]+\\)\\s-*,*" tpl-end-pt t)
	  (setq sig-list (cons (list (match-string 1) nil nil) sig-list))))
      sig-list)))

(defun bsv-read-auto-lisp (start end)
  "Look for and evaluate a AUTO_LISP between START and END."
  (save-excursion
    (goto-char start)
    (while (re-search-forward "\\<AUTO_LISP(" end t)
      (backward-char)
      (let* ((beg-pt (prog1 (point)
		       (forward-sexp 1)))	;; Closing paren
	     (end-pt (point)))
	(eval-region beg-pt end-pt nil)))))

(eval-when-compile
  ;; These are passed in a let, not global
  (if (not (boundp 'sigs-in))
      (defvar sigs-in nil) (defvar sigs-out nil)
      (defvar got-sig nil) (defvar got-rvalue nil) (defvar uses-delayed nil)))

(defun bsv-read-always-signals-recurse
  (exit-keywd rvalue ignore-next)
  "Recursive routine for parentheses/bracket matching.
EXIT-KEYWD is expression to stop at, nil if top level.
RVALUE is true if at right hand side of equal.
IGNORE-NEXT is true to ignore next token, fake from inside case statement."
  (let* ((semi-rvalue (equal "endcase" exit-keywd)) ;; true if after a ; we are looking for rvalue
	 keywd last-keywd sig-tolk sig-last-tolk gotend end-else-check)
    ;;(if dbg (setq dbg (concat dbg (format "Recursion %S %S %S\n" exit-keywd rvalue ignore-next))))
    (while (not (or (eobp) gotend))
      (cond
       ((looking-at "//")
	(search-forward "\n"))
       ((looking-at "/\\*")
	(or (search-forward "*/")
	    (error "%s: Unmatched /* */, at char %d" (bsv-point-text) (point))))
       (t (setq keywd (buffer-substring-no-properties
		       (point)
		       (save-excursion (when (eq 0 (skip-chars-forward "a-zA-Z0-9$_.%`"))
					 (forward-char 1))
				       (point)))
		sig-last-tolk sig-tolk
		sig-tolk nil)
	  ;;(if dbg (setq dbg (concat dbg (format "\tPt %S %S\t%S %S %S\n" (point) keywd rvalue ignore-next end-else-check))))
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
	   ((and end-else-check (looking-at "[^ \t\n]"))
	    ;;(if dbg (setq dbg (concat dbg (format "\tif-check-else-other %s\n" keywd))))
	    (setq gotend t))
	   ;; Final statement?
	   ((and exit-keywd (equal keywd exit-keywd))
	    (setq gotend t)
	    (forward-char (length keywd)))
	   ;; Standard tokens...
	   ((equal keywd ";")
	    (setq ignore-next nil rvalue semi-rvalue)
	    ;; Final statement at top level loop?
	    (when (not exit-keywd)
	      ;;(if dbg (setq dbg (concat dbg (format "\ttop-end-check %s\n" keywd))))
	      (setq end-else-check t))
	    (forward-char 1))
	   ((equal keywd "'")
	    (if (looking-at "'s?[hdxbo][0-9a-fA-F_xz? \t]*")
		(goto-char (match-end 0))
	      (forward-char 1)))
	   ((equal keywd ":")	;; Case statement, begin/end label, x?y:z
	    (cond ((equal "endcase" exit-keywd)  ;; case x: y=z; statement next
		   (setq ignore-next nil rvalue nil))
		  ((not rvalue)	;; begin label
		   (setq ignore-next t rvalue nil)))
	    (forward-char 1))
	   ((equal keywd "=")
	    (if (eq (char-before) ?< )
		(setq uses-delayed 1))
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
		   (bsv-read-always-signals-recurse ";" nil nil)
		   (bsv-read-always-signals-recurse ";" t nil)
		   (bsv-read-always-signals-recurse ")" nil nil))
		  (t (bsv-read-always-signals-recurse ")" t nil))))
	   ((equal keywd "begin")
	    (skip-syntax-forward "w_")
	    (bsv-read-always-signals-recurse "end" nil nil)
	    ;;(if dbg (setq dbg (concat dbg (format "\tgot-end %s\n" exit-keywd))))
	    (setq ignore-next nil rvalue semi-rvalue)
	    (if (not exit-keywd) (setq end-else-check t)))
	   ((or (equal keywd "case")
		(equal keywd "casex")
		(equal keywd "casez"))
	    (skip-syntax-forward "w_")
	    (bsv-read-always-signals-recurse "endcase" t nil)
	    (setq ignore-next nil rvalue semi-rvalue)
	    (if (not exit-keywd) (setq gotend t)))	;; top level begin/end
	   ((string-match "^[$`a-zA-Z_]" keywd)	;; not exactly word constituent
	    (cond ((equal keywd "`ifdef")
		   (setq ignore-next t))
		  ((or ignore-next
		       (member keywd bsv-keywords)
		       (string-match "^\\$" keywd))	;; PLI task
		   (setq ignore-next nil))
		  (t
		   (setq keywd (bsv-symbol-detick-denumber keywd))
		   (if got-sig (if got-rvalue
				   (setq sigs-in (cons got-sig sigs-in))
				 (setq sigs-out (cons got-sig sigs-out))))
		   (setq got-rvalue rvalue
			 got-sig (if (or (not keywd)
					 (assoc keywd (if got-rvalue sigs-in sigs-out)))
				     nil (list keywd nil nil))
			 sig-tolk t)))
	    (skip-chars-forward "a-zA-Z0-9$_.%`"))
	   (t
	    (forward-char 1)))
	  ;; End of non-comment token
	  (setq last-keywd keywd)
	  ))
      (skip-syntax-forward " "))
    ;;(if dbg (setq dbg (concat dbg (format "ENDRecursion %s\n" exit-keywd))))
    ))

(defun bsv-read-always-signals ()
  "Parse always block at point and return list of (outputs inout inputs)."
  ;; Insert new
  (save-excursion
    (let* (;;(dbg "")
	   sigs-in sigs-out
	   got-sig got-rvalue
	   uses-delayed)	;; Found signal/rvalue; push if not function
      (search-forward ")")
      (bsv-read-always-signals-recurse nil nil nil)
      ;; Return what was found
      (if got-sig (if got-rvalue
		      (setq sigs-in (cons got-sig sigs-in))
		    (setq sigs-out (cons got-sig sigs-out))))
      ;;(if dbg (message dbg))
      (list sigs-out nil sigs-in uses-delayed))))

(defun bsv-read-instants ()
  "Parse module at point and return list of ( ( file instance ) ... )."
  (bsv-beg-of-defun)
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
	(forward-line 1)
	))
    instants-list))


(defun bsv-read-auto-template (module)
  "Look for a auto_template for the instantiation of the given MODULE.
If found returns the signal name connections.  Return nil or list of
 ( (signal_name connection_name)... )"
  (save-excursion
    ;; Find beginning
    (let (tpl-sig-list tpl-wild-list tpl-end-pt rep)
      (cond ((or
	       (re-search-backward (concat "^\\s-*/?\\*?\\s-*" module "\\s-+AUTO_TEMPLATE") nil t)
	       (progn
		 (goto-char (point-min))
		 (re-search-forward (concat "^\\s-*/?\\*?\\s-*" module "\\s-+AUTO_TEMPLATE") nil t)))
	     (search-forward "(")
	     (setq tpl-end-pt (save-excursion
				(backward-char 1)
				(forward-sexp 1)   ;; Moves to paren that closes argdecl's
				(backward-char 1)
				(point)))
	     ;;
	     (while (< (point) tpl-end-pt)
	       (cond ((looking-at "\\s-*\\.\\([a-zA-Z0-9`_$]+\\)\\s-*(\\(.*\\))\\s-*\\(,\\|)\\s-*;\\)")
		      (setq tpl-sig-list (cons (list
						(match-string-no-properties 1)
						(match-string-no-properties 2))
					       tpl-sig-list)))
		     ;; Regexp form??
		     ((looking-at
		       ;; Regexp bug in xemacs disallows ][ inside [], and wants + last
		       "\\s-*\\.\\(\\([a-zA-Z0-9`_$+@^.*?---]+\\|[][]\\|\\\\[()]\\)+\\)\\s-*(\\(.*\\))\\s-*\\(,\\|)\\s-*;\\)")
		      (setq rep (match-string-no-properties 3))
		      (setq tpl-wild-list
			    (cons (list
				   (concat "^"
					   (bsv-string-replace-matches "@" "\\\\([0-9]+\\\\)" nil nil
									   (match-string 1))
					   "$")
				   rep)
				  tpl-wild-list))))
	       (forward-line 1))
	     ;;
	     (list tpl-sig-list tpl-wild-list)
	     )))))
;;(progn (find-file "auto-template.v") (bsv-read-auto-template "ptl_entry"))

(defun bsv-set-define (defname defvalue &optional buffer enumname)
  "In BUFFER, set the definition DEFNAME to the DEFVALUE."
  (save-excursion
    (set-buffer (or buffer (current-buffer)))
    (let ((mac (intern (concat "vh-" defname))))
      ;;(message "Define %s=%s" defname defvalue) (sleep-for 1)
      (set (make-variable-buffer-local mac) defvalue))
    (if enumname
	(let ((enumvar (intern (concat "venum-" enumname))))
	  ;;(message "Define %s=%s" defname defvalue) (sleep-for 1)
	  (make-variable-buffer-local enumvar) 
	  (add-to-list enumvar defname)))
    ))

(defun bsv-read-defines (&optional filename recurse)
  "Read `defines for the current file, or from the optional FILENAME.
If the filename is provided, `bsv-library-directories' and
`bsv-library-extensions' will be used to resolve it.
If optional RECURSE is non-nil, recurse through `includes.

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

(setq enable-local-eval t)
"
  (let ((origbuf (current-buffer)))
    (save-excursion
      (when filename
	(let ((fns (bsv-library-filenames filename (buffer-file-name))))
	  (if fns
	      (set-buffer (find-file-noselect (car fns)))
	    (error (concat (bsv-point-text)
			   ": Can't find bsv-read-defines file: " filename)))))
      (when recurse
	(goto-char (point-min))
	(while (re-search-forward "^\\s-*`include\\s-+\\([^ \t\n]+\\)" nil t)
	  (let ((inc (bsv-string-replace-matches "\"" "" nil nil (match-string-no-properties 1))))
	    (unless (bsv-inside-comment-p)
	      (bsv-read-defines inc recurse)))))
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
	      "^\\s-*parameter\\(\\(\\s-*\\[[^]]*\\]\\|\\)\\s-+\\([a-zA-Z0-9_$]+\\)\\s-*=\\s-*\\([^;,]*\\),?\\|\\)\\s-*" nil t)
	(let ((var (match-string-no-properties 3))
	      (val (match-string-no-properties 4))
	      enumname)
	  ;; The primary way of getting defines is bsv-read-decls
	  ;; However, that isn't called yet for included files, so we'll add another scheme
	  (if (looking-at "[^\n]*synopsys\\s +enum\\s +\\([a-zA-Z0-9_]+\\)")
	      (setq enumname (match-string-no-properties 1)))
	  (if var
	    (bsv-set-define var val origbuf enumname))
	  (forward-comment 999)
	  (while (looking-at "\\s-*,?\\s-*\\([a-zA-Z0-9_$]+\\)\\s-*=\\s-*\\([^;,]*\\),?\\s-*")
	    (bsv-set-define (match-string-no-properties 1) (match-string-no-properties 2) origbuf enumname)
	    (goto-char (match-end 0))
	    (forward-comment 999))))
      )))

(defun bsv-read-includes ()
  "Read `includes for the current file.
This will find all of the `includes which are at the beginning of lines,
ignoring any ifdefs or multiline comments around them.
`bsv-read-defines' is then performed on the current and each included
file.

It is often useful put at the *END* of your file something like:

// Local Variables:
// eval:(bsv-read-includes)
// End:

Note includes are only read when the file is first visited, you must use
\\[find-alternate-file] RET  to have these take effect after editing them!

It is good to get in the habit of including all needed files in each .v
file that needs it, rather then waiting for compile time.  This will aid
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
    (goto-char (point-min))
    (while (re-search-forward "^\\s-*`include\\s-+\\([^ \t\n]+\\)" nil t)
      (let ((inc (bsv-string-replace-matches "\"" "" nil nil (match-string 1))))
	(bsv-read-defines inc)))))

(defun bsv-read-signals (&optional start end)
  "Return a simple list of all possible signals in the file.
Bounded by optional region from START to END.  Overly aggressive but fast.
Some macros and such are also found and included.  For dinotrace.el"
  (let (sigs-all keywd)
    (progn;save-excursion
      (goto-char (or start (point-min)))
      (setq end (or end (point-max)))
      (while (re-search-forward "[\"/a-zA-Z_]" end t)
	(forward-char -1)
	(cond
	 ((looking-at "//")
	  (search-forward "\n"))
	 ((looking-at "/\\*")
	  (search-forward "*/"))
	 ((eq ?\" (following-char))
	  (re-search-forward "[^\\]\""))	;; don't forward-char first, since we look for a non backslash first
	 ((looking-at "\\s-*\\([a-zA-Z0-9`_$]+\\)")
	  (goto-char (match-end 0))
	  (setq keywd (match-string-no-properties 1))
	  (or (member keywd bsv-keywords)
	      (member keywd sigs-all)
	      (setq sigs-all (cons keywd sigs-all))))
	 (t (forward-char 1)))
	)
      ;; Return list
      sigs-all)))


;;
;; Module name lookup
;;

(defun bsv-module-inside-filename-p (module filename)
  "Return point if MODULE is specified inside FILENAME, else nil.
Allows version control to check out the file if need be."
  (and (or (file-exists-p filename)
	   (and 
	    (condition-case nil
		(fboundp 'vc-backend) 
	      (error nil))
	    (vc-backend filename)))
       (let (pt)
	 (save-excursion
	   (set-buffer (find-file-noselect filename))
	   (goto-char (point-min))
	   (while (and
		   ;; It may be tempting to look for bsv-defun-re, don't, it slows things down a lot!
		   (bsv-re-search-forward-quick "module" nil t)
		   (bsv-re-search-forward-quick "[(;]" nil t))
	     (if (equal module (bsv-read-module-name))
		 (setq pt (point))))
	   pt))))

(defun bsv-is-number (symbol)
  "Return true if SYMBOL is number-like."
  (or (string-match "^[0-9 \t:]+$" symbol)
      (string-match "^[---]*[0-9]+$" symbol)
      (string-match "^[0-9 \t]+'s?[hdxbo][0-9a-fA-F_xz? \t]*$" symbol)
      ))

(defun bsv-symbol-detick (symbol wing-it)
  "Return a expanded SYMBOL name without any defines.
If the variable vh-{symbol} is defined, return that value.
If undefined, and WING-IT, return just SYMBOL without the tick, else nil."
  (while (and symbol (string-match "^`" symbol))
    (setq symbol (substring symbol 1))
    (setq symbol
	  (if (boundp (intern (concat "vh-" symbol)))
	      ;; Emacs has a bug where boundp on a buffer-local variable in only one
	      ;; buffer returns t in another.  This can confuse, so check for nil.
	      (let ((val (eval (intern (concat "vh-" symbol)))))
		(if (eq val nil)
		    (if wing-it symbol nil)
		  val))
	    (if wing-it symbol nil))))
  symbol)
;;(bsv-symbol-detick "`mod" nil)

(defun bsv-symbol-detick-denumber (symbol)
  "Return symbol with defines converted and any numbers dropped to nil."
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

(defun bsv-expand-dirnames (&optional dirnames)
  "Return a list of existing directories given a list of wildcarded dirnames
or just the existing dirnames themselves if there are no wildcards."
  (interactive)
  (unless dirnames (error "bsv-library-directories should include at least '.'"))
  (setq dirnames (reverse dirnames))	; not nreverse
  (let ((dirlist nil)
	pattern dirfile dirfiles dirname root filename rest)
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
	     ;;bsv-string-replace-matches
	     (setq pattern (bsv-string-replace-matches "[*]" ".+" nil nil pattern)
		   pattern (bsv-string-replace-matches "[?]" "." nil nil pattern)

		   ;; Unfortunately allows abc/*/rtl to match abc/rtl
		   ;; because abc/.. shows up in dirfiles.  Solutions welcome.
		   dirfiles (directory-files root t pattern nil))
	     (while dirfiles
	       (setq dirfile (expand-file-name (concat (car dirfiles) rest))
		     dirfiles (cdr dirfiles))
	       (if (file-directory-p dirfile)
		   (setq dirlist (cons dirfile dirlist))))
	     )
	    ;; Defaults
	    (t
	     (if (file-directory-p dirname)
		 (setq dirlist (cons dirname dirlist))))
	    ))
    dirlist))
;;(bsv-expand-dirnames (list "." ".." "nonexist" "../*" "/home/wsnyder/*/v"))

(defun bsv-library-filenames (filename current)
  "Return a search path to find the given FILENAME name.
Uses the CURRENT filename, `bsv-library-directories' and
`bsv-library-extensions' variables to build the path."
  (let ((ckdir (bsv-expand-dirnames bsv-library-directories))
	fn outlist)
    (while ckdir
      (setq fn (expand-file-name
		filename
		(expand-file-name (car ckdir) (file-name-directory current))))
      (if (file-exists-p fn)
	  (setq outlist (cons fn outlist)))
      (setq ckdir (cdr ckdir)))
    (nreverse outlist)))

(defun bsv-module-filenames (module current)
  "Return a search path to find the given MODULE name.
Uses the CURRENT filename, `bsv-library-extensions',
`bsv-library-directories' and `bsv-library-files'
variables to build the path."
  ;; Return search locations for it
  (append (list current)	; first, current buffer
 	  (let ((ext bsv-library-extensions) flist)
 	    (while ext
 	      (setq flist
 		    (append (bsv-library-filenames
 			     (concat module (car ext)) current) flist)
		    ext (cdr ext)))
	    flist)
	  bsv-library-files	 ; finally, any libraries
	  ))

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

(defvar bsv-modi-cache-preserve-tick nil
  "Modification tick after which the cache is still considered valid.
Use bsv-preserve-cache's to set")
(defvar bsv-modi-cache-preserve-buffer nil
  "Modification tick after which the cache is still considered valid.
Use bsv-preserve-cache's to set")

(defun bsv-modi-current ()
  "Return the modi structure for the module currently at point."
  (let* (name pt)
    ;; read current module's name
    (save-excursion
      (bsv-re-search-backward-quick bsv-defun-re nil nil)
      (bsv-re-search-forward-quick "(" nil nil)
      (setq name (bsv-read-module-name))
      (setq pt (point)))
    ;; return
    (vector name (or (buffer-file-name) (current-buffer)) pt)))

(defvar bsv-modi-lookup-last-mod nil "Cache of last module looked up.")
(defvar bsv-modi-lookup-last-current nil "Cache of last current looked up.")
(defvar bsv-modi-lookup-last-modi nil "Cache of last modi returned.")

(defun bsv-modi-lookup (module allow-cache)
  "Find the file and point at which MODULE is defined.
If ALLOW-CACHE is set, check and remember cache of previous lookups.
Return modi if successful, else print message."
  (let* ((current (or (buffer-file-name) (current-buffer))))
    (cond ((and (equal bsv-modi-lookup-last-mod module)
		(equal bsv-modi-lookup-last-current current)
		bsv-modi-lookup-last-modi
		bsv-cache-enabled
		allow-cache)
	   ;; ok as is
	   )
	  (t (let* ((realmod (bsv-symbol-detick module t))
		    (orig-filenames (bsv-module-filenames realmod current))
		    (filenames orig-filenames)
		    pt)
	       (while (and filenames (not pt))
		 (if (not (setq pt (bsv-module-inside-filename-p realmod (car filenames))))
		     (setq filenames (cdr filenames))))
	       (cond (pt (setq bsv-modi-lookup-last-modi
			       (vector realmod (car filenames) pt)))
		     (t (setq bsv-modi-lookup-last-modi nil)
			(error (concat (bsv-point-text)
				       ": Can't locate " module " module definition"
				       (if (not (equal module realmod))
					   (concat " (Expanded macro to " realmod ")")
					 "")
				       "\n    Check the bsv-library-directories variable."
				       "\n    I looked in (if not listed, doesn't exist):\n\t" (mapconcat 'concat orig-filenames "\n\t"))))
		     )
	       (setq bsv-modi-lookup-last-mod module
		     bsv-modi-lookup-last-current current))))
    bsv-modi-lookup-last-modi
    ))

(defsubst bsv-modi-name (modi)
  (aref modi 0))
(defsubst bsv-modi-file-or-buffer (modi)
  (aref modi 1))
(defsubst bsv-modi-point (modi)
  (aref modi 2))

(defun bsv-modi-filename (modi)
  "Filename of modi, or name of buffer if its never been saved"
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
  (or (equal major-mode `bsv-mode)	;; Put into bsv mode to get syntax
      (bsv-mode))
  (goto-char (bsv-modi-point modi)))

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
  (let (func-returns fass)
    (save-excursion
      (bsv-modi-goto modi)
      (if (and (setq fass (assoc (list (bsv-modi-name modi) function)
				 bsv-modi-cache-list))
	       ;; Destroy caching when incorrect; Modified or file changed
	       (not (and bsv-cache-enabled
			 (or (equal (buffer-modified-tick) (nth 1 fass))
			     (and bsv-modi-cache-preserve-tick
				  (<= bsv-modi-cache-preserve-tick  (nth 1 fass))
				  (equal  bsv-modi-cache-preserve-buffer (current-buffer))))
			 (equal (visited-file-modtime) (nth 2 fass)))))
	  (setq bsv-modi-cache-list nil
		fass nil))
      (cond (fass
	     ;; Found
	     (setq func-returns (nth 3 fass)))
	    (t
	     ;; Read from file
	     ;; Clear then restore any hilighting to make emacs19 happy
	     (let ((fontlocked (when (and (memq 'v19 bsv-emacs-features)
					  (boundp 'font-lock-mode)
					  font-lock-mode)
				 (font-lock-mode nil)
				 t)))
	       (setq func-returns (funcall function))
	       (when fontlocked (font-lock-mode t)))
	     ;; Cache for next time
	     (make-variable-buffer-local 'bsv-modi-cache-list)
	     (setq bsv-modi-cache-list
		   (cons (list (list (bsv-modi-name modi) function)
			       (buffer-modified-tick)
			       (visited-file-modtime)
			       func-returns)
			 bsv-modi-cache-list)))
	    ))
      ;;
      func-returns))

(defun bsv-modi-cache-add (modi function element sig-list)
  "Add function return results to the module cache.
Update MODI's cache for given FUNCTION so that the return ELEMENT of that
function now contains the additional SIG-LIST parameters."
  (let (fass)
    (save-excursion
      (bsv-modi-goto modi)
      (if (setq fass (assoc (list (bsv-modi-name modi) function)
			    bsv-modi-cache-list))
	  (let ((func-returns (nth 3 fass)))
	    (aset func-returns element
		  (append sig-list (aref func-returns element))))))))

(defmacro bsv-preserve-cache (&rest body)
  "Execute the BODY forms, allowing cache preservation within BODY.
This means that changes to the buffer will not result in the cache being
flushed.  If the changes affect the modsig state, they must call the
modsig-cache-add-* function, else the results of later calls may be
incorrect.  Without this, changes are assumed to be adding/removing signals
and invalidating the cache."
  `(let ((bsv-modi-cache-preserve-tick (buffer-modified-tick))
	 (bsv-modi-cache-preserve-buffer (current-buffer)))
     (progn ,@body)))

(defsubst bsv-modi-get-decls (modi)
  (bsv-modi-cache-results modi 'bsv-read-decls))

(defsubst bsv-modi-get-sub-decls (modi)
  (bsv-modi-cache-results modi 'bsv-read-sub-decls))

;; Signal reading for given module
;; Note these all take modi's - as returned from the bsv-modi-current function
(defsubst bsv-modi-get-outputs (modi)
  (aref (bsv-modi-get-decls modi) 0))
(defsubst bsv-modi-get-inouts (modi)
  (aref (bsv-modi-get-decls modi) 1))
(defsubst bsv-modi-get-inputs (modi)
  (aref (bsv-modi-get-decls modi) 2))
(defsubst bsv-modi-get-wires (modi)
  (aref (bsv-modi-get-decls modi) 3))
(defsubst bsv-modi-get-regs (modi)
  (aref (bsv-modi-get-decls modi) 4))
(defsubst bsv-modi-get-assigns (modi)
  (aref (bsv-modi-get-decls modi) 5))
(defsubst bsv-modi-get-consts (modi)
  (aref (bsv-modi-get-decls modi) 6))
(defsubst bsv-modi-get-sub-outputs (modi)
  (aref (bsv-modi-get-sub-decls modi) 0))
(defsubst bsv-modi-get-sub-inouts (modi)
  (aref (bsv-modi-get-sub-decls modi) 1))
(defsubst bsv-modi-get-sub-inputs (modi)
  (aref (bsv-modi-get-sub-decls modi) 2))

;; Elements of a signal list
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
(defsubst bsv-sig-width (sig)
  (bsv-make-width-expression (bsv-sig-bits sig)))

(defsubst bsv-alw-get-inputs (sigs)
  (nth 2 sigs))
(defsubst bsv-alw-get-outputs (sigs)
  (nth 0 sigs))
(defsubst bsv-alw-get-uses-delayed (sigs)
  (nth 3 sigs))

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

;; Combined
(defun bsv-modi-get-signals (modi)
  (append
   (bsv-modi-get-outputs modi)
   (bsv-modi-get-inouts modi)
   (bsv-modi-get-inputs modi)
   (bsv-modi-get-wires modi)
   (bsv-modi-get-regs modi)
   (bsv-modi-get-assigns modi)
   (bsv-modi-get-consts modi)))

(defun bsv-modi-get-ports (modi)
  (append
   (bsv-modi-get-outputs modi)
   (bsv-modi-get-inouts modi)
   (bsv-modi-get-inputs modi)))

(defsubst bsv-modi-cache-add-outputs (modi sig-list)
  (bsv-modi-cache-add modi 'bsv-read-decls 0 sig-list))
(defsubst bsv-modi-cache-add-inouts (modi sig-list)
  (bsv-modi-cache-add modi 'bsv-read-decls 1 sig-list))
(defsubst bsv-modi-cache-add-inputs (modi sig-list)
  (bsv-modi-cache-add modi 'bsv-read-decls 2 sig-list))
(defsubst bsv-modi-cache-add-wires (modi sig-list)
  (bsv-modi-cache-add modi 'bsv-read-decls 3 sig-list))
(defsubst bsv-modi-cache-add-regs (modi sig-list)
  (bsv-modi-cache-add modi 'bsv-read-decls 4 sig-list))

(defun bsv-signals-from-signame (signame-list)
  "Return signals in standard form from SIGNAME-LIST, a simple list of signal names."
  (mapcar (function (lambda (name) (list name nil nil)))
	  signame-list))

;;
;; Auto creation utilities
;;

(defun bsv-auto-search-do (search-for func)
  "Search for the given auto text SEARCH-FOR, and perform FUNC where it occurs."
  (goto-char (point-min))
  (while (search-forward search-for nil t)
    (if (not (save-excursion
	       (goto-char (match-beginning 0))
	       (bsv-inside-comment-p)))
	(funcall func))))

(defun bsv-auto-re-search-do (search-for func)
  "Search for the given auto text SEARCH-FOR, and perform FUNC where it occurs."
  (goto-char (point-min))
  (while (re-search-forward search-for nil t)
    (if (not (save-excursion
	       (goto-char (match-beginning 0))
	       (bsv-inside-comment-p)))
	(funcall func))))

(defun bsv-insert-definition (sigs type indent-pt &optional dont-sort)
  "Print out a definition for a list of SIGS of the given TYPE,
with appropriate INDENT-PT indentation.  Sort unless DONT-SORT.
TYPE is normally wire/reg/output."
  (or dont-sort
      (setq sigs (sort (copy-alist sigs) `bsv-signals-sort-compare)))
  (while sigs
    (let ((sig (car sigs)))
      (indent-to indent-pt)
      (insert type)
      (when (bsv-sig-signed sig)
	(insert " " (bsv-sig-signed sig)))
      (when (bsv-sig-bits sig)
	(insert " " (bsv-sig-bits sig)))
      (indent-to (max 24 (+ indent-pt 16)))
      (insert (concat (bsv-sig-name sig) ";"))
      (if (or (not (bsv-sig-comment sig))
	      (equal "" (bsv-sig-comment sig)))
	  (insert "\n")
	(indent-to (max 48 (+ indent-pt 40)))
	(insert (concat "// " (bsv-sig-comment sig) "\n")))
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
      (insert (car stuff))
      (setq need-indent (string-match "\n$" (car stuff))
	    stuff (cdr stuff)))))
;;(let ((indent-pt 10)) (bsv-insert-indent "hello\n" "addon" "there\n"))

(defun bsv-get-list (start end)
  "Return the elements of a comma separated list."
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
  "Return an expression calculating the length of a range [x:y]."
  ;; strip off the []
  (cond ((not range-exp)
	 "1")
	(t
	 (if (string-match "^\\[\\(.*\\)\\]$" range-exp)
	     (setq range-exp (match-string 1 range-exp)))
	 (cond ((not range-exp)
		"1")
	       ((string-match "^\\s *\\([0-9]+\\)\\s *:\\s *\\([0-9]+\\)\\s *$" range-exp)
		(int-to-string (1+ (- (string-to-int (match-string 1 range-exp))
				      (string-to-int (match-string 2 range-exp))))))
	       ((string-match "^\\(.*\\)\\s *:\\s *\\(.*\\)\\s *$" range-exp)
		(concat "(1+(" (match-string 1 range-exp)
			")-(" (match-string 2 range-exp) "))"))
	       (t nil)))))
;;(bsv-make-width-expression "`A:`B")


;;
;; Auto deletion
;;

(defun bsv-delete-autos-lined ()
  "Delete autos that occupy multiple lines, between begin and end comments."
  (let ((pt (point)))
    (forward-line 1)
    (when (and
	   (looking-at "\\s-*// Beginning")
	   (search-forward "// End of automatic" nil t))
      ;; End exists
      (end-of-line)
      (delete-region pt (point))
      (forward-line 1))
  ))

(defun bsv-backward-open-paren ()
  "Find the open parenthesis that match the current point,
ignore other open parenthesis with matching close parens"
  (let ((parens 1))
    (while (> parens 0)
      (unless (bsv-re-search-backward-quick "[()]" nil t)
	(error "%s: Mismatching ()" (bsv-point-text)))
      (cond ((looking-at ")")
	     (setq parens (1+ parens)))
	    ((looking-at "(")
	     (setq parens (1- parens)))))))

(defun bsv-delete-to-paren ()
  "Delete the automatic inst/sense/arg created by autos.
Deletion stops at the matching end parenthesis."
  (delete-region (point)
		 (save-excursion
		   (bsv-backward-open-paren)
		   (forward-sexp 1)   ;; Moves to paren that closes argdecl's
		   (backward-char 1)
		   (point))))

(defun bsv-delete-auto ()
  "Delete the automatic outputs, regs, and wires created by \\[bsv-auto].
Use \\[bsv-auto] to re-insert the updated AUTOs."
  (interactive)
  (save-excursion
    (if (buffer-file-name)
	(find-file-noselect (buffer-file-name)))	;; To check we have latest version
    ;; Remove those that have multi-line insertions
    (bsv-auto-re-search-do "/\\*AUTO\\(OUTPUTEVERY\\|CONCATCOMMENT\\|WIRE\\|REG\\|DEFINEVALUE\\|REGINPUT\\|INPUT\\|OUTPUT\\|RESET\\)\\*/"
			       'bsv-delete-autos-lined)
    ;; Remove those that have multi-line insertions with parameters
    (bsv-auto-re-search-do "/\\*AUTO\\(INOUTMODULE\\|ASCIIENUM\\)([^)]*)\\*/"
			       'bsv-delete-autos-lined)
    ;; Remove those that are in parenthesis
    (bsv-auto-re-search-do "/\\*\\(AS\\|AUTO\\(ARG\\|CONCATWIDTH\\|INST\\|SENSE\\)\\)\\*/"
			       'bsv-delete-to-paren)

    ;; Remove template comments ... anywhere in case was pasted after AUTOINST removed
    (goto-char (point-min))
    (while (re-search-forward "\\s-*// Templated\\s-*$" nil t)
      (replace-match ""))))


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
	((eq bsv-auto-update-tick (buffer-modified-tick))) ; up-to-date
	((eq bsv-auto-save-policy 'detect)
	 (bsv-auto))
	(t
	 (when (yes-or-no-p "AUTO statements not recomputed, do it now? ")
	   (bsv-auto))
	 ;; Don't ask again if didn't update
	 (set (make-local-variable 'bsv-auto-update-tick) (buffer-modified-tick))
	 ))
  nil)	;; Always return nil -- we don't write the file ourselves

(defun bsv-auto-read-locals ()
  "Return file local variable segment at bottom of file."
  (save-excursion
    (goto-char (point-max))
    (if (re-search-backward "Local Variables:" nil t)
	(buffer-substring-no-properties (point) (point-max))
      "")))

(defun bsv-auto-reeval-locals (&optional just-cache)
  "Read file local variable segment at bottom of file if it's changed since last read."
  (make-variable-buffer-local 'bsv-auto-last-file-locals)
  (let ((curlocal (bsv-auto-read-locals)))
    (when (not (equal bsv-auto-last-file-locals curlocal))
      (unless just-cache (hack-local-variables))
      (setq bsv-auto-last-file-locals curlocal)
      t)))

;;
;; Auto creation
;;

(defun bsv-auto-arg-ports (sigs message indent-pt)
  "Print a list of ports for a AUTOINST.
Takes SIGS list, adds MESSAGE to front and inserts each at INDENT-PT."
  (when sigs
    (insert "\n")
    (indent-to indent-pt)
    (insert message)
    (insert "\n")
    (indent-to indent-pt)
    (while sigs
      (cond ((> (+ 2 (current-column) (length (bsv-sig-name (car sigs)))) fill-column)
	     (insert "\n")
	     (indent-to indent-pt)))
      (insert (bsv-sig-name (car sigs)) ", ")
      (setq sigs (cdr sigs)))))

(defun bsv-auto-arg ()
  "Expand AUTOARG statements.
Replace the argument declarations at the beginning of the
module with ones automatically derived from input and output
statements.  This can be dangerous if the module is instantiated
using position-based connections, so use only name-based when
instantiating the resulting module.  Long lines are split based
on the `fill-column', see \\[set-fill-column].

Limitations:
   Concatenation and outputting partial busses is not supported.

For example:

	module ex_arg (/*AUTOARG*/);
	  input i;
	  output o;
	endmodule

Typing \\[bsv-auto] will make this into:

	module ex_arg (/*AUTOARG*/
	  // Outputs
	  o,
	  // Inputs
	  i
	);
	  input i;
	  output o;
	endmodule

Any ports declared between the ( and /*AUTOARG*/ are presumed to be
predeclared and are not redeclared by AUTOARG.  You need to know whether to
put a comma just before the AUTOARG or not, based upon whether there will be
ports in the AUTOARG or not; this is not determined for you.  Avoid
declaring ports manually, as it makes code harder to maintain."
  (save-excursion
    (let ((modi (bsv-modi-current))
	  (skip-pins (aref (bsv-read-arg-pins) 0))
	  (pt (point)))
      (bsv-auto-arg-ports (bsv-signals-not-in
			       (bsv-modi-get-outputs modi)
			       skip-pins)
			      "// Outputs"
			      bsv-indent-level-declaration)
      (bsv-auto-arg-ports (bsv-signals-not-in
			       (bsv-modi-get-inouts modi)
			       skip-pins)
			      "// Inouts"
			      bsv-indent-level-declaration)
      (bsv-auto-arg-ports (bsv-signals-not-in
			       (bsv-modi-get-inputs modi)
			       skip-pins)
			      "// Inputs"
			      bsv-indent-level-declaration)
      (save-excursion
	(if (re-search-backward "," pt t)
	    (delete-char 2)))
      (unless (eq (char-before) ?/ )
	(insert "\n"))
      (indent-to bsv-indent-level-declaration)
      )))

(defun bsv-auto-inst-port-map (port-st)
  nil)

(defvar vector-skip-list nil) ; Prevent compile warning
(defvar vl-cell-type nil "See bsv-auto-inst") ; Prevent compile warning
(defvar vl-cell-name nil "See bsv-auto-inst") ; Prevent compile warning

(defun bsv-auto-inst-port (port-st indent-pt tpl-list tpl-num)
  "Print out a instantiation connection for this PORT-ST.
Insert to INDENT-PT, use template TPL-LIST.
@ are instantiation numbers, replaced with TPL-NUM.
@\"(expression @)\" are evaluated, with @ as a variable."
  (let* ((port (bsv-sig-name port-st))
	 (tpl-ass (or (assoc port (car tpl-list))
		      (bsv-auto-inst-port-map port-st)))
	 ;; vl-* are documented for user use
	 (vl-name (bsv-sig-name port-st))
	 (vl-bits (if (or bsv-auto-inst-vector
			  (not (assoc port vector-skip-list))
			  (not (equal (bsv-sig-bits port-st)
				      (bsv-sig-bits (assoc port vector-skip-list)))))
		      (or (bsv-sig-bits port-st) "")
		    ""))
	 ;; Default if not found
	 (tpl-net (concat port vl-bits)))
    ;; Find template
    (cond (tpl-ass	    ; Template of exact port name
	   (setq tpl-net (nth 1 tpl-ass)))
	  ((nth 1 tpl-list) ; Wildcards in template, search them
	   (let ((wildcards (nth 1 tpl-list)))
	     (while wildcards
	       (when (string-match (nth 0 (car wildcards)) port)
		 (setq tpl-ass t  ; so allow @ parsing
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
		     value
		     ))
		 (substring tpl-net (match-end 0))))))
      ;; Replace @ and [] magic variables in final output
      (setq tpl-net (bsv-string-replace-matches "@" tpl-num nil nil tpl-net))
      (setq tpl-net (bsv-string-replace-matches "\\[\\]" vl-bits nil nil tpl-net))
      )
    (indent-to indent-pt)
    (insert "." port)
    (indent-to 40)
    (insert "(" tpl-net "),")
    (when tpl-ass
      (indent-to 64)
      (insert " // Templated"))
    (insert "\n")))
;;(bsv-auto-inst-port (list "foo" "[5:0]") 10 (list (list "foo" "a@\"(% (+ @ 1) 4)\"a")) "3")
;;(x "incom[@\"(+ (* 8 @) 7)\":@\"(* 8 @)\"]")
;;(x ".out (outgo[@\"(concat (+ (* 8 @) 7) \\\":\\\" ( * 8 @))\"]));")

(defun bsv-auto-inst ()
  "Expand AUTOINST statements, as part of \\[bsv-auto].
Replace the argument calls inside an instantiation with ones
automatically derived from the module header of the instantiated netlist.

Limitations:
  Module names must be resolvable to filenames by adding a
  bsv-library-extension, and being found in the same directory, or
  by changing the variable `bsv-library-directories' or
  `bsv-library-files'.  Macros `modname are translated through the
  vh-{name} Emacs variable, if that is not found, it just ignores the `.

  In templates you must have one signal per line, ending in a ), or ));,
  and have proper () nesting, including a final ); to end the template.

For example, first take the submodule inst.v:

	module inst (o,i)
	   output [31:0] o;
	   input i;
	   wire [31:0] o = {32{i}};
	endmodule

This is then used in a upper level module:

	module ex_inst (o,i)
	   output o;
	   input i;
	   inst inst (/*AUTOINST*/);
	endmodule

Typing \\[bsv-auto] will make this into:

	module ex_inst (o,i)
	   output o;
	   input i;
	   inst inst (/*AUTOINST*/
		      // Outputs
		      .ov			(ov[31:0]),
		      // Inputs
		      .i			(i));
	endmodule

Where the list of inputs and outputs came from the inst module.

Exceptions:

Unless you are instantiating a module multiple times, or the module is
something trivial like a adder, DO NOT CHANGE SIGNAL NAMES ACROSS HIERARCHY.
It just makes for unmaintainable code.  To sanitize signal names, try
vrename from http://www.veripool.com

When you need to violate this suggestion there are several ways to list
exceptions.

Any ports defined before the /*AUTOINST*/ are not included in the list of
automatics.  This is similar to making a template as described below, but
is restricted to simple connections just like you normally make.  Also note
that any signals before the AUTOINST will only be picked up by AUTOWIRE if
you have the appropriate // Input or // Output comment, and exactly the
same line formatting as AUTOINST itself uses.

	   inst inst (// Inputs
		      .i			(my_i_dont_mess_with_it),
		      /*AUTOINST*/
		      // Outputs
		      .ov			(ov[31:0]));


Auto Templates:

For multiple instantiations based upon a single template, create a
commented out template:
	/* psm_mas AUTO_TEMPLATE (
		.PTL_MAPVALIDX		(PTL_MAPVALID[@]),
		.PTL_MAPVALIDP1X	(PTL_MAPVALID[@\"(% (+ 1 @) 4)\"]),
		.PTL_BUS		(PTL_BUSNEW[]),
		);
	*/

Templates go ABOVE the instantiation(s).  When a instantiation is expanded
`bsv-mode' simply searches up for the closest template.  Thus you can have
multiple templates for the same module, just alternate between the template
for a instantiation and the instantiation itself.

The @ character should be replaced by the instantiation number; the first
digits found in the cell's instantiation name.  The module name must be the
same as the name of the module in the instantiation name, and the code
\"AUTO_TEMPLATE\" must be in these exact words and capitalized.  Only
signals that must be different for each instantiation need to be listed.

The above template will convert:

	psm_mas ms2m (/*AUTOINST*/);

Typing \\[bsv-auto] will make this into:

	psm_mas ms2m (/*AUTOINST*/
	    // Outputs
	    .INSTDATAOUT		(INSTDATAOUT),
	    .PTL_MAPVALIDX		(PTL_MAPVALID[2]),
	    .PTL_MAPVALIDP1X		(PTL_MAPVALID[3]),
  	    .PTL_BUS			(PTL_BUSNEW[3:0]),
	    ....

Note the @ character was replaced with the 2 from \"ms2m\".  Also, if a
signal wasn't in the template, it is assumed to be a direct connection.

A [] in a template (with nothing else inside the brackets) will be replaced
by the same bus subscript as it is being connected to, or \"\" (nothing) if
it is a single bit signal.  See PTL_BUS becoming PTL_BUSNEW above.

Regexp templates:

  A template entry of the form
	    .pci_req\\([0-9]+\\)_l	(pci_req_jtag_[\\1]),

  will apply a Emacs style regular expression search for any port beginning
  in pci_req followed by numbers and ending in _l and connecting that to
  the pci_req_jtag_[] net, with the bus subscript coming from what matches
  inside the first set of \\( \\).  Thus pci_req2_l becomes pci_req_jtag_[2].

  Since \\([0-9]+\\) is so common and ugly to read, a @ does the same thing
  (Note a @ in replacement text is completely different -- still use \\1
  there!)  Thus this is the same as the above template:

	    .pci_req@_l		(pci_req_jtag_[\\1]),

  Here's another example to remove the _l, if naming conventions specify _
  alone to mean active low.  Note the use of [] to keep the bus subscript:
	    .\\(.*\\)_l		(\\1_[]),

Lisp templates:

  First any regular expression template is expanded.

  If the syntax @\"( ... )\" is found, the expression in quotes will be
  evaluated as a Lisp expression, with @ replaced by the instantiation
  number.  The MAPVALIDP1X example above would put @+1 modulo 4 into the
  brackets.  Quote all double-quotes inside the expression with a leading
  backslash (\\\").  There are special variables defined that are useful
  in these Lisp functions:
	vl-name        Name portion of the input/output port
	vl-bits        Bus bits portion of the input/output port ('[2:0]')
	vl-cell-type   Module name/type of the cell ('psm_mas')
	vl-cell-name   Instance name of the cell ('ms2m')

  Normal Lisp variables may be used in expressions.  See
  `bsv-read-defines' which can set vh-{definename} variables for use
  here.  Also, any comments of the form:

	/*AUTO_LISP(setq foo 1)*/

  will evaluate any Lisp expression inside the parenthesis between the
  beginning of the buffer and the point of the AUTOINST.  This allows
  variables to be changed between each instantiation.

  After the evaluation is completed, @ substitution and [] substitution
  occur."
  (save-excursion
    ;; Find beginning
    (let* ((pt (point))
	   (indent-pt (save-excursion (bsv-backward-open-paren)
				      (1+ (current-column))))
	   (modi (bsv-modi-current))
	   (vector-skip-list (unless bsv-auto-inst-vector
			       (bsv-modi-get-signals modi)))
	   submod submodi inst skip-pins tpl-list tpl-num)
      ;; Find module name that is instantiated
      (setq submod  (bsv-read-inst-module)
	    inst (bsv-read-inst-name)
	    vl-cell-type submod
	    vl-cell-name inst
	    skip-pins (aref (bsv-read-inst-pins) 0))

      ;; Parse any AUTO_LISP() before here
      (bsv-read-auto-lisp (point-min) pt)

      ;; Lookup position, etc of submodule
      ;; Note this may raise an error
      (when (setq submodi (bsv-modi-lookup submod t))
	;; If there's a number in the instantiation, it may be a argument to the
	;; automatic variable instantiation program.
	(setq tpl-num (if (string-match "\\([0-9]+\\)" inst)
			  (substring inst (match-beginning 1) (match-end 1))
			"")
	      tpl-list (bsv-read-auto-template submod))
	;; Find submodule's signals and dump
	(insert "\n")
	(let ((sig-list (bsv-signals-not-in
			 (bsv-modi-get-outputs submodi)
			 skip-pins)))
	  (when sig-list
	    (indent-to indent-pt)
	    (insert "// Outputs\n")	;; Note these are searched for in bsv-read-sub-decl
	    (mapcar (function (lambda (port)
				(bsv-auto-inst-port port indent-pt tpl-list tpl-num)))
		    sig-list)))
	(let ((sig-list (bsv-signals-not-in
			 (bsv-modi-get-inouts submodi)
			 skip-pins)))
	  (when sig-list
	    (indent-to indent-pt)
	    (insert "// Inouts\n")
	    (mapcar (function (lambda (port)
				(bsv-auto-inst-port port indent-pt tpl-list tpl-num)))
		    sig-list)))
	(let ((sig-list (bsv-signals-not-in
			 (bsv-modi-get-inputs submodi)
			 skip-pins)))
	  (when sig-list
	    (indent-to indent-pt)
	    (insert "// Inputs\n")
	    (mapcar (function (lambda (port)
				(bsv-auto-inst-port port indent-pt tpl-list tpl-num)))
		    sig-list)))
	;; Kill extra semi
	(save-excursion
	  (cond ((re-search-backward "," pt t)
		 (delete-char 1)
		 (insert ");")
		 (search-forward "\n")	;; Added by inst-port
		 (delete-backward-char 1)
		 (if (search-forward ")" nil t) ;; From user, moved up a line
		     (delete-backward-char 1))
		 (if (search-forward ";" nil t) ;; Don't error if user had syntax error and forgot it
		     (delete-backward-char 1))
		 )
		(t
		 (delete-backward-char 1)	;; Newline Inserted above
		 )))
	))))

(defun bsv-auto-reg ()
  "Expand AUTOREG statements, as part of \\[bsv-auto].
Make reg statements for any output that isn't already declared,
and isn't a wire output from a block.

Limitations:
  This ONLY detects outputs of AUTOINSTants (see bsv-read-sub-decl).
  This does NOT work on memories, declare those yourself.

A simple example:

	module ex_reg (o,i)
	   output o;
	   input i;
	   /*AUTOREG*/
	   always o = i;
	endmodule

Typing \\[bsv-auto] will make this into:

	module ex_reg (o,i)
	   output o;
	   input i;
	   /*AUTOREG*/
	   // Beginning of automatic regs (for this module's undeclared outputs)
	   reg			o;
	   // End of automatics
	   always o = i;
	endmodule"
  (save-excursion
    ;; Point must be at insertion point.
    (let* ((indent-pt (current-indentation))
	   (modi (bsv-modi-current))
	   (sig-list (bsv-signals-not-in
		      (bsv-modi-get-outputs modi)
		      (append (bsv-modi-get-wires modi)
			      (bsv-modi-get-regs modi)
			      (bsv-modi-get-assigns modi)
			      (bsv-modi-get-consts modi)
			      (bsv-modi-get-sub-outputs modi)
			      (bsv-modi-get-sub-inouts modi)
			      ))))
      (forward-line 1)
      (bsv-insert-indent "// Beginning of automatic regs (for this module's undeclared outputs)\n")
      (bsv-insert-definition sig-list "reg" indent-pt)
      (bsv-modi-cache-add-regs modi sig-list)
      (bsv-insert-indent "// End of automatics\n")
      )))

(defun bsv-auto-reg-input ()
  "Expand AUTOREGINPUT statements, as part of \\[bsv-auto].
Make reg statements instantiation inputs that aren't already declared.
This is useful for making a top level shell for testing the module that is
to be instantiated.

Limitations:
  This ONLY detects inputs of AUTOINSTants (see bsv-read-sub-decl).
  This does NOT work on memories, declare those yourself.

A simple example (see `bsv-auto-inst' for what else is going on here):

	module ex_reg_input (o,i)
	   output o;
	   input i;
	   /*AUTOREGINPUT*/
           inst inst (/*AUTOINST*/);
	endmodule

Typing \\[bsv-auto] will make this into:

	module ex_reg_input (o,i)
	   output o;
	   input i;
	   /*AUTOREGINPUT*/
	   // Beginning of automatic reg inputs (for undeclared ...
	   reg [31:0]		iv;		// From inst of inst.v
	   // End of automatics
	   inst inst (/*AUTOINST*/
		      // Outputs
		      .o			(o[31:0]),
		      // Inputs
		      .iv			(iv));
	endmodule"
  (save-excursion
    ;; Point must be at insertion point.
    (let* ((indent-pt (current-indentation))
	   (modi (bsv-modi-current))
	   (sig-list (bsv-signals-combine-bus
		      (bsv-signals-not-in
		       (append (bsv-modi-get-sub-inputs modi)
			       (bsv-modi-get-sub-inouts modi))
		       (bsv-modi-get-signals modi)
		       ))))
      (forward-line 1)
      (bsv-insert-indent "// Beginning of automatic reg inputs (for undeclared instantiated-module inputs)\n")
      (bsv-insert-definition sig-list "reg" indent-pt)
      (bsv-modi-cache-add-wires modi sig-list)
      (bsv-insert-indent "// End of automatics\n")
      )))

(defun bsv-auto-wire ()
  "Expand AUTOWIRE statements, as part of \\[bsv-auto].
Make wire statements for instantiations outputs that aren't
already declared.

Limitations:
  This ONLY detects outputs of AUTOINSTants (see bsv-read-sub-decl).
  This does NOT work on memories, declare those yourself.

A simple example (see `bsv-auto-inst' for what else is going on here):

	module ex_wire (o,i)
	   output o;
	   input i;
	   /*AUTOWIRE*/
           inst inst (/*AUTOINST*/);
	endmodule

Typing \\[bsv-auto] will make this into:

	module ex_wire (o,i)
	   output o;
	   input i;
	   /*AUTOWIRE*/
	   // Beginning of automatic wires
	   wire [31:0]		ov;	// From inst of inst.v
	   // End of automatics
	   inst inst (/*AUTOINST*/
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
	   (sig-list (bsv-signals-combine-bus
		      (bsv-signals-not-in
		       (append (bsv-modi-get-sub-outputs modi)
			       (bsv-modi-get-sub-inouts modi))
		       (bsv-modi-get-signals modi)
		       ))))
      (forward-line 1)
      (bsv-insert-indent "// Beginning of automatic wires (for undeclared instantiated-module outputs)\n")
      (bsv-insert-definition sig-list "wire" indent-pt)
      (bsv-modi-cache-add-wires modi sig-list)
      (bsv-insert-indent "// End of automatics\n")
      (when nil	;; Too slow on huge modules, plus makes everyone's module change
	(beginning-of-line)
	(setq pnt (point))
	(bsv-pretty-declarations)
	(goto-char pnt)
	(bsv-pretty-expr "//"))
      )))

(defun bsv-auto-output ()
  "Expand AUTOOUTPUT statements, as part of \\[bsv-auto].
Make output statements for any output signal from an /*AUTOINST*/ that
isn't used elsewhere inside the module.  This is useful for modules which
only instantiate other modules.

Limitations:
  This ONLY detects outputs of AUTOINSTants (see bsv-read-sub-decl).

  If any concatenation, or bit-subscripts are missing in the AUTOINSTant's
  instantiation, all bets are off.  (For example due to a AUTO_TEMPLATE).

A simple example (see `bsv-auto-inst' for what else is going on here):

	module ex_output (ov,i)
	   input i;
	   /*AUTOWIRE*/
	   inst inst (/*AUTOINST*/);
	endmodule

Typing \\[bsv-auto] will make this into:

	module ex_output (ov,i)
	   input i;
	   /*AUTOOUTPUT*/
	   // Beginning of automatic outputs (from unused autoinst outputs)
	   output [31:0]	ov;			// From inst of inst.v
	   // End of automatics
	   inst inst (/*AUTOINST*/
		      // Outputs
		      .ov			(ov[31:0]),
		      // Inputs
		      .i			(i));
	endmodule"
  (save-excursion
    ;; Point must be at insertion point.
    (let* ((indent-pt (current-indentation))
	   (modi (bsv-modi-current))
	   (sig-list (bsv-signals-not-in
		      (bsv-modi-get-sub-outputs modi)
		      (append (bsv-modi-get-outputs modi)
			      (bsv-modi-get-inouts modi)
			      (bsv-modi-get-sub-inputs modi)
			      (bsv-modi-get-sub-inouts modi)
			      ))))
      (forward-line 1)
      (bsv-insert-indent "// Beginning of automatic outputs (from unused autoinst outputs)\n")
      (bsv-insert-definition sig-list "output" indent-pt)
      (bsv-modi-cache-add-outputs modi sig-list)
      (bsv-insert-indent "// End of automatics\n")
      )))

(defun bsv-auto-output-every ()
  "Expand AUTOOUTPUTEVERY statements, as part of \\[bsv-auto].
Make output statements for any signals that aren't primary inputs or
outputs already.  This makes every signal in the design a output.  This is
useful to get Synopsys to preserve every signal in the design, since it
won't optimize away the outputs.

A simple example:

	module ex_output_every (o,i,tempa,tempb)
	   output o;
	   input i;
	   /*AUTOOUTPUTEVERY*/
	   wire tempa = i;
	   wire tempb = tempa;
	   wire o = tempb;
	endmodule

Typing \\[bsv-auto] will make this into:

	module ex_output_every (o,i,tempa,tempb)
	   output o;
	   input i;
	   /*AUTOOUTPUTEVERY*/
	   // Beginning of automatic outputs (every signal)
	   output		tempb;
	   output		tempa;
	   // End of automatics
	   wire tempa = i;
	   wire tempb = tempa;
	   wire o = tempb;
	endmodule"
  (save-excursion
    ;;Point must be at insertion point
    (let* ((indent-pt (current-indentation))
	   (modi (bsv-modi-current))
	   (sig-list (bsv-signals-combine-bus
		      (bsv-signals-not-in
		       (bsv-modi-get-signals modi)
		       (bsv-modi-get-ports modi)
		       ))))
      (forward-line 1)
      (bsv-insert-indent "// Beginning of automatic outputs (every signal)\n")
      (bsv-insert-definition sig-list "output" indent-pt)
      (bsv-modi-cache-add-outputs modi sig-list)
      (bsv-insert-indent "// End of automatics\n")
      )))

(defun bsv-auto-input ()
  "Expand AUTOINPUT statements, as part of \\[bsv-auto].
Make input statements for any input signal into an /*AUTOINST*/ that
isn't declared elsewhere inside the module.  This is useful for modules which
only instantiate other modules.

Limitations:
  This ONLY detects outputs of AUTOINSTants (see bsv-read-sub-decl).

  If any concatenation, or bit-subscripts are missing in the AUTOINSTant's
  instantiation, all bets are off.  (For example due to a AUTO_TEMPLATE).

A simple example (see `bsv-auto-inst' for what else is going on here):

	module ex_input (ov,i)
	   output [31:0] ov;
	   /*AUTOINPUT*/
	   inst inst (/*AUTOINST*/);
	endmodule

Typing \\[bsv-auto] will make this into:

	module ex_input (ov,i)
	   output [31:0] ov;
	   /*AUTOINPUT*/
	   // Beginning of automatic inputs (from unused autoinst inputs)
	   input		i;			// From inst of inst.v
	   // End of automatics
	   inst inst (/*AUTOINST*/
		      // Outputs
		      .ov			(ov[31:0]),
		      // Inputs
		      .i			(i));
	endmodule"
  (save-excursion
    (let* ((indent-pt (current-indentation))
	   (modi (bsv-modi-current))
	   (sig-list (bsv-signals-not-in
		      (bsv-modi-get-sub-inputs modi)
		      (append (bsv-modi-get-inputs modi)
			      (bsv-modi-get-inouts modi)
			      (bsv-modi-get-wires modi)
			      (bsv-modi-get-regs modi)
			      (bsv-modi-get-consts modi)
			      (bsv-modi-get-sub-outputs modi)
			      (bsv-modi-get-sub-inouts modi)
			      ))))
      (forward-line 1)
      (bsv-insert-indent "// Beginning of automatic inputs (from unused autoinst inputs)\n")
      (bsv-insert-definition sig-list "input" indent-pt)
      (bsv-modi-cache-add-inputs modi sig-list)
      (bsv-insert-indent "// End of automatics\n")
      )))

(defun bsv-auto-inout-module ()
  "Expand AUTOINOUTMODULE statements, as part of \\[bsv-auto].
Take input/output/inout statements from the specified module and insert
into the current module.  This is useful for making null templates and
shell modules which need to have identical I/O with another module.  Any
I/O which are already defined in this module will not be redefined.

Limitations:
  Concatenation and outputting partial busses is not supported.
  Module names must be resolvable to filenames.  See \\[bsv-auto-inst].
  Signals are not inserted in the same order as in the original module,
  though they will appear to be in the same order to a AUTOINST
  instantiating either module.

A simple example:

	module ex_shell (/*AUTOARG*/)
	   /*AUTOINOUTMODULE(\"ex_main\")*/
	endmodule

	module ex_main (i,o,io)
          input i;
          output o;
          inout io;
        endmodule

Typing \\[bsv-auto] will make this into:

	module ex_shell (/*AUTOARG*/i,o,io)
	   /*AUTOINOUTMODULE(\"ex_main\")*/
           // Beginning of automatic in/out/inouts (from specific module)
           input i;
           output o;
           inout io;
	   // End of automatics
	endmodule"
  (save-excursion
    (let* ((submod (car (bsv-read-auto-params 1))) submodi)
      ;; Lookup position, etc of co-module
      ;; Note this may raise an error
      (when (setq submodi (bsv-modi-lookup submod t))
	(let* ((indent-pt (current-indentation))
	       (modi (bsv-modi-current))
	       (sig-list-i  (bsv-signals-not-in
			     (bsv-modi-get-inputs submodi)
			     (append (bsv-modi-get-inputs modi))))
	       (sig-list-o  (bsv-signals-not-in
			     (bsv-modi-get-outputs submodi)
			     (append (bsv-modi-get-outputs modi))))
	       (sig-list-io (bsv-signals-not-in
			     (bsv-modi-get-inouts submodi)
			     (append (bsv-modi-get-inouts modi)))))
	  (forward-line 1)
	  (bsv-insert-indent "// Beginning of automatic in/out/inouts (from specific module)\n")
	  ;; Don't sort them so a upper AUTOINST will match the main module
	  (bsv-insert-definition sig-list-o  "output" indent-pt t)
	  (bsv-insert-definition sig-list-io "inout" indent-pt t)
	  (bsv-insert-definition sig-list-i  "input" indent-pt t)
	  (bsv-modi-cache-add-inputs modi sig-list-i)
	  (bsv-modi-cache-add-outputs modi sig-list-o)
	  (bsv-modi-cache-add-inouts modi sig-list-io)
	  (bsv-insert-indent "// End of automatics\n")
	  )))))

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

A simple example:

	   always @ (/*AUTOSENSE*/) begin
	      /* AUTO_CONSTANT (`constant) */
	      outin = ina | inb | `constant;
	      out = outin;
	   end

Typing \\[bsv-auto] will make this into:

	   always @ (/*AUTOSENSE*/ina or inb) begin
	      /* AUTO_CONSTANT (`constant) */
	      outin = ina | inb | `constant;
	      out = outin;
	   end"
  (save-excursion
    ;; Find beginning
    (let* ((start-pt (save-excursion
		       (bsv-re-search-backward "(" nil t)
		       (point)))
	   (indent-pt (save-excursion
			(or (and (goto-char start-pt) (1+ (current-column)))
			    (current-indentation))))
	   (modi (bsv-modi-current))
	   (sig-memories (bsv-signals-memory (bsv-modi-get-regs modi)))
	   sigss sig-list not-first presense-sigs)
      ;; Read signals in always, eliminate outputs from sense list
      (setq presense-sigs (bsv-signals-from-signame
			   (save-excursion
			     (bsv-read-signals start-pt (point)))))
      (setq sigss (bsv-read-always-signals))
      (setq sig-list (bsv-signals-not-params
		      (bsv-signals-not-in (bsv-alw-get-inputs sigss)
					      (append (and (not bsv-auto-sense-include-inputs)
							   (bsv-alw-get-outputs sigss))
						      (bsv-modi-get-consts modi)
						      presense-sigs)
					      )))
      (when sig-memories
	(let ((tlen (length sig-list)))
	  (setq sig-list (bsv-signals-not-in sig-list sig-memories))
	  (if (not (eq tlen (length sig-list))) (insert " /*memory or*/ "))))
      (if (and presense-sigs  ;; Add a "or" if not "(.... or /*AUTOSENSE*/"
	       (save-excursion (goto-char (point))
			       (bsv-re-search-backward "[a-zA-Z0-9`_\$]+" start-pt t)
			       (bsv-re-search-backward "\\s-" start-pt t)
			       (while (looking-at "\\s-`endif")
				 (bsv-re-search-backward "[a-zA-Z0-9`_\$]+" start-pt t)
				 (bsv-re-search-backward "\\s-" start-pt t))
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
	      not-first t))
      )))

(defun bsv-auto-reset ()
  "Expand AUTORESET statements, as part of \\[bsv-auto].  
Replace the /*AUTORESET*/ comment with code to initialize all
registers set elsewhere in the always block.

Limitations:
  AUTORESET will not clear memories.
  AUTORESET uses <= if there are any <= in the block, else it uses =.

/*AUTORESET*/ presumes that any signals mentioned between the previous
begin/case/if statement and the AUTORESET comment are being reset manually
and should not be automatically reset.  This includes ommitting any signals
used on the right hand side of assignments.

A simple example:

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
            b <= 0;
            // End of automatics
        end
        else begin
            a <= in_a;
            b <= in_b;
            c <= in_c;
        end
    end"

  (interactive)
  (save-excursion
    ;; Find beginning
    (let* ((indent-pt (current-indentation))
	   (modi (bsv-modi-current))
	   (all-list (bsv-modi-get-signals modi))
	   sigss sig-list prereset-sigs assignment-str)
      ;; Read signals in always, eliminate outputs from reset list
      (setq prereset-sigs (bsv-signals-from-signame
			   (save-excursion
			     (bsv-read-signals
			      (save-excursion
				(bsv-re-search-backward "\\(@\\|\\<begin\\>\\|\\<if\\>\\|\\<case\\>\\)" nil t)
				(point))
			      (point)))))
      (save-excursion
	(bsv-re-search-backward "@" nil t)
        (setq sigss (bsv-read-always-signals)))
      (setq assignment-str (if (bsv-alw-get-uses-delayed sigss)
			       (concat " <= " bsv-assignment-delay)
			     " = "))
      (setq sig-list (bsv-signals-not-in (bsv-alw-get-outputs sigss)
					     prereset-sigs))
      (setq sig-list (sort sig-list `bsv-signals-sort-compare))
      (insert "\n");
      (indent-to indent-pt)
      (insert "// Beginning of autoreset for uninitialized flops\n");
      (indent-to indent-pt)
      (while sig-list
	(let* ((defn-sig (if bsv-auto-reset-widths
			     (assoc (bsv-sig-name (car sig-list)) all-list)))
	       (width (if defn-sig (bsv-sig-width defn-sig))))
	  (insert (bsv-sig-name (car sig-list)))
	  (cond ((not width)
		 (insert assignment-str "0;\n"))
		((string-match "^[0-9]+$" width)
		 (insert assignment-str (bsv-sig-width defn-sig) "'h0;\n" ))
		(t
		 (insert assignment-str "{" (bsv-sig-width defn-sig) "{1'b0}};\n" )))
	  (indent-to indent-pt)
	  (setq sig-list (cdr sig-list))))
      (insert "// End of automatics")
      )))

(defun bsv-enum-ascii (signm elim-regexp)
  "Convert a enum name SIGNM to a ascii string for insertion.
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
  (Annoying, but that's what Synopsys's dc_shell FSM reader requires.)

Next, registers which that enum applies to are also tagged with the same
  enum.  Synopsys also suggests labeling state vectors, but `bsv-mode'
  doesn't care.

Finally, a AUTOASCIIENUM command is used.
  The first parameter is the name of the signal to be decoded.

  The second parameter is the name to store the ASCII code into.  For the
  signal foo, I suggest the name _foo__ascii, where the leading _ indicates
  a signal that is just for simulation, and the magic characters _ascii
  tell viewers like Dinotrace to display in ASCII format.

  The final optional parameter is a string which will be removed from the
  state names.


A simple example:

   //== State enumeration
   parameter [2:0] // synopsys enum state_info
		   SM_IDLE =  3'b000,
		   SM_SEND =  3'b001,
		   SM_WAIT1 = 3'b010;
   //== State variables
   reg [2:0]	/* synopsys enum state_info */
		state_r;		/* synopsys state_vector state_r */
   reg [2:0]	/* synopsys enum state_info */
		state_e1;

   //== ASCII state decoding

   /*AUTOASCIIENUM(\"state_r\", \"_stateascii_r\", \"sm_\")*/

Typing \\[bsv-auto] will make this into:

   ... same front matter ...

   /*AUTOASCIIENUM(\"state_r\", \"_stateascii_r\", \"sm_\")*/
   // Beginning of automatic ASCII enum decoding
   reg [39:0]		_stateascii_r;		// Decode of state_r
   always @(state_r) begin
      case ({state_r})
	SM_IDLE:  _stateascii_r = \"idle \";
	SM_SEND:  _stateascii_r = \"send \";
	SM_WAIT1: _stateascii_r = \"wait1\";
	default:  _stateascii_r = \"%Erro\";
      endcase
   end
   // End of automatics"
  (save-excursion
    (let* ((params (bsv-read-auto-params 2 3))
	   (undecode-name (nth 0 params))
	   (ascii-name (nth 1 params))
	   (elim-regexp (nth 2 params))
	   ;;
	   (indent-pt (current-indentation))
	   (modi (bsv-modi-current))
	   ;;
	   (sig-list-consts (bsv-modi-get-consts modi))
	   (sig-list-all  (append (bsv-modi-get-regs modi)
				  (bsv-modi-get-outputs modi)
				  (bsv-modi-get-inouts modi)
				  (bsv-modi-get-inputs modi)
				  (bsv-modi-get-wires modi)))
	   ;;
	   (undecode-sig (or (assoc undecode-name sig-list-all)
			     (error "%s: Signal %s not found in design" (bsv-point-text) undecode-name)))
	   (undecode-enum (or (bsv-sig-enum undecode-sig)
			      (error "%s: Signal %s does not have a enum tag" (bsv-point-text) undecode-name)))
	   ;;
	   (enum-sigs (or (bsv-signals-matching-enum sig-list-consts undecode-enum)
			  (error "%s: No state definitions for %s" (bsv-point-text) undecode-enum)))
	   ;;
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
	(bsv-insert-definition decode-sig-list "reg" indent-pt)
	(bsv-modi-cache-add-regs modi decode-sig-list))
      ;;
      (bsv-insert-indent "always @(" undecode-name ") begin\n")
      (setq indent-pt (+ indent-pt bsv-indent-level))
      (indent-to indent-pt)
      (insert "case ({" undecode-name "})\n")
      (setq indent-pt (+ indent-pt bsv-case-indent))
      ;;
      (let ((tmp-sigs enum-sigs)
	    (chrfmt (format "%%-%ds %s = \"%%-%ds\";\n" (1+ (max 8 enum-chars))
			    ascii-name ascii-chars))
	    (errname (substring "%Error" 0 (min 6 ascii-chars))))
	(while tmp-sigs
	  (bsv-insert-indent
	   (format chrfmt (concat (bsv-sig-name (car tmp-sigs)) ":")
		   (bsv-enum-ascii (bsv-sig-name (car tmp-sigs))
				       elim-regexp)))
	  (setq tmp-sigs (cdr tmp-sigs)))
	(bsv-insert-indent (format chrfmt "default:" errname)))
      ;;
      (setq indent-pt (- indent-pt bsv-case-indent))
      (bsv-insert-indent "endcase\n")
      (setq indent-pt (- indent-pt bsv-indent-level))
      (bsv-insert-indent "end\n"
			     "// End of automatics\n")
      )))


;;
;; Auto top level
;;

(defun bsv-auto ()
  "Expand AUTO statements.
Look for any /*AUTO...*/ commands in the code, as used in
instantiations or argument headers.  Update the list of signals
following the /*AUTO...*/ command.

Use \\[bsv-delete-auto] to remove the AUTOs.

The hooks `bsv-before-auto-hook' and `bsv-auto-hook' are
called before and after this function, respectively.

For example:
	module (/*AUTOARG*/)
	/*AUTOINPUT*/
	/*AUTOOUTPUT*/
	/*AUTOWIRE*/
	/*AUTOREG*/
	somesub sub (/*AUTOINST*/);

You can also update the AUTOs from the shell using:
	emacs --batch $FILENAME_V -f bsv-auto -f save-buffer

Using \\[describe-function], see also:
   `bsv-auto-arg'          for AUTOARG module instantiations
   `bsv-auto-ascii-enum'   for AUTOASCIIENUM enumeration decoding
   `bsv-auto-inout-module' for AUTOINOUTMODULE copying i/o from elsewhere
   `bsv-auto-input'        for AUTOINPUT making hierarchy inputs
   `bsv-auto-inst'         for AUTOINST argument declarations
   `bsv-auto-output'       for AUTOOUTPUT making hierarchy outputs
   `bsv-auto-output-every' for AUTOOUTPUTEVERY making all outputs
   `bsv-auto-reg'          for AUTOREG registers
   `bsv-auto-reg-input'    for AUTOREGINPUT instantiation registers
   `bsv-auto-reset'        for AUTORESET flop resets
   `bsv-auto-sense'        for AUTOSENSE always sensitivity lists
   `bsv-auto-wire'         for AUTOWIRE instantiation wires

   `bsv-read-defines'      for reading `define values
   `bsv-read-includes'     for reading `includes

If you have bugs with these autos, try contacting the AUTOAUTHOR
Wilson Snyder (wsnyder@wsnyder.org or wsnyder@world.std.com)"
  (interactive)
  (unless noninteractive (message "Updating AUTOs..."))
  (if (featurep 'dinotrace)
      (dinotrace-unannotate-all))
  (let ((oldbuf (if (not (buffer-modified-p))
		    (buffer-string)))
	;; Before version 20, match-string with font-lock returns a
	;; vector that is not equal to the string.  IE if on "input"
	;; nil==(equal "input" (progn (looking-at "input") (match-string 0)))
	(fontlocked (when (and ;(memq 'v19 bsv-emacs-features)
			       (boundp 'font-lock-mode)
			       font-lock-mode)
		      (font-lock-mode nil)
		      t)))
    (save-excursion
      (run-hooks 'bsv-before-auto-hook)
      ;; Try to save the user from needing to revert-file to reread file local-variables
      (bsv-auto-reeval-locals)
      ;; These two may seem obvious to do always, but on large includes it can be way too slow
      (when bsv-auto-read-includes
	(bsv-read-includes)
	(bsv-read-defines))
      ;; This particular ordering is important
      ;; INST: Lower modules correct, no internal dependencies, FIRST
      (bsv-preserve-cache
       ;; Clear existing autos else we'll be screwed by existing ones
       (bsv-delete-auto)
       ;;
       (bsv-auto-search-do "/*AUTOINST*/" 'bsv-auto-inst)
       ;; Doesn't matter when done, but combine it with a common changer
       (bsv-auto-re-search-do "/\\*\\(AUTOSENSE\\|AS\\)\\*/" 'bsv-auto-sense)
       (bsv-auto-re-search-do "/\\*AUTORESET\\*/" 'bsv-auto-reset)
       ;; Must be done before autoin/out as creates a reg
       (bsv-auto-re-search-do "/\\*AUTOASCIIENUM([^)]*)\\*/" 'bsv-auto-ascii-enum)
       ;;
       ;; first in/outs from other files
       (bsv-auto-re-search-do "/\\*AUTOINOUTMODULE([^)]*)\\*/" 'bsv-auto-inout-module)
       ;; next in/outs which need previous sucked inputs first
       (bsv-auto-search-do "/*AUTOOUTPUT*/" 'bsv-auto-output)
       (bsv-auto-search-do "/*AUTOINPUT*/" 'bsv-auto-input)
       ;; Wires/regs must be after inputs/outputs
       (bsv-auto-search-do "/*AUTOWIRE*/" 'bsv-auto-wire)
       (bsv-auto-search-do "/*AUTOREG*/" 'bsv-auto-reg)
       (bsv-auto-search-do "/*AUTOREGINPUT*/" 'bsv-auto-reg-input)
       ;; outputevery needs autooutputs done first
       (bsv-auto-search-do "/*AUTOOUTPUTEVERY*/" 'bsv-auto-output-every)
       ;; Must be after all inputs outputs are generated
       (bsv-auto-search-do "/*AUTOARG*/" 'bsv-auto-arg)
       )
      ;;
      (run-hooks 'bsv-auto-hook)
      ;;
      (set (make-local-variable 'bsv-auto-update-tick) (buffer-modified-tick))
      ;;
      ;; If end result is same as when started, clear modified flag
      (cond ((and oldbuf (equal oldbuf (buffer-string)))
	     (set-buffer-modified-p nil)
	     (unless noninteractive (message "Updating AUTOs...done (no changes)")))
	    (t (unless noninteractive (message "Updating AUTOs...done"))))
      ;; Restore font-lock
      (when fontlocked (font-lock-mode t))
      )))


;; 
;; Skeleton based code insertion
;;
(defvar bsv-template-map nil
  "Keymap used in BSV mode for smart template operations.")

(let ((bsv-mp (make-sparse-keymap)))
  (define-key bsv-mp "a" 'bsv-sk-always)
  (define-key bsv-mp "b" 'bsv-sk-begin)
  (define-key bsv-mp "c" 'bsv-sk-case)
  (define-key bsv-mp "e" 'bsv-sk-else)
  (define-key bsv-mp "f" 'bsv-sk-for)
  (define-key bsv-mp "g" 'bsv-sk-generate)
  (define-key bsv-mp "h" 'bsv-sk-header)
  (define-key bsv-mp "i" 'bsv-sk-initial)
  (define-key bsv-mp "j" 'bsv-sk-fork)
  (define-key bsv-mp "m" 'bsv-sk-module)
  (define-key bsv-mp "p" 'bsv-sk-primitive)
  (define-key bsv-mp "r" 'bsv-sk-repeat)
  (define-key bsv-mp "s" 'bsv-sk-specify)
  (define-key bsv-mp "t" 'bsv-sk-task)
  (define-key bsv-mp "w" 'bsv-sk-while)
  (define-key bsv-mp "x" 'bsv-sk-casex)
  (define-key bsv-mp "z" 'bsv-sk-casez)
  (define-key bsv-mp "?" 'bsv-sk-if)
  (define-key bsv-mp ":" 'bsv-sk-else-if)
  (define-key bsv-mp "/" 'bsv-sk-comment)
  (define-key bsv-mp "A" 'bsv-sk-assign)
  (define-key bsv-mp "F" 'bsv-sk-function)
  (define-key bsv-mp "I" 'bsv-sk-input)
  (define-key bsv-mp "O" 'bsv-sk-output)
  (define-key bsv-mp "S" 'bsv-sk-state-machine)
  (define-key bsv-mp "=" 'bsv-sk-inout)
  (define-key bsv-mp "W" 'bsv-sk-wire)
  (define-key bsv-mp "R" 'bsv-sk-reg)
  (setq bsv-template-map bsv-mp))

;;
;; Place the templates into BSV Mode.  They may be inserted under any key.
;; C-c C-t will be the default.  If you use templates a lot, you
;; may want to consider moving the binding to another key in your .emacs
;; file.
;;
;(define-key bsv-mode-map "\C-ct" bsv-template-map)
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
  (setq bsv-sk-reset (read-input "name of reset: " "rst")))


(define-skeleton bsv-sk-prompt-state-selector
  "Prompt for the name of a state machine selector."
  "name of selector (eg {a,b,c,d}): " str )

(define-skeleton bsv-sk-prompt-output
  "Prompt for the name of something."
  "output: " str)

(define-skeleton bsv-sk-prompt-msb
  "Prompt for least signifcant bit specification."
  "msb:" str & ?: & (bsv-sk-prompt-lsb) | -1 )

(define-skeleton bsv-sk-prompt-lsb
  "Prompt for least signifcant bit specification."
  "lsb:" str )

(defvar bsv-sk-p nil)
(define-skeleton bsv-sk-prompt-width
  "Prompt for a width specification."
  ()
  (progn (setq bsv-sk-p (point)) nil)
  (bsv-sk-prompt-msb)
  (if (> (point) bsv-sk-p) "] " " "))

(defun bsv-sk-header ()
  "Insert a descriptive header at the top of the file."
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
  "\n// Last Modified By: ."
  "\n// Last Modified On: ."
  "\n// Update Count    : 0"
  "\n// Status          : Unknown, Use with caution!"
  "\n")

(define-skeleton bsv-sk-module
  "Insert a module definition."
  ()
  > "module " (bsv-sk-prompt-name) " (/*AUTOARG*/ ) ;" \n
  > _ \n
  > (- bsv-indent-level-behavioral) "endmodule" (progn (bsv-electric-terminate-line) nil))

(define-skeleton bsv-sk-primitive
  "Insert a task definition."
  ()
  > "primitive " (bsv-sk-prompt-name) " ( " (bsv-sk-prompt-output) ("input:" ", " str ) " );"\n
  > _ \n
  > (- bsv-indent-level-behavioral) "endprimitive" (progn (bsv-electric-terminate-line) nil))

(define-skeleton bsv-sk-task
  "Insert a task definition."
  ()
  > "task " (bsv-sk-prompt-name) & ?; \n
  > _ \n
  > "begin" \n
  > \n
  > (- bsv-indent-level-behavioral) "end" \n
  > (- bsv-indent-level-behavioral) "endtask" (progn (bsv-electric-terminate-line) nil))

(define-skeleton bsv-sk-function
  "Insert a function definition."
  ()
  > "function [" (bsv-sk-prompt-width) | -1 (bsv-sk-prompt-name) ?; \n
  > _ \n
  > "begin" \n
  > \n
  > (- bsv-indent-level-behavioral) "end" \n
  > (- bsv-indent-level-behavioral) "endfunction" (progn (bsv-electric-terminate-line) nil))

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
  "Insert begin end block.  Uses the minibuffer to prompt for name"
  ()
  > "begin" (bsv-sk-prompt-name) \n
  > _ \n
  > (- bsv-indent-level-behavioral) "end"
)

(define-skeleton bsv-sk-fork
  "Insert an fork join block."
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
  > ("case selector: " str ": begin" \n > _ \n > (- bsv-indent-level-behavioral) "end" \n )
  resume: >  (- bsv-case-indent) "endcase" (progn (bsv-electric-terminate-line) nil))

(define-skeleton bsv-sk-casex
  "Build skeleton casex statement, prompting for the selector expression,
and the case items."
  "[selector expression]: "
  > "casex (" str ") " \n
  > ("case selector: " str ": begin" \n > _ \n > (- bsv-indent-level-behavioral) "end" \n )
  resume: >  (- bsv-case-indent) "endcase" (progn (bsv-electric-terminate-line) nil))

(define-skeleton bsv-sk-casez
  "Build skeleton casez statement, prompting for the selector expression,
and the case items."
  "[selector expression]: "
  > "casez (" str ") " \n
  > ("case selector: " str ": begin" \n > _ \n > (- bsv-indent-level-behavioral) "end" \n )
  resume: >  (- bsv-case-indent) "endcase" (progn (bsv-electric-terminate-line) nil))

(define-skeleton bsv-sk-if
  "Insert a skeleton if statement."
  > "if (" (bsv-sk-prompt-condition) & ")" " begin" \n
  > _ \n
  > (- bsv-indent-level-behavioral) "end " \n )

(define-skeleton bsv-sk-else-if
  "Insert a skeleton else if statement."
  > (bsv-indent-line) "else if ("
  (progn (setq bsv-sk-p (point)) nil) (bsv-sk-prompt-condition) (if (> (point) bsv-sk-p) ") " -1 ) & " begin" \n
  > _ \n
  > "end" (progn (bsv-electric-terminate-line) nil))

(define-skeleton bsv-sk-datadef
  "Common routine to get data definition"
  ()
  (bsv-sk-prompt-width) | -1 ("name (RET to end):" str ", ") -2 ";" \n)

(define-skeleton bsv-sk-input
  "Insert an input definition."
  ()
  > "input  [" (bsv-sk-datadef))

(define-skeleton bsv-sk-output
  "Insert an output definition."
  ()
  > "output [" (bsv-sk-datadef))

(define-skeleton bsv-sk-inout
  "Insert an inout definition."
  ()
  > "inout  [" (bsv-sk-datadef))

(define-skeleton bsv-sk-reg
  "Insert a reg definition."
  ()
  > "reg    [" (bsv-sk-datadef))

(define-skeleton bsv-sk-wire
  "Insert a wire definition."
  ()
  > "wire   [" (bsv-sk-datadef))

(define-skeleton bsv-sk-assign
  "Insert a skeleton assign statement."
  ()
  > "assign " (bsv-sk-prompt-name) " = " _ ";" \n)

(define-skeleton bsv-sk-while
  "Insert a skeleton while loop statement."
  ()
  > "while ("  (bsv-sk-prompt-condition)  ") begin" \n
  > _ \n
  > (- bsv-indent-level-behavioral) "end " (progn (bsv-electric-terminate-line) nil))

(define-skeleton bsv-sk-repeat
  "Insert a skeleton repeat loop statement."
  ()
  > "repeat ("  (bsv-sk-prompt-condition)  ") begin" \n
  > _ \n
  > (- bsv-indent-level-behavioral) "end " (progn (bsv-electric-terminate-line) nil))

(define-skeleton bsv-sk-for
  "Insert a skeleton while loop statement."
  ()
  > "for ("
  (bsv-sk-prompt-init) "; "
  (bsv-sk-prompt-condition) "; "
  (bsv-sk-prompt-inc)
  ") begin" \n
  > _ \n
  > (- bsv-indent-level-behavioral) "end " (progn (bsv-electric-terminate-line) nil))

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
  > "reg [" (bsv-sk-prompt-width) | -1 bsv-sk-state ", next_" bsv-sk-state ?; \n
  '(setq input nil)
  > \n
  > "// State FF for " bsv-sk-state \n
  > "always @ ( " (read-string "clock:" "posedge clk") " or " (bsv-sk-prompt-reset) " ) begin" \n
  > "if ( " bsv-sk-reset " ) " bsv-sk-state " = 0; else" \n
  > bsv-sk-state " = next_" bsv-sk-state ?; \n
  > (- bsv-indent-level-behavioral) "end" (progn (bsv-electric-terminate-line) nil)
  > \n
  > "// Next State Logic for " bsv-sk-state \n
  > "always @ ( /*AUTOSENSE*/ ) begin\n"
  > "case (" (bsv-sk-prompt-state-selector) ") " \n
  > ("case selector: " str ": begin" \n > "next_" bsv-sk-state " = " _ ";" \n > (- bsv-indent-level-behavioral) "end" \n )
  resume: >  (- bsv-case-indent) "endcase" (progn (bsv-electric-terminate-line) nil)
  > (- bsv-indent-level-behavioral) "end" (progn (bsv-electric-terminate-line) nil))

;; Eliminate compile warning
(eval-when-compile
  (if (not (boundp 'mode-popup-menu))
      (defvar mode-popup-menu nil "Compatibility with XEmacs.")))

;; ---- add menu 'Statements' in BSV mode (MH)
(defun bsv-add-statement-menu ()
  "Add the menu 'Statements' to the menu bar in BSV mode."
  (easy-menu-define bsv-stmt-menu bsv-mode-map
		    "Menu for statement templates in BSV."
		    '("Statements"
		      ["Header"		bsv-sk-header  t]
		      ["Comment"	bsv-sk-comment t]
		      "----"
		      ["Module"		bsv-sk-module t]
		      ["Primitive"	bsv-sk-primitive t]
		      "----"
		      ["Input"		bsv-sk-input t]
		      ["Output"		bsv-sk-output t]
		      ["Inout"		bsv-sk-inout t]
		      ["Wire"		bsv-sk-wire t]
		      ["Reg"		bsv-sk-reg t]
		      "----"
		      ["Initial"	bsv-sk-initial t]
		      ["Always" 	bsv-sk-always t]
		      ["Function"	bsv-sk-function t]
		      ["Task" 		bsv-sk-task t]
		      ["Specify"	bsv-sk-specify t]
		      ["Generate"	bsv-sk-generate t]
		      "----"
		      ["Begin"		bsv-sk-begin t]
		      ["If" 		bsv-sk-if t]
		      ["(if) else"	bsv-sk-else-if t]
		      ["For" 		bsv-sk-for t]
		      ["While" 		bsv-sk-while t]
		      ["Fork" 		bsv-sk-fork t]
		      ["Repeat" 	bsv-sk-repeat t]
		      ["Case" 		bsv-sk-case t]
		      ["Casex" 		bsv-sk-casex t]
		      ["Casez" 		bsv-sk-casez t]
		      ))
  (if bsv-running-on-xemacs
      (progn
	(easy-menu-add bsv-stmt-menu)
	(setq mode-popup-menu (cons "BSV Mode" bsv-stmt-menu)))))

(add-hook 'bsv-mode-hook 'bsv-add-statement-menu)



;;
;; Include file loading with mouse/return event
;; 
;; idea & first impl.: M. Rouat (eldo-mode.el)
;; second (emacs/xemacs) impl.: G. Van der Plas (spice-mode.el)

(if bsv-running-on-xemacs
    (require 'overlay)
  (require 'lucid)) ;; what else can we do ??

(defconst bsv-include-file-regexp
  "^`include\\s-+\"\\([^\n\"]*\\)\""
  "Regexp that matches the include file")

(defvar bsv-mode-mouse-map nil
  "Map containing mouse bindings for bsv-mode.")

(if bsv-mode-mouse-map 
    ()
  (let ((map (make-sparse-keymap))) ; as described in info pages, make a map
    (set-keymap-parent map bsv-mode-map)
    ;; mouse button bindings
    (define-key map "\r"            'bsv-load-file-at-point)
    (if bsv-running-on-xemacs
	(define-key map 'button2    'bsv-load-file-at-mouse);ffap-at-mouse ?
      (define-key map [mouse-2]     'bsv-load-file-at-mouse))
    (if bsv-running-on-xemacs
	(define-key map 'Sh-button2 'mouse-yank) ; you wanna paste don't you ?
      (define-key map [S-mouse-2]   'mouse-yank-at-click))
    (setq bsv-mode-mouse-map map))) ;; copy complete map now

;; create set-extent-keymap procedure when it does not exist
(eval-and-compile
  (unless (fboundp 'set-extent-keymap)
    (defun set-extent-keymap (extent keymap)
      "fallback version of set-extent-keymap (for emacs 2[01])"
      (set-extent-property extent 'local-map keymap))))

(defun bsv-colorize-include-files (beg end old-len)
  "This function colorises included files when the mouse passes over them.
Clicking on the middle-mouse button loads them in a buffer (as in dired)."
  (save-excursion
    (save-match-data
      (let (end-point)
	(goto-char end)
	(setq end-point (bsv-get-end-of-line))
	(goto-char beg)
	(beginning-of-line)  ; scan entire line !
	;; delete overlays existing on this line 
	(let ((overlays (overlays-in (point) end-point)))
	  (while overlays
	    (if (and 
		 (overlay-get (car overlays) 'detachable)
		 (overlay-get (car overlays) 'bsv-include-file))
		(delete-overlay (car overlays)))
	    (setq overlays (cdr overlays)))) ; let
	;; make new ones, could reuse deleted one ?
	(while (search-forward-regexp bsv-include-file-regexp end-point t)
	  (let (extent)
	    (goto-char (match-beginning 1))
	    (or (extent-at (point) (buffer-name) 'mouse-face) ;; not yet extended
		(progn
		  (setq extent (make-extent (match-beginning 1) (match-end 1)))
		  (set-extent-property extent 'start-closed 't)
		  (set-extent-property extent 'end-closed 't)
		  (set-extent-property extent 'detachable 't)
		  (set-extent-property extent 'bsv-include-file 't)
		  (set-extent-property extent 'mouse-face 'highlight)
		  (set-extent-keymap extent bsv-mode-mouse-map)))))))))


(defun bsv-colorize-include-files-buffer ()
  (interactive)
  ;; delete overlays
  (let ((overlays (overlays-in (point-min) (point-max))))
    (while overlays
      (if (and 
	   (overlay-get (car overlays) 'detachable)
	   (overlay-get (car overlays) 'bsv-include-file))
	  (delete-overlay (car overlays)))
      (setq overlays (cdr overlays)))) ; let
  ;; remake overlays
  (bsv-colorize-include-files (point-min) (point-max) nil))

;; ffap-at-mouse isn't useful for bsv mode. It uses library paths.
;; so define this function to do more or less the same as ffap-at-mouse
;; but first resolve filename...
(defun bsv-load-file-at-mouse (event)
  "loads file under button 2 click. Files are checked based on
`bsv-library-directories'."
  (interactive "@e")
  (save-excursion ;; implement a bsv specific ffap-at-mouse
    (mouse-set-point event)
    (beginning-of-line)
    (if (looking-at bsv-include-file-regexp)
	(if (and (car (bsv-library-filenames 
		       (match-string 1) (buffer-file-name)))
		 (file-readable-p (car (bsv-library-filenames 
					(match-string 1) (buffer-file-name)))))
	    (find-file (car (bsv-library-filenames 
			     (match-string 1) (buffer-file-name))))
	  (progn
	    (message 
	     "File '%s' isn't readable, use shift-mouse2 to paste in this field" 
	     (match-string 1))))
      )))

;; ffap isn't useable for bsv mode. It uses library paths.
;; so define this function to do more or less the same as ffap
;; but first resolve filename...
(defun bsv-load-file-at-point ()
  "loads file under point. Files are checked based on
`bsv-library-directories'."
  (interactive)
  (save-excursion ;; implement a bsv specific ffap
    (beginning-of-line)
    (if (looking-at bsv-include-file-regexp)
	(if (and 
	     (car (bsv-library-filenames 
		   (match-string 1) (buffer-file-name)))
	     (file-readable-p (car (bsv-library-filenames 
				    (match-string 1) (buffer-file-name)))))
	    (find-file (car (bsv-library-filenames 
			     (match-string 1) (buffer-file-name))))))
      ))


;;
;; Bug reporting
;;

(defun bsv-submit-bug-report ()
  "Submit via mail a bug report on lazy-lock.el."
  (interactive)
  (let ((reporter-prompt-for-summary-p t))
    (reporter-submit-bug-report
     "support@sbluespec.com"
     (concat "bsv-mode v" (substring bsv-mode-version 12 -3))
     '(
       bsv-align-ifelse
       bsv-auto-endcomments
       bsv-auto-hook
       bsv-auto-indent-on-newline
       bsv-auto-inst-vector
       bsv-auto-lineup
       bsv-auto-newline
       bsv-auto-save-policy
       bsv-auto-sense-defines-constant
       bsv-auto-sense-include-inputs
       bsv-before-auto-hook
       bsv-case-indent
       bsv-cexp-indent
       bsv-compiler
       bsv-coverage
       bsv-highlight-translate-off
       bsv-indent-begin-after-if
       bsv-indent-declaration-macros
       bsv-indent-level
       bsv-indent-level-behavioral
       bsv-indent-level-declaration
       bsv-indent-level-directive
       bsv-indent-level-module
       bsv-indent-lists
       bsv-library-directories
       bsv-library-extensions
       bsv-library-files
       bsv-linter
       bsv-minimum-comment-distance
       bsv-mode-hook
       bsv-simulator
       bsv-tab-always-indent
       bsv-tab-to-comment
       )
     nil nil
     (concat "Hi Mac,

I want to report a bug.  I've read the `Bugs' section of `Info' on
Emacs, so I know how to make a clear and unambiguous report.  To get
to that Info section, I typed

M-x info RET m " invocation-name " RET m bugs RET

Before I go further, I want to say that BSV mode has changed my life.
I save so much time, my files are colored nicely, my co workers respect
my coding ability... until now.  I'd really appreciate anything you
could do to help me out with this minor deficiency in the product.

To reproduce the bug, start a fresh Emacs via " invocation-name "
-no-init-file -no-site-file'.  In a new buffer, in bsv mode, type
the code included below.

If you have bugs with the AUTO functions, please CC the AUTOAUTHOR
Wilson Snyder (wsnyder@wsnyder.org or wsnyder@world.std.com)

Given those lines, I expected [[Fill in here]] to happen;
but instead, [[Fill in here]] happens!.

== The code: =="))))

;; Local Variables:
;; checkdoc-permit-comma-termination-flag:t
;; checkdoc-force-docstrings-flag:nil
;; End:

;;; bsv-mode.el ends here


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
      (if (eq col-orig (first bsv-multiple-indent-list))
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
    (if (eq col (first indent-list))
	()
      (setq indent-list (bsv-get-combined-indent-list))
      (bsv-indent-line-to-closest col indent-list))))

(defun bsv-indent-line-basic ()
  (let (indent-list)
    (setq indent-list (bsv-get-combined-indent-list 1))
    (if (not (null indent-list))
	(indent-line-to (first indent-list)))))

(defun bsv-indent-line-to-closest (col indent-list)
  (if (not (null indent-list))
	(let ()
	  (setq indent-list (bsv-sort-indent-list-closest-first col indent-list))
	  (indent-line-to (first indent-list)))))

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
    (setq col (first values))
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
  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; The font-lock personalization.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst bsv-font-lock-keywords-1 nil
  "Subdued level highlighting for BSV modes.")

(defconst bsv-font-lock-keywords-2 nil
  "Medium level highlighting for BSV modes.")

(defconst bsv-font-lock-keywords-3 nil
  "Gaudy level highlighting for BSV modes.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun font-lock-match-bsv-style-declaration-item-and-skip-to-next (limit)
  ;; Match, and move over, any declaration/definition item after point.
  ;; The expect syntax of an item is "word" or "word::word", possibly ending
  ;; with optional whitespace and a "(".  Everything following the item (but
  ;; belonging to it) is expected to by skip-able by `forward-sexp', and items
  ;; are expected to be separated with a " ".
  (if (looking-at "[ \t*&]*\\(\\sw+\\)\\(::\\(\\sw+\\)\\)?[ \t]*\\((\\)?")
      (save-match-data
	(condition-case nil
	    (save-restriction
	      ;; Restrict to the end of line, currently guaranteed to be LIMIT.
	      (narrow-to-region (point-min) limit)
	      (goto-char (match-end 1))
	      ;; Move over any item value, etc., to the next item.
	      (while (not (looking-at "[ \t]*\\([ ]\\|$\\)"))
		(goto-char (or (scan-sexps (point) 1) (point-max))))
	      (goto-char (match-end 0)))
	  (error t)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(let ((bsv-keywords
       (bsv-regexp-opt
	(append
	 (list "typedef" "import" "export" "tagged")
	 (list "provisos" "return" "matches" "match")
         (list "union" "struct" "type" "void")
	 bsv-start-only-list
	 (mapcar 'car bsv-start-end-alist)
	 (mapcar 'cadr bsv-start-end-alist))))
      (bsv-type-types
       (concat
	"enum\\|"
	"Action\\|ActionValue\\|"
	"Bool\\|Bit\\|"
	"Integer\\|Int\\|Nat\\|UInt\\|"
	"Vector\\|List\\|ListN\\|"
	"Tuple2\\|Tuple3\\|Tuple4\\|Tuple5\\|Tuple6\\|Tuple7\\|"
	)
       ))
 (setq bsv-font-lock-keywords-1
  (list
   ;;
   ;; These are all anchored at the beginning of line for speed.
   ;;

   ;; Fontify comments.
   '("\\([ \t]*//+.*\\)" 1 font-lock-comment-face t)
   '("\\(/\\*.*\\*/\\)" 1 font-lock-comment-face t)

   ;; Fontify attributes
   '("synthesize" 0 font-lock-reference-face)
   '("options" 0 font-lock-reference-face)
   '("noinline" 0 font-lock-reference-face)
   '("always_enabled" 0 font-lock-reference-face)
   '("always_ready" 0 font-lock-reference-face)
   '("no_implicit_conditions" 0 font-lock-reference-face)
   '("fire_when_enabled" 0 font-lock-reference-face)
   '("aggressive_implicit_conditions" 0 font-lock-reference-face)

   ;; and other stuff
   '("\\(^[ \t]*\\|[ \t]+\\)package[ \t]+\\(\\sw+\\)[ \t]*" 2 font-lock-function-name-face)
   '("\\(^[ \t]*\\|[ \t]+\\)module[ \t]+\\(\\sw+#*\\)[ \t]*" 2 font-lock-function-name-face)
   '("\\(^[ \t]*\\|[ \t]+\\)interface[ \t]+\\(\\sw+\\)[ \t]*" 2 font-lock-function-name-face)
   '("\\(^[ \t]*\\|[ \t]+\\)rule[ \t]+\\(\\sw+\\)[ \t]*" 2 font-lock-function-name-face)
   '("\\(^[ \t]*\\|[ \t]+\\)end[^ \t]+:[ \t]+\\(\\sw+\\)[ \t]*" 2 font-lock-function-name-face)

   ;; Fontify all builtin keywords.
   (cons (concat "\\<\\(" bsv-keywords "\\)\\>") 'font-lock-keyword-face)

   ))

 (setq bsv-font-lock-keywords-2
  (append bsv-font-lock-keywords-1
   (list
    ;;
    ;; Simple regexps for speed.
    ;;
    ;; Fontify all type specifiers.

    `("\\(^[ \t]*\\|(\\|const[ \t]+\\)\\(list\\)[ \t]+" 2 font-lock-type-face)
    (cons "\\<const\\>\\|\\<abstract\\>\\|\\<xx\\>" 'font-lock-type-face)
    (cons (concat "\\<\\(" bsv-type-types "\\)\\>") 'font-lock-type-face)

    )))

 (setq bsv-font-lock-keywords-3
  (append 
   bsv-font-lock-keywords-2
   
   (list
    
    ;; Fontify variable names.
    '("\\(\\sw+\\)[ \t]+=" 1 font-lock-variable-name-face)
    '("\\(@\\|[ \t(]ref[ \t]+\\|[ \t(]prepend[ \t]+\\)\\(\\sw+\\)" 2 font-lock-variable-name-face)

    ;; More complicated regexps for more complete highlighting for types.
    ;;
    ;; Fontify all type specifiers, plus their items.
    (list (concat "\\<\\(" "list\\|" bsv-type-types "\\)\\>"
		  "\\([ \t*&]+\\sw+\\>\\)*")
	  ;; Fontify each declaration item.
	  '(font-lock-match-bsv-style-declaration-item-and-skip-to-next
	    ;; Start with point after all type specifiers.
	    (goto-char (or (match-beginning 8) (match-end 1)))
	    ;; Finish with point after first type specifier.
	    (goto-char (match-end 1))
	    ;; Fontify as a variable or function name.
	    (1 (if (match-beginning 4)
		   font-lock-function-name-face
		 font-lock-variable-name-face))))

    )))
 )

(defvar bsv-font-lock-keywords bsv-font-lock-keywords-1
  "Default expressions to highlight in BSV mode.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(unless bsv-running-on-xemacs
  (push 
   (cons 'bsv-mode
	 '((bsv-font-lock-keywords bsv-font-lock-keywords-1
				   bsv-font-lock-keywords-2 bsv-font-lock-keywords-3)
	   nil nil ((?_ . "w")) bsv-beg-of-defun
	   (font-lock-mark-block-function . bsv-mark-function)))
   font-lock-defaults-alist))
  
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
