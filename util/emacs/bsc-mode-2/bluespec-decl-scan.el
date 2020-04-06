;;; bluespec-decl-scan.el --- Declaration scanning module for Bluespec Mode

;; copied from the original Haskell mode, changing Haskell to Bluespec throughout.

;; Copyright (C) 1997-1998 Graeme E Moss

;; Authors: 1997-1998 Graeme E Moss <gem@cs.york.ac.uk>
;; Keywords: declarations menu files Bluespec
;; Version: 1.2

;;; This file is not part of GNU Emacs.

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.


;;; Commentary:

;; Purpose:
;;
;; Top-level declarations are scanned and placed in a menu.  Supports
;; full Latin1 Bluespec 1.4 as well as literate scripts.
;;
;;
;; Installation:
;; 
;; To turn declaration scanning on for all Bluespec buffers under the
;; Bluespec mode of Moss&Thorn, add this to .emacs:
;;
;;    (add-hook bluespec-mode-hook 'turn-on-bluespec-decl-scan)
;;
;; Otherwise, call `turn-on-bluespec-decl-scan'.
;;
;;
;; Customisation:
;;
;; None available so far.
;;
;;
;; History:
;;
;; If you have any problems or suggestions, after consulting the list
;; below, email gem@cs.york.ac.uk quoting the version of the library
;; you are using, the version of emacs you are using, and a small
;; example of the problem or suggestion.  Note that this library
;; requires a reasonably recent version of Emacs.
;;
;; Uses `imenu' under FSF Emacs, and `func-menu' under XEmacs.
;;
;; Version 1.2:
;;   Added support for LaTeX-style literate scripts.
;;
;; Version 1.1:
;;   Use own syntax table.  Fixed bug for very small buffers.  Use
;;   markers instead of pointers (markers move with the text).
;;
;; Version 1.0:
;;   Brought over from Bluespec mode v1.1.
;;
;;
;; Present Limitations/Future Work (contributions are most welcome!):
;;
;; . Unicode is still a mystery...  has anyone used it yet?  We still
;;   support Latin-ISO-8859-1 though (the character set of Bluespec 1.3).
;;
;; . Declarations requiring information extending beyond starting line
;;   don't get scanned properly, eg.
;;   > class Eq a =>
;;   >       Test a
;;
;; . Comments placed in the midst of the first few lexemes of a
;;   declaration will cause havoc, eg.
;;   > infixWithComments :: Int -> Int -> Int
;;   > x {-nastyComment-} `infixWithComments` y = x + y
;;   but are not worth worrying about.
;;
;; . Would be nice to scan other top-level declarations such as
;;   methods of a class, datatype field labels...  any more?
;;
;; . Support for Green Card?
;;
;; . Re-running (literate-)bluespec-imenu should not cause the problems
;;   that it does.  The ability to turn off scanning would also be
;;   useful.  (Note that re-running (literate-)bluespec-mode seems to
;;   cause no problems.)
;;
;; . Inconsistency: we define the start of a declaration in `imenu' as
;;   the start of the line the declaration starts on, but in
;;   `func-menu' as the start of the name that the declaration is
;;   given (eg. "class Eq a => Ord a ..." starts at "class" in `imenu'
;;   but at "Ord" in `func-menu').  This avoids rescanning of the
;;   buffer by the goto functions of `func-menu' but allows `imenu' to
;;   have the better definition of the start of the declaration (IMO).
;;
;; . `func-menu' cannot cope well with spaces in declaration names.
;;   This is unavoidable in "instance Eq Int" (changing the spaces to
;;   underscores would cause rescans of the buffer).  Note though that
;;   `fume-prompt-function-goto' (usually bound to "C-c g") does cope
;;   with spaces okay.
;;
;; . Would like to extend the goto functions given by `func-menu'
;;   under XEmacs to FSF Emacs.  Would have to implement these
;;   ourselves as `imenu' does not provide them.
;;
;; . `func-menu' uses its own syntax table when grabbing a declaration
;;   name to lookup (why doesn't it use the syntax table of the
;;   buffer?) so some declaration names will not be grabbed correctly,
;;   eg. "fib'" will be grabbed as "fib" since "'" is not a word or
;;   symbol constituent under the syntax table `func-menu' uses.

;;; All functions/variables start with
;;; `(turn-(on/off)-)bluespec-decl-scan' or `bluespec-ds-'.

;;; The imenu support is based on code taken from `hugs-mode',
;;; thanks go to Chris Van Humbeeck.

;; Version.
(defconst bluespec-decl-scan-version "1.1"
  "bluespec-decl-scan version number.")
(defun bluespec-decl-scan-version ()
  "Echo the current version of bluespec-decl-scan in the minibuffer."
  (interactive)
  (message "Using bluespec-decl-scan version %s" bluespec-decl-scan-version))

;;###autoload
;; As `cl' defines macros that `imenu' uses, we must require them at
;; compile time.
(eval-when-compile
  ;; `imenu' isn't used in XEmacs.
  (if (not (string-match "Lucid\\|XEmacs" emacs-version))
      (progn
	(require 'cl)
	(require 'imenu))))

;; Are we running FSF Emacs or XEmacs?
(defvar bluespec-ds-running-xemacs
  (string-match "Lucid\\|XEmacs" emacs-version)
  "non-nil if we are running XEmacs, nil otherwise.")

;; Bluespec-like function for creating [from..to].
(defun enum-from-to (from to)
  (if (> from to)
      ()
    (cons from (enum-from-to (1+ from) to))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; General declaration scanning functions.

(defun bluespec-ds-match-string (num)
  "As `match-string' except that the string is stripped of properties."
  (format "%s" (match-string num)))

(defvar bluespec-ds-start-keywords-re
  (concat "\\(\\<"
	  "class\\|data\\|i\\(mport\\|n\\(fix\\(\\|[lr]\\)\\|stance\\)\\)\\|"
	  "module\\|primitive\\|type\\|newtype"
	  "\\)\\>")
  "Keywords that may start a declaration.")

(defvar bluespec-ds-syntax-table nil
  "Syntax table used for Bluespec declaration scanning.")

(if (not bluespec-ds-syntax-table)
    (progn
      (setq bluespec-ds-syntax-table (make-syntax-table))
  (modify-syntax-entry ?\  " " bluespec-ds-syntax-table)
  (modify-syntax-entry ?\t " " bluespec-ds-syntax-table)
  (modify-syntax-entry ?\" "\"" bluespec-ds-syntax-table)
  (modify-syntax-entry ?\' "w" bluespec-ds-syntax-table)
  (modify-syntax-entry ?_  "w" bluespec-ds-syntax-table)
  (modify-syntax-entry ?\( "()" bluespec-ds-syntax-table)
  (modify-syntax-entry ?\) ")(" bluespec-ds-syntax-table)
  (modify-syntax-entry ?[  "(]" bluespec-ds-syntax-table)
  (modify-syntax-entry ?]  ")[" bluespec-ds-syntax-table)
  (modify-syntax-entry ?{  "(}1" bluespec-ds-syntax-table)
  (modify-syntax-entry ?}  "){4" bluespec-ds-syntax-table)
  (modify-syntax-entry ?-  "_ 23" bluespec-ds-syntax-table)
  (modify-syntax-entry ?\` "$`" bluespec-ds-syntax-table)
  (mapcar (lambda (x)
            (modify-syntax-entry x "_" bluespec-ds-syntax-table))
          (concat "!#$%&*+./:<=>?@\\^|~"
                  (enum-from-to ?\241 ?\277)
                  "\327\367"))
  (mapcar (lambda (x)
            (modify-syntax-entry x "w" bluespec-ds-syntax-table))
          (concat (enum-from-to ?\300 ?\326)
                  (enum-from-to ?\330 ?\337)
                  (enum-from-to ?\340 ?\366)
                  (enum-from-to ?\370 ?\377)))))

(defun bluespec-ds-get-variable (prefix)
  "Assuming point is looking at the regexp PREFIX followed by the
start of a declaration (perhaps in the middle of a series of
declarations concerning a single variable), if this declaration is a
value binding or type signature, return the variable involved, and
otherwise returns nil.  Point is not moved in either case."
  ;; I think I can now handle all declarations bar those with comments
  ;; nested before the second lexeme.
  (let ((orig-table (syntax-table))
	(start (point))
	par-start
	name)
    (set-syntax-table bluespec-ds-syntax-table)
    (re-search-forward (concat "\\=" prefix) (point-max) t)
    ;; Keyword.
    (if (looking-at bluespec-ds-start-keywords-re)
	()
      (if (looking-at "(\\(\\s_+\\))")
	  ;; Paranthesised symbolic variable.
	  (setq name (bluespec-ds-match-string 1))
	(if (if (looking-at "(")
		;; Skip paranthesised expression.
		(progn
		  (setq par-start t)
		  (forward-sexp)
		  ;; Repeating this code and avoiding moving point if
		  ;; possible speeds things up.
		  (looking-at "\\(\\)\\s-*\\(\\s_+\\|`\\(\\sw+\\)`\\)"))
	      (looking-at "\\(\\sw+\\)\\s-*\\(\\s_+\\|`\\(\\sw+\\)`\\)"))
	    (let ((match2 (bluespec-ds-match-string 2)))
	      ;; Weed out `::', `=' and `|' from potential infix
	      ;; symbolic variable.
	      (if (member match2 '("::" "=" "|"))
		  (if (not par-start)
		      ;; Variable identifier.
		      (setq name (bluespec-ds-match-string 1)))
		(if (eq (aref match2 0) ?\`)
		    ;; Infix variable identifier.
		    (setq name (bluespec-ds-match-string 3))
		  ;; Infix symbolic variable.
		  (setq name match2)))))
	;; Variable identifier.
	(if (and (not name) (looking-at "\\sw+"))
	    (setq name (bluespec-ds-match-string 0)))))
    ;; Return the result.
    (goto-char start)
    (set-syntax-table orig-table)
    name))

(defun bluespec-ds-move-to-start-regexp (inc regexp)
  "Move to beginning of line that succeeds/precedes (INC = 1/-1)
current line that starts with REGEXP and is not in font-lock-comment-face."
  ;; Making this defsubst instead of defun appears to have little or
  ;; no effect on efficiency.  It is probably not called enough to do
  ;; so.
  (while (and (= (forward-line inc) 0)
	      (or (not (looking-at regexp))
		  (eq (get-text-property (point) 'face)
		      'font-lock-comment-face)))))

(defvar literate-bluespec-ds-line-prefix "> "
  "The regexp that matches the start of a line of Bird-style literate
code for the purposes of imenu support.  Current value is \"> \" as we
assume top-level declarations start at column 3.  Must not contain the
special \"^\" regexp as we may not use the regexp at the start of a
regexp string.  Note this is only for imenu support.")

(defvar bluespec-ds-start-decl-re "\\(\\sw\\|(\\)"
  "The regexp that starts a Bluespec declaration.")

(defvar literate-bluespec-ds-start-decl-re
  (concat literate-bluespec-ds-line-prefix bluespec-ds-start-decl-re)
  "The regexp that starts a Bird-style literate Bluespec declaration.")

(defun bluespec-ds-move-to-decl (direction bird-literate fix)
  "General function for moving to the start of a declaration, either
forwards or backwards from point, with normal or with Bird-style
literate scripts.  If DIRECTION is t, then forward, else backward.  If
BIRD-LITERATE is t, then treat as Bird-style literate scripts, else
normal scripts.  Returns point if point is left at the start of a
declaration, and nil otherwise, ie. because point is at the beginning
or end of the buffer and no declaration starts there.  If FIX is t,
then point does not move if already at the start of a declaration."
  ;; As `bluespec-ds-get-variable' cannot separate an infix variable
  ;; identifier out of a value binding with non-alphanumeric first
  ;; argument, this function will treat such value bindings as
  ;; separate from the declarations surrounding it.
  (let (;; The variable typed or bound in the current series of
	;; declarations.
	name
	;; The variable typed or bound in the new declaration.
	newname
	;; Hack to solve hard problem for Bird-style literate scripts
	;; that start with a declaration.  We are in the abyss if
	;; point is before start of this declaration.
	abyss
	(line-prefix (if bird-literate literate-bluespec-ds-line-prefix ""))
	;; The regexp to match for the start of a declaration.
	(start-decl-re (if bird-literate
			   literate-bluespec-ds-start-decl-re
			 bluespec-ds-start-decl-re))
	(increment (if direction 1 -1))
	(bound (if direction (point-max) (point-min)))
	;; Original syntax table.
	(orig-table (syntax-table))
	result)
    ;; Change syntax table.
    (set-syntax-table bluespec-ds-syntax-table)
    ;; Move to beginning of line that starts the "current
    ;; declaration" (dependent on DIRECTION and FIX), and then get
    ;; the variable typed or bound by this declaration, if any.
    (let (;; Where point was at call of function.
	  (here (point))
	  ;; Where the declaration on this line (if any) starts.
	  (start (progn
		   (beginning-of-line)
                   ;; Checking the face to ensure a declaration starts
                   ;; here seems to be the only addition to make this
                   ;; module support LaTeX-style literate scripts.
		   (if (and (looking-at start-decl-re)
                            (not (eq (get-text-property (point) 'face)
                                     'font-lock-comment-face)))
		       (match-beginning 1)))))
      (if (and start
	       ;; This complicated boolean determines whether we
	       ;; should include the declaration that starts on the
	       ;; current line as the "current declaration" or not.
	       (or (and (or (and direction (not fix))
			    (and (not direction) fix))
			(>= here start))
		   (and (or (and direction fix)
			    (and (not direction) (not fix)))
			(> here start))))
	  ;; If so, we are already at start of the current line, so
	  ;; do nothing.
	  ()
	;; If point was before start of a declaration on the first
	;; line of the buffer (possible for Bird-style literate
	;; scripts) then we are in the abyss.
	(if (and start (bobp))
	    (setq abyss t)
	  ;; Otherwise we move to the start of the first declaration
	  ;; on a line preceding the current one.
	  (bluespec-ds-move-to-start-regexp -1 start-decl-re))))
    ;; If we are in the abyss, position and return as appropriate.
    (if abyss
	(if (not direction)
	    (setq result nil)
	  (re-search-forward (concat "\\=" line-prefix) (point-max) t)
	  (setq result (point)))
      ;; Get the variable typed or bound by this declaration, if any. 
      (setq name (bluespec-ds-get-variable line-prefix))
      (if (not name)
	  ;; If no such variable, stop at the start of this
	  ;; declaration if moving backward, or move to the next
	  ;; declaration if moving forward.
	  (if direction
	      (bluespec-ds-move-to-start-regexp 1 start-decl-re))
	;; If there is a variable, find the first
	;; succeeding/preceding declaration that does not type or
	;; bind it.  Check for reaching start/end of buffer.
	(bluespec-ds-move-to-start-regexp increment start-decl-re)
	(while (and (/= (point) bound)
		    (and (setq newname (bluespec-ds-get-variable line-prefix))
			 (string= name newname)))
	  (setq name newname)
	  (bluespec-ds-move-to-start-regexp increment start-decl-re))
	;; If we are going backward, and have either reached a new
	;; declaration or the beginning of a buffer that does not
	;; start with a declaration, move forward to start of next
	;; declaration (which must exist).  Otherwise, we are done.
	(if (and (not direction)
		 (or (and (looking-at start-decl-re)
			  (not (string= name
					;; Note we must not use
					;; newname here as this may
					;; not have been set if we
					;; have reached the beginning
					;; of the buffer.
					(bluespec-ds-get-variable
					 line-prefix))))
		     (and (not (looking-at start-decl-re))
			  (bobp))))
	    (bluespec-ds-move-to-start-regexp 1 start-decl-re)))
      ;; Store whether we are at the start of a declaration or not.
      ;; Used to calculate final result.
      (let ((at-start-decl (looking-at start-decl-re)))
	;; If we are at the beginning of a line, move over
	;; line-prefix, if present at point.
	(if (bolp)
	    (re-search-forward (concat "\\=" line-prefix) (point-max) t))
	;; Return point if at the start of a declaration and nil
	;; otherwise.
	(setq result (if at-start-decl (point) nil))))
    ;; Replace original syntax table.
    (set-syntax-table orig-table)
    ;; Return the result.
    result))

(defun bluespec-ds-backward-decl ()
  "Move point backward to the first character preceding the current
point that starts a top-level declaration.  A series of declarations
concerning one variable is treated as one declaration by this
function.  So, if point is within a top-level declaration then move it
to the start of that declaration.  If point is already at the start of
a top-level declaration, then move it to the start of the preceding
declaration.  Returns point if point is left at the start of a
declaration, and nil otherwise, ie. because point is at the beginning
of the buffer and no declaration starts there."
  (interactive)
  (bluespec-ds-move-to-decl nil
                           (if (boundp 'bluespec-literate)
                               (eq bluespec-literate 'bird) nil)
                           nil))

(defun bluespec-ds-forward-decl ()
  "As `bluespec-ds-backward-decl' but forward."
  (interactive)
  (bluespec-ds-move-to-decl t
                           (if (boundp 'bluespec-literate)
                               (eq bluespec-literate 'bird) nil)
                           nil))

(defun bluespec-ds-generic-find-next-decl (bird-literate)
  "Find the name, position and type of the declaration at or after
point.  Returns `((name . (start-position . name-position)) . type)'
if one exists and nil otherwise.  The start-position is at the start
of the declaration, and the name-position is at the start of the name
of the declaration.  The name is a string, the positions are buffer
positions and the type is one of the symbols `variable', `datatype',
`class', `import' and `instance'."
  (let (;; The name, type and name-position of the declaration to
	;; return.
	name
	type
	name-pos
	;; Buffer positions marking the start and end of the space
	;; containing a declaration.
	start
	end
	;; Original syntax table.
	(orig-table (syntax-table)))
    ;; Change to declaration scanning syntax.
    (set-syntax-table bluespec-ds-syntax-table)
    ;; Stop when we are at the end of the buffer or when a valid
    ;; declaration is grabbed.
    (while (not (or (eobp) name))
      ;; Move forward to next declaration at or after point.
      (bluespec-ds-move-to-decl t bird-literate t)
      ;; Start and end of search space is currently just the starting
      ;; line of the declaration.
      (setq start (point)
	    end   (progn (end-of-line) (point)))
      (goto-char start)
      (cond
       ;; If the start of the top-level declaration does not begin
       ;; with a starting keyword, then (if legal) must be a type
       ;; signature or value binding, and the variable concerned is
       ;; grabbed.
       ((not (looking-at bluespec-ds-start-keywords-re))
	(setq name (bluespec-ds-get-variable ""))
	(if name
	    (progn
	      (setq type 'variable)
	      (re-search-forward (regexp-quote name) end t)
	      (setq name-pos (match-beginning 0)))))
       ;; User-defined datatype declaration.
       ((re-search-forward "\\=\\(data\\|newtype\\|type\\)\\>" end t)
	(re-search-forward "=>" end t)
	(if (looking-at "[ \t]*\\(\\sw+\\)")
	    (progn
	      (setq name (bluespec-ds-match-string 1))
	      (setq name-pos (match-beginning 1))
	      (setq type 'datatype))))
       ;; Class declaration.
       ((re-search-forward "\\=class\\>" end t)
	(re-search-forward "=>" end t)
	(if (looking-at "[ \t]*\\(\\sw+\\)")
	    (progn
	      (setq name (bluespec-ds-match-string 1))
	      (setq name-pos (match-beginning 1))
	      (setq type 'class))))
       ;; Import declaration.
       ((looking-at "import[ \t]+\\(qualified[ \t]+\\)?\\(\\sw+\\)")
	(setq name (bluespec-ds-match-string 2))
	(setq name-pos (match-beginning 2))
	(setq type 'import))
       ;; Instance declaration.
       ((re-search-forward "\\=instance[ \t]+" end t)
	(re-search-forward "=>[ \t]+" end t)
	;; The instance "title" starts just after the `instance' (and
	;; any context) and finishes just before the _first_ `where'
	;; if one exists.  This solution is ugly, but I can't find a
	;; nicer one---a simple regexp will pick up the last `where',
	;; which may be rare but nevertheless...
	(setq name-pos (point))
	(setq name (format "%s"
			   (buffer-substring
			    (point)
			    (progn			       
			      ;; Look for a `where'.
			      (if (re-search-forward "\\<where\\>" end t)
				  ;; Move back to just before the `where'.
				  (progn
				    (re-search-backward "\\s-where")
				    (point))
				;; No `where' so move to last non-whitespace
				;; before `end'.
				(progn
				  (goto-char end)
				  (skip-chars-backward " \t")
				  (point)))))))
	;; If we did not manage to extract a name, cancel this
	;; declaration (eg. when line ends in "=> ").
	(if (string-match "^[ \t]*$" name) (setq name nil))
	(setq type 'instance)))
      ;; Move past start of current declaration.
      (goto-char end))
    ;; Replace syntax table.
    (set-syntax-table orig-table)
    ;; If we have a valid declaration then return it, otherwise return
    ;; nil.
    (if name
	(cons (cons name (cons (copy-marker start t) (copy-marker name-pos t)))
	      type)
      nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Declaration scanning via `imenu'.

(defun bluespec-ds-create-imenu-index ()
  "Non-literate Bluespec version of `bluespec-ds-generic-create-menu-index'."
  (bluespec-ds-generic-create-imenu-index nil))

(defun literate-bluespec-ds-create-imenu-index ()
  "Bird-style literate Bluespec version of
`bluespec-ds-generic-create-menu-index'."
  (bluespec-ds-generic-create-imenu-index t))

(defun bluespec-ds-generic-create-imenu-index (bird-literate)
  "Function for finding imenu declarations in (BIRD-LITERATE) Bluespec mode.
Finds all declarations (classes, variables, imports, instances and
datatypes) in a Bluespec file for the imenu package."
  ;; Each list has elements of the form `(INDEX-NAME . INDEX-POSITION)'.
  ;; These lists are nested using `(INDEX-TITLE . INDEX-ALIST)'.
  (let* ((index-alist '())
	 (index-class-alist '())   ;; Classes
	 (index-var-alist '())     ;; Variables
	 (index-imp-alist '())     ;; Imports
	 (index-inst-alist '())    ;; Instances
	 (index-type-alist '())    ;; Datatypes
	 ;; Variables for showing progress.
	 (bufname (buffer-name))
	 (divisor-of-progress (max 1 (/ (point-max) 100)))
	 ;; The result we wish to return.
	 result)
    (goto-char (point-min))
    ;; Loop forwards from the beginning of the buffer through the
    ;; starts of the top-level declarations.
    (while (< (point) (point-max))
      (message "Scanning declarations in %s... (%3d%%)" bufname
	       (/ (point) divisor-of-progress))
      ;; Grab the next declaration.
      (setq result (bluespec-ds-generic-find-next-decl bird-literate))
      (if result
	  ;; If valid, extract the components of the result.
	  (let* ((name-posns (car result))
		 (name (car name-posns))
		 (posns (cdr name-posns))
		 (start-pos (car posns))
		 (type (cdr result))
		 ;; Place `(name . start-pos)' in the correct alist.
		 (alist (cond
			 ((eq type 'variable) 'index-var-alist)
			 ((eq type 'datatype) 'index-type-alist)
			 ((eq type 'class) 'index-class-alist)
			 ((eq type 'import) 'index-imp-alist)
			 ((eq type 'instance) 'index-inst-alist))))
	    (set alist (cons (cons name start-pos) (eval alist))))))
    ;; Now sort all the lists, label them, and place them in one list.
    (message "Sorting declarations in %s..." bufname)
    (and index-type-alist
	 (push (cons "Datatypes"
		     (sort index-type-alist 'bluespec-ds-imenu-label-cmp))
	       index-alist))
    (and index-inst-alist
	 (push (cons "Instances"
		     (sort index-inst-alist 'bluespec-ds-imenu-label-cmp))
	       index-alist))
    (and index-imp-alist
	 (push (cons "Imports"
		     (sort index-imp-alist 'bluespec-ds-imenu-label-cmp))
	       index-alist))
    (and index-var-alist
	 (push (cons "Variables"
		     (sort index-var-alist 'bluespec-ds-imenu-label-cmp))
	       index-alist))
    (and index-class-alist
	 (push (cons "Classes"
		     (sort index-class-alist 'bluespec-ds-imenu-label-cmp))
	       index-alist))
    (message "Sorting declarations in %s...done" bufname)
    ;; Return the alist.
    index-alist))

(defun bluespec-ds-imenu-label-cmp (el1 el2)
  "Predicate to compare labels in lists produced by
`bluespec-ds-create-imenu-index'."
  (string< (car el1) (car el2)))

(defun bluespec-ds-imenu (bird-literate)
  "Install imenu for (BIRD-LITERATE) Bluespec scripts."
  ;; Would prefer to toggle imenu but can't see how to turn it off...
  (require 'imenu)
  ;; In emacs-20's imenu we have to bind some functions first -- HWL
  (if (and  (not bluespec-ds-running-xemacs)
	    (>= (string-to-number (substring emacs-version 0 2)) 20)
	    (not (fboundp 'imenu-extract-index-name-function)))
    (setq imenu-extract-index-name-function
	  (if bird-literate (function literate-bluespec-ds-create-imenu-index)
	    (function bluespec-ds-create-imenu-index))))
  (setq imenu-create-index-function
	(if bird-literate (function literate-bluespec-ds-create-imenu-index)
	  (function bluespec-ds-create-imenu-index)))
  (if (fboundp 'imenu-add-to-menubar)
      (imenu-add-to-menubar "Declarations")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Declaration scanning via `func-menu'.

(defun bluespec-ds-func-menu-next (buffer)
  "Non-literate Bluespec version of `bluespec-ds-generic-func-menu-next'." 
  (bluespec-ds-generic-func-menu-next nil buffer)) 

(defun literate-bluespec-ds-func-menu-next (buffer)
  "Bird-style literate Bluespec version of `bluespec-ds-generic-func-menu-next'."
  (bluespec-ds-generic-func-menu-next t buffer)) 

(defun bluespec-ds-generic-func-menu-next (bird-literate buffer)
  "Returns `(name . pos)' of next declaration."
  (set-buffer buffer)
  (let ((result (bluespec-ds-generic-find-next-decl bird-literate)))
    (if result
	(let* ((name-posns (car result))
	       (name (car name-posns))
	       (posns (cdr name-posns))
	       (name-pos (cdr posns))
	       ;(type (cdr result))
	       )
	  (cons ;(concat
		 ;; func-menu has problems with spaces, and adding a
		 ;; qualifying keyword will not allow the "goto fn"
		 ;; functions to work properly.  Sigh.
;		 (cond
;		  ((eq type 'variable) "")
;		  ((eq type 'datatype) "datatype ")
;		  ((eq type 'class) "class ")
;		  ((eq type 'import) "import ")
;		  ((eq type 'instance) "instance "))
		 name;)
		name-pos))
      nil)))

(defvar bluespec-ds-func-menu-regexp
  (concat "^" bluespec-ds-start-decl-re)
  "Regexp to match the start of a possible declaration.")

(defvar literate-bluespec-ds-func-menu-regexp
  (concat "^" literate-bluespec-ds-start-decl-re)
  "As `bluespec-ds-func-menu-regexp' but for Bird-style literate scripts.")

(defun bluespec-ds-func-menu (bird-literate)
  "Uses `func-menu' to establish declaration scanning for (BIRD-LITERATE)
Bluespec scripts."
  (require 'func-menu)
  (make-local-variable 'fume-menubar-menu-name)
  (setq fume-menubar-menu-name "Declarations")
  (make-local-variable 'fume-function-name-regexp-alist)
  (setq fume-function-name-regexp-alist
	(if bird-literate
            '((bluespec-mode . literate-bluespec-ds-func-menu-regexp))
          '((bluespec-mode . bluespec-ds-func-menu-regexp))))
  (make-local-variable 'fume-find-function-name-method-alist)
  (setq fume-find-function-name-method-alist
        (if bird-literate
            '((bluespec-mode . literate-bluespec-ds-func-menu-next))
          '((bluespec-mode . bluespec-ds-func-menu-next))))
  (fume-add-menubar-entry)
  (local-set-key "\C-cl" 'fume-list-functions)
  (local-set-key "\C-cg" 'fume-prompt-function-goto)
  (local-set-key [(meta button1)] 'fume-mouse-function-goto))

;; Key mappings.
(defun bluespec-ds-keys ()
  "Map the keys for forward and backward declaration movement."
  (local-set-key "\M-\C-e" 'bluespec-ds-forward-decl)
  (local-set-key "\M-\C-a" 'bluespec-ds-backward-decl))

;; The main functions to turn on declaration scanning.
(defun turn-on-bluespec-decl-scan ()
  "Turn on declaration scanning for Bluespec mode.  Top-level
declarations are scanned and listed in the menu item \"Declarations\".
Selecting an item from this menu will take point to the start of the
declaration.

\\[bluespec-ds-forward-decl] and \\[bluespec-ds-backward-decl] move forward and backward to the start of a declaration.

Under XEmacs, the following keys are also defined:

\\[fume-list-functions] lists the declarations of the current buffer,
\\[fume-prompt-function-goto] prompts for a declaration to move to, and
\\[fume-mouse-function-goto] moves to the declaration whose name is at point.

This may link with `bluespec-doc' (only for FSF Emacs currently).

For non-literate and LaTeX-style literate scripts, we assume the
common convention that top-level declarations start at the first
column.  For Bird-style literate scripts, we assume the common
convention that top-level declarations start at the third column,
ie. after \"> \".

Anything in `font-lock-comment-face' is not considered for a
declaration.  Therefore, using Bluespec font locking with comments
coloured in `font-lock-comment-face' improves declaration scanning.

To turn on declaration scanning for all Bluespec buffers, add this to
.emacs:

  (add-hook 'bluespec-mode-hook 'turn-on-bluespec-decl-scan)

To turn declaration scanning on for the current buffer, call
`turn-on-bluespec-decl-scan'.

Literate Bluespec scripts are supported: If the value of
`bluespec-literate' (automatically set by the Bluespec mode of
Moss&Thorn) is 'bird, a Bird-style literate script is assumed.  If it
is nil or 'latex, a non-literate or LaTeX-style literate script is
assumed, respectively.

Invokes `bluespec-decl-scan-hook' if not nil.

Use `bluespec-decl-scan-version' to find out what version this is."
  (interactive)
  (bluespec-ds-keys)
  (let ((bird-literate (if (boundp 'bluespec-literate)
                           (eq bluespec-literate 'bird) nil)))
    (if bluespec-ds-running-xemacs
        (bluespec-ds-func-menu bird-literate)
      (bluespec-ds-imenu bird-literate)))
  (run-hooks 'bluespec-decl-scan-hook))

;;; Provide ourselves:

(provide 'bluespec-decl-scan)

;;; bluespec-decl-scan ends here.
