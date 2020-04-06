;;; bluespec-simple-indent.el --- Simple indentation module for Bluespec Mode

;; copied from the original Haskell mode, changing Haskell to Bluespec throughout.

;; Copyright 1998 Heribert Schuetz, Graeme E Moss

;; Authors:
;;   1998 Heribert Schuetz <Heribert.Schuetz@informatik.uni-muenchen.de> and
;;        Graeme E Moss <gem@cs.york.ac.uk>
;; Keywords: indentation files Bluespec
;; Version: 1.0

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
;; To support simple indentation of Bluespec scripts.
;;
;;
;; Installation:
;; 
;; To bind TAB to the indentation command for all Bluespec buffers, add
;; this to .emacs:
;;
;;    (add-hook 'bluespec-mode-hook 'turn-on-bluespec-simple-indent)
;;
;; Otherwise, call `turn-on-bluespec-simple-indent'.
;;
;;
;; Customisation:
;;
;; None supported.
;;
;;
;; History:
;;
;; If you have any problems or suggestions, after consulting the list
;; below, email gem@cs.york.ac.uk quoting the version of you are
;; using, the version of emacs you are using, and a small example of
;; the problem or suggestion.
;;
;; Version 1.0:
;;   Brought over from Bluespec mode v1.1.
;;
;; Present Limitations/Future Work (contributions are most welcome!):
;;
;; (None so far.)

;;; All functions/variables start with
;;; `(turn-(on/off)-)bluespec-simple-indent'.

;; Version.
(defconst bluespec-simple-indent-version "1.1"
  "bluespec-simple-indent version number.")
(defun bluespec-simple-indent-version ()
  "Echo the current version of bluespec-simple-indent in the minibuffer."
  (interactive)
  (message "Using bluespec-simple-indent version %s"
           bluespec-simple-indent-version))

;; Partly stolen from `indent-relative' in indent.el:
(defun bluespec-simple-indent ()
  "Space out to under next visible indent point.
Indent points are positions of non-whitespace following whitespace in
lines preceding point. A position is visible if it is to the left of
the first non-whitespace of every nonblank line between the position and
the current line. If there is no visible indent point beyond the current
column, `tab-to-tab-stop' is done instead."
  (interactive)
  (let ((start-column (current-column))
	(invisible-from nil)		; `nil' means infinity here
	indent )
    (catch 'bluespec-simple-indent-break
      (save-excursion
	(while (progn (beginning-of-line)
		      (> (point) (point-min)))
	  (forward-line -1)
	  (if (not (looking-at "[ \t]*\n"))
	      (let ((this-indentation (current-indentation)))
		(if (or (not invisible-from)
			(< this-indentation invisible-from))
		    (if (> this-indentation start-column)
			(setq invisible-from this-indentation)
		      (let ((end (save-excursion (forward-line 1) (point))))
			(move-to-column start-column)
			;; Is start-column inside a tab on this line?
			(if (> (current-column) start-column)
			    (backward-char 1))
			(or (looking-at "[ \t]")
			    (skip-chars-forward "^ \t" end))
			(skip-chars-forward " \t" end)
			(let ((col (current-column)))
			  (setq indent
				(if (or (= (point) end)
					(and invisible-from
					     (> col invisible-from)))
				    invisible-from
				  col ) ) )
			(throw 'bluespec-simple-indent-break nil)))))))))
    (if indent
	(let ((opoint (point-marker)))
	  (delete-region (point) (progn (skip-chars-backward " \t") (point)))
	  (indent-to indent 0)
	  (if (> opoint (point))
	      (goto-char opoint))
	  (move-marker opoint nil))
      (tab-to-tab-stop)) ) )

;; The main functions.
(defun turn-on-bluespec-simple-indent ()
  "Sets `indent-line-function' to `bluespec-simple-indent'---a simple
indentation function.  Ensures TAB is bound to
`indent-for-tab-command', and LFD to `newline-and-indent'.  TAB will
now move the cursor to the next indent point in the previous nonblank
line.  An indent point is a non-whitespace character following
whitespace.

Invokes `bluespec-simple-indent-hook' if not nil.

Use `bluespec-simple-indent-version' to find out what version this is."

  (interactive)
  (make-local-variable 'bluespec-simple-indent-old)
  (setq bluespec-simple-indent-old indent-line-function)
  (make-local-variable 'indent-line-function)
  (setq indent-line-function 'bluespec-simple-indent)
  (local-set-key "\t" 'indent-for-tab-command)
  (local-set-key "\n" 'newline-and-indent)
  (run-hooks 'bluespec-simple-indent-hook))

(defun turn-off-bluespec-simple-indent ()
  "Returns `indent-line-function' to original value, before
`turn-on-bluespec-simple-indent' was called.  Leaves TAB and LFD bound
to `indent-for-tab-command' and `newline-and-indent' respectively."

  (interactive)
  (if (boundp 'bluespec-simple-indent-old)
      (setq indent-line-function bluespec-simple-indent-old)))

;;; Provide ourselves:

(provide 'bluespec-simple-indent)

;;; bluespec-simple-indent ends here.
