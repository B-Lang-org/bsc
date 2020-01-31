;;; bluespec-mode.el --- A Bluespec editing mode

;; Original Haskell mode:
;; Copyright (C) 1992, 1997-1998 Simon Marlow, Graeme E Moss, and Tommy Thorn

;; Authors: 2001 Revised by Joe Stoy for Bluespec.  Original Haskell mode:
;;	    1997-1998 Graeme E Moss <gem@cs.york.ac.uk> and
;;                    Tommy Thorn <thorn@irisa.fr>,
;;          1992 Simon Marlow
;; Keywords: faces files Bluespec
;; Version: 1.3

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
;; To provide a pleasant mode to browse and edit Bluespec files, linking
;; into the following supported modules:
;;
;; `bluespec-font-lock', Graeme E Moss and Tommy Thorn
;;   Fontifies standard Bluespec keywords, symbols, functions, etc.
;;
;; `bluespec-decl-scan', Graeme E Moss
;;   Scans top-level declarations, and places them in a menu.
;;
;; `bluespec-doc', Hans-Wolfgang Loidl
;;   Echoes types of functions or syntax of keywords when the cursor is idle.
;;
;; `bluespec-indent', Guy Lapalme
;;   Intelligent semi-automatic indentation.
;;
;; `bluespec-simple-indent', Graeme E Moss and Heribert Schuetz
;;   Simple indentation.
;;
;; `haskell-hugs', Guy Lapalme
;;   Interaction with Hugs interpreter.
;;
;;
;; This mode supports full Latin1 Bluespec.  (Note: we do not support any
;; "literate" version of Bluespec: any references to literate Bluespec or
;; Haskell in the code are vestigial, and (it is hoped) irrelevant.)
;;
;; Installation:
;; 
;; Put in your ~/.emacs:
;;
;;    (setq auto-mode-alist
;;          (append auto-mode-alist
;;                  '(("\\.bs$"  . bluespec-mode)
;;                    ("\\.bi$"     . bluespec-mode))))
;;
;;    (autoload 'bluespec-mode "bluespec-mode"
;;       "Major mode for editing Bluespec scripts." t)
;;
;; with `bluespec-mode.el' accessible somewhere on the load-path.
;; To add a directory `~/lib/emacs' (for example) to the load-path,
;; add the following to .emacs:
;;
;;    (setq load-path (cons "~/lib/emacs" load-path))
;;
;; To turn any of the supported modules on for all buffers, add the
;; appropriate line(s) to .emacs:
;;
;;    (add-hook 'bluespec-mode-hook 'turn-on-bluespec-font-lock)
;;    (add-hook 'bluespec-mode-hook 'turn-on-bluespec-decl-scan)
;;    (add-hook 'bluespec-mode-hook 'turn-on-bluespec-doc-mode)
;;    (add-hook 'bluespec-mode-hook 'turn-on-bluespec-indent)
;;    (add-hook 'bluespec-mode-hook 'turn-on-bluespec-simple-indent)
;;
;; Make sure the module files are also on the load-path.  Note that
;; the two indentation modules are mutually exclusive: Use only one.
;;
;;
;; Customisation:
;;
;; History:
;;
;; This mode is snarfed from the Haskell mode, which was
;; based on an editing mode by Simon Marlow 11/1/92
;; and heavily modified by Graeme E Moss and Tommy Thorn 7/11/98.
;; 
;; Present Limitations/Future Work (contributions are most welcome!):
;;
;; . Unicode is still a mystery...  has anyone used it yet?  We still
;;   support Latin-ISO-8859-1 though (the character set of Haskell 1.3).
;;
;;; All functions/variables start with `(literate-)bluespec-'.

;; Version of mode.
(defconst bluespec-version "1.3"
  "bluespec-mode version number.")
(defun bluespec-version ()
  "Echo the current version of bluespec-mode in the minibuffer."
  (interactive)
  (message "Using bluespec-mode version %s" bluespec-version))

;; Set up autoloads for the modules we supply
(autoload 'turn-on-bluespec-font-lock "bluespec-font-lock"
  "Turn on Bluespec font locking." t)
(autoload 'turn-on-bluespec-decl-scan "bluespec-decl-scan"
  "Turn on Bluespec declaration scanning." t)
(autoload 'turn-on-bluespec-doc-mode "bluespec-doc"
  "Turn on Bluespec Doc minor mode." t)
(autoload 'turn-on-bluespec-indent "bluespec-indent"
  "Turn on Bluespec indentation." t)
(autoload 'turn-on-bluespec-simple-indent "bluespec-simple-indent"
  "Turn on simple Bluespec indentation." t)

;; Are we running FSF Emacs or XEmacs?
(defvar bluespec-running-xemacs
  (string-match "Lucid\\|XEmacs" emacs-version)
  "non-nil if we are running XEmacs, nil otherwise.")

;; Are we looking at a literate script?
(defvar bluespec-literate nil
  "*If not nil, the current buffer contains a literate Bluespec script (which
does not exist).

Always buffer-local.")
(make-variable-buffer-local 'bluespec-literate)
;; Default literate style for ambiguous literate buffers.
(defvar bluespec-literate-default nil "")

;; Mode maps.
(defvar bluespec-mode-map ()
  "Keymap used in Bluespec mode.")
(make-variable-buffer-local 'bluespec-mode-map)

(if (not (default-value 'bluespec-mode-map))
    (set-default 'bluespec-mode-map
                 (progn
                   (let ((keymap (make-sparse-keymap)))
                     (define-key keymap "\C-c\C-c" 'comment-region)
                     keymap))))

;; Bluespec-like function for creating [from..to].
(defun bluespec-enum-from-to (from to)
  (if (> from to)
      ()
    (cons from (bluespec-enum-from-to (1+ from) to))))

;; Syntax table.
(defvar bluespec-mode-syntax-table nil
  "Syntax table used in Bluespec mode.")

(if (not bluespec-mode-syntax-table)
    (progn
      (setq bluespec-mode-syntax-table (make-syntax-table))
  (modify-syntax-entry ?\  " " bluespec-mode-syntax-table)
  (modify-syntax-entry ?\t " " bluespec-mode-syntax-table)
  (modify-syntax-entry ?\" "\"" bluespec-mode-syntax-table)
  (modify-syntax-entry ?\' "\'" bluespec-mode-syntax-table)
  (modify-syntax-entry ?_  "w" bluespec-mode-syntax-table)
  (modify-syntax-entry ?\( "()" bluespec-mode-syntax-table)
  (modify-syntax-entry ?\) ")(" bluespec-mode-syntax-table)
  (modify-syntax-entry ?[  "(]" bluespec-mode-syntax-table)
  (modify-syntax-entry ?]  ")[" bluespec-mode-syntax-table)
  (modify-syntax-entry ?{  "(}1" bluespec-mode-syntax-table)
  (modify-syntax-entry ?}  "){4" bluespec-mode-syntax-table)
  (modify-syntax-entry ?-  "_ 23" bluespec-mode-syntax-table)
  (modify-syntax-entry ?\` "$`" bluespec-mode-syntax-table)
  (modify-syntax-entry ?\\ "\\" bluespec-mode-syntax-table)
  (mapcar (lambda (x)
            (modify-syntax-entry x "_" bluespec-mode-syntax-table))
          (concat "!#$%&*+./:<=>?@^|~"
                  (bluespec-enum-from-to ?\241 ?\277)
                  "\327\367"))
  (mapcar (lambda (x)
            (modify-syntax-entry x "w" bluespec-mode-syntax-table))
          (concat (bluespec-enum-from-to ?\300 ?\326)
                  (bluespec-enum-from-to ?\330 ?\337)
                  (bluespec-enum-from-to ?\340 ?\366)
                  (bluespec-enum-from-to ?\370 ?\377)))))

;; Various mode variables.
(defun bluespec-vars ()
  (kill-all-local-variables)
  (make-local-variable 'paragraph-start)
  (setq paragraph-start (concat "^$\\|" page-delimiter))
  (make-local-variable 'paragraph-separate)
  (setq paragraph-separate paragraph-start)
  (make-local-variable 'comment-start)
  (setq comment-start "-- ")
  (make-local-variable 'comment-padding)
  (setq comment-padding 0)
  (make-local-variable 'comment-start-skip)
  (setq comment-start-skip "[-{]- *")
  (make-local-variable 'comment-column)
  (setq comment-column 40)
  (make-local-variable 'comment-indent-function)
  (setq comment-indent-function 'bluespec-comment-indent)
  (make-local-variable 'comment-end)
  (setq comment-end ""))

;; The main mode functions
(defun bluespec-mode ()
  "Major mode for editing Bluespec programs.  

\\<bluespec-mode-map>\\[indent-for-comment] will place a comment at an appropriate place on the current line.
\\<bluespec-mode-map>\\[comment-region] comments (or with prefix arg, uncomments) each line in the region.

Modules can hook in via `bluespec-mode-hook'.  The following modules
are supported with an `autoload' command:

   `bluespec-font-lock', Graeme E Moss and Tommy Thorn (revised Joe Stoy)
     Fontifies standard Bluespec keywords, symbols, functions, etc.

   `bluespec-decl-scan', Graeme E Moss
     Scans top-level declarations, and places them in a menu.

   `bluespec-doc', Hans-Wolfgang Loidl
     Echoes types of functions or syntax of keywords when the cursor is idle.

   `bluespec-indent', Guy Lapalme
     Intelligent semi-automatic indentation.

   `bluespec-simple-indent', Graeme E Moss and Heribert Schuetz
     Simple indentation.

Module X is activated using the command `turn-on-bluespec-X'.  For example,
`bluespec-font-lock' is activated using `turn-on-bluespec-font-lock'.
For more information on a module, see the help for its `turn-on-X'
function.  Some modules can be deactivated using `turn-off-X'.  (Note
that `bluespec-doc' is irregular in using `turn-(on/off)-bluespec-doc-mode'.)

Use `bluespec-version' to find out what version this is.

Invokes `bluespec-mode-hook' if not nil."

  (interactive)
  (bluespec-mode-generic nil))

(defun bluespec-mode-generic (literate)
  "Common part of bluespec-mode and literate-bluespec-mode.  Former
calls with LITERATE nil."

  (bluespec-vars)
  (setq major-mode 'bluespec-mode)
  (setq mode-name "Bluespec")
  (setq bluespec-literate literate)
  (use-local-map bluespec-mode-map)
  (set-syntax-table bluespec-mode-syntax-table)
  (run-hooks 'bluespec-mode-hook))

;; Find the indentation level for a comment.
(defun bluespec-comment-indent ()
  (skip-chars-backward " \t")
  ;; if the line is blank, put the comment at the beginning,
  ;; else at comment-column
  (if (bolp) 0 (max (1+ (current-column)) comment-column)))

;;; Provide ourselves:

(provide 'bluespec-mode)

;;; bluespec-mode.el ends here
