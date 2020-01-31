;;; -*- Emacs-Lisp -*- ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Commands to mark with a visible region.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-key global-map "\M-[" 'mark-to-start)
(define-key global-map "\M-]" 'mark-to-end)

(define-key global-map "\M-w" 'visible-copy-region-as-kill)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(unless (fboundp 'deactivate-mark)
  (defvar mark-active nil)
  (defsubst deactivate-mark ()
    (if transient-mark-mode
	(progn
	  (setq mark-active nil)
	  (run-hooks 'deactivate-mark-hook)))))

(setq highlight-nonselected-windows nil)

(setq transient-mark-mode t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun mark-to-start ()
  "Mark from beginning of buffer to point."
  (interactive)
  (push-mark (point-min))
  (when transient-mark-mode
    (setq mark-active t)
    (setq deactivate-mark nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun mark-to-end ()
  "Mark from point to end of buffer."
  (interactive)
  (push-mark (point-max))
  (when transient-mark-mode
    (setq mark-active t)
    (setq deactivate-mark nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun visible-copy-region-as-kill (beg end)
  "Save the region as if killed, but don't kill it.
If `interprogram-cut-function' is non-nil, also save the text for a window
system cut and paste."
  (interactive "r")
  (if (eq last-command 'kill-region)
      (kill-append (buffer-substring beg end) (< end beg))
    (kill-new (buffer-substring beg end)))
  (setq this-command 'kill-region)
  (when transient-mark-mode
    (deactivate-mark))
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; This is an edited version of isearch-mode which does not deactivate mark
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;(defun isearch-mode (forward &optional regexp op-fun recursive-edit word-p)
;  "Start isearch minor mode.  Called by isearch-forward, etc."

;  ;; Initialize global vars.
;  (setq isearch-forward forward
;	isearch-regexp regexp
;	isearch-word word-p
;	isearch-op-fun op-fun
;	isearch-case-fold-search case-fold-search
;	isearch-string ""
;	isearch-message ""
;	isearch-cmds nil
;	isearch-success t
;	isearch-wrapped nil
;	isearch-barrier (point)
;	isearch-adjusted nil
;	isearch-yank-flag nil
;	isearch-invalid-regexp nil
;	isearch-within-brackets nil
;	;; Use (baud-rate) for now, for sake of other versions.
;	isearch-slow-terminal-mode (and (<= (baud-rate) search-slow-speed)
;					(> (window-height)
;					   (* 4 search-slow-window-lines)))
;	isearch-other-end nil
;	isearch-small-window nil

;	isearch-opoint (point)
;	search-ring-yank-pointer nil
;	regexp-search-ring-yank-pointer nil)
;  (setq isearch-window-configuration
;	(if isearch-slow-terminal-mode (current-window-configuration) nil))


;;; This was for Lucid Emacs.  But now that we have pre-command-hook,
;;; it causes trouble.
;;;  (if isearch-pre-command-hook-exists
;;;      (add-hook 'pre-command-hook 'isearch-pre-command-hook))
;  (setq	isearch-mode " Isearch")  ;; forward? regexp?
;  (set-buffer-modified-p (buffer-modified-p)) ; update modeline

;  ;; It is ugly to show region highlighting while the search
;  ;; is going on.  And we don't want the mark active at the end either.
;;  (setq deactivate-mark t)

;  (isearch-push-state)

;  (make-local-variable 'overriding-local-map)
;  (setq overriding-local-map isearch-mode-map)
;  (isearch-update)
;  (run-hooks 'isearch-mode-hook)

;  ;; isearch-mode can be made modal (in the sense of not returning to 
;  ;; the calling function until searching is completed) by entering 
;  ;; a recursive-edit and exiting it when done isearching.
;  (if recursive-edit
;      (let ((isearch-recursive-edit t))
;	(recursive-edit)))
;  isearch-success)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun visible-beginning-of-buffer (&optional arg)
  "Move point to the beginning of the buffer; leave mark at previous position.
With arg N, put point N/10 of the way from the true beginning.

Don't use this command in Lisp programs!
\(goto-char (point-min)) is faster and avoids clobbering the mark."
  (interactive "P")
  (let (start)
    (setq start (point))
    (push-mark)
    (goto-char (if arg
		   (if (> (buffer-size) 10000)
		       ;; Avoid overflow for large buffer sizes!
		       (* (prefix-numeric-value arg)
			  (/ (buffer-size) 10))
		     (/ (+ 10 (* (buffer-size) (prefix-numeric-value arg))) 10))
		 (point-min)))
    (if arg (forward-line 1))
    (when transient-mark-mode
      (when (= start (point-max))
	(setq mark-active t)
	(setq deactivate-mark nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun visible-end-of-buffer (&optional arg)
  "Move point to the end of the buffer; leave mark at previous position.
With arg N, put point N/10 of the way from the true end.

Don't use this command in Lisp programs!
\(goto-char (point-max)) is faster and avoids clobbering the mark."
  (interactive "P")
  (let (start)
    (setq start (point))
    (push-mark)
    (goto-char (if arg
		   (- (1+ (buffer-size))
		      (if (> (buffer-size) 10000)
			  ;; Avoid overflow for large buffer sizes!
			  (* (prefix-numeric-value arg)
			     (/ (buffer-size) 10))
			(/ (* (buffer-size) (prefix-numeric-value arg)) 10)))
		 (point-max)))
    ;; If we went to a place in the middle of the buffer,
    ;; adjust it to the beginning of a line.
    (if arg (forward-line 1)
      ;; If the end of the buffer is not already on the screen,
      ;; then scroll specially to put it near, but not at, the bottom.
      (if (let ((old-point (point)))
	    (save-excursion
	      (goto-char (window-start))
	      (vertical-motion (window-height))
	      (< (point) old-point)))
	  (progn
	    (overlay-recenter (point))
	    (recenter -3))))
    (when transient-mark-mode
      (when (= start (point-min))
	(setq mark-active t)
	(setq deactivate-mark nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(provide 'mark)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

