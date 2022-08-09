(put 'with-capability 'lisp-indent-function 'defun)
(put 'require-capability 'lisp-indent-function 'defun)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; defcap

(defcap TRANSFER (from:string to:string amount:integer)
  @managed amount TRANSFER-mgr
  (assert (!= from to))
  (compose-capability (WITHDRAW from))
  (compose-capability (DEPOSIT from)))

(insert! 'module-capability-signatures
         (list :name 'TRANSFER
               :args (list (cons 'from 'string)
                           (cons 'to 'string)
                           (cons 'amount 'integer))
               :managed (cons #'TRANSFER-mgr 'amount)
               :predicate
               (lambda (from to amount)
                 (assert (!= from to))
                 (compose-capability (WITHDRAW from))
                 (compose-capability (DEPOSIT from)))))

;;; install-capability

(install-capability (TRANSFER "john" "jose" 100))

(unless (lookup module-capability-resources
                'TRANFER (list "john" "jose"))
  (let ((sig (lookup-capability-signature
              module-capability-signatures
              'TRANSFER
              ;; inferred types; how close much they match?
              (list 'string 'string 'integer))))
    ;; Here the `:managed' spec is used to determine which argument is moved
    ;; to the outside.
    (insert! module-capability-resources
             'TRANSFER (list "john" "jose") 100)))

;;; with-capability

(with-capability (TRANSFER "john" "jose" 20) expr)

(if (lookup-capabality-token-in-current-scope
     'TRANSFER (list "john" "jose"))
    expr
  (let* ((sig (lookup-capability-signature
               module-capability-signatures
               'TRANSFER
               (list 'string 'string 'integer)))
         (managed (get-key :managed sig)))
    (when managed
      ;; this will raise an exception if it fails; it also mutates
      ;; `module-capability-resources'
      (funcall (car managed) 20))
    (eval-with-scoped-value
     (list 'TRANSFER "john" "jose")
     expr)))

;;; require-capability

(require-capabality (TRANSFER "john" "jose"))

(unless (lookup-capabality-token-in-current-scope
         'TRANSFER (list "john" "jose"))
  (error "capability X unavailable"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Do lambda abstraction close over capabilities? If not, does mapping a
;;; lambda that requires a capability work because it's always a dynamic
;;; lookup in the environment?

(with-capability C
  ;; C was available when this lambda was created, but is it also available
  ;; when the lambda is called after being returned from this form?
  (lambda ()
    (foo)))

(require-capability C
  ;; C is required to create this lambda, but is it also available when the
  ;; lambda is called after being returned from this form?
  (lambda ()
    (foo)))

;;; What is this 'if' expression's static requirement? A and B, or A or B?
(if b
    (require-capability A)
  (require-capability B))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun hash-and-sign (_args) 0)

(defvar granted-capabilities nil)
(make-variable-buffer-local 'granted-capabilities)

;; A capability is a list of the following data:
;;
;; (SIGNED-HASH FULL-MODULE-NAME CNAME &rest ARGS)

;; `grant' is an internal function that grants a capability. It is secure by
;; virtue of generating a keypair along with each module at time of
;; installation. When the capability is created, the associated data is signed
;; by that private key so that `require-capability' can validate that it
;; received a genuine certificate at time of use.
(defun make-capability (cname &rest args)
  (list (list (hash-and-sign
               (append (list (buffer-file-name) cname) args))
              (buffer-file-name) cname args)))

(defun grant-capabilities (caps)
  (setq granted-capabilities (cons caps granted-capabilities)))

(defun compose-capabilities (&rest caps)
  (append caps))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro defcap (cname args docstr body))

(defun with-capability (cap)
  (unless (string= (nth 1 cap) (buffer-file-name))
    (error "with-capability called on invalid capability")))

(defun require-capability (cap)
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; "Stateless capablities" are a form of guard that relies on dynamic
;;; variables.

(defvar *to-be-composed*)

;;; `grant' is a special function that cannot be called by users.
(defun grant (name &rest args)
  (cons name args))

;; Just a fancy defun; `body' should throw an exception if it fails.
(defmacro defcap (name args &rest body)
  `(defun ,name ,args
     (let ((*to-be-composed* (list nil)))
       ,@body
       (cons (grant (quote ,name) ,@args)
             (cdr *to-be-composed*)))))

(defun compose-capability (cap)
  (nconc *to-be-composed* cap))

(defvar *capabilities*)

;;; Needs to be a macro for the sake of both arguments.
(defmacro with-capability (cap &rest body)
  `(if (member (quote ,cap) *capabilities*)
       (progn ,@body)
     (let ((*capabilities* (append ,cap *capabilities*)))
       ,@body)))

;;; Only a macro so `cap` can be passed unevaluated.
(defmacro require-capability (cap)
  `(unless (member (quote ,cap) *capabilities*)
     (error "capability unavailable")))

;;; Example of use

(defcap ALLOW_ENTRY (user_id)
  (assert (not (string= user_id ""))))

(with-capability (ALLOW_ENTRY "john")
  (require-capability (ALLOW_ENTRY "john")))

;;; This expands to....

(defun ALLOW_ENTRY (user_id)
  (let ((*to-be-composed* (list nil)))
    (assert (not (string= user_id "")))
    (cons (grant 'ALLOW_ENTRY user_id)
          (cdr *to-be-composed*))))

(if (member '(ALLOW_ENTRY "john") *capabilities*)
    (progn
      (unless (member '(ALLOW_ENTRY "john") *capabilities*)
        (error "capability unavailable")))
  (let ((*capabilities* (append (ALLOW_ENTRY "john") *capabilities*)))
    (unless (member '(ALLOW_ENTRY "john") *capabilities*)
      (error "capability unavailable"))))

;;; Note here that "granting" is merely appending to the dynamic variable in a
;;; scoped manner (due to `let'), while confirming the granting just checks
;;; membership in that variable.
