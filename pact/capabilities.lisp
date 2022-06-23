;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; If I implement these things functionally, use data values for caps...

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; defcap

;; (defcap TRANSFER (from:string to:string amount:integer)
;;   @managed amount TRANSFER-mgr
;;   (assert (!= from to))
;;   (compose-capability (WITHDRAW from))
;;   (compose-capability (DEPOSIT from)))

;;; EXPANDS TO
(insert! 'module-capability-signatures
         'TRANSFER
         (list :args (list (cons 'from 'string)
                           (cons 'to 'string)
                           (cons 'amount 'integer))
               :managed (cons #'TRANSFER-mgr 'amount)
               :predicate
               (lambda (from to amount)
                 (assert (!= from to))
                 (compose-capability (WITHDRAW from))
                 (compose-capability (DEPOSIT from)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; install-capability

(install-capability (TRANSFER "john" "jose" 100))

;;; EXPANDS TO
(unless (lookup module-capability-resources
                'TRANFER (list "john" "jose"))
  (let ((sig (lookup module-capability-signatures
                     'TRANSFER
                     ;; inferred types; how close much they match?
                     (list 'string 'string 'integer))))
    ;; Here the `:managed' spec is used to determine which argument is moved
    ;; to the outside.
    (insert! module-capability-resources
             'TRANSFER (list "john" "jose") 100)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; with-capability

(with-capability (TRANSFER "john" "jose" 20) expr)

;;; EXPANDS TO
(if (lookup-capabality-token-in-current-scope
     'TRANSFER (list "john" "jose"))
    expr
    (let* ((sig (lookup module-capability-signatures
                        'TRANSFER
                        (list 'string 'string 'integer)))
           (managed (get-key :managed sig)))
      (funcall (get-key :predicate) (list "john" "jose"))
      (when managed
        ;; this will raise an exception if it fails; it also mutates
        ;; `module-capability-resources'
        (funcall (car managed) 20))
      (eval-with-scoped-value
       (list 'TRANSFER "john" "jose")
       expr)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; require-capability

;;; EXPANDS TO
(require-capabality (TRANSFER "john" "jose"))

(unless (lookup-capabality-token-in-current-scope
         'TRANSFER (list "john" "jose"))
  (error "capability X unavailable"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; If I implement these things functionally, using lambda terms for caps

;; Primitives:
;;
;; These manage the "resources" in the evaluation environment:
;; - allocate
;; - allocated-p
;; - reserve

;; These manage the "capabilities" in the evaluation environment:
;; - grant
;; - granted-p
;; - with-scoped-value

(defmacro defcap (name args &rest body)
  (if (eq (car body) '@managed)
      (let* ((v (cadr body))
             (f (caddr body))
             (b (cdddr body))
             (a (remove v args)))
        `(defun ,name ,(append args (list '&optional 'install))
           (if install
               (unless (allocated-p (quote ,name) (list ,@a))
                 (allocate (quote ,name) (list ,@a) ,f ,v))
             (unless (granted-p (quote ,name) (list ,@a))
               ,@b
               (reserve (quote ,name) (list ,@a) ,v)
               (grant (quote ,name) (list ,@a))))))
    `(defun ,name ,args
       (unless (granted-p (quote ,name) (list ,@args))
         ,@body
         (grant (quote ,name) (list ,@args))))))

(defmacro with-capability (cap &rest body)
  `(if (granted-p (quote ,(car cap)) (list ,@(cdr cap)))
       (progn
         ,@body)
     (with-scoped-value ,cap ,@body)))

(defmacro require-capability (cap)
  `(unless (granted-p (quote ,(car cap)) (list ,@(cdr cap)))
     (error "capability has not been granted")))

(defcap ALLOW-ENTRY (user-id)
  (assert (= user-id "jose")))

(defcap TRANSFER (from to amount)
  @managed amount TRANSFER-mgr
  (assert (!= from to))
  ;; (compose-capability (WITHDRAW from))
  ;; (compose-capability (DEPOSIT from))
  )

(with-capability (TRANSFER "john" "jose" 100) expr)

(require-capability (TRANSFER "john" "jose"))
