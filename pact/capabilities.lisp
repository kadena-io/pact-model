;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; defcap

(defcap TRANSFER (from:string to:string amount:integer)
  @managed amount TRANSFER-mgr
  (assert (!= from to))
  (compose-capability (WITHDRAW from))
  (compose-capability (DEPOSIT from)))

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
