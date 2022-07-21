;; (put 'with-capability 'lisp-indent-function 'defun)
;; (put 'require-capability 'lisp-indent-function 'defun)
;; (put 'defcap 'lisp-indent-function 'defun)

(module example1 gov

  (defcap FOO_CALLABLE (value:integer)
    (enforce (> value 0) "Value must be greater than zero"))

  (defcap BAR_CALLABLE (value:integer)
    (enforce (< value 0) "Value must be less than zero"))

  (defun entry (value:integer)
    (if (> value 0)
        (with-capability (FOO_CALLABLE value)
          (foo value))
        (if (< value 0)
            (with-capability (BAR_CALLABLE value)
              (bar value))
            (print "entry ignoring a zero value"))))

  (defun foo (value:integer)
    "Foo never deals with negative numbers or zero."
    (require-capability (FOO_CALLABLE value))
    (print value))

  (defun bar (value:integer)
    "Bar never deals with positive numbers or zero."
    (require-capability (BAR_CALLABLE value))
    (print value)))
