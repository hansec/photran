! Controlled DO loop must be selected for refactoring.
! Test invalid selection that refactoring will no proceed.

PROGRAM TestInvalidSelection
  REAL :: counter, sum
  sum = 0.0
  DO counter = 1.2, 1.8, 0.1
    sum = sum + counter
  END DO
  PRINT *, sum                  !<<<<< 10,3,10,15, 0, fail-initial
END PROGRAM TestInvalidSelection
