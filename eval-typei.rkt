Assignment: Type Inferrer
Name: Andrew Huff and Adrian Foong

Instructions:
* Open this file in DrRacket (or your favorite plain-text editor) and add your answers
  at the end of each line for each question. If you want to add more explanation or
  justification, you may add one or more lines under the question.  Remember to add
  your name as well.  Once complete, submit this to Learning Suite as a plain text file.
* For the questions asking about function correctness, indicate Yes (Y) or No (N)
  depending on whether the function meets ALL specifications.
* For each of the documentation questions, indicate Yes (Y) or No (N) based on whether
  the function has both contract and purpose statements.
* For each of the test case questions, indicate the line number of the corresponding
  test (or tests) using "L" and the number of the line.  For example, a test on
  line 61 of the file would be "L61".  If you don't have a particular test, put "N".
* If you need to add any more explanation of justification, just add it on a line
  underneath the respective question.

Function: alpha-vary
 * Is the function correct? Yes
 * Is the function documented correctly (i.e. contract and purpose statement)? Yes
 * Is there an example of alpha-varying a number expression properly? 457
 * Is there an example of alpha-varying a true expression properly? 459
 * Is there an example of alpha-varying a false expression properly? 461
 * Is there an example of alpha-varying a + expression properly? 463
 * Is there an example of alpha-varying a - expression properly? 465
 * Is there an example of alpha-varying a * expression properly? 467
 * Is there an example of alpha-varying a iszero expression properly? 470
 * Is there an example of alpha-varying a bif expression properly? 472
 * Is there an example of alpha-varying a id expression properly? 475
 * Is there an example of alpha-varying a with expression properly? 510
 * Is there an example of alpha-varying a rec expression properly? 477
 * Is there an example of alpha-varying a fun expression properly? 479
 * Is there an example of alpha-varying a app expression properly? 481
 * Is there an example of alpha-varying a tempty expression properly? 484
 * Is there an example of alpha-varying a tcons expression properly? 486
 * Is there an example of alpha-varying a tempty? expression properly? 488
 * Is there an example of alpha-varying a tfirst expression properly? 490
 * Is there an example of alpha-varying a trest expression properly? 492

Function: generate-constraints
 * Is the function correct? Yes
 * Is the function documented correctly (i.e. contract and purpose statement)? Yes
 * Is there an example of generating constraints for a number expression? 753
 * Is there an example of generating constraints for a true expression? 765
 * Is there an example of generating constraints for a false expression? 775
 * Is there an example of generating constraints for a + expression? 793
 * Is there an example of generating constraints for a - expression? 813
 * Is there an example of generating constraints for a * expression? 833
 * Is there an example of generating constraints for a iszero expression? 850
 * Is there an example of generating constraints for a bif expression? 887
 * Is there an example of generating constraints for a id expression? 901
 * Is there an example of generating constraints for a with expression? 942
 * Is there an example of generating constraints for a rec expression? 1004
 * Is there an example of generating constraints for a fun expression? 1053
 * Is there an example of generating constraints for a app expression? 1073
 * Is there an example of generating constraints for a tempty expression? 1087
 * Is there an example of generating constraints for a tcons expression? 1109
 * Is there an example of generating constraints for a tempty? expression? 1245
 * Is there an example of generating constraints for a tfirst expression? 1155
 * Is there an example of generating constraints for a trest expression? 1199

Function: unify
 * Is the function correct? Yes
 * Is the function documented correctly (i.e. contract and purpose statement)? Yes
 * Is there a Case 1 case test? 1266
 * Is there a Case 2 case test? 1275
 * Is there a Case 2 (occurs check) case test? 1285
 * Is there a Case 3 case test? 1294
 * Is there a Case 4 (lists) case test? 1301
 * Is there a Case 4 (functions) case test? 1309
 * Is there a Case 5 case test? 1314

Function: infer-type
 * Is the function correct? Yes
 * Is the function documented correctly (i.e. contract and purpose statement)? Yes
 * Does infer-type allow through runtime errors? Yes (e.g. L1339)

 Expression:  num
 * Is there an example of infer-type on a correct num expression? 757

 Expression:  true
 * Is there an example of infer-type on a correct true expression? 767

 Expression:  false
 * Is there an example of infer-type on a correct false expression? 777

 Expression:  +
 * Is there an example of infer-type on a correct + expression? 797
 * Is there a test case for a lhs error? 1470
 * Is there a test case for a rhs error? 1467

 Expression:  -
 * Is there an example of infer-type on a correct - expression? 817
 * Is there a test case for a lhs error (not a number)? 1476
 * Is there a test case for a rhs error (not a number)? 1473

 Expression:  *
 * Is there an example of infer-type on a correct * expression? 837
 * Is there a test case for a lhs error (not a number)? 1482
 * Is there a test case for a rhs error (not a number)? 1479

 Expression:  iszero
 * Is there an example of infer-type on a correct iszero expression? 854
 * Is there a test case for an input that is not a number? 1486

 Expression:  bif
 * Is there an example of infer-type on a correct bif expression? 891
 * Is there a test case for a non-boolean conditional error? 1490
 * Is there a test case for a branch return value mismatch error? 1493

 Expression:  id
 * Is there an example of infer-type on a correct id expression? 1342
 * Is there a test case for an unbound identifier? 1500

 Expression:  with
 * Is there an example of infer-type on a correct with expression? 946
 * Is there a test case for a mis-use of a bound variable? 1504

 Expression:  rec
 * Is there an example of infer-type on a correct rec expression? 1008
 * Is there a test case for a mis-use of a bound variable in bexpr? 1509
 * Is there a test case for a mis-use of a bound variable in body? 1507

 Expression:  fun
 * Is there an example of infer-type on a correct fun expression? 1057
 * Is there a test case for a mis-use of the formal parameter? 1514

 Expression:  app
 * Is there an example of infer-type on a correct app expression? 1347
 * Is there a test case for the operator not a function? 1517
 * Is there a test case for a wrong argument? 1519

 Expression:  tempty
 * Is there an example of infer-type on a correct tempty expression? 1091

 Expression:  tcons
 * Is there an example of infer-type on a correct tcons expression? 1113
 * Is there a test case for an element mismatch? 1523
 * Is there a test case for not a list? 1525

 Expression:  tempty?
 * Is there an example of infer-type on a correct tempty? expression? 1249
 * Is there a test case for not a list? 1529

 Expression:  tfirst
 * Is there an example of infer-type on a correct tfirst expression? 1159
 * Is there a test case for not a list? 1533

 Expression:  trest
 * Is there an example of infer-type on a correct trest expression? 1203
 * Is there a test case for not a list? 1536

Extra Credit:
 * Is there a test case for A -> B from infer-type? 1462

