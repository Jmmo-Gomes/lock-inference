open OUnit2
open Lib
open Resource

let tests = "test suite for resourceAccessCons" >::: [
  "1st Test" >:: (fun _ -> assert_equal 
  {Access.first = -1; Access.firstRead = -1; Access.lastRead = -1; Access.firstWrite = -1; Access.lastWrite = -1 } 
  (Access.resourceAccessCons [-1; -1; -1; -1; -1]));
  "2nd Test" >:: (fun _ -> assert_equal 
  {Access.first = 2; Access.firstRead = 1; Access.lastRead = 0; Access.firstWrite = 2; Access.lastWrite = 3 } 
  (Access.resourceAccessCons [2; 1; 0; 2; 3]));
  "3rd Test" >:: (fun _ -> assert_equal 
  {Access.first = -3; Access.firstRead = 2; Access.lastRead = 5; Access.firstWrite = 7; Access.lastWrite = 10 } 
  (Access.resourceAccessCons [3; 2; 5; 7; 10]));
]

let _ = run_test_tt_main tests