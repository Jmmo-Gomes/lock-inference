(*
open OUnit2
open Lib
open Roperation
open ResourceGroup
open ROperationsMapGeneration
open Mapping
(*
let rec checkGroupsLastRelease (set:ResourceGroup.resourceGroup list) guard  = 
   match set with 
   | [] -> false
   | x :: xs -> 

      let rec checkRopList guard (ropList:rOp list) = 
         match ropList with
         | [] -> false
         | x :: xs ->
            if x.r = guard && x.op = 7 then 
               true
            else 
               checkRopList guard xs in
         
         if (checkRopList guard x.ropList ) then
            true
         else checkGroupsLastRelease xs guard 

 *)
let rop = {op= 7; r = 200 } 
let rop2 = {op = 2; r = 200} 
let rop3 = {op = 5; r = 100}
let rGroup = {id = 100; ropList = [rop;rop2]}
let rGroup1 = {id = 200; ropList = [rop3]}

let checkGroupsLastWriteTest = 
  let set = [rGroup; rGroup1] in 
  let guard = 200 in 
  let result = LockGeneration.checkGroupsLastRelease set guard in
  result
let checkGroupsLastWriteTest2 = 
   let set = [ rGroup1] in 
   let guard = 200 in 
   let result = LockGeneration.checkGroupsLastRelease set guard in
   result
  (* let checkLastWrite (roMap:ResourceGroup.resourceGroup list ResourceGroupMap.t) guard (guardRAccess:Access.resourceAccess)= 
      let guardLastWrite = guardRAccess.lastWrite in 
      computeReleaseBindings guardLastWrite roMap guard
      *)

   let checkLastWriteTest = 
      let rop1 = {op = 7; r = 300 } in 
      let rop2 = {op = 7; r = 100 } in 
      let rop3 = {op = 7; r = 200 } in 
      let rGroup1 = {id = 1; ropList = [rop1]} in 
      let rGroup2 = {id = 2; ropList = [rop2]} in 
      let rGroup3 = {id = 3; ropList = [rop3]} in 
      let roMap = IntMap.empty in 
      let roMap = IntMap.add 7 [rGroup1] roMap in
      let roMap = IntMap.add 8 [rGroup2] roMap in
      let roMap = IntMap.add 9 [rGroup3] roMap in
      let labelsRes = [1; -1; -1; 3; 7] in 
      let resAccess = Resource.Access.resourceAccessCons labelsRes in
      LockGeneration.checkLastWrite roMap 300 resAccess

   let checkLastWriteTest2 = 
         let rop1 = {op = 7; r = 300 } in 
         let rop2 = {op = 7; r = 100 } in 
         let rop3 = {op = 7; r = 200 } in 
         let rop4 = {op = 7; r = 300 } in 
         let rGroup1 = {id = 1; ropList = [rop1]} in 
         let rGroup2 = {id = 2; ropList = [rop2]} in 
         let rGroup3 = {id = 3; ropList = [rop3; rop4]} in 
         let roMap = IntMap.empty in 
         let roMap = IntMap.add 7 [rGroup1] roMap in
         let roMap = IntMap.add 8 [rGroup2] roMap in
         let roMap = IntMap.add 9 [rGroup3] roMap in
         let labelsRes = [1; -1; -1; 3; 7] in 
         let resAccess = Resource.Access.resourceAccessCons labelsRes in
         LockGeneration.checkLastWrite roMap 300 resAccess

      (* Test where resource300 is guarded by 100 on its read lock*)
      let globalTest1 = 
         let rAccess100 = Resource.Access.resourceAccessCons [1; 1; 5; -1; -1] in 
         let rAccess200 = Resource.Access.resourceAccessCons [1; -1; -1; 2; 6] in 
         let rAccess300 = Resource.Access.resourceAccessCons [1; 3; 4; -1; -1] in 

         let rop1 = {op = 2; r = 100 } in 
         let rop2 = {op = 4; r = 200 } in 
         let rop3 = {op = 2; r = 300 } in 
         let rop4 = {op = 7; r = 300 } in 
         let rop5 = {op = 7; r = 100 } in 
         let rop6 = {op = 7; r = 200 } in 

         let rGroup1 = {id = 1; ropList = [rop1]} in 
         let rGroup2 = {id = 2; ropList = [rop2]} in 
         let rGroup3 = {id = 3; ropList = [rop3]} in 
         let rGroup4 = {id = 4; ropList = [rop4]} in 
         let rGroup5 = {id = 5; ropList = [rop5]} in 
         let rGroup6 = {id = 6; ropList = [rop6]} in 

         let roMap = IntMap.empty in 
         let roMap = IntMap.add 1 [rGroup1] roMap in
         let roMap = IntMap.add 2 [rGroup2] roMap in
         let roMap = IntMap.add 3 [rGroup3] roMap in
         let roMap = IntMap.add 4 [rGroup4] roMap in
         let roMap = IntMap.add 5 [rGroup5] roMap in
         let roMap = IntMap.add 6 [rGroup6] roMap in

         let resource1 = Resource.ResourceClass.resourceCons 100 1 1 1 4 in 
         let resource2 = Resource.ResourceClass.resourceCons 200 1 1 1 4 in 
         let resource3 = Resource.ResourceClass.resourceCons 300 1 1 1 4 in 

         let resource3 = Resource.ResourceClass.setGuard 100 resource3 in
         
         let resourceMap = IntMap.empty in
         let resourceMap = IntMap.add 100 resource1 resourceMap in 
         let resourceMap = IntMap.add 200 resource2 resourceMap in 
         let resourceMap = IntMap.add 300 resource3 resourceMap in 
      
         let (ramap:Resource.Access.resourceAccess ResourceMethodsMap.t) = ResourceAcessHashMap.empty in 
         let ramap = ResourceAcessHashMap.add 100 rAccess100 ramap in 
         let ramap = ResourceAcessHashMap.add 200 rAccess200 ramap in 
         let ramap = ResourceAcessHashMap.add 300 rAccess300 ramap in 

         print_string " start of test \n";
         LockGeneration.lockGeneration roMap resourceMap ramap 

      
      (*  Test where resource300 is guarded by 100 on its write lock**)
      let globalTest2 = 
         let rAccess100 = Resource.Access.resourceAccessCons [1; -1; -1; 1; 5] in 
         let rAccess200 = Resource.Access.resourceAccessCons [1; -1; -1; 2; 6] in 
         let rAccess300 = Resource.Access.resourceAccessCons [1; 3; 4; -1; -1] in 

         let rop1 = {op = 4; r = 100 } in 
         let rop2 = {op = 4; r = 200 } in 
         let rop3 = {op = 2; r = 300 } in 
         let rop4 = {op = 7; r = 300 } in 
         let rop5 = {op = 7; r = 100 } in 
         let rop6 = {op = 7; r = 200 } in 

         let rGroup1 = {id = 1; ropList = [rop1]} in 
         let rGroup2 = {id = 2; ropList = [rop2]} in 
         let rGroup3 = {id = 3; ropList = [rop3]} in 
         let rGroup4 = {id = 4; ropList = [rop4]} in 
         let rGroup5 = {id = 5; ropList = [rop5]} in 
         let rGroup6 = {id = 6; ropList = [rop6]} in 

         let roMap = ResourceOperationsMap.empty in 
         let roMap = ResourceOperationsMap.add 1 [rGroup1] roMap in
         let roMap = ResourceOperationsMap.add 2 [rGroup2] roMap in
         let roMap = ResourceOperationsMap.add 3 [rGroup3] roMap in
         let roMap = ResourceOperationsMap.add 4 [rGroup4] roMap in
         let roMap = ResourceOperationsMap.add 5 [rGroup5] roMap in
         let roMap = ResourceOperationsMap.add 6 [rGroup6] roMap in

         let resource1 = Resource.ResourceClass.resourceCons 100 1 1 1 4 in 
         let resource2 = Resource.ResourceClass.resourceCons 200 1 1 1 4 in 
         let resource3 = Resource.ResourceClass.resourceCons 300 1 1 1 4 in 

         let resource3 = Resource.ResourceClass.setGuard 100 resource3 in
         
         let resourceMap = ResourceMap.empty in
         let resourceMap = ResourceMap.add 100 resource1 resourceMap in 
         let resourceMap = ResourceMap.add 200 resource2 resourceMap in 
         let resourceMap = ResourceMap.add 300 resource3 resourceMap in 
      
         let (ramap:Resource.Access.resourceAccess ResourceMethodsMap.t) = ResourceAcessHashMap.empty in 
         let ramap = ResourceAcessHashMap.add 100 rAccess100 ramap in 
         let ramap = ResourceAcessHashMap.add 200 rAccess200 ramap in 
         let ramap = ResourceAcessHashMap.add 300 rAccess300 ramap in 

         print_string " start of test \n";
         LockGeneration.lockGeneration roMap resourceMap ramap 

      let globalTest3 = 
         let rAccess100 = Resource.Access.resourceAccessCons [1; -1; -1; 1; 6] in 
         let rAccess200 = Resource.Access.resourceAccessCons [1; -1; -1; 2; 5] in 
         let rAccess300 = Resource.Access.resourceAccessCons [1; 3; 4; -1; -1] in 

         let rop1 = {op = 4; r = 100 } in 
         let rop2 = {op = 4; r = 200 } in 
         let rop3 = {op = 2; r = 300 } in 
         let rop4 = {op = 7; r = 300 } in 
         let rop5 = {op = 7; r = 200 } in 
         let rop6 = {op = 7; r = 100 } in 

         let rGroup1 = {id = 1; ropList = [rop1]} in 
         let rGroup2 = {id = 2; ropList = [rop2]} in 
         let rGroup3 = {id = 3; ropList = [rop3]} in 
         let rGroup4 = {id = 4; ropList = [rop4]} in 
         let rGroup5 = {id = 5; ropList = [rop5]} in 
         let rGroup6 = {id = 6; ropList = [rop6]} in 

         let roMap = ResourceOperationsMap.empty in 
         let roMap = ResourceOperationsMap.add 1 [rGroup1] roMap in
         let roMap = ResourceOperationsMap.add 2 [rGroup2] roMap in
         let roMap = ResourceOperationsMap.add 3 [rGroup3] roMap in
         let roMap = ResourceOperationsMap.add 4 [rGroup4] roMap in
         let roMap = ResourceOperationsMap.add 5 [rGroup5] roMap in
         let roMap = ResourceOperationsMap.add 6 [rGroup6] roMap in

         let resource1 = Resource.ResourceClass.resourceCons 100 1 1 1 4 in 
         let resource2 = Resource.ResourceClass.resourceCons 200 1 1 1 4 in 
         let resource3 = Resource.ResourceClass.resourceCons 300 1 1 1 4 in 

         let resource2 = Resource.ResourceClass.setGuard 100 resource2 in
         let resource3 = Resource.ResourceClass.setGuard 100 resource3 in
         
         let resourceMap = ResourceMap.empty in
         let resourceMap = ResourceMap.add 100 resource1 resourceMap in 
         let resourceMap = ResourceMap.add 200 resource2 resourceMap in 
         let resourceMap = ResourceMap.add 300 resource3 resourceMap in 
      
         let (ramap:Resource.Access.resourceAccess ResourceMethodsMap.t) = ResourceAcessHashMap.empty in 
         let ramap = ResourceAcessHashMap.add 100 rAccess100 ramap in 
         let ramap = ResourceAcessHashMap.add 200 rAccess200 ramap in 
         let ramap = ResourceAcessHashMap.add 300 rAccess300 ramap in 

         print_string " start of test \n";
         LockGeneration.lockGeneration roMap resourceMap ramap 

         
      let globalTest4 = 
         let rAccess100 = Resource.Access.resourceAccessCons [1; 2; 7; 1; 6] in 
         let rAccess200 = Resource.Access.resourceAccessCons [1; -1; -1; 2; 5] in 
         let rAccess300 = Resource.Access.resourceAccessCons [1; 3; 4; -1; -1] in 

         let rop1 = {op = 4; r = 100 } in 
         let rop21 = {op = 2; r = 100 } in 
         let rop22 = {op = 4; r = 200 } in 
         let rop3 = {op = 2; r = 300 } in 
         let rop4 = {op = 7; r = 300 } in 
         let rop5 = {op = 7; r = 200 } in 
         let rop6 = {op = 7; r = 100 } in 
         let rop7 = {op = 7; r = 100 } in 

         let rGroup1 = {id = 1; ropList = [rop1]} in 
         let rGroup2 = {id = 2; ropList = [rop21;rop22 ]} in 
         let rGroup3 = {id = 3; ropList = [rop3]} in 
         let rGroup4 = {id = 4; ropList = [rop4]} in 
         let rGroup5 = {id = 5; ropList = [rop5]} in 
         let rGroup6 = {id = 6; ropList = [rop6]} in 
         let rGroup7 = {id = 7; ropList = [rop7]} in 

         let roMap = ResourceOperationsMap.empty in 
         let roMap = ResourceOperationsMap.add 1 [rGroup1] roMap in
         let roMap = ResourceOperationsMap.add 2 [rGroup2] roMap in
         let roMap = ResourceOperationsMap.add 3 [rGroup3] roMap in
         let roMap = ResourceOperationsMap.add 4 [rGroup4] roMap in
         let roMap = ResourceOperationsMap.add 5 [rGroup5] roMap in
         let roMap = ResourceOperationsMap.add 6 [rGroup6] roMap in
         let roMap = ResourceOperationsMap.add 7 [rGroup7] roMap in

         let resource1 = Resource.ResourceClass.resourceCons 100 1 1 1 4 in 
         let resource2 = Resource.ResourceClass.resourceCons 200 1 1 1 4 in 
         let resource3 = Resource.ResourceClass.resourceCons 300 1 1 1 4 in 

         let resource2 = Resource.ResourceClass.setGuard 100 resource2 in
         let resource3 = Resource.ResourceClass.setGuard 100 resource3 in
         
         let resourceMap = ResourceMap.empty in
         let resourceMap = ResourceMap.add 100 resource1 resourceMap in 
         let resourceMap = ResourceMap.add 200 resource2 resourceMap in 
         let resourceMap = ResourceMap.add 300 resource3 resourceMap in 
      
         let (ramap:Resource.Access.resourceAccess ResourceMethodsMap.t) = ResourceAcessHashMap.empty in 
         let ramap = ResourceAcessHashMap.add 100 rAccess100 ramap in 
         let ramap = ResourceAcessHashMap.add 200 rAccess200 ramap in 
         let ramap = ResourceAcessHashMap.add 300 rAccess300 ramap in 

         print_string "Start of test \n";
         LockGeneration.lockGeneration roMap resourceMap ramap 





let lockTests = "test suite for lockGeneration" >::: [
  "1- First Test checkGroupsLastWrite" >:: (fun _ -> assert_equal 
  true
  (checkGroupsLastWriteTest) ~printer:string_of_bool);
  "2- Second Test checkGroupsLastWrite" >:: (fun _ -> assert_equal 
  false
  (checkGroupsLastWriteTest2) ~printer:string_of_bool);
  "3- First Test checkLastWriteTest" >:: (fun _ -> assert_equal 
  true
  (checkLastWriteTest) ~printer:string_of_bool);
  "4- Second Test checkLastWriteTest" >:: (fun _ -> assert_equal 
  false
  (checkLastWriteTest2) ~printer:string_of_bool);
  "5- Global Test" >:: (fun _ -> assert_equal 
  true
  (globalTest1) ~printer:string_of_bool);
  "6- Global Test2" >:: (fun _ -> assert_equal 
  true
  (globalTest2) ~printer:string_of_bool);
  "6- Global Test3" >:: (fun _ -> assert_equal 
  true
  (globalTest3) ~printer:string_of_bool);
  "6- Global Test4" >:: (fun _ -> assert_equal 
  false
  (globalTest4) ~printer:string_of_bool);
  


  
]

let _ = run_test_tt_main lockTests*)