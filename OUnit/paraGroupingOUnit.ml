open Lib
open OUnit2
open Mapping
open Roperation
open ResourceGroup


  let removeTestRopListEmpty label =
    let (rop1:Roperation.rOp) = { r = 1000; op = 2} in 
    let ropList2 = [rop1] in
    let rGroup2 = {id = 2; ropList = ropList2} in 
    let rGroupList = [rGroup2] in 
    let romap = IntMap.empty in 
    let romap = IntMap.add label rGroupList romap in 
    let rGroup = ResourceGroup.remove rop1 rGroup2 in
    let newRomap = ParameterGrouping.removeR label rGroup romap in 
    if IntMap.mem label newRomap then false else true

     

let checkSBEtest = 
  let roMap = IntMap.empty in

  let rOp1 = {op = 2; r = 1} in 
  let rOp2 = {op = 7; r = 2} in 
  let rOp3 = {op = 3; r = 3} in 

  let rGroup1 = {id = 1; ropList = [rOp1]} in
  let rGroup2 = {id = 2; ropList = [rOp2;rOp3]} in 

  let newSet1 = [rGroup1;rGroup2] in 
  let label = 1 in 

  let roMap = IntMap.add label newSet1 roMap in 

  let resource2 = 3 in 
  let foundSBE = false in 
  let finished = false in

  let roMap, foundSBE, finished = ParameterGrouping.checkSBE newSet1 resource2 label roMap foundSBE finished in 

  let set = IntMap.find 1 roMap in 

  if List.length (List.nth set 1).ropList < List.length rGroup2.ropList && foundSBE = true && finished = true then 
    true
  else false

  let checkSBEtest2 = 
    let roMap = IntMap.empty in
  
    let rOp1 = {op = 2; r = 1} in 
    let rOp2 = {op = 7; r = 2} in 
    let rOp3 = {op = 3; r = 3} in 
    let rOp4 = {op = 3; r = 4} in 
  
    let rGroup1 = {id = 1; ropList = [rOp1]} in
    let rGroup2 = {id = 2; ropList = [rOp2;rOp3]} in 
    let rGroup3 = {id = 3; ropList = [rOp4]} in
  
    let rGroupSet1 = [rGroup1;rGroup2] in 
    let rGroupSet2 = [rGroup3] in 
    let label1 = 1 in
    let label5 = 5 in 
  
    let roMap = IntMap.add label1 rGroupSet1 roMap in 
    let roMap = IntMap.add label5 rGroupSet2 roMap in 
  
    let resource2 = 4 in 
    let foundSBE = false in 
    let finished = false in
  
    let newROMap, foundSBE, finished = ParameterGrouping.checkSBE rGroupSet2 resource2 label5 roMap foundSBE finished in 
  
    if IntMap.mem label5 newROMap = false  && foundSBE = true && finished = true then 
      true
    else false

    let checkSBEtest3 = 
      let roMap = IntMap.empty in
    
      let rOp1 = {op = 2; r = 1} in 
      let rOp3 = {op = 3; r = 3} in 
      let rOp4 = {op = 3; r = 4} in 
    
      let rGroup1 = {id = 1; ropList = [rOp1]} in
      let rGroup2 = {id = 2; ropList = [rOp3]} in 
      let rGroup3 = {id = 3; ropList = [rOp4]} in
    
      let rGroupSet1 = [rGroup1;rGroup2] in 
      let rGroupSet2 = [rGroup3] in 
      let label1 = 1 in
      let label5 = 5 in 
    
      let roMap = IntMap.add label1 rGroupSet1 roMap in 
      let roMap = IntMap.add label5 rGroupSet2 roMap in 
    
      let resource2 = 3 in 
      let foundSBE = false in 
      let finished = false in
    
      let newROMap, foundSBE, finished = ParameterGrouping.checkSBE rGroupSet1 resource2 label1 roMap foundSBE finished in 
    
      let newSet = IntMap.find label1 newROMap in  
      if List.length newSet < List.length rGroupSet1  && foundSBE = true && finished = true then 
        true
      else false

    

  let checkConflictTest =
    let hasR2 = false in 
    let rOp1 = {op = 4; r = 2} in 
    let rOp2 = {op = 5; r = 2} in 
    let r1 = Resource.ResourceClass.make_resource 3 30 0 false 3 3 true in 
    let r2 = Resource.ResourceClass.make_resource 6 30 0 false 3 6 true in 
    let parameters = ParameterGrouping.Parameters.empty in 
    let label2 = 4 in 
    let roMap = IntMap.empty in 
    let handled = ParameterGrouping.Handled.empty in 
    let keys = [3;4;5] in

    let parameters = ParameterGrouping.Parameters.add r1.position parameters in 
    let parameters = ParameterGrouping.Parameters.add r2.position parameters in 

    let rGroup1 ={id = 1; ropList = [rOp1]} in 
    let rGroup2 = { id = 2; ropList = [rOp2]} in

    let roMap = IntMap.add label2 [rGroup2] roMap in 
    let roMap = IntMap.add 2 [rGroup1] roMap in 

    let _, _ , newHandled = ParameterGrouping.checkConflict hasR2 rOp1.op rOp2 r1 r2 parameters label2 roMap handled keys in 
    if ParameterGrouping.Handled.cardinal newHandled > ParameterGrouping.Handled.cardinal handled then
      true
    else false


   let testAddToParameters = 
    let parameters = ParameterGrouping.Parameters.empty in 
    let roMap = IntMap.empty in 
    let resourceMap = IntMap.empty in 
    let keys = [1;2;3;4;5] in 

    let resource1 : Resource.ResourceClass.resource = {position = 1; ty = 12341; vis = 0; nature = false; whatIs= 3; guardedBy = 1; isParameter= true} in 
    let resource2 : Resource.ResourceClass.resource = {position = 2; ty = 12341; vis = 0; nature = true; whatIs= 3; guardedBy = 1; isParameter= true} in 
    let resource3 : Resource.ResourceClass.resource = {position = 3; ty = 12341; vis = 0; nature = false; whatIs= 3; guardedBy = 1; isParameter= true} in 
    let resource4 : Resource.ResourceClass.resource = {position = 4; ty = 12341; vis = 0; nature = false; whatIs= 3; guardedBy = 1; isParameter= false} in 
    let resource5 : Resource.ResourceClass.resource = {position = 5; ty = 12341; vis = 0; nature = false; whatIs= 3; guardedBy = 1; isParameter= true} in 
    let resource6 : Resource.ResourceClass.resource = {position = 6; ty = 12341; vis = 0; nature = false; whatIs= 3; guardedBy = 1; isParameter= false} in 

    let resourceMap = IntMap.add 1 resource1 resourceMap in
    let resourceMap = IntMap.add 2 resource2 resourceMap in 
    let resourceMap = IntMap.add 3 resource3 resourceMap in 
    let resourceMap = IntMap.add 4 resource4 resourceMap in 
    let resourceMap = IntMap.add 5 resource5 resourceMap in 
    let resourceMap = IntMap.add 6 resource6 resourceMap in

    let rOp1 = {op = 2; r = 1} in 
    let rOp2 = {op = 2; r = 2} in 
    let rOp3 = {op = 3; r = 3} in 
    let rOp4 = {op = 3; r = 4} in 
    let rOp5 = {op = 2; r = 5} in 
    let rOp6 = {op = 4; r = 6} in 
  
    let rGroup1 = {id = 1; ropList = [rOp1]} in
    let rGroup2 = {id = 2; ropList = [rOp2]} in 
    let rGroup3 = {id = 3; ropList = [rOp3]} in
    let rGroup4 = {id = 4; ropList = [rOp4]} in
    let rGroup5 = {id = 5; ropList = [rOp5]} in
    let rGroup6 = {id = 6; ropList = [rOp6]} in
  
    let rGroupSet1 = [rGroup1;rGroup2] in 
    let rGroupSet2 = [rGroup3] in 
    let rGroupSet3 = [rGroup4] in 
    let rGroupSet4 = [rGroup5] in 
    let rGroupSet5 = [rGroup6] in 

    let label1 = 1 in
    let label2 = 2 in
    let label3 = 3 in
    let label4 = 4 in
    let label5 = 5 in 

    let roMap = IntMap.add label1 rGroupSet1 roMap in 
    let roMap = IntMap.add label2 rGroupSet2 roMap in 
    let roMap = IntMap.add label3 rGroupSet3 roMap in 
    let roMap = IntMap.add label4 rGroupSet4 roMap in
    let roMap = IntMap.add label5 rGroupSet5 roMap in
    
    let newParameters = ParameterGrouping.addToParameters keys parameters roMap resourceMap in 
    let bindings = ParameterGrouping.Parameters.cardinal newParameters in 
    if bindings = 4 then true else false


   let testAddToParameters2 = 
    let parameters = ParameterGrouping.Parameters.empty in 
    let roMap = IntMap.empty in 
    let resourceMap = IntMap.empty in 
    let keys = [1;2] in 

    let resource1 : Resource.ResourceClass.resource = {position = 1; ty = 12341; vis = 0; nature = false; whatIs= 3; guardedBy = 1; isParameter= true} in 
    let resource2 : Resource.ResourceClass.resource = {position = 2; ty = 12341; vis = 0; nature = true; whatIs= 3; guardedBy = 1; isParameter= true} in 
    let resource3 : Resource.ResourceClass.resource = {position = 3; ty = 12341; vis = 0; nature = false; whatIs= 3; guardedBy = 1; isParameter= true} in 
    let resource4 : Resource.ResourceClass.resource = {position = 4; ty = 12341; vis = 0; nature = false; whatIs= 3; guardedBy = 1; isParameter= false} in 
    let resource5 : Resource.ResourceClass.resource = {position = 5; ty = 12341; vis = 0; nature = false; whatIs= 3; guardedBy = 1; isParameter= false} in 


    let resourceMap = IntMap.add 1 resource1 resourceMap in
    let resourceMap = IntMap.add 2 resource2 resourceMap in 
    let resourceMap = IntMap.add 3 resource3 resourceMap in 
    let resourceMap = IntMap.add 4 resource4 resourceMap in 
    let resourceMap = IntMap.add 5 resource5 resourceMap in 

    let rOp1 = {op = 2; r = 1} in 
    let rOp2 = {op = 2; r = 2} in 
    let rOp3 = {op = 3; r = 3} in 
    let rOp4 = {op = 3; r = 4} in 
    let rOp5 = {op = 2; r = 5} in 
    let rOp6 = {op = 7; r = 3} in 
  
    let rGroup1 = {id = 1; ropList = [rOp1;rOp2]} in 
    let rGroup3 = {id = 3; ropList = [rOp3;rOp4;rOp5;rOp6]} in
  
    let rGroupSet1 = [rGroup1] in 
    let rGroupSet2 = [rGroup3] in 

    let label1 = 1 in
    let label2 = 2 in

    let roMap = IntMap.add label1 rGroupSet1 roMap in 
    let roMap = IntMap.add label2 rGroupSet2 roMap in 

    
    let newParameters = ParameterGrouping.addToParameters keys parameters roMap resourceMap in 
    let bindings = ParameterGrouping.Parameters.cardinal newParameters in 
    if bindings = 3 then true else false



let parameterGroupingTests = "test suite for subsumeResource" >::: [
  "RemoveTestRopListEmpty" >:: (fun _ -> assert_equal 
  true
  (removeTestRopListEmpty 3) ~printer:string_of_bool);
  "CheckSBE Test- a resource operation list is removed" >:: (fun _ -> assert_equal 
  true
  (checkSBEtest) ~printer:string_of_bool);
  "CheckSBE Test2- An entry is removed from the map " >:: (fun _ -> assert_equal 
  true
  (checkSBEtest2) ~printer:string_of_bool);
  "CheckSBE Test3- An entry is removed from the map " >:: (fun _ -> assert_equal 
  true
  (checkSBEtest3) ~printer:string_of_bool);
  "CheckConflict Test where there is a type conflict" >:: (fun _ -> assert_equal 
  true
  (checkConflictTest) ~printer:string_of_bool);
  "testAddToParameters Test where 4 are parameters">:: (fun _ -> assert_equal 
  true
  (testAddToParameters) ~printer:string_of_bool);
  "testAddToParameters2 Test where 3 are parameters">:: (fun _ -> assert_equal 
  true
  (testAddToParameters2) ~printer:string_of_bool);
]

let _ = run_test_tt_main parameterGroupingTests
